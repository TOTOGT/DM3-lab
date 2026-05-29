#!/usr/bin/env python3
"""
axle_paper_trader.py
════════════════════
TOGT / Generative Contact Mechanics — Paper Trading Bot
Strategy: Operator-order detection → limit buy → +1% limit sell
Capital preservation mode: max 2% portfolio risk per trade.

Author : Pablo Nogueira Grossi
Affil  : G6 LLC, Newark, NJ | ORCID: 0009-0000-6496-2186
Repo   : github.com/TOTOGT/AXLE

SETUP (one time)
────────────────
1. Create a FREE Alpaca account: https://alpaca.markets
2. Go to Paper Trading → API Keys → Generate
3. Copy your PAPER API key and secret into this file below
   (or set as environment variables ALPACA_KEY / ALPACA_SECRET)
4. pip install alpaca-py yfinance pandas numpy scipy

RUN
───
  python3 axle_paper_trader.py              # monitor + trade SPY
  python3 axle_paper_trader.py AAPL         # trade AAPL
  python3 axle_paper_trader.py BTC/USD      # crypto (24/7)

STRATEGY
────────
  Entry  : C→K active (squeeze + trending) with no open position
           → place LIMIT BUY at current ask
  Exit   : +1.0% above fill price → LIMIT SELL (take profit)
           OR -0.5% stop loss (capital preservation)
  Size   : 2% of portfolio equity per trade (max)
  Log    : every trade logged to axle_trades.csv
"""

import os
import sys
import time
import logging
import csv
from datetime import datetime, timezone
from pathlib import Path

import pandas as pd
import numpy as np

# ── ANSI colours ─────────────────────────────────────────────────────────────
R  = '\033[91m'; G = '\033[92m'; Y = '\033[93m'
B  = '\033[94m'; W = '\033[97m'; BO = '\033[1m'; RS = '\033[0m'

# ─────────────────────────────────────────────────────────────────────────────
# §1  CONFIGURATION — edit these or set as env vars
# ─────────────────────────────────────────────────────────────────────────────

ALPACA_KEY    = os.environ.get('ALPACA_KEY',    'YOUR_PAPER_KEY_HERE')
ALPACA_SECRET = os.environ.get('ALPACA_SECRET', 'YOUR_PAPER_SECRET_HERE')
PAPER_BASE_URL = 'https://paper-api.alpaca.markets'   # PAPER — no real money

SYMBOL          = sys.argv[1] if len(sys.argv) > 1 else 'SPY'
TAKE_PROFIT_PCT = 0.010    # +1.0% sell target
STOP_LOSS_PCT   = 0.005    # -0.5% stop loss (capital preservation)
RISK_PER_TRADE  = 0.02     # 2% of equity per trade
POLL_SECONDS    = 60        # check every 60 seconds
LOG_FILE        = 'axle_trades.csv'

# Operator thresholds (same as detection bot)
BB_SQUEEZE_PCT  = 0.25
ADX_MIN         = 20.0
FOLD_Z_THRESH   = 1.5
IPR_THRESH      = 0.5

# ─────────────────────────────────────────────────────────────────────────────
# §2  Logging setup
# ─────────────────────────────────────────────────────────────────────────────

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s  %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)
log = logging.getLogger('AXLE')

def stamp():
    return datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M:%S UTC')

# ─────────────────────────────────────────────────────────────────────────────
# §3  Trade log (CSV)
# ─────────────────────────────────────────────────────────────────────────────

def init_log():
    if not Path(LOG_FILE).exists():
        with open(LOG_FILE, 'w', newline='') as f:
            w = csv.writer(f)
            w.writerow(['timestamp','symbol','side','qty','price',
                        'order_id','sequence','pnl_usd','equity'])
    log.info(f"Trade log: {LOG_FILE}")

def write_trade(symbol, side, qty, price, order_id,
                sequence='', pnl=None, equity=None):
    with open(LOG_FILE, 'a', newline='') as f:
        w = csv.writer(f)
        w.writerow([stamp(), symbol, side, qty, price,
                    order_id, sequence, pnl or '', equity or ''])

# ─────────────────────────────────────────────────────────────────────────────
# §4  Alpaca client (graceful import)
# ─────────────────────────────────────────────────────────────────────────────

def get_alpaca_client():
    """Return trading client. Raises clear error if alpaca-py not installed."""
    try:
        from alpaca.trading.client import TradingClient
        from alpaca.trading.requests import (
            MarketOrderRequest, LimitOrderRequest,
            TakeProfitRequest, StopLossRequest
        )
        from alpaca.trading.enums import OrderSide, TimeInForce, OrderType
        return TradingClient(ALPACA_KEY, ALPACA_SECRET, paper=True)
    except ImportError:
        print(f"{R}alpaca-py not installed. Run: pip install alpaca-py{RS}")
        sys.exit(1)
    except Exception as e:
        print(f"{R}Alpaca connection error: {e}{RS}")
        print(f"  Check your ALPACA_KEY and ALPACA_SECRET.")
        print(f"  Get free paper keys at: https://alpaca.markets")
        sys.exit(1)

# ─────────────────────────────────────────────────────────────────────────────
# §5  Market data via yfinance (no Alpaca data subscription needed)
# ─────────────────────────────────────────────────────────────────────────────

def get_bars(symbol, period='5d', interval='1h'):
    """Fetch recent bars from Yahoo Finance for signal computation."""
    try:
        import yfinance as yf
        ticker = symbol.replace('/', '-')   # BTC/USD → BTC-USD for yfinance
        df = yf.download(ticker, period=period, interval=interval,
                         auto_adjust=True, progress=False)
        if df.empty:
            return None
        if isinstance(df.columns, pd.MultiIndex):
            df.columns = [col[0] for col in df.columns]
        df.columns = [c.lower() for c in df.columns]
        df = df[['open','high','low','close','volume']].dropna()
        return df
    except Exception as e:
        log.warning(f"Data fetch error: {e}")
        return None

def current_price(df):
    return float(df['close'].iloc[-1])

# ─────────────────────────────────────────────────────────────────────────────
# §6  Operator signal computation
# ─────────────────────────────────────────────────────────────────────────────

def compute_signals(df):
    close   = df['close']
    high    = df['high']
    low     = df['low']
    returns = close.pct_change()

    # C — Bollinger Band squeeze
    mid   = close.rolling(20).mean()
    std20 = close.rolling(20).std()
    bb_w  = (4 * std20) / (mid + 1e-9)
    w_min = bb_w.rolling(100, min_periods=20).min()
    w_max = bb_w.rolling(100, min_periods=20).max()
    bb_norm = float(((bb_w - w_min) / (w_max - w_min + 1e-9)).iloc[-1])

    # K — ADX
    dh = high.diff(); dl = -low.diff()
    plus_dm  = np.where((dh > dl) & (dh > 0), dh, 0.0)
    minus_dm = np.where((dl > dh) & (dl > 0), dl, 0.0)
    tr = pd.concat([high-low, (high-close.shift()).abs(),
                    (low-close.shift()).abs()], axis=1).max(axis=1)
    atr = tr.ewm(span=14, adjust=False).mean()
    pdi = 100*pd.Series(plus_dm,  index=high.index).ewm(span=14,adjust=False).mean()/(atr+1e-9)
    mdi = 100*pd.Series(minus_dm, index=high.index).ewm(span=14,adjust=False).mean()/(atr+1e-9)
    dx  = 100*(pdi-mdi).abs()/(pdi+mdi+1e-9)
    adx_val = float(dx.ewm(span=14, adjust=False).mean().iloc[-1])

    # F — fold z-score
    abs_ret   = returns.abs()
    fold_z    = float((abs_ret.rolling(5).mean() / (abs_ret.rolling(60).std()+1e-9)).iloc[-1])

    # IPR
    def _ipr(arr):
        a = arr**2
        d = np.sum(a)**2
        return np.sum(a**2)/d if d > 1e-20 else 1.0/len(arr)
    ipr = float(returns.rolling(20).apply(_ipr, raw=True).iloc[-1])

    # Operator flags
    C = bb_norm < BB_SQUEEZE_PCT
    K = adx_val > ADX_MIN
    F = fold_z  > FOLD_Z_THRESH
    U = (returns.rolling(10).std().iloc[-1] <
         0.8 * returns.rolling(60).std().iloc[-1]) and not F

    # Sequence label
    if C and K and not F:
        seq = 'C→K'        # Entry signal: constrained compression
    elif K and F:
        seq = 'K→F'        # Breakout from channel
    elif F and not K:
        seq = 'F!'         # Fold without channel — higher risk
    elif U:
        seq = 'U'          # Stabilised
    else:
        seq = '—'

    entry_signal = C and K and not F   # C→K is our entry condition

    return {
        'C': C, 'K': K, 'F': F, 'U': U,
        'bb_norm': bb_norm, 'adx': adx_val,
        'fold_z': fold_z, 'ipr': ipr,
        'sequence': seq,
        'entry_signal': entry_signal,
        'price': current_price(df)
    }

# ─────────────────────────────────────────────────────────────────────────────
# §7  Order management
# ─────────────────────────────────────────────────────────────────────────────

def get_equity(client):
    try:
        acct = client.get_account()
        return float(acct.equity)
    except:
        return 100_000.0   # fallback for display

def has_open_position(client, symbol):
    try:
        positions = client.get_all_positions()
        syms = [p.symbol for p in positions]
        return symbol in syms or symbol.replace('/', '') in syms
    except:
        return False

def has_pending_order(client, symbol):
    try:
        from alpaca.trading.requests import GetOrdersRequest
        from alpaca.trading.enums import QueryOrderStatus
        req = GetOrdersRequest(status=QueryOrderStatus.OPEN, symbols=[symbol])
        orders = client.get_orders(filter=req)
        return len(orders) > 0
    except:
        return False

def place_bracket_order(client, symbol, price, equity, sequence):
    """
    Place a bracket order:
      LIMIT BUY  at price
      LIMIT SELL at price * (1 + TAKE_PROFIT_PCT)   ← +1%
      STOP LOSS  at price * (1 - STOP_LOSS_PCT)      ← -0.5%
    Size: RISK_PER_TRADE * equity / price shares
    """
    from alpaca.trading.requests import LimitOrderRequest, TakeProfitRequest, StopLossRequest
    from alpaca.trading.enums import OrderSide, TimeInForce

    qty = max(1, int((equity * RISK_PER_TRADE) / price))
    tp  = round(price * (1 + TAKE_PROFIT_PCT), 2)
    sl  = round(price * (1 - STOP_LOSS_PCT),   2)

    log.info(f"{B}ENTRY SIGNAL{RS} {sequence} | "
             f"BUY {qty} {symbol} @ ${price:.2f} | "
             f"TP=${tp:.2f} (+1%) | SL=${sl:.2f} (-0.5%)")

    try:
        req = LimitOrderRequest(
            symbol        = symbol,
            qty           = qty,
            side          = OrderSide.BUY,
            type          = 'limit',
            limit_price   = price,
            time_in_force = TimeInForce.DAY,
            order_class   = 'bracket',
            take_profit   = TakeProfitRequest(limit_price=tp),
            stop_loss     = StopLossRequest(stop_price=sl)
        )
        order = client.submit_order(req)
        log.info(f"{G}Order submitted{RS} | ID: {order.id}")
        write_trade(symbol, 'BUY', qty, price, order.id, sequence)
        return order
    except Exception as e:
        log.error(f"{R}Order failed: {e}{RS}")
        return None

# ─────────────────────────────────────────────────────────────────────────────
# §8  Status display
# ─────────────────────────────────────────────────────────────────────────────

def print_status(sig, equity, has_pos, has_order):
    c_str = f"{B}{BO}C{RS}" if sig['C'] else 'c'
    k_str = f"{Y}{BO}K{RS}" if sig['K'] else 'k'
    f_str = f"{R}{BO}F{RS}" if sig['F'] else 'f'
    u_str = f"{G}{BO}U{RS}" if sig['U'] else 'u'

    pos_str = f"{G}POSITION OPEN{RS}" if has_pos else \
              f"{Y}ORDER PENDING{RS}" if has_order else \
              f"{W}FLAT{RS}"

    ipr_str = f"{R} ← IPR WARN{RS}" if sig['ipr'] > IPR_THRESH else ''

    entry_str = f"{G}{BO}  ← ENTRY SIGNAL{RS}" if sig['entry_signal'] else ''

    print(f"\r[{stamp()}] "
          f"${sig['price']:.2f} | "
          f"Operators: {c_str}{k_str}{f_str}{u_str} | "
          f"Seq: {sig['sequence']}{entry_str} | "
          f"BB:{sig['bb_norm']:.2f} ADX:{sig['adx']:.1f} "
          f"Fz:{sig['fold_z']:.2f} IPR:{sig['ipr']:.3f}{ipr_str} | "
          f"Equity:${equity:,.0f} | {pos_str}",
          end='', flush=True)

# ─────────────────────────────────────────────────────────────────────────────
# §9  Main loop
# ─────────────────────────────────────────────────────────────────────────────

def main():
    print(f"\n{BO}{'═'*64}{RS}")
    print(f"{BO}  AXLE PAPER TRADER — TOGT Operator-Order Strategy{RS}")
    print(f"  Symbol  : {BO}{SYMBOL}{RS}")
    print(f"  Target  : +{TAKE_PROFIT_PCT*100:.1f}% per trade (limit sell)")
    print(f"  Stop    : -{STOP_LOSS_PCT*100:.1f}% per trade (capital preservation)")
    print(f"  Risk    : {RISK_PER_TRADE*100:.0f}% equity per position")
    print(f"  Mode    : {G}{BO}PAPER TRADING — no real money{RS}")
    print(f"  Entry   : C→K active (squeeze + trending channel)")
    print(f"  Theory  : TO/TOGT | github.com/TOTOGT/AXLE")
    print(f"{BO}{'═'*64}{RS}\n")

    if ALPACA_KEY == 'YOUR_PAPER_KEY_HERE':
        print(f"{Y}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━{RS}")
        print(f"{Y}  SETUP REQUIRED:{RS}")
        print(f"  1. Go to https://alpaca.markets → Paper Trading → API Keys")
        print(f"  2. Generate a key pair (free)")
        print(f"  3. Set environment variables:")
        print(f"     export ALPACA_KEY='your_key_here'")
        print(f"     export ALPACA_SECRET='your_secret_here'")
        print(f"  4. Re-run: python3 axle_paper_trader.py")
        print(f"{Y}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━{RS}\n")
        print(f"Running in {G}SIGNAL-ONLY mode{RS} (no orders placed)...\n")
        signal_only = True
    else:
        client = get_alpaca_client()
        signal_only = False
        log.info("Connected to Alpaca paper trading account.")

    init_log()

    cycle = 0
    while True:
        cycle += 1
        try:
            # Fetch data and compute signals
            df = get_bars(SYMBOL)
            if df is None:
                log.warning("No data — retrying in 60s")
                time.sleep(POLL_SECONDS)
                continue

            sig = compute_signals(df)

            if signal_only:
                # Just print signals — no orders
                equity = 100_000.0
                print_status(sig, equity, False, False)
            else:
                equity   = get_equity(client)
                has_pos  = has_open_position(client, SYMBOL)
                has_ord  = has_pending_order(client, SYMBOL)
                print_status(sig, equity, has_pos, has_ord)

                # Entry logic
                if sig['entry_signal'] and not has_pos and not has_ord:
                    print()   # newline before order log
                    place_bracket_order(client, SYMBOL,
                                        sig['price'], equity, sig['sequence'])

            # Every 10 cycles print a full summary line
            if cycle % 10 == 0:
                print(f"\n  [{cycle} polls | {stamp()}] "
                      f"Sequence history logged to {LOG_FILE}\n")

            time.sleep(POLL_SECONDS)

        except KeyboardInterrupt:
            print(f"\n\n{Y}Stopped by user.{RS}")
            print(f"Trade log saved to: {LOG_FILE}")
            break
        except Exception as e:
            log.error(f"Loop error: {e} — retrying in 60s")
            time.sleep(POLL_SECONDS)

if __name__ == '__main__':
    main()
