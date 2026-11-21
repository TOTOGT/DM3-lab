#!/usr/bin/env python3
"""Audit script for 'Gravity Across Scales' (Grossi 2026), sections 3-5.
Reproduces or refutes each numerical/algebraic claim. Needs numpy, scipy, sympy.
Run:  python3 audit_gravity_scales.py
Every line printed is a check; PASS/FAIL is decided here, not by the paper.
"""
import numpy as np, sympy as sp
from scipy.integrate import solve_ivp

def rhs(t, y):
    r, z = y
    return [r*(1-r*r) + 2*(r-1)*np.exp(-z), r*r - 2*(r-1)**2*np.exp(-z)]

def report(name, ok, detail=""):
    print(f"{'PASS' if ok else 'FAIL'}  {name}  {detail}")

# --- T3: saddle polynomial, roots, trace, determinant -------------------------------
x = sp.symbols('x')
p = x**3 - x**2 - 2*x + 1
report("T3 discriminant of p equals 49", sp.discriminant(p, x) == 49)
roots = sorted(float(v) for v in sp.nroots(p))
cos_roots = sorted(2*np.cos(k*np.pi/7) for k in (1, 3, 5))
report("T3 roots are 2cos(k pi/7), k=1,3,5", np.allclose(roots, cos_roots), str(np.round(roots, 6)))
rs = 2*np.cos(3*np.pi/7); zs = -np.log(rs*(1+rs)/2)
report("T3 (rs,zs) is a fixed point", np.allclose(rhs(0, [rs, zs]), 0, atol=1e-12), f"rs={rs:.6f} zs={zs:.6f}")
r, z = sp.symbols('r z')
F = r*(1-r**2) + 2*(r-1)*sp.exp(-z); G = r**2 - 2*(r-1)**2*sp.exp(-z)
J = sp.Matrix([F, G]).jacobian([r, z]).subs({r: rs, z: zs}).evalf()
report("T3 tr(J) = 2cos(2pi/7)", abs(float(J.trace()) - 2*np.cos(2*np.pi/7)) < 1e-12, f"{float(J.trace()):.9f}")
report("T3 det(J) < 0 (saddle)", float(J.det()) < 0, f"det={float(J.det()):.6f}")

# --- T2: basin boundary of r(0) depends on z(0) ------------------------------------
def collapses(r0, z0, T=80):
    ev = lambda t, y: y[0] - 1e-3
    ev.terminal = True
    s = solve_ivp(rhs, [0, T], [r0, z0], method='DOP853', rtol=1e-12, atol=1e-14, events=ev)
    return s.t_events[0].size > 0 or s.y[0, -1] < 0.5

def rstar(z0):
    lo, hi = 0.02, 1.2
    if not collapses(lo, z0) or collapses(hi, z0):
        return None
    for _ in range(50):
        mid = (lo + hi)/2
        if collapses(mid, z0): lo = mid
        else: hi = mid
    return (lo + hi)/2

print("\nBasin boundary r*(z0) (bisection on r(0), DOP853, rtol 1e-12):")
rows = {}
for z0 in (0.0, 0.2, np.log(2), 1.0, 2.0, 3.0):
    rows[z0] = rstar(z0)
    print(f"   z0 = {z0:7.4f}   r* = {rows[z0]}")
report("T2 paper's r* = 0.77594059 reproduced at z0 = 0", abs(rows[0.0] - 0.77594059) < 2e-7, f"{rows[0.0]:.9f}")
report("T2 paper's stated hypothesis z0 >= log 2 gives the same r*", abs(rows[np.log(2)] - 0.77594059) < 1e-3,
       f"r*(log 2) = {rows[np.log(2)]:.6f}")
report("T2 r* is independent of z0 (needed for it to be a constant)", len({round(v, 3) for v in rows.values()}) == 1)

# --- T1: attraction for r0 > 0.7759406, z0 >= log 2 ---------------------------------
bad = [(z0, r0) for z0 in (np.log(2), 1.0, 2.0, 4.0) for r0 in np.linspace(0.78, 3.0, 25) if collapses(r0, z0)]
report("T1 grid: every (r0 > 0.78, z0 >= log 2) tested attracts", not bad, f"failures: {bad[:3]}")
