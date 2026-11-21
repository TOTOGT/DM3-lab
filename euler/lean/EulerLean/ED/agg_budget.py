# Exact allowable-error budget for Section63b.prop61_core (read from Stage63a.final_arith / Stage63b.large_primes).
# total(n,E) = 21/50 + E*(2P/15+1) + L(n),  L = (4/3)*(11/5)*u^4*(2/(15P)+2/P^2+(2u^10/15+1)/u^20), u=n^(1/20), P=floor(2 n^(1/4)).
# Condition: total < 2/3.  We compute E_max(n) = (2/3 - 21/50 - L)/(2P/15+1).
import math
def parts(n):
    u=n**(1/20); P=math.floor(2*n**0.25)
    L=(4/3)*(11/5*u**4)*(2/(15*P)+2/P**2+(2*u**10/15+1)/u**20)
    return u,P,L
print("n=2m;  u;  P;  L(large primes);  E_max;  Lean-side cap .98/u^6;  sharp E=tau*sqrt(m)/(3 sigma) with sigma>=m, tau<=2sqrt(m)->use tau=2 (min):")
for n in [64**4, 10**8, 10**10, 10**12, 10**16, 10**20, 10**30]:
    u,P,L=parts(n); Emax=(2/3-21/50-L)/(2*P/15+1); m=n/2
    Esharp=2*math.sqrt(m)/(3*m)  # tau=2 lower bound shape; E ~ tau/(3 sqrt m)
    print(f"{n:.3e} u={u:.3f} P={P} L={L:.4f} Emax={Emax:.3e} cap={0.98/u**6:.3e} E_sharp(tau=2)={Esharp:.3e}")
# exponent test: allowed E ~ m^(-a); fit slope of log Emax vs log m
import numpy as np
ns=[10.0**k for k in range(20,41,4)]
for a,b in zip(ns,ns[1:]):
    ea=parts(a); eb=parts(b)
    Ea=(2/3-21/50-ea[2])/(2*ea[1]/15+1); Eb=(2/3-21/50-eb[2])/(2*eb[1]/15+1)
    print("slope of E_max in m:", (math.log(Eb)-math.log(Ea))/(math.log(b/2)-math.log(a/2)))
