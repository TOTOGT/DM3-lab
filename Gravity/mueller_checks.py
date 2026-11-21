#!/usr/bin/env python3
"""
mueller_checks.py -- symbolic checks of three steps in A. Mueller, "The Lorentz Factor as the Slope of an Additional
Spatial Coordinate ..." (Zenodo v1, 16 Nov 2026) that are not in MuellerChecks.lean (they need second derivatives of
square roots).  Run first (R24).  Units G = c = 1.

  1. Slice curvature (eq. 118): for beta^2 = rs/R the scalar curvature (3)R = (2/R^2) d(R beta^2)/dR vanishes, and
     for beta^2 = R^2/L^2 it equals 6/L^2 (a 3-sphere of radius L).
  2. Proposition 1, radial component: with N = sqrt(1 - rs/R), d/dl = (1/gamma) d/dR, the paper's claim
     N_{,ll}/N = 2 beta beta'/R holds.
  3. Interior Schwarzschild (eq. 125): N = (3 s* - s)/2, p = rho (s - s*)/(3 s* - s), s = sqrt(1 - R^2/L^2), satisfies
     the TOV potential gradient (124)  N'/N = G (m + 4 pi R^3 p) / (R^2 (1 - 2 G m / R))  and hydrostatic equilibrium
     p' = -(rho + p) N'/N, with m = (4 pi/3) rho R^3 and L^2 = 3/(8 pi rho).
NOT checked: that equations (114)/(123) are the right field equations (the paper imports them from GR).
"""
import sys, sympy as sp
FAIL = []
def check(name, ok):
    print("  [%s] %s" % ("SHOWN" if ok else "FAIL ", name))
    if not ok: FAIL.append(name)

R, rs, L, rho, G, ss = sp.symbols("R rs L rho G s_star", positive=True)

print("1. slice curvature")
b2 = rs / R
check("(2/R^2) d(R beta^2)/dR = 0 for beta^2 = rs/R", sp.simplify(2 / R**2 * sp.diff(R * b2, R)) == 0)
b2 = R**2 / L**2
check("(2/R^2) d(R beta^2)/dR = 6/L^2 for beta^2 = R^2/L^2", sp.simplify(2 / R**2 * sp.diff(R * b2, R) - 6 / L**2) == 0)

print("2. Proposition 1, radial component")
N = sp.sqrt(1 - rs / R)
gam = 1 / sp.sqrt(1 - rs / R)
beta = sp.sqrt(rs / R)
dl = lambda f: sp.diff(f, R) / gam          # d/dl, dl = gamma dR
Nll = dl(dl(N))
lhs = sp.simplify(Nll / N)
rhs = sp.simplify(2 * beta * sp.diff(beta, R) / R)
check("N_ll / N = 2 beta beta' / R", sp.simplify(lhs - rhs) == 0)
check("angular: N'/(gamma^2 R N) = beta beta'/R + beta^2/R^2", sp.simplify(
    sp.diff(N, R) / (gam**2 * R * N) - (beta * sp.diff(beta, R) / R + beta**2 / R**2)) == 0)

print("3. interior Schwarzschild (125)")
rho_ = sp.symbols("rho", positive=True)
Lq = sp.sqrt(3 / (8 * sp.pi * rho_))
s = sp.sqrt(1 - R**2 / Lq**2)
Nn = (3 * ss - s) / 2
pp = rho_ * (s - ss) / (3 * ss - s)
m = sp.Rational(4, 3) * sp.pi * rho_ * R**3
tov = sp.diff(Nn, R) / Nn - (m + 4 * sp.pi * R**3 * pp) / (R**2 * (1 - 2 * m / R))
check("N'/N = (m + 4 pi R^3 p)/(R^2 (1 - 2m/R))  [G = c = 1]", sp.simplify(tov) == 0)
hyd = sp.diff(pp, R) + (rho_ + pp) * sp.diff(Nn, R) / Nn
check("p' = -(rho + p) N'/N  (hydrostatic equilibrium)", sp.simplify(hyd) == 0)
s_surf = sp.symbols("R_star", positive=True)
check("p(R*) = 0 when s_star = s(R*)", sp.simplify(pp.subs(ss, s).subs(R, R)) == 0)
pc = sp.simplify((pp.subs(R, 0)) / rho_)
check("central pressure p_c/rho = (1 - s*)/(3 s* - 1)", sp.simplify(pc - (1 - ss) / (3 * ss - 1)) == 0)

print()
if FAIL: print("FAIL: " + "; ".join(FAIL)); sys.exit(1)
print("ALL PASS")
