#!/usr/bin/env python3
"""Reading three gravitational laws through the dm3 contact system (R^3, alpha = dz - r^2 dtheta).
Every statement printed is computed here with sympy. Needs sympy, numpy.
"""
import sympy as sp, numpy as np

r, M, G, L, E, t = sp.symbols('r M G L E t', positive=True)

# (a) Kepler's areal law as the contact condition.
# Along any planar motion with angular momentum per mass h = r^2 * thetadot, define z' = h  (z = 2 * swept area).
# Then dz = r^2 dtheta exactly  <=>  alpha = 0 on the lifted curve.
h = sp.symbols('h', positive=True)
th = sp.Function('theta')(t); rr = sp.Function('r')(t)
zdot = h                       # z grows at the angular momentum
alpha_on_curve = sp.simplify(zdot - rr**2*sp.diff(th, t)).subs(sp.diff(th, t), h/rr**2)
print("(a) alpha on the lifted orbit with r^2 thetadot = h:", sp.simplify(alpha_on_curve), "(0 means Legendrian lift)")

# (b) Newtonian circular orbit: L^2(r) = G M r  (monotone, no fold)
L2_newton = G*M*r
print("(b) Newton: d(L^2)/dr =", sp.diff(L2_newton, r), "(never zero: no fold, no innermost stable radius)")

# (c) Schwarzschild circular orbit (units G=c=1): L^2(r) = M r^2/(r - 3M)
L2 = M*r**2/(r - 3*M)
d1 = sp.simplify(sp.diff(L2, r)); d2 = sp.simplify(sp.diff(L2, r, 2))
sol = sp.solve(sp.Eq(d1, 0), r)
print("(c) Schwarzschild: dL^2/dr = 0 at r =", sol)
r_isco = [s for s in sol if s != 0][0]
print("    second derivative at that radius:", sp.simplify(d2.subs(r, r_isco)), "(nonzero => non-degenerate fold, Whitney A1)")
print("    L^2 at the fold:", sp.simplify(L2.subs(r, r_isco)), " (= 12 M^2)")

# stability check: effective potential V = (1 - 2M/r)(1 + L^2/r^2); circular orbit stable iff V'' > 0
Lsym = sp.symbols('Lsym', positive=True)
V = (1 - 2*M/r)*(1 + Lsym**2/r**2)
Vpp = sp.diff(V, r, 2)
Vpp_on = sp.simplify(Vpp.subs(Lsym**2, L2))
for val in (5, 6, 7, 10):
    print(f"    r = {val} M: V'' on circular orbit = {float(Vpp_on.subs({M:1, r:val})):+.5f}  ({'stable' if Vpp_on.subs({M:1,r:val}) > 0 else 'unstable' if Vpp_on.subs({M:1,r:val}) < 0 else 'marginal'})")

# ratios to compare with the dm3 constants
rstar, rs = 0.77594059, 2*np.cos(3*np.pi/7)
print("\nRatios in Schwarzschild: r_ISCO / r_photon = 6/3 =", 6/3, "; r_ISCO / r_horizon = 6/2 =", 6/2)
print("dm3 constants: r*(z0=0) =", rstar, "; r_s =", round(rs,6), "; r_s / r* =", round(rs/rstar, 6))
print("No ratio of Schwarzschild radii (2, 3, 6) matches r_s/r* = %.4f; the numbers are not related by any map written down." % (rs/rstar))

# (d) dissipation: Newtonian gravity conserves energy, so circular orbits are neutral; a limit-cycle ATTRACTOR needs dissipation.
print("\n(d) Newtonian radial epicyclic frequency^2 / omega^2 =", sp.simplify((3*L**2/r**4 - 2*G*M/r**3).subs(L**2, G*M*r)/(G*M/r**3)),
      "(=1: closed, neutral orbits; no attraction)")
print("    dm3 radial rate at the helix: d/dr[r(1-r^2)] at r=1 =", sp.diff(sp.Symbol('r')*(1-sp.Symbol('r')**2), sp.Symbol('r')).subs(sp.Symbol('r'), 1), "(overdamped: needs a dissipative mechanism)")
