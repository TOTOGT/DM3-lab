"""Anchor numbers for the Earth-Moon entry of the dm3 taxonomy (v2 of Gravity Across Scales).
Constants from standard published values (CODATA/IAU rounded); the script recomputes every derived number.
Every derived number is a Newtonian/tidal estimate, not a measurement. Control checks at the end can fail."""
import math
G=6.674e-11; c=2.998e8
M_sun=1.989e30; M_E=5.972e24; m_moon=7.342e22
R_E=6.371e6; rho_E=M_E/(4/3*math.pi*R_E**3)
R_m=1.7374e6; rho_m=m_moon/(4/3*math.pi*R_m**3)
a_E=1.496e11          # Earth-Sun distance, m
d_m=3.844e8           # Earth-Moon distance, m
rec=0.038             # observed lunar recession, m/yr (laser ranging, ~3.8 cm/yr)
yr=3.156e7

rH=a_E*(M_E/(3*M_sun))**(1/3)
roche=2.44*R_E*(rho_E/rho_m)**(1/3)
isco_E=6*G*M_E/c**2
print(f"Earth Hill radius      r_H = {rH/1e3:,.0f} km")
print(f"Moon distance / r_H        = {d_m/rH:.3f}")
print(f"Stable-prograde limit ~0.5 r_H = {0.5*rH/1e3:,.0f} km ; Moon at {d_m/(0.5*rH):.2f} of that")
print(f"Fluid Roche limit          = {roche/1e3:,.0f} km ; Moon / Roche = {d_m/roche:.1f}")
print(f"Schwarzschild ISCO (Earth) = {isco_E*100:.2f} cm")
# Hill-problem axial critical point (scaled units): W = 1.5 x^2 + 1/x -> x^3 = 1/3
x=(1/3)**(1/3)*3**(1/3); print(f"Hill L1/L2 axial critical point (W=1.5x^2+1/x, x in units a(m/M)^(1/3)) at x=3^(-1/3); in units of r_H that is {x:.4f} r_H, i.e. exactly r_H; r_H/a = {rH/a_E:.5f}")
assert abs(x-1)<1e-12
# Toy recession model, constant tidal Q: adot ~ a^(-11/2). Not a measurement; ignores solar tide and spin changes.
af=0.5*rH
t=(d_m/rec)*(2/13)*((af/d_m)**6.5-1)/1e9*1  # in Gyr (units: m/(m/yr)=yr)
print(f"Toy time to reach 0.5 r_H at constant-Q: {t:.0f} Gyr  (compare Sun age ~4.6 Gyr, so unreachable; the point is the geometry, not a forecast)")
# Mutual motion, radiation, mass scaling (added 21 Nov 2026)
bary=d_m*m_moon/(M_E+m_moon)
P_gw=32/5*G**4*(M_E*m_moon)**2*(M_E+m_moon)/(c**5*d_m**5)
E_orb=G*M_E*m_moon/(2*d_m)
print(f"Earth-Moon barycentre {bary/1e3:,.0f} km from Earth's centre (Earth radius {R_E/1e3:,.0f} km): inside Earth")
print(f"Quadrupole GW power, circular orbit: {P_gw:.2e} W ; naive decay time {E_orb/P_gw/yr:.1e} yr (tides dominate; GW loss irrelevant here)")
fgw=lambda M: c**3/(math.pi*6**1.5*G*M)
for name,M in (("1 Msun",M_sun),("10 Msun",10*M_sun),("Sgr A* 4.3e6 Msun",4.3e6*M_sun),("Earth",M_E)):
    print(f"  {name:18s} r_ISCO(6GM/c^2)={6*G*M/c**2:.3g} m  GM/c^3={G*M/c**3:.3g} s  GW freq at ISCO (2x orbital)={fgw(M):.3g} Hz")
print(f"  orbital speed at ISCO = c/sqrt(6) = {1/math.sqrt(6):.4f} c, independent of mass")
# controls
assert abs(isco_E*1e2 - 2.66)<0.1, "Earth ISCO should be ~2.7 cm"
assert 1.4e9 < rH < 1.6e9, "Earth Hill radius should be ~1.5e6 km"
assert 17000e3 < roche < 20000e3, "Roche limit should be ~18,000 km"
assert abs(bary/1e3-4670)<30 and bary<R_E
assert 1e-6<P_gw<1e-4
assert abs(fgw(M_sun)-4397)<30
print("controls passed")
