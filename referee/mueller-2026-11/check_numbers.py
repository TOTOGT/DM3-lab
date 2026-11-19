#!/usr/bin/env python3
"""Recomputes the numbers quoted in Mueller (Zenodo 10.5281/zenodo.24280888), Appendix A / section 3.
Inputs are public constants (CODATA/IAU, Planck 2018 dipole 369.82 km/s). Tests arithmetic, not physics. stdlib only."""
import math, sys
G=6.67430e-11; c=299792458.0; Ms=1.98847e30; kpc=3.0856775814913673e19; GMe=3.986004418e14
bad=[]
def chk(n,ok,d=""):
    print(("PASS  " if ok else "FAIL  ")+n+(("  -- "+d) if d else "")); 
    if not ok: bad.append(n)
R=6378.1e3; d=GMe/R**3
vc=c*math.sqrt(1-1/(1+d)**2); vk=c*math.sqrt(1-1/(1+d/2)**2)
chk("A17 v_cosmo = 525,493 m/s (equatorial R)", abs(vc-525493)<2, f"{vc:.0f}")
chk("A20 v_kinematic = 371,580 m/s", abs(vk-371580)<2, f"{vk:.0f}")
chk("A32 ratio = sqrt2 to 5 digits (holds BY CONSTRUCTION: phi-1 vs (phi-1)/2, small-d limit)", abs(vc/vk-math.sqrt(2))<1e-4, f"{vc/vk:.5f}")
chk("control: ratio is sqrt2 for ANY d<<1 (d=1e-9 and d=1e-4)", all(abs(c*math.sqrt(1-1/(1+x)**2)/(c*math.sqrt(1-1/(1+x/2)**2))-math.sqrt(2))<1e-3 for x in (1e-9,1e-4)))
chk("A9/A28 within 0.5% of Planck dipole 369.82 km/s", abs(371.580/369.82-1)<0.005, f"{(371.580/369.82-1)*100:.2f}%")
M=4.44e10*Ms; Rg=8.12*kpc
chk("A25 v_orbit = 216,874 m/s equals sqrt(2GM/R) to 0.01%", abs(math.sqrt(2*G*M/Rg)-216874)/216874<1e-4, f"{math.sqrt(2*G*M/Rg):.0f}")
chk("text: Newtonian circular speed ~153 km/s; flow/circular = sqrt2", abs(math.sqrt(G*M/Rg)/1e3-153)<1 and abs(math.sqrt(2)-math.sqrt(2*G*M/Rg)/math.sqrt(G*M/Rg))<1e-12)
chk("GM/R^3 ~ 4e-31 s^-2 at the solar radius", abs(G*M/Rg**3-4e-31)/4e-31<0.1, f"{G*M/Rg**3:.2e}")
al=1/137.035999084
om=(2*GMe/R**3)**(1/3)
chk("A3 omega_earth = 0.014537 (equatorial R)", abs(om-0.014537)<2e-6, f"{om:.6f}")
chk("A4 alpha(2-alpha) within 0.0253% of omega_earth", abs(al*(2-al)/om-1)<2.6e-4, f"{(al*(2-al)/om-1)*100:.4f}%")
chk("note: 2*alpha alone is off by", abs(2*al/om-1)>3e-3, f"{(2*al/om-1)*100:.2f}%  (chosen form a(2-a) fits better; paper discloses this selection)")
H0=70e3/(1e6*3.0856775814913673e16)
chk("g0 = cH0/2pi ~ 1.1e-10 m/s^2", abs(c*H0/2/math.pi-1.1e-10)<0.05e-10, f"{c*H0/2/math.pi:.3e}")
chk("TableA3 cH0 = 6.8e-10 m/s^2", abs(c*H0-6.8e-10)<0.1e-10, f"{c*H0:.2e}")
for s_,g0,r in ((1.0,2.4,0.35),(1.31,1.5,0.22),(1.6,1.0,0.15)):
    chk(f"TableA3 s={s_}: g0/(cH0) = {r}", abs(g0*1e-10/(c*H0)-r)<0.006, f"{g0*1e-10/(c*H0):.3f}")
Ms3=6e10*Ms
for kp,exp in ((8,1e-5),(25,3e-4)):
    Rk=kp*kpc; chk(f"3.1 H0^2 R/gN at {kp} kpc ~ {exp:g}", abs(H0**2*Rk/(G*Ms3/Rk**2)/exp-1)<0.1, f"{H0**2*Rk/(G*Ms3/Rk**2):.2e}")
chk("2.5.1 tilt at the Buchdahl limit: arccos(1/3) = 70.53 deg (paper: below 70.5)", abs(math.degrees(math.acos(1/3))-70.53)<0.01)
GMs=1.32712440018e20; a=5.7909e10; e=0.205630
adv=6*math.pi*GMs/(a*(1-e*e)*c*c)*(180/math.pi)*3600*(36525/87.9691)
chk("eq129 Mercury perihelion advance 42.98 arcsec/century", abs(adv-42.98)<0.02, f"{adv:.2f}")
print(); print("FAILED: "+", ".join(bad) if bad else "all passed")
sys.exit(1 if bad else 0)
