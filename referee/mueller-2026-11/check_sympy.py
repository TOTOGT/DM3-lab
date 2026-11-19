#!/usr/bin/env python3
"""Symbolic checks of the algebra in Mueller, 'The Lorentz Factor as the Slope of an Additional Spatial Coordinate' (Zenodo 10.5281/zenodo.24280888).
Each check re-derives a displayed equation from its stated premises. Tests algebra only, not physics."""
import sympy as sp
fails=[]
def chk(name, expr):
    ok = sp.simplify(expr)==0
    if not ok:  # sqrt branches: fall back to exact-rational spot checks over the free symbols
        import random
        syms=sorted(expr.free_symbols,key=str); pts=0; good=0
        for _ in range(12):
            sub={s_:sp.Rational(random.randint(5,12)*7+random.randint(0,6),7) for s_ in syms}
            for k_,v_ in {'c':10,'v':random.randint(2,9),'r_s':random.randint(1,4),'R':random.randint(6,12)}.items():
                for s_ in syms:
                    if str(s_)==k_: sub[s_]=sp.Integer(v_)
            try:
                val=sp.N(expr.subs(sub),30)
            except Exception: continue
            if val.is_real is False or val.has(sp.nan): continue
            pts+=1; good+= bool(abs(val)<1e-20)
        ok = pts>=6 and good==pts
        if ok: name+="  [numeric spot-check, 12 pts]"
    print(("PASS  " if ok else "FAIL  ")+name)
    if not ok: fails.append(name)
v,c,R,rs,tau,x=sp.symbols('v c R r_s tau x',positive=True)
g=1/sp.sqrt(1-v**2/c**2)
y_x = x*v/sp.sqrt(c**2-v**2)
chk("eq13/14  dy/dx = gamma v/c", sp.diff(y_x,x)-g*v/c)
chk("eq26     gamma^2 = 1+(dy/dx)^2", g**2-(1+sp.diff(y_x,x)**2))
chk("eq11/16  d_tau y = v^2/sqrt(c^2-v^2) = gamma v^2/c", v**2/sp.sqrt(c**2-v**2)-g*v**2/c)
chk("eq15     v*dy/dx = v*sqrt(gamma^2-1)", v*sp.diff(y_x,x)-v*sp.sqrt(g**2-1))
# interval (eq17-21), dt=0
dx=sp.symbols('dx')
chk("eq18-21  ds'^2 = -dx^2", ((-g*v/c*dx)**2-(g*dx)**2)+dx**2)
# Flamm (eq 144-146, 2.4.4)
Rr=sp.symbols('R',positive=True)
yF=2*sp.sqrt(rs*(Rr-rs))
chk("eq144/146 Flamm: y'=sqrt(rs/(R-rs))", sp.diff(yF,Rr)-sp.sqrt(rs/(Rr-rs)))
chk("eq134    1+y'^2 = 1/(1-rs/R)", 1+sp.diff(yF,Rr)**2-1/(1-rs/Rr))
L=sp.symbols('L',positive=True)
yc=-sp.sqrt(L**2-Rr**2)
b=Rr/L
chk("2.4.4 cap: y'=beta*gamma, beta=R/L", sp.diff(yc,Rr)-b/sp.sqrt(1-b**2))
# curvatures (117-118)
beta=sp.Function('beta')(Rr)
bp=sp.diff(beta,Rr)
Rrr=2*beta*bp/Rr; Rtt=beta*bp/Rr+beta**2/Rr**2
chk("eq118->109  R3 = (2/R^2) d(R beta^2)/dR", Rrr+2*Rtt-2/Rr**2*sp.diff(Rr*beta**2,Rr))
G,rho,m=sp.symbols('G rho m',positive=True)
# Prop 1 (eq 119-121)
bs=sp.sqrt(rs/Rr)
N=sp.sqrt(1-rs/Rr)
gam2=1/(1-bs**2)
chk("eq120/121 N'/N = gamma^2(beta beta' + beta^2/R)", sp.diff(N,Rr)/N-gam2*(bs*sp.diff(bs,Rr)+bs**2/Rr))
# radial component: N_ll/N = 2 beta beta'/R with d/dl = (1/gamma) d/dR
Nl=sp.diff(N,Rr)/sp.sqrt(gam2)
Nll=sp.diff(Nl,Rr)/sp.sqrt(gam2)
chk("Prop1 radial: N_,ll/N = 2 beta beta'/R", Nll/N-2*bs*sp.diff(bs,Rr)/Rr)
# TOV potential gradient eq124, with beta^2=2Gm/(c^2R), (R beta^2)'=8 pi G rho R^2/c^2 not needed here
p=sp.symbols('p',positive=True)
b2=2*G*m/(c**2*Rr)
lhs=(1/(1-b2))*(b2/(2*Rr)+4*sp.pi*G*p*Rr/c**4)
rhs=G*(m+4*sp.pi*Rr**3*p/c**2)/(c**2*Rr**2*(1-2*G*m/(c**2*Rr)))
chk("eq124 two forms agree", lhs-rhs)
# uniform density interior Schwarzschild (125)
rstar,rho_,s=sp.symbols('Rstar rho_ s',positive=True)
Ls2=Rr  # placeholder
Lsq=rstar**3/rs
sR=sp.sqrt(1-Rr**2/Lsq); ss=sp.sqrt(1-rs/rstar)
Nin=(3*ss-sR)/2
pin=(sR-ss)/(3*ss-sR)   # p/(rho c^2)
# hydrostatic: p' = -(rho c^2 + p) N'/N  with units p/(rho c^2)
chk("eq125 hydrostatic eq", sp.diff(pin,Rr)+(1+pin)*sp.diff(Nin,Rr)/Nin)
chk("eq125 N(R*)=s*", Nin.subs(Rr,rstar)-ss)
chk("eq125 p(R*)=0", pin.subs(Rr,rstar))
# TOV gradient check with p: N'/N = gamma^2(beta^2/2R + 4 pi G p R/c^4) in units: 4piG rho/c^2 = 3/(2 L^2)
pc=pin*sp.Rational(3,2)/Lsq   # 4 pi G p /c^4 = (4piG rho/c^2)(p/rho c^2)/c^2 ; 4piG rho/c^2 = 3/(2L^2)
lhs=sp.diff(Nin,Rr)/Nin
rhs=(1/sR**2)*(Rr/Lsq/2+pc*Rr)
chk("eq124 vs uniform density N'/N", lhs-rhs)
# central pressure / Buchdahl
sc=sp.symbols('s_star',positive=True)
chk("central p/rho c^2 = (1-s*)/(3s*-1)", pin.subs(Rr,0)-(1-ss)/(3*ss-1))
chk("Buchdahl: 3s*>1 <=> R*>9rs/8 at boundary", (3*ss-1).subs(rstar,sp.Rational(9,8)*rs))
# weak-field log expansion (91) and Phi solution (88-89)
Q=sp.symbols('Q')
Phi=Q/rs*sp.log(1-rs/Rr)
chk("eq88/89 Phi' = Q/(R(R-rs))", sp.diff(Phi,Rr)-Q/(Rr*(Rr-rs)))
chk("eq87 R^2(1-rs/R)Phi'=Q", Rr**2*(1-rs/Rr)*sp.diff(Phi,Rr)-Q)
# 5D reduction: eq 66,65 -> 68 -> 72
kap,Phs,boxP,Rs,T44,T4=sp.symbols('kappa Phi boxPhi Rs T44 T4')
Rscal=-2*kap*T44/Phs**2
sol=sp.solve(sp.Eq(-Rscal+3*boxP/Phs,kap*T4),boxP)[0]
chk("eq68 box Phi = (kappa Phi/3)(T4 - 2 T44/Phi^2)", sol-kap*Phs/3*(T4-2*T44/Phs**2))
eps,pr,py=sp.symbols('epsilon p p_y')
chk("eq72  with T4=-eps+3p, T44=Phi^2 p_y", (kap*Phs/3*((-eps+3*pr)-2*py))+kap*Phs/3*(eps-3*pr+2*py))
# eq 96
sig0,Rst,r=sp.symbols('sigma0 Rstar r',positive=True)
chk("eq96 integral", -kap/3*sp.integrate(Phs*sig0*r**2,(r,0,Rst))+kap*Phs*sig0*Rst**3/9)
# Hubble / critical density (2.4.4, 2.8.2)
H=sp.symbols('H',positive=True)
rho_c=3*H**2/(8*sp.pi*G)
M_=sp.Rational(4,3)*sp.pi*rho_c*(c/H)**3
chk("critical density: r_s(c/H) = c/H", 2*G*M_/c**2-c/H)
chk("beta_H^2 = 2Gm/(c^2R) = (HR/c)^2", 2*G*(sp.Rational(4,3)*sp.pi*rho_c*Rr**3)/(c**2*Rr)-(H*Rr/c)**2)
# Sciama eq137
chk("eq137 G m_H(R_H)/(c^2 R_H) = 1/2", G*M_/(c**2*(c/H))-sp.Rational(1,2))
# circular orbit speed / momentum (2.6)
Nn=sp.sqrt(1-rs/Rr); GM=rs*c**2/2
chk("2.6 v_local^2 = GM/(R-rs)", c**2*Rr*sp.diff(Nn,Rr)/Nn-GM/(Rr-rs))
# eq 140 deep-MOND algebra: v^4 = G M g0 with g0 = k c H ; (v/c)^4 = (k/2) bN^2 bH
k,Mm=sp.symbols('kappa_p M',positive=True)
bN2=2*G*Mm/(c**2*Rr); bH2=H**2*Rr**2/c**2
chk("eq140 (G M k c H)/c^4 = (k/2) bN^2 bH", G*Mm*k*c*H/c**4-(k/2)*(bN2*sp.sqrt(bH2)))
chk("eq140 bN^2*bH independent of R, =2GMH/c^3", bN2*sp.sqrt(bH2)-2*G*Mm*H/c**3)
print(); print("FAILED: "+", ".join(fails) if fails else "all passed")
