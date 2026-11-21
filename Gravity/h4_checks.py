"""Identities behind the geometric reading (S^3 in H^4, global AdS5 slicing, Kaluza-Klein form). sympy."""
import sympy as sp
rho=sp.symbols('rho',positive=True); r=sp.sinh(rho)
# global AdS5 spatial slice: dr^2/(1+r^2) + r^2 dOmega3^2 with r = sinh(rho)  ->  d rho^2 + sinh^2(rho) dOmega3^2 (= H^4)
g_rr=sp.simplify((sp.diff(r,rho))**2/(1+r**2)); print("g_rho_rho =",g_rr,"(1 means dr^2/(1+r^2) = d rho^2)"); assert g_rr==1
print("sphere radius sinh(rho); area 2*pi^2*sinh^3(rho); flat-space area 2*pi^2*rho^3; ratio ->",sp.limit(sp.sinh(rho)**3/rho**3,rho,0),"as rho->0 and grows like e^{3rho}/8")
print("principal curvature of geodesic sphere = f'/f =",sp.simplify(sp.diff(sp.sinh(rho),rho)/sp.sinh(rho)),"-> 1 as rho->oo (horosphere, intrinsically flat R^3)")
# Kaluza-Klein form of the Sasakian metric: g = (dz - A)^2 + dx^2 + dy^2, A = x dy - y dx, F = dA
x,y,z=sp.symbols('x y z',real=True); A=sp.Matrix([-y,x,0])
F=sp.diff(A[1],x)-sp.diff(A[0],y); print("F = dA_xy =",F," (uniform field 2 dx^dy)"); assert F==2
print("alpha = dz - A has d alpha = -F dx^dy = -2 dx^dy, matching the contact check")
