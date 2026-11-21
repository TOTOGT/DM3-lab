"""Math checks for Gravity Across Scales v2. Everything printed is computed here; controls can fail."""
import numpy as np, sympy as sp
from scipy.integrate import solve_ivp
eps=2.0
def rhs(t,u):
    r,z=u; e=np.exp(-z)
    return [r*(1-r*r)+eps*(r-1)*e, r*r-eps*(r-1)**2*e]
def outcome(r0,z0,T=60):
    ev=lambda t,u:u[0]-1e-3; ev.terminal=True
    ev2=lambda t,u:abs(u[0]-1)-1e-6; ev2.terminal=True
    s=solve_ivp(rhs,[0,T],[r0,z0],method='DOP853',rtol=1e-12,atol=1e-14,events=[ev,ev2])
    return 1 if len(s.t_events[1])>0 else (0 if len(s.t_events[0])>0 else 1)
def rstar(z0):
    lo,hi=0.01,1.2
    assert outcome(lo,z0)==0 and outcome(hi,z0)==1
    while hi-lo>1e-12:
        m=(lo+hi)/2
        if outcome(m,z0): hi=m
        else: lo=m
    return (lo+hi)/2
print("== A. basin boundary r*(z0), bisection, DOP853")
vals={}
for z0 in [0,np.log(2),1,2,3,4]:
    vals[z0]=rstar(z0); print(f"  z0={z0:.4f}  r*={vals[z0]:.10f}")
print("  repo rigorous certificate for z0=0: [0.7759405755019531, 0.7759405755023437] -> rounds to 0.77594058, not ...059")
assert 0.77594057<vals[0]<0.77594059
# B. does the boundary trajectory approach the saddle?
x=sp.symbols('x'); rs=2*np.cos(3*np.pi/7); zs=-np.log(rs*(1+rs)/2)
print(f"== B. saddle r_s={rs:.6f} z_s={zs:.6f}")
r0=vals[0]; s=solve_ivp(rhs,[0,200],[r0-1e-12,0],method='DOP853',rtol=1e-13,atol=1e-15,dense_output=True)
best=min(((np.hypot(s.sol(t)[0]-rs,s.sol(t)[1]-zs),t) for t in np.linspace(0,40,4001)))
print(f"  closest approach of the boundary trajectory to the saddle: dist={best[0]:.3e} at t={best[1]:.2f}")
J=np.array([[1-3*rs**2+2*np.exp(-zs), -2*(rs-1)*np.exp(-zs)],[2*rs-4*(rs-1)*np.exp(-zs), 2*(rs-1)**2*np.exp(-zs)]])
ev=np.linalg.eigvals(J); print("  Jacobian eigenvalues at saddle:",ev, " tr=",np.trace(J)," det=",np.linalg.det(J), " 2cos(2pi/7)=",2*np.cos(2*np.pi/7))
# C. compare with frozen nullcline root rf(z)= (-1+sqrt(1+8e^-z))/2 (r' = 0 with r != 1)
print("== C. r*(z0) against the rdot=0 nullcline root rf(z0)")
for z0 in [0,np.log(2),1,2,3,4]:
    rf=(-1+np.sqrt(1+8*np.exp(-z0)))/2; print(f"  z0={z0:.3f} r*={vals[z0]:.5f} rf={rf:.5f} 2e^-z={2*np.exp(-z0):.5f}")
# D. T1: forward invariance of {r>=phi^-1, z>=log2} and Vdot<=0 there
phi=(np.sqrt(5)-1)/2
rr=np.linspace(phi,3,2000); zz=np.linspace(np.log(2),12,2000); R,Z=np.meshgrid(rr,zz)
br=R*(1+R)-2*np.exp(-Z); zdot=R**2-2*(R-1)**2*np.exp(-Z)
print(f"== D. T1 region: min bracket r(1+r)-2e^-z = {br.min():.2e} (>=0), min zdot = {zdot.min():.4f} (>= 2r-1 >= {2*phi-1:.3f}>0)")
assert br.min()>=-1e-12 and zdot.min()>0
# E. Hill problem axial critical point type
X,Y=sp.symbols('X Y',real=True); W=sp.Rational(3,2)*X**2+1/sp.sqrt(X**2+Y**2)
x0=sp.Rational(1,3)**sp.Rational(1,3)
H=sp.hessian(W,(X,Y)).subs({X:x0,Y:0}); print("== E. Hill W Hessian at L1 (x=3^-1/3):",[sp.nsimplify(sp.simplify(h)) for h in H], " det=",sp.simplify(H.det()),"-> index-1 Morse saddle (nondegenerate)")
# G. stable manifold of the saddle, followed backward in time, against r*(0)
J=np.array([[1-3*rs**2+2*np.exp(-zs), -2*(rs-1)*np.exp(-zs)],[2*rs-4*(rs-1)*np.exp(-zs), 2*(rs-1)**2*np.exp(-zs)]])
w,V=np.linalg.eig(J); vs=np.real(V[:,np.argmin(w)])
print("== G. stable manifold of the saddle, branch followed backward in time, crossing of z=0:")
for sgn in (+1,-1):
    u0=np.array([rs,zs])+sgn*1e-9*vs
    evz=lambda t,u:u[1]; big=lambda t,u:max(abs(u[0]),abs(u[1]))-20; big.terminal=True
    s=solve_ivp(lambda t,u:[-x for x in rhs(t,u)],[0,400],u0,method='DOP853',rtol=1e-13,atol=1e-15,events=[evz,big])
    cr=[float(e[0]) for e in s.y_events[0]]; print("  branch",sgn,"z=0 crossing r=",cr)
    if cr: assert abs(cr[0]-vals[0])<1e-8
