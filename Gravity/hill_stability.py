"""Hill problem: do circular initial orbits around the secondary stay bound? (units n=1, mu=1; r_H=3^(-1/3))"""
import numpy as np, sys
from scipy.integrate import solve_ivp
def hill(t,u):
    x,y,vx,vy=u; r3=(x*x+y*y)**1.5
    return [vx,vy,2*vy+3*x-x/r3,-2*vx-y/r3]
rH=(1/3)**(1/3); T=float(sys.argv[1]) if len(sys.argv)>1 else 400
def stays(rho,sign):
    v=sign*rho**-0.5-rho
    esc=lambda t,u: np.hypot(u[0],u[1])-3*rH; esc.terminal=True
    s=solve_ivp(hill,[0,T],[rho,0,0,v],method='DOP853',rtol=1e-10,atol=1e-12,events=esc)
    return len(s.t_events[0])==0
for sign,name in ((1,'prograde'),(-1,'retrograde')):
    fr=np.arange(0.20,0.96,0.02); res=[stays(f*rH,sign) for f in fr]
    print(name,"bound(1)/escaped(0) for rho/rH from 0.20 step 0.02:","".join("1" if r else "0" for r in res))
    firstbad=[f for f,r in zip(fr,res) if not r]; print("  first escape at rho/rH =",round(firstbad[0],2) if firstbad else None)
