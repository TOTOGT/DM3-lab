# Exact tests of the case branches in Prop 3.1's proof (p | m cases) and the p=3 branch. EMPIRICAL.
import numpy as np, math
from sympy import factorint, primerange
def sigma(m): return sum(d for d in range(1,m+1) if m%d==0)
def good_m(m): return m%2==1 and all(q%4==3 for q in factorint(m))
res={"p|m, p^2 !| m":[0,0],"p^2 | m":[0,0],"p=3, 3 !| m":[0,0]}
fails=[]
for m in range(1,3000,2):
    if not good_m(m): continue
    n=2*m; B=int(math.isqrt(n))
    xs=np.arange(-B,B+1); X,Y=np.meshgrid(xs,xs); nm=X*X+Y*Y
    opp=((X+Y)%2==1)&(nm<=n); N=np.bincount(nm[opp],minlength=n+1).astype(np.int64)
    for p in primerange(3,B+1):
        if p%4!=3: continue
        D=np.bincount(nm[opp&(X%p==0)&(Y%p==0)],minlength=n+1).astype(np.int64)
        bp=int(np.dot(D,N[::-1])+np.dot(N,D[::-1])-np.dot(D,D[::-1]))
        if m%p==0 and m%(p*p)!=0:
            res["p|m, p^2 !| m"][0]+=1
            if bp!=0: res["p|m, p^2 !| m"][1]+=1; fails.append((m,p,bp,"expected 0"))
        elif m%(p*p)==0:
            res["p^2 | m"][0]+=1
            if bp!=16*sigma(m//(p*p)): res["p^2 | m"][1]+=1; fails.append((m,p,bp,16*sigma(m//(p*p))))
        elif p==3 and m%3!=0:
            R=24*sigma(m); res["p=3, 3 !| m"][0]+=1
            if bp/R>2/(3*2)+1e-12: res["p=3, 3 !| m"][1]+=1; fails.append((m,p,bp/R,"p=3 bound 1/3"))
for k,v in res.items(): print(f"branch [{k}]: tested {v[0]}, failures {v[1]}")
print("failures:",fails[:3])
# ratio claim in the completion: sigma(m/p^2)/sigma(m) < 1/p^2 * ... check  sigma(m/p^2)/sigma(m) < 1/p^2 ... paper: < 1/p
bad=0;tot=0
for m in range(1,20000,2):
    if not good_m(m): continue
    for p,e in factorint(m).items():
        if e>=2:
            tot+=1
            r=sigma(m//(p*p))/sigma(m)
            if not (r<1/p**2*(p**2)/p*1.0000001 and 2*(16*sigma(m//(p*p)))/ (3*16*sigma(m)*3/2) >= 0): pass
            # direct claim: b_p/R = 16 sigma(m/p^2)/(24 sigma(m)) <= 2/(3 p^2)
            if 16*sigma(m//(p*p))/(24*sigma(m))>2/(3*p*p)+1e-15: bad+=1
print(f"completion bound b_p/R <= 2/(3 p^2) for p^2|m: tested {tot}, violations {bad}")
