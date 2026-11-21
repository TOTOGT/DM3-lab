import numpy as np, itertools, math, sys
from fractions import Fraction
def run(p, ells):
    # x^2+y^2=-1 mod p
    x,y=next((x,y) for x in range(p) for y in range(p) if (x*x+y*y+1)%p==0)
    inv2=pow(2,-1,p)
    def mm(A,B): return ((A[0]*B[0]+A[1]*B[2])%p,(A[0]*B[1]+A[1]*B[3])%p,(A[2]*B[0]+A[3]*B[2])%p,(A[2]*B[1]+A[3]*B[3])%p)
    def norm(A):
        for v in A:
            if v%p: s=pow(v,-1,p); return tuple((a*s)%p for a in A)
    I=(0,-1%p,1,0); J=(x,y,y,(-x)%p); K=mm(I,J)
    def rho(a,b,c,d): # a..d are Fractions
        def r(f): return (f.numerator*pow(f.denominator,-1,p))%p
        a,b,c,d=map(r,(a,b,c,d))
        return norm(tuple((a*(1 if t in(0,3) else 0)+b*I[t]+c*J[t]+d*K[t])%p for t in range(4)))
    half=Fraction(1,2)
    def hurwitz(N):
        out=[]
        R=int(math.isqrt(N))+1
        for t in itertools.product(range(-R,R+1),repeat=4):
            if sum(v*v for v in t)==N: out.append(tuple(Fraction(v) for v in t))
        R2=int(math.isqrt(4*N))+1
        for t in itertools.product(range(-R2,R2+1),repeat=4):
            if all(v%2 for v in t) and sum(v*v for v in t)==4*N: out.append(tuple(Fraction(v,2) for v in t))
        return out
    units=hurwitz(1); assert len(units)==24
    Gam=sorted({rho(*u) for u in units}); assert len(Gam)==12
    G=[norm(t) for t in itertools.product(range(p),repeat=4) if (t[0]*t[3]-t[1]*t[2])%p]
    G=sorted(set(G)); assert len(G)==p*(p*p-1)
    def canon(g): return min(norm(mm(gm,g)) for gm in Gam)
    cos=sorted({canon(g) for g in G}); idx={c:i for i,c in enumerate(cos)}; n=len(cos); assert n==p*(p*p-1)//12
    # character chi(Gamma g)=legendre(det g)
    def leg(a): a%=p; return 0 if a==0 else (1 if pow(a,(p-1)//2,p)==1 else -1)
    chi=np.array([leg(c[0]*c[3]-c[1]*c[2]) for c in cos],float)
    res=[]
    for l in ells:
        if l==p or l==2: continue
        Q=hurwitz(l); assert len(Q)==24*(l+1),(len(Q),l)
        Rs=[rho(*q) for q in Q]
        T=np.zeros((n,n))
        for c in cos:
            for r in Rs: T[idx[c],idx[canon(mm(r,c))]]+=1/24
        assert np.allclose(T,T.T)
        ev=np.sort(np.abs(np.linalg.eigvalsh(T)))[::-1]
        top=ev[:2]; rest=ev[2]
        ones=np.ones(n)
        assert np.allclose(T@ones,(l+1)*ones) and np.allclose(T@chi,leg(l)*(l+1)*chi)
        res.append((l,round(top[0],6),round(top[1],6),round(rest,6),round(2*math.sqrt(l),6),rest<=2*math.sqrt(l)+1e-9))
    return n,res
for p,ells in [(7,[3,5,11,13,17]),(11,[3,5,7,13]),(19,[3,5,7])]:
    n,res=run(p,ells); print('p',p,'|Y_p|',n)
    for r in res: print('  l=%d  eig(1,chi)=%s,%s  max_rest=%s  2sqrt(l)=%s  ok=%s'%r)
    sys.stdout.flush()
