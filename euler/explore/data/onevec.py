# One-vector slack experiment for H31gt3. EMPIRICAL, not a proof.
# O_p = image in Y_p = Gamma_p \ PGL2(F_p) of nonzero matrices x2*J + x3*K (p | x0,x1 plane); also tested: union with x0 + x1*I plane.
# A = 24 (T_m 1_O)(Gamma_p) = #{alpha in Q_m : Gamma_p rho(alpha) in O}.  R = (D*A - 144 sigma)/(24 tau (D-6) sqrt m), D = p(p-1).
# Violation of R <= 1 (p>3) iff N>0 and N^2 > K^2 m, N = D*A - 144 sigma, K = 24 tau (D-6).  Integer test used for the verdict.
import math, itertools, sys
import numpy as np
from sympy import factorint, legendre_symbol

def ts(m):
    f=factorint(m); t=1; s=1
    for q,e in f.items(): t*=e+1; s*=(q**(e+1)-1)//(q-1)
    return t,s
def good(m): return m%2==1 and all(q%4==3 for q in factorint(m))

def quats(m):  # u = 2*coords, all even or all odd, sum u^2 = 4m  (vectorised)
    N=4*m; B=math.isqrt(N); out=[]
    rng=np.arange(-B,B+1,dtype=np.int64)
    for u0 in range(-B,B+1):
        par=u0%2
        g=rng[(rng%2)==par]
        X,Y=np.meshgrid(g,g)
        r=N-u0*u0-X*X-Y*Y
        ok=r>=0
        rr=np.where(ok,r,0)
        u3=np.rint(np.sqrt(rr)).astype(np.int64)
        ok&=(u3*u3==rr)&((u3%2)==par)
        xs,ys=np.nonzero(ok)
        for i,j in zip(xs,ys):
            a1=int(X[i,j]); a2=int(Y[i,j]); a3=int(u3[i,j])
            out.append((u0,a1,a2,a3))
            if a3!=0: out.append((u0,a1,a2,-a3))
    return out

def build(p):
    inv2=pow(2,-1,p)
    a,b=next((a,b) for a in range(p) for b in range(p) if (a*a+b*b+1)%p==0)
    def rho(u):
        u0,u1,u2,u3=u
        return ((u0+u2*a-u3*b)*inv2%p,(-u1+u2*b+u3*a)*inv2%p,(u1+u2*b+u3*a)*inv2%p,(u0-u2*a+u3*b)*inv2%p)
    def norm(M):
        s=next(x for x in M if x%p); si=pow(s,-1,p)
        return tuple(x*si%p for x in M)
    def mul(A,B): return ((A[0]*B[0]+A[1]*B[2])%p,(A[0]*B[1]+A[1]*B[3])%p,(A[2]*B[0]+A[3]*B[2])%p,(A[2]*B[1]+A[3]*B[3])%p)
    units=quats(1); assert len(units)==24
    Gam=sorted({norm(rho(u)) for u in units}); assert len(Gam)==12
    G=set()
    for A in itertools.product(range(p),repeat=4):
        if (A[0]*A[3]-A[1]*A[2])%p: G.add(norm(A))
    assert len(G)==p*(p*p-1)
    coset={}; reps=[]
    for g in sorted(G):
        if g in coset: continue
        idx=len(reps); reps.append(g)
        for h in Gam: coset[norm(mul(h,g))]=idx
    Y=len(reps); assert Y==p*(p*p-1)//12
    P1={norm(((x2*a-x3*b)%p,(x2*b+x3*a)%p,(x2*b+x3*a)%p,(-x2*a+x3*b)%p)) for x2 in range(p) for x3 in range(p) if (x2,x3)!=(0,0)}
    P2={norm((x0%p,(-x1)%p,x1%p,x0%p)) for x0 in range(p) for x1 in range(p) if (x0,x1)!=(0,0)}
    O1={coset[g] for g in P1}; O12=O1|{coset[g] for g in P2}
    return dict(p=p,rho=rho,norm=norm,coset=coset,reps=reps,Y=Y,O1=O1,O12=O12,base=coset[norm((1,0,0,1))],mul=mul)

def bp_brute(m,p):  # as audit_prop31.py
    n=2*m; B=math.isqrt(n)
    pairs=[(x,y) for x in range(-B,B+1) for y in range(-B,B+1) if (x+y)%2==1 and x*x+y*y<=n]
    N=[0]*(n+1); D=[0]*(n+1)
    for x,y in pairs:
        N[x*x+y*y]+=1
        if x%p==0 and y%p==0: D[x*x+y*y]+=1
    return sum(D[u]*N[n-u]+N[u]*D[n-u]-D[u]*D[n-u] for u in range(n+1))

def A_count(S,m,O):
    return sum(1 for u in quats(m) if S['coset'][S['norm'](S['rho'](u))] in O)

def verdict(A,m,p):
    t,s=ts(m); D=p*(p-1); Nn=D*A-144*s; K=24*t*(D-6)
    viol = Nn>0 and Nn*Nn>K*K*m
    R=Nn/(K*math.sqrt(m))
    return R,viol,t,s

if __name__=="__main__":
    mode=sys.argv[1]
    if mode=="check":   # the 22 earlier pairs, full spectrum, p=7,11,19
        sets=[(7,[3,5,9,15,25,27,45]),(11,[3,5,7,9,15,21,25,27]),(19,[3,5,7,9,11,15,21])]
        for p,ms in sets:
            S=build(p); Y=S['Y']
            print(f"p={p}: |Y|={Y} |O1|={len(S['O1'])} |O1 u O2|={len(S['O12'])} expected (p+1)/2={(p+1)//2}")
            from sympy import legendre_symbol as ls
            reps=S['reps']
            chi=np.array([ls((g[0]*g[3]-g[1]*g[2])%p,p) for g in reps],dtype=float)
            for m in ms:
                if m%p==0: continue
                t,s=ts(m); Q=quats(m); assert len(Q)==24*s
                coset=S['coset']; norm=S['norm']; rho=S['rho']; mul=S['mul']
                T=np.zeros((Y,Y))
                Rm=[rho(u) for u in Q]
                for c,g in enumerate(reps):
                    for R_ in Rm: T[c,coset[norm(mul(R_,g))]]+=1/24
                one=np.ones(Y)
                Bm=np.stack([one/np.linalg.norm(one),chi/np.linalg.norm(chi)],axis=1); Pm=np.eye(Y)-Bm@Bm.T
                Tc=Pm@T@Pm; mx=np.abs(np.linalg.eigvalsh((Tc+Tc.T)/2)).max()
                for name,O in (("O1",S['O1']),):
                    ind=np.zeros(Y); ind[list(O)]=1
                    f=T@ind; vals=f[list(O)]; const=(vals.max()-vals.min())
                    A=A_count(S,m,O); R,viol,_,_=verdict(A,m,p)
                    mu=len(O)/Y; h=ind-mu; q=(h@T@h)/(h@h)
                    bp=bp_brute(m,p)
                    print(f"  p={p} m={m:3d} good={good(m)!s:5} p^4<=32m={p**4<=32*m!s:5} A/24={A/24:.4f} T1_O(base)={f[S['base']]:.4f} constOnO={const:.1e} "
                          f"R={R:+.4f} q/(tau sqrt m)={q/(t*math.sqrt(m)):+.4f} norm-ratio={mx/(t*math.sqrt(m)):.4f} viol={viol} | b_p={bp} <= A/3={A/3:.1f}: {bp<=A/3+1e-9}")
    else:  # extend: A only, larger p and m
        for p in [int(x) for x in sys.argv[2].split(',')]:
            S=build(p); worst=None
            rows=[]
            for m in range(3,int(sys.argv[3]),2):
                if m%p==0 or not good(m): continue
                A=A_count(S,m,S['O1']); R,viol,t,s=verdict(A,m,p)
                rows.append((m,R,viol,p**4<=32*m))
            if not rows: continue
            mx=max(rows,key=lambda r:r[1]); mn=min(rows,key=lambda r:r[1])
            inr=[r for r in rows if r[3]]
            print(f"p={p}: |O1|={len(S['O1'])} (p+1)/2={(p+1)//2}; good m tested={len(rows)}; max R={mx[1]:+.4f} at m={mx[0]}; min R={mn[1]:+.4f}; violations={sum(r[2] for r in rows)}; in-cutoff pairs={len(inr)}"
                  + (f", their max R={max(r[1] for r in inr):+.4f}" if inr else ""))
