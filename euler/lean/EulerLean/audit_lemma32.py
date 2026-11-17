# Direct numerical test of the paper's Lemma 3.2 (and T_m 1 = sigma(m) 1, T_m chi = (m/p) sigma(m) chi).
# Builds H/pH = M2(F_p), Y_p = Gamma_p \ PGL2(F_p), the operator T_m of eq (3.4), and its spectrum.
# EMPIRICAL test of the lemma's conclusion, not a proof of the lemma.
import numpy as np, itertools, math, sys
from sympy import factorint, primerange, legendre_symbol
def tau_sigma(m):
    f=factorint(m); t=1; s=1
    for q,e in f.items(): t*=e+1; s*=(q**(e+1)-1)//(q-1)
    return t,s
def setup(p):
    inv2=pow(2,-1,p)
    # find a,b with a^2+b^2 = -1 mod p
    ab=next((a,b) for a in range(p) for b in range(p) if (a*a+b*b+1)%p==0)
    a,b=ab
    I=np.array([[0,-1],[1,0]]); J=np.array([[a,b],[b,-a]])%p; K=(I@J)%p
    one=np.eye(2,dtype=int)
    def rho(u):  # u = 4 integers = 2*(coords); element = u/2
        M=(u[0]*one+u[1]*I+u[2]*J+u[3]*K)*inv2
        return M%p
    return rho
def norm_mat(M,p):
    M=M%p; d=(M[0,0]*M[1,1]-M[0,1]*M[1,0])%p
    assert d!=0
    flat=[M[0,0],M[0,1],M[1,0],M[1,1]]
    s=next(x for x in flat if x%p!=0); si=pow(int(s),-1,p)
    return tuple(int(x*si%p) for x in flat)
def mat(t): return np.array([[t[0],t[1]],[t[2],t[3]]])
def quats(m):  # u in Z^4, all even or all odd, sum u^2 = 4m
    N=4*m; B=int(math.isqrt(N)); out=[]
    for u0 in range(-B,B+1):
      for u1 in range(-B,B+1):
        for u2 in range(-B,B+1):
            r=N-u0*u0-u1*u1-u2*u2
            if r<0: continue
            u3=math.isqrt(r)
            if u3*u3!=r: continue
            for s in ({u3,-u3}):
                u=(u0,u1,u2,s)
                par={x%2 for x in u}
                if len(par)==1: out.append(u)
    return out
def run(p,ms):
    rho=setup(p)
    units=quats(1); assert len(units)==24
    Gam=[norm_mat(rho(u),p) for u in units]; Gam=sorted(set(Gam)); assert len(Gam)==12,len(Gam)
    # enumerate PGL2(F_p)
    G=set()
    for a,b,c,d in itertools.product(range(p),repeat=4):
        if (a*d-b*c)%p: G.add(norm_mat(np.array([[a,b],[c,d]]),p))
    G=sorted(G); assert len(G)==p*(p*p-1)
    Gm=[mat(g) for g in Gam]
    coset={}; reps=[]
    for g in G:
        if g in coset: continue
        M=mat(g); orb={norm_mat(h@M,p) for h in Gm}
        idx=len(reps); reps.append(g)
        for o in orb: coset[o]=idx
    Y=len(reps); assert Y==p*(p*p-1)//12
    chi=np.array([legendre_symbol(int(round((mat(g)[0,0]*mat(g)[1,1]-mat(g)[0,1]*mat(g)[1,0])%p)),p) for g in reps],dtype=float)
    res=[]
    for m in ms:
        if m%2==0 or m%p==0: continue
        Q=quats(m); t,s=tau_sigma(m); assert len(Q)==24*s,(m,len(Q),24*s)
        Rm=[rho(u) for u in Q]
        T=np.zeros((Y,Y))
        for c,g in enumerate(reps):
            M=mat(g)
            for R in Rm:
                T[c,coset[norm_mat(R@M,p)]]+=1/24
        sym=np.abs(T-T.T).max()
        one=np.ones(Y)
        e1=np.abs(T@one-s*one).max()
        ech=np.abs(T@chi-legendre_symbol(m%p,p)*s*chi).max()
        # complement of span{1,chi}
        B=np.stack([one/np.linalg.norm(one),chi/np.linalg.norm(chi)],axis=1)
        Pm=np.eye(Y)-B@B.T
        Tc=Pm@T@Pm
        ev=np.linalg.eigvalsh((Tc+Tc.T)/2)
        mx=np.abs(ev).max()
        res.append((m,sym,e1,ech,mx,t*math.sqrt(m),mx/(t*math.sqrt(m))))
    return Y,res

worst=0;bad=[]
for p,ms in [(7,[3,5,9,15,25,27,45]),(11,[3,5,7,9,15,21,25,27]),(19,[3,5,7,9,11,15,21])]:
    Y,res=run(p,ms)
    for r in res:
        print(f"p={p} m={r[0]:3d}  sym_err={r[1]:.0e} T1_err={r[2]:.0e} Tchi_err={r[3]:.0e}  max|eig| on {{1,chi}}^perp = {r[4]:.4f}  bound tau*sqrt(m) = {r[5]:.4f}  ratio = {r[6]:.3f}")
        worst=max(worst,r[6])
        if r[6]>1+1e-9: bad.append(r)
print("worst ratio over all (m>1) tests:",round(worst,4),"| violations:",bad)
