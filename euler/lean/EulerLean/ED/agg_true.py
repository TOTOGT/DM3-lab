# Exact aggregate sum  S(m) = (1/(24 sigma m)) * sum_{p in PT(Pn(2m))} b_p(2m)  for sample m,
# compared with the target T*(n) = 2/3 - L(n).  b_p(n) = #{x in Z^4 : |x|^2=n, x0+x1 odd, x2+x3 odd,
# (p|x0 and p|x1) or (p|x2 and p|x3)}.  Computed by r2odd convolution, no per-prime bound assumed.
import numpy as np, math, sympy, sys
def r2odd(N):
    r=np.zeros(N+1,dtype=np.int64); R=int(math.isqrt(N))
    for a in range(-R,R+1):
        b=np.arange(-R,R+1); v=a*a+b*b; ok=(v<=N)&(((a+b)&1)==1)
        np.add.at(r,v[ok],1)
    return r
def run(m):
    n=2*m; r=r2odd(n)
    P=math.floor(2*n**0.25); PT=[p for p in sympy.primerange(2,P+1) if p%4==3]
    sig=int(sympy.divisor_sigma(m)); tau=int(sympy.divisor_count(m))
    tot=0; rows=[]
    for p in PT:
        q=p*p; vmax=n//q
        v=np.arange(0,vmax+1); E1=int((r[v]*r[n-q*v]).sum())   # first pair = p*(a',b')
        E12=0
        if n%q==0:
            v=np.arange(0,n//q+1); E12=int((r[v]*r[n//q-v]).sum())  # both pairs divisible by p
        b=2*E1-E12; tot+=b; rows.append((p,b/(24*sig),2/(p*(p-1))))
    u=n**(1/20)
    L=(4/3)*(11/5*u**4)*(2/(15*P)+2/P**2+(2*u**10/15+1)/u**20)
    return n,P,len(PT),tot/(24*sig),2/3-L,sum(x[2] for x in rows),max(x[1]-x[2] for x in rows),tau,sig
if __name__=="__main__":
    for m in map(int,sys.argv[1:]):
        n,P,k,S,T,main,maxdev,tau,sig=run(m)
        print(f"m={m} n={n} P={P} #p={k}  S={S:.4f}  target T*={T:.4f}  sum 2/(p(p-1))={main:.4f}  max_p(b_p/24sigma - 2/(p(p-1)))={maxdev:.2e}  tau={tau}  S<T*={S<T}")
