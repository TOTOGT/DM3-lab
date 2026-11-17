from fractions import Fraction as F
import math
# ---- primes
N=3_000_000
sieve=bytearray([1])*(N+1); sieve[0]=sieve[1]=0
for i in range(2,int(N**.5)+1):
    if sieve[i]: sieve[i*i::i]=bytearray(len(sieve[i*i::i]))
primes=[i for i in range(N+1) if sieve[i]]
P3=[p for p in primes if p%4==3]
P1=[p for p in primes if p%4==1]
# ---- Lemma 5.1 constants (exact)
def best_C1():
    tot=F(1); tab={}
    for p in [p for p in P3 if p<32]:
        best=F(1);be=0
        for e in range(1,40):
            # (e+1) p^e / (sigma(p^e) p^{e/5}); compare fifth powers exactly:
            # value^5 = (e+1)^5 p^(5e) / (sigma^5 p^e)
            sig=sum(p**k for k in range(e+1))
            v5=F((e+1)**5*p**(5*e), sig**5*p**e)
            if v5>best: best=v5;be=e
        tab[p]=be; tot*=best
    return tot,tab
def best_C2():
    tot=F(1); tab={}
    for q in [q for q in P1 if q<32]:
        best=F(1);be=0
        for e in range(1,40):
            v5=F((e+1)**5, q**e)
            if v5>best: best=v5;be=e
        tab[q]=be; tot*=best
    return tot,tab
c1,t1=best_C1(); c2,t2=best_C2()
print("C1^5 =",c1,"=",float(c1)," paper claims 183143120027364343/2849934139195392 =",float(F(183143120027364343,2849934139195392)),"; equal:",c1==F(183143120027364343,2849934139195392))
print("  (23/10)^5 =",float(F(23,10)**5),"; C1^5 < (23/10)^5:",c1<F(23,10)**5, " maximizing e:",t1)
print("C2^5 =",c2,"=",float(c2)," paper 7962624/160225:",c2==F(7962624,160225))
print("  (11/5)^5 =",float(F(11,5)**5),"; C2^5 < (11/5)^5:",c2<F(11,5)**5," maximizing e:",t2)
# Note: C1 as tabulated in the paper uses the factor p/(p+1); recompute that version too
def best_C1p():
    tot=F(1)
    for p in [p for p in P3 if p<32]:
        best=F(1)
        for e in range(1,40):
            v5=F(p**5*(e+1)**5, (p+1)**5*p**e)
            best=max(best,v5)
        tot*=best
    return tot
c1p=best_C1p()
print("C1^5 with the p/(p+1) form =",c1p,"=",float(c1p)," equals paper's:",c1p==F(183143120027364343,2849934139195392))
# ---- Lemma 5.2
cnt=0; bad=[]
t_checkpoints=set(range(0,2000))|{10**4,10**5,10**6,2*10**6,3*10**6}
cum=0; idx=0
P3gt3=[p for p in P3 if p>3]
import bisect
for t in list(range(1,3001))+[10**4,10**5,10**6,3*10**6]:
    c=bisect.bisect_right(P3gt3,t)
    if c> 2*t/15+1: bad.append(("5.2",t,c))
print("(5.2) violations up to checked range:",bad[:3])
s54=2*sum(F(1,p*(p-1)) for p in P3 if p<=10**5)
tail=float(2*sum(1/(p*(p-1)) for p in P3 if p>10**5))
print("(5.4) partial sum to 1e5 =",float(s54)," (+tiny tail) vs 21/50 =",21/50, " ok:",float(s54)<21/50)
viol=[]
for Pp in [3,4,5,7,10,50,100,128,1000,10**4,10**5]:
    s=sum(1/(p*p) for p in P3 if p>Pp)  # truncated at 3e6, add tail bound ~ 1/(2 ln)... negligible
    s+= 1/(3e6*math.log(3e6))   # crude tail
    if s> 2/(15*Pp)+2/Pp**2: viol.append((Pp,s,2/(15*Pp)+2/Pp**2))
print("(5.3) violations:",viol)
# ---- final inequality (6.1)+(6.2) at X=64 exactly
X=F(64)
x15=F(4,9)   # bound used for X^{-1/5}
t1=F(21,50)+F(23,30)*F(5,4)*x15*(F(4,15)+F(1,64))
t2=F(44,15)*x15*(F(1,15)+F(19,30*64)+F(1,64**3))
tot=t1+t2
print("(6.1) bound =",t1,float(t1)); print("(6.2) bound =",t2,float(t2))
print("sum =",tot,float(tot),"  paper: 21235493/33177600 =",F(21235493,33177600)==tot," <2/3:",tot<F(2,3))
# direction check of the three side inequalities at X=64
print("64^(-1/5) =",64**-.2," <= 4/9:",64**-.2<=4/9,"; 2^(3/10) =",2**.3,"< 5/4:",2**.3<1.25)
# monotonic: bound decreases in X? check worst case is X=64
for X_ in [64,100,1000,10**4]:
    xx=X_**-0.2
    s=0.42+ (23/30)*(2**0.3)*xx*(4/15+1/X_) + (44/15)*xx*(1/15+19/(30*X_)+1/X_**3)
    print("X=",X_,"real-valued bound",round(s,4))
