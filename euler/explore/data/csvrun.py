import sys, onevec as o
p=int(sys.argv[1]); M=int(sys.argv[2])
S=o.build(p)
with open(f"R_{p}.csv","w") as f:
    f.write("p,m,A,sigma,tau,R,incut\n")
    for m in range(3,M,2):
        if m%p==0 or not o.good(m): continue
        A=o.A_count(S,m,S['O1']); R,viol,t,s=o.verdict(A,m,p)
        f.write(f"{p},{m},{A},{s},{t},{R:.6f},{int(p**4<=32*m)}\n"); f.flush()
