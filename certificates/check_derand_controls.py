import sys; sys.argv=['x']
src=open(__file__.rsplit('/',1)[0]+'/check_derand.py').read().split('# ---------- 3SUM')[0]
exec(src)
# control 1: Lemma 4.1 without the k-free case must fail
f=lambda v,t,tau: any((v>>k)+(t>>k) in ((tau>>k)-2,(tau>>k)-3) for k in range(max(v,t,tau).bit_length()))
print("control 4.1 without v+t=tau-1:", sum(1 for v in range(30) for t in range(30) for tau in range(70) if f(v,t,tau)!=(v+t<tau)), "mismatches (must be > 0)")
# control 2: plain count N as the all-edges potential: zero slots never leave, so S' need not empty
import random, math
random.seed(3); n=3; U=30; fails=0
for it in range(40):
    w=[[[random.randint(-U,U) for _ in range(n)] for _ in range(n)] for _ in range(3)]
    a,b,c=0,0,0; w[0][a][b]=-(w[1][b][c]+w[2][c][a]) if abs(w[1][b][c]+w[2][c][a])<=U else w[0][a][b]
    S3=lambda a,b,c: w[0][a][b]+w[1][b][c]+w[2][c][a]
    Sp=[(a,b) for a in range(n) for b in range(n)]
    for l in range(6):
        m=1
        for _ in range(3): m*=min(P,key=lambda p:(sum(sum(1 for c in range(n) if S3(*q,c)%(m*p)==0) for q in Sp),p))
        Sp=[q for q in Sp if any(S3(*q,c)%m==0 for c in range(n))]
    fails+= len(Sp)>0
print("control plain-N potential: survivors nonempty in",fails,"of 40 (zero slots never leave)")
