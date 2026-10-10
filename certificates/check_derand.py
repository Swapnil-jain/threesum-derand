"""Mechanical check of proofs/derandomisation.md on small instances (logic, not asymptotics): interval groups, the
residue sets of Lemma 2.4, survivor-restricted greedy chains, the weight H of Lemma 3.3, and Lemmas 4.1-4.3, all
against brute force. Standard library only. Usage: python check_derand.py"""
import sys as _sys
# These checks rely on assert, which python -O strips; refuse to run there rather than pass silently.
if not __debug__:
    _sys.exit("refusing to run under python -O: the checks are assert statements")
import random, math, itertools
random.seed(7)
def primes(lo,hi): return [p for p in range(max(2,lo),hi) if all(p%d for d in range(2,int(p**.5)+1))]
P=primes(20,40)            # chain primes
def Kmax(bound): # max number of primes in P dividing a nonzero |k|<=bound
    best=0
    for r in range(1,len(P)+1):
        for c in itertools.combinations(P,r):
            if math.prod(c)<=bound: best=max(best,r)
    return best
def first_primes_prod(bound):
    out=[];p=2
    while math.prod(out)<=bound:
        if all(p%d for d in range(2,int(p**.5)+1)): out.append(p)
        p+=1
    return out
# ---------- stress test of the greedy choice and the halving lemmas ----------
# With chain primes in [20, 40) and small U the chain moduli soon exceed 3U, so the modulus test becomes exact and
# the greedy choice never matters. Here the primes are in [20, 200), U = 10^5, and every input is a multiple of
# 23*29 (or 23*29*31), so the smallest chain primes divide every k and the greedy minimum must avoid them. Every
# chain modulus is asserted to stay below 0.35 * 3U, so no chain is an exact zero test by itself.
SP = primes(20, 200); SU = 10**5
def kmax_sorted(Pr, bound):  # most primes of Pr dividing one nonzero |k| <= bound: the smallest ones give the max
    r, prod = 0, 1
    for p in sorted(Pr):
        if prod*p > bound: break
        prod *= p; r += 1
    return r
SRHO = kmax_sorted(SP, 3*SU)/len(SP)   # Lemma 2.2: at most this fraction of SP divides a nonzero k/m'
def greedy_choice(phi):          # the proof's rule: the minimiser of the potential, ties to the smallest prime
    return min(SP, key=lambda p: (phi(p), p))
def worst_small_choice(phi):     # bad-prime control: the worst of the three smallest primes
    return max(sorted(SP)[:3], key=lambda p: (phi(p), -p))
def fkp_cover(G, R):  # Lemma 2.3(ii) with the corrected ranges, 1-indexed blocks
    chains = {}
    for i in range(1, G+1):
        for j in range(1, G+1):
            for k in range(1, G+1):
                u, v = j - i, k + i
                assert 1 - G <= u <= G - 1 and 2 <= v <= 2*G
                chains.setdefault((u, v), []).append((i, j, k))
    assert len(chains) <= (2*G - 1)**2
    for ch in chains.values():   # each chain is ordered (i up, j up, k down) and holds at most one nontrivial triple
        assert sum(1 for (i, j, k) in ch if (i-1, j-1, k-1) in R) <= 1
def threesum_stress(A, B, C, s, choose):
    """Returns (answer, halving violations). Halving is Lemma 2.5, stated for the queries without a solution:
    |S_l minus Z| <= |S_{l-1}|/4 (equal to the lemma on no-instances)."""
    V = sorted(set(A) | set(B) | set(C)); blocks = [V[i:i+s] for i in range(0, len(V), s)]; G = len(blocks)
    grp = {v: i for i, b in enumerate(blocks) for v in b}
    Bi = [[b for b in B if grp[b] == i] for i in range(G)]; Ci = [[c for c in C if grp[c] == i] for i in range(G)]
    mn = [b[0] for b in blocks]; mx = [b[-1] for b in blocks]
    R = {(i, j, k) for i in range(G) for j in range(G) for k in range(G) if not (mn[i]+mn[j] > mx[k] or mx[i]+mx[j] < mn[k])}
    fkp_cover(G, R)
    Q = [(a, i, j, k) for (i, j, k) in R for a in A if grp[a] == i]
    ks = {q: [q[0]+b-c for b in Bi[q[2]] for c in Ci[q[3]]] for q in Q}
    Z = {q for q in Q if 0 in ks[q]}
    N = lambda m, q: sum(1 for x in ks[q] if x % m == 0)
    r = 1
    while s*s*SRHO**r > 0.25: r += 1
    L = math.ceil(math.log2(len(Q)+1)); S = list(Q); viol = 0
    for _ in range(L):
        m = 1
        for _ in range(r): m *= choose(lambda p: sum(N(m*p, q) for q in S))
        assert m < 0.35*3*SU
        new = [q for q in S if N(m, q) >= 1]
        viol += len([q for q in new if q not in Z]) > len(S)/4
        S = new
    return len(S) > 0, viol
def et_stress(w, n, s, choose):
    """Returns (all-edges answer, halving violations, zero-free slots left in T). Lemma 3.5 is asserted by the caller."""
    Pi = first_primes_prod(3*SU); assert max(Pi) < min(SP)
    h = lambda S: sum(1 for p in Pi if S % p)
    pieces = [list(range(i, min(n, i+s))) for i in range(0, n, s)]
    Q = [(a, b, k) for a in range(n) for b in range(n) for k in range(len(pieces))]
    Sv = {q: [w['ab'][q[0]][q[1]]+w['bc'][q[1]][c]+w['ca'][c][q[0]] for c in pieces[q[2]]] for q in Q}
    NM = lambda M, q: sum(1 for x in Sv[q] if x % M == 0)
    HM = lambda M, q: sum(h(x) for x in Sv[q] if x % M == 0)
    t = len(Pi); r = 1
    while s*t*SRHO**r > 0.5: r += 1
    L = math.ceil(math.log2(len(Q)+1)); Sp = list(Q); T = set(Q); viol = 0
    for _ in range(L):
        m = 1
        for _ in range(r): m *= choose(lambda p: sum(HM(m*p, q) for q in Sp))
        assert m < 0.35*3*SU and all(m % p for p in Pi)
        for q in Sp: assert HM(m, q) == sum(NM(m, q) - NM(m*p, q) for p in Pi)   # Lemma 3.3
        new = [q for q in Sp if HM(m, q) >= 1]
        viol += len(new) > len(Sp)/2
        Sp = new; T = {q for q in T if NM(m, q) >= 1}
    zero_free_in_T = sum(1 for q in T if 0 not in Sv[q])
    return [[any((a, b, k) in T for k in range(len(pieces))) for b in range(n)] for a in range(n)], viol, zero_free_in_T, Sp
def stress_3sum_instances(rng, count):
    for _ in range(count):
        base = 667 * rng.choice([1, 1, 31]); vals = range(-(SU//base)*base, SU+1, base)
        n = rng.randint(2, 6); A, B, C = (rng.sample(vals, n) for _ in range(3))
        if rng.random() < 0.3:
            x = A[0] + B[-1]
            if abs(x) <= SU and x not in C: C[0] = x
        yield A, B, C, rng.randint(1, 3)
def stress_et_instances(rng, count):
    for _ in range(count):
        base = 667 * rng.choice([1, 1, 31]); n = rng.randint(2, 5)
        rw = lambda: [[base*rng.randint(-(SU//base), SU//base) for _ in range(n)] for _ in range(n)]
        w = {'ab': rw(), 'bc': rw(), 'ca': rw()}
        for _ in range(rng.randint(0, 3)):
            a, b, c = rng.randrange(n), rng.randrange(n), rng.randrange(n); v = -(w['bc'][b][c]+w['ca'][c][a])
            if abs(v) <= SU: w['ab'][a][b] = v
        yield w, n, rng.randint(1, 3)
def brute3(A,B,C): return any(a+b in set(C) for a in A for b in B)
# ---------- 3SUM (sec. 2) ----------
def threesum(A,B,C,U,g):
    V=sorted(set(A)|set(B)|set(C)); bs=math.ceil(len(V)/g); blocks=[V[i:i+bs] for i in range(0,len(V),bs)]
    G=len(blocks); grp={v:i for i,b in enumerate(blocks) for v in b}
    Ai=[[a for a in A if grp[a]==i] for i in range(G)]; Bi=[[b for b in B if grp[b]==i] for i in range(G)]; Ci=[[c for c in C if grp[c]==i] for i in range(G)]
    mn=[b[0] for b in blocks]; mx=[b[-1] for b in blocks]
    R=[(i,j,k) for i in range(G) for j in range(G) for k in range(G) if not (mn[i]+mn[j]>mx[k] or mx[i]+mx[j]<mn[k])]
    assert len(R)<=(2*G+1)**2
    s=max([len(x) for x in Ai+Bi+Ci]+[1])
    Q=[(a,i,j,k) for (i,j,k) in R for a in Ai[i]]
    def N(m,q):  # via the set construction of Lemma 2.4
        a,i,j,k=q; M0=math.isqrt(m-1)+1 if m>1 else 1; r=a%m; x=-(-r//M0); y=x*M0-r
        assert 0<=y<M0 and x<=M0
        Xr={}; 
        for b in Bi[j]: Xr[(b+x*M0)%m]=Xr.get((b+x*M0)%m,0)+1
        tot=sum(Xr.get((c+y)%m,0) for c in Ci[k])
        assert tot==sum(1 for b in Bi[j] for c in Ci[k] if (a+b-c)%m==0)
        return tot
    rho=Kmax(3*U)/len(P); r=1
    while s*s*rho**r>0.25: r+=1
    L=math.ceil(math.log2(len(Q)+1)); S=list(Q)
    for l in range(L):
        m=1
        for _ in range(r):
            m*=min(P,key=lambda p:(sum(N(m*p,q) for q in S),p))
        S=[q for q in S if N(m,q)>=1]
    return len(S)>0
bad=0; yes=0
for it in range(300):
    U=200; n=random.randint(2,9)
    A=random.sample(range(-U,U+1),n); B=random.sample(range(-U,U+1),n); C=random.sample(range(-U,U+1),n)
    if it%3==0: C[0]=A[0]+B[-1] if abs(A[0]+B[-1])<=U else C[0]
    t=brute3(A,B,C); yes+=t
    if threesum(A,B,C,U,g=random.randint(1,4))!=t: bad+=1
print("3SUM: instances 300, yes",yes,"mismatches",bad)
# ---------- all-edges ET (sec. 3) ----------
def allEdgesET(w,n,U,s):
    Pi=first_primes_prod(3*U); assert max(Pi)<min(P)
    h=lambda S: sum(1 for p in Pi if S%p)
    pieces=[list(range(i,min(n,i+s))) for i in range(0,n,s)]
    S3=lambda a,b,c: w['ab'][a][b]+w['bc'][b][c]+w['ca'][c][a]
    def NM(M,q): a,b,k=q; return sum(1 for c in pieces[k] if S3(a,b,c)%M==0)
    def HM(M,q): 
        v=sum(NM(M,q)-NM(M*p,q) for p in Pi); a,b,k=q
        assert v==sum(h(S3(a,b,c)) for c in pieces[k] if S3(a,b,c)%M==0); return v
    Q=[(a,b,k) for a in range(n) for b in range(n) for k in range(len(pieces))]
    rho=Kmax(3*U)/len(P); r=1; t=len(Pi)
    while s*t*rho**r>0.5: r+=1
    L=math.ceil(math.log2(len(Q)+1)); Sp=list(Q); T=set(Q)
    for l in range(L):
        m=1
        for _ in range(r): m*=min(P,key=lambda p:(sum(HM(m*p,q) for q in Sp),p))
        Sp=[q for q in Sp if HM(m,q)>=1]; T={q for q in T if NM(m,q)>=1}
    assert not Sp
    return [[any((a,b,k) in T for k in range(len(pieces))) for b in range(n)] for a in range(n)]
bad=0; pos=0
for it in range(120):
    U=60; n=random.randint(2,5)
    rw=lambda: [[random.randint(-U,U) for _ in range(n)] for _ in range(n)]
    w={'ab':rw(),'bc':rw(),'ca':rw()}
    for _ in range(random.randint(0,3)):
        a,b,c=random.randrange(n),random.randrange(n),random.randrange(n); v=-(w['bc'][b][c]+w['ca'][c][a])
        if abs(v)<=U: w['ab'][a][b]=v
    br=[[any(w['ab'][a][b]+w['bc'][b][c]+w['ca'][c][a]==0 for c in range(n)) for b in range(n)] for a in range(n)]
    pos+=sum(map(sum,br))
    if allEdgesET(w,n,U,s=random.randint(1,3))!=br: bad+=1
print("all-edges ET: instances 120, positive pairs",pos,"mismatches",bad)
# ---------- Lemma 4.1 exhaustive, Lemmas 4.2-4.3 end to end ----------
def lem41(v,t,tau):
    b=max(v,t,tau).bit_length()
    return v+t==tau-1 or any((v>>k)+(t>>k) in ((tau>>k)-2,(tau>>k)-3) for k in range(b))
bad=sum(1 for v in range(70) for t in range(70) for tau in range(150) if lem41(v,t,tau)!=(v+t<tau))
print("Lemma 4.1 exhaustive v,t<70, tau<150 mismatches",bad)
def ae_bruteforce(wab,wik,wkj,n):  # all-edges ET oracle (brute force) on parts I,K,J
    return [[any(wab[i][j]+wik[i][k]+wkj[k][j]==0 for k in range(n)) for j in range(n)] for i in range(n)]
def pairs_neg(A,B,tau,V,n):
    K=(4*V+1).bit_length(); v=[[A[i][k]+V for k in range(n)] for i in range(n)]; t=[[B[k][j]+V for j in range(n)] for k in range(n)]
    u=[[max(tau[i][j]+2*V,0) for j in range(n)] for i in range(n)]
    out=[[False]*n for _ in range(n)]; calls=[]
    calls.append(([[1-u[i][j] for j in range(n)] for i in range(n)],v,t))
    for kk in range(K):
        for jj in (2,3):
            calls.append(([[jj-(u[i][j]>>kk) for j in range(n)] for i in range(n)],[[x>>kk for x in row] for row in v],[[x>>kk for x in row] for row in t]))
    for wab,wik,wkj in calls:
        r=ae_bruteforce(wab,wik,wkj,n)
        for i in range(n):
            for j in range(n): out[i][j]|=r[i][j]
    return out
def minplus(A,B,V,n):
    lo=[[-2*V]*n for _ in range(n)]; hi=[[2*V]*n for _ in range(n)]
    for _ in range(math.ceil(math.log2(4*V+1))):
        tau=[[(lo[i][j]+hi[i][j])//2+1 for j in range(n)] for i in range(n)]
        r=pairs_neg(A,B,tau,V,n)
        for i in range(n):
            for j in range(n):
                if r[i][j]: hi[i][j]=tau[i][j]-1
                else: lo[i][j]=tau[i][j]
    assert lo==hi; return lo
bad=0
for it in range(150):
    n=random.randint(1,4); V=random.choice([1,2,3,7,20])
    A=[[random.randint(-V,V) for _ in range(n)] for _ in range(n)]; B=[[random.randint(-V,V) for _ in range(n)] for _ in range(n)]
    C=[[min(A[i][k]+B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
    if minplus(A,B,V,n)!=C: bad+=1
print("(min,+) via all-edges ET: instances 150, mismatches",bad)
# ---------- stress run (greedy choice and halving exercised) ----------
srng = random.Random(23); bad = yes = 0
for A, B, C, s in stress_3sum_instances(srng, 120):
    t = brute3(A, B, C); yes += t
    got, viol = threesum_stress(A, B, C, s, greedy_choice)
    assert viol == 0          # Lemma 2.5 on every chain
    bad += got != t
print("stress 3SUM (primes in [20,200), U=1e5, inputs multiples of 667): instances 120, yes", yes, "mismatches", bad)
bad = pos = 0
for w, n, s in stress_et_instances(srng, 60):
    br = [[any(w['ab'][a][b]+w['bc'][b][c]+w['ca'][c][a] == 0 for c in range(n)) for b in range(n)] for a in range(n)]
    pos += sum(map(sum, br))
    got, viol, zf, Sp = et_stress(w, n, s, greedy_choice)
    assert viol == 0 and zf == 0 and not Sp   # Lemma 3.5 on every chain, S'_L empty, Lemma 3.6
    bad += got != br
print("stress all-edges ET: instances 60, positive pairs", pos, "mismatches", bad)
