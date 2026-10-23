import sys
from itertools import product

def crooked(f):
    n=len(f)
    for s in range(n):
        for t in range(s+1,n):
            if abs(f[t]-f[s])>=3:
                ok=False
                for r in range(s+1,t):
                    for r2 in range(r+1,t):
                        c=True
                        if f[s]<f[t]:
                            c = (f[t]-2<=f[r]<=f[t]-1) and (f[s]<=f[r2]<=f[s]+1)
                        if c and f[t]<f[s]:
                            c = (f[t]<=f[r]<=f[t]+1) and (f[s]-2<=f[r2]<=f[s]-1)
                        if c:
                            ok=True; break
                    if ok: break
                if not ok: return False
    return True

def phases(A):
    n=len(A); ph=[0]*n; cur=0
    for j in range(n):
        if j>0 and A[j]<=A[j-1]: cur=1
        ph[j]=cur
    return ph

def hStarArm(A,p):
    best=None
    for j in range(len(A)):
        if all(A[jp]>=p-1 for jp in range(j+1)):
            v=A[j]
            if best is None or v>best: best=v
    return best

def hReach(A,p):
    ph=phases(A); best=None
    for j in range(len(A)):
        if all(A[jp]>=p-1 for jp in range(j+1)):
            v=A[j]+ph[j]
            if best is None or v>best: best=v
    return best

def neg(A): return [-x for x in A]

def lStarArm(A,p): return -hStarArm(neg(A),-p)

def drops(A,p): return any(x<=p-2 for x in A)

def okLam(A,p,h): return (not drops(A,p)) or h<=hReach(A,p)
def okVee(A,p,l): return okLam(neg(A),-p,-l)

def valleyBefore(A,L,h,s):
    n=len(A)
    for u in range(s,n):
        if A[u]>h+1:
            if not any(A[j]<=L+1 for j in range(s,u)): return False
    return True

def checkseq(f,report):
    n=len(f); H=max(f); L=min(f)
    if L+3>H: return True
    for i in range(n):
        p=f[i]
        G=f[i:]; T=f[i::-1]
        hG=hStarArm(G,p); hT=hStarArm(T,p)
        lG=lStarArm(G,p); lT=lStarArm(T,p)
        hStar=min(max(max(hG,hT),max(p,L+1)),max(H-1,p))
        lStar=max(min(min(lG,lT),min(p,H-1)),min(L+1,p))
        er=(okLam(G,p,hStar) and okLam(T,p,hStar)) or (okVee(G,p,lStar) and okVee(T,p,lStar))
        if not er:
            report.setdefault('ExitReach',[]).append((f,i))
        # HighExitValley
        for A in (G,T):
            ph=phases(A)
            for s in range(len(A)+1):
                if all(A[j]+ph[j]<hStar for j in range(s)):
                    if not valleyBefore(A,L,hStar,s):
                        report.setdefault('HighExitValley',[]).append((f,i,s))
        # LowExitPeak  (ValleyBefore of negated arm at -lStar with lower bound -H)
        for A in (G,T):
            B=neg(A); ph=phases(B)
            for s in range(len(B)+1):
                if all(B[j]+ph[j]< -lStar for j in range(s)):
                    if not valleyBefore(B,-H,-lStar,s):
                        report.setdefault('LowExitPeak',[]).append((f,i,s))
    return True

def gen(n,levels):
    for start in range(levels):
        stack=[[start]]
        while stack:
            cur=stack.pop()
            if len(cur)==n:
                yield cur
            else:
                for d in (-1,0,1):
                    v=cur[-1]+d
                    if 0<=v<levels:
                        stack.append(cur+[v])

report={}
count=0
maxn=int(sys.argv[1]) if len(sys.argv)>1 else 11
levels=int(sys.argv[2]) if len(sys.argv)>2 else 6
for n in range(4,maxn+1):
    c=0
    for f in gen(n,levels):
        if crooked(f):
            c+=1
            checkseq(f,report)
    count+=c
    print("len",n,"crooked",c,"report keys",{k:len(v) for k,v in report.items()},flush=True)
print("total crooked",count)
for k,v in report.items():
    print(k,"failures",len(v),v[:3])
