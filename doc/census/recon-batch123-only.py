"""Batch 123, item 3: census for the only-clause of Bing's Theorem 3 (and its pair form).

Model of batch 122 (BHyp): fine links t < n with coarse interval [rho t, sigma t] (width <= 1,
adjacent links compatible), meeting table T = forced meetings plus any subset of the possible
unforced ones, crookedness (1948) read with T.  A solution is a time function beta with
beta(i) = 0, moving by at most one, every fibre in a window {j, j+1} (j <= sigma, rho <= j+1),
and Bing's end clause ("or" reading) for the end links that meet level 0 or level K-1.

Modes:
  only N K       interior basepoints i whose link may be covered by its neighbours:
                 T(i) contained in T(i-1) u T(i+1), and every coarse link containing both
                 neighbours contains link i.  Question: is there a solution with a neighbour of
                 i in the block of i (so that the only-clause holds, onlyIn_of_neighbour)?
  nocontain N K  the same without the containment constraint (it is forced in chains: a link
                 covered by two neighbours lying in e_j lies in e_j); shows failures.
  pair N K       every adjacent pair (i, i+1) lying in a common coarse link: is there a
                 solution with both in block 0?  (Theorem3Pair)
Not Lean-checked.
"""
import sys
sys.setrecursionlimit(10000)

def seqs(n,K):
    # (rho,sigma) sequences
    res=[]
    def rec(pre):
        if len(pre)==n: res.append(tuple(pre)); return
        for r in range(K):
            for s in (r,r+1):
                if s>=K: continue
                if pre:
                    r0,s0=pre[-1]
                    if not (s0<=r+1 and s<=r0+1): continue
                rec(pre+[(r,s)])
    rec([]); return res

def forced(rs,n,K):
    T=[set() for _ in range(n)]
    for t in range(n):
        r,s=rs[t]
        for j in range(r,s+1):
            T[t].add(j)
            if t>0: T[t-1].add(j)
            if t+1<n: T[t+1].add(j)
    return T

def poss(rs,t,K):
    r,s=rs[t]
    return [j for j in range(K) if s<=j+1 and j<=r+1]

def crooked(rs,T,n,K):
    for s_ in range(n):
        for t in range(s_+1,n):
            for a in T[s_]:
                for b in T[t]:
                    if a+3<=b:
                        ok=False
                        for r in range(s_+1,t):
                            if rs[r][0]<=b-1<=rs[r][1]:
                                for r2 in range(r+1,t):
                                    if rs[r2][0]<=a+1<=rs[r2][1]: ok=True;break
                            if ok:break
                        if not ok: return False
                    if b+3<=a:
                        ok=False
                        for r in range(s_+1,t):
                            if rs[r][0]<=b+1<=rs[r][1]:
                                for r2 in range(r+1,t):
                                    if rs[r2][0]<=a-1<=rs[r2][1]: ok=True;break
                            if ok:break
                        if not ok: return False
    return True

def wins(rs,t,K):
    r,s=rs[t]
    return frozenset(j for j in range(K) if j<=s and r<=j+1)

def search(rs,T,n,K,i,need_nb,extra=None):
    # find beta: beta[i]=0, lipschitz, windows, end clause; if need_nb, beta[i-1]==0 or beta[i+1]==0
    W=[wins(rs,t,K) for t in range(n)]
    lowW=frozenset([0]) # block in e1+e2 : all rho<=1  -> modeled as condition on links
    beta=[None]*n
    order=[i]+[t for d in range(1,n) for t in (i-d,i+d) if 0<=t<n]
    # assign along order, each must be adjacent to assigned
    blocks={}  # v -> (windowset, lowok, highok)
    def endok():
        for e in (0,n-1):
            if (0 in T[e]) or (K-1 in T[e]):
                v=beta[e]
                if not (all(rs[t][0]<=1 for t in range(n) if beta[t]==v) or all(K-2<=rs[t][1] for t in range(n) if beta[t]==v)):
                    return False
        return True
    def rec(k):
        if k==len(order):
            if need_nb and not ((i>0 and beta[i-1]==0) or (i+1<n and beta[i+1]==0)): return False
            if extra and not extra(beta): return False
            return endok()
        t=order[k]
        nb = t+1 if t<i else t-1
        cands=[0] if t==i else [beta[nb]-1,beta[nb],beta[nb]+1]
        for v in cands:
            if v<0: continue
            old=blocks.get(v)
            w = W[t] if old is None else old & W[t]
            if not w: continue
            blocks[v]=w; beta[t]=v
            if rec(k+1): return True
            beta[t]=None
            if old is None: del blocks[v]
            else: blocks[v]=old
        return False
    return rec(0)


def instances(n,K):
    for rs in seqs(n,K):
        F=forced(rs,n,K)
        opt=[(t,j) for t in range(n) for j in poss(rs,t,K) if j not in F[t]]
        for m in range(1<<len(opt)):
            T=[set(x) for x in F]
            for b,(t,j) in enumerate(opt):
                if m>>b&1: T[t].add(j)
            if crooked(rs,T,n,K): yield rs,T

def main(mode,n,K):
    cnt=0; bad=0
    for rs,T in instances(n,K):
        if mode in ('only','nocontain'):
            for i in range(1,n-1):
                if not all((j in T[i-1]) or (j in T[i+1]) for j in T[i]): continue
                if mode=='only' and not all(rs[i][0]<=j<=rs[i][1] for j in range(K)
                        if rs[i-1][0]<=j<=rs[i-1][1] and rs[i+1][0]<=j<=rs[i+1][1]): continue
                cnt+=1
                if not search(rs,T,n,K,i,True):
                    bad+=1
                    if bad<=5: print("FAIL",rs,[sorted(x) for x in T],"i =",i)
        else:
            for i in range(0,n-1):
                a,b_=rs[i],rs[i+1]
                if max(a[0],b_[0])>min(a[1],b_[1]): continue
                cnt+=1
                if not search(rs,T,n,K,i,False,extra=lambda be:be[i+1]==0):
                    bad+=1
                    if bad<=5: print("FAIL",rs,[sorted(x) for x in T],"i =",i)
    print(mode,"n =",n,"K =",K,"instances",cnt,"failures",bad,flush=True)

if __name__=="__main__":
    main(sys.argv[1],int(sys.argv[2]),int(sys.argv[3]))
