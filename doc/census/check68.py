"""check68.py -- an independent check of the probe-68 counterexamples.

Written from the definitions in HPC/Fold/LandList.lean and HPC/Fold/Itinerary.lean,
independently of probe68.c: walkList / walkLen / walkStop / walkLevel, the corrected
landmark sentence LandWalkP with the clause of batch 66 section 2.3 added, and FoldsOnto.
"""
import re, sys

def parse_arm(s):
    return [int(t) for t in re.findall(r'-?\d', s)]

def walk(s, ts):
    lv = [s]; stop = [0]; level = [s]; cur = s
    for t in ts:
        while cur != t:
            cur += 1 if t > cur else -1
            lv.append(cur)
        stop.append(len(lv) - 1); level.append(cur)
    return lv, stop, level

def served(lv, v, p):  return abs(v - lv[p]) <= 1
def band_ok(lv, f):    return all(any(served(lv, v, p) for p in range(len(lv))) for v in f)
def is_lip(f):         return all(abs(f[i+1] - f[i]) <= 1 for i in range(len(f) - 1))

def folds(lv, f):
    reach = {0} if served(lv, f[0], 0) else set()
    for v in f[1:]:
        nxt = {q for p in reach for q in (p-1, p, p+1)
               if 0 <= q < len(lv) and served(lv, v, q)}
        if not nxt: return False
        reach = nxt
    return bool(reach)

def sentence(lv, stop, level, f):
    """LandWalkP with the added clause, chains decided by the backwards greedy."""
    n = len(f)
    for d in range(n):
        P = next((p for p in range(len(lv)) if served(lv, f[d], p)), None)
        if P is None: return False
        for r in range(len(stop)):
            if stop[r] > P: continue
            jr = next((j for j in range(d - (P - stop[r]), -1, -1)
                       if abs(f[j] - level[r]) <= 1), None)
            if jr is None: return False
            # the added clause of batch 66 section 2.3
            for e in range(n):
                last = max((p for p in range(len(lv)) if served(lv, f[e], p)), default=None)
                if last is not None and last < stop[r] and e >= jr: return False
            cur = jr
            for u in range(r - 1, -1, -1):
                gap = stop[u+1] - stop[u]
                found = next((j for j in range(cur - gap, -1, -1)
                              if abs(f[j] - level[u]) <= 1), None)
                if found is None: return False
                cur = found
    return True

CASES = [
    (0, [4, 1, 5], "-101210-10-10101223343234343210-101232233456"),
    (0, [5, 2, 6], "-100110-1-10-101233343210010-1010123343456667"),
    (0, [5, 1, 6, 0], "-10-1-1-1010-1-10-10112123434334433210-101234567"),
    (0, [5, 1, 6, 0], "-10-100-10012223232321212223443210-101234567"),
]

for s, ts, arm in CASES:
    f = parse_arm(arm)
    lv, stop, level = walk(s, ts)
    print("walk s=%d ts=%s  walkList=%s  stops=%s  levels=%s" % (s, ts, lv, stop, level))
    print("  arm (%d times): %s" % (len(f), f))
    print("  1-Lipschitz            :", is_lip(f))
    print("  |f 0 - s| <= 1         :", abs(f[0] - s) <= 1)
    print("  every level served     :", band_ok(lv, f))
    print("  sentence + added clause:", sentence(lv, stop, level, f))
    print("  folds onto the walk    :", folds(lv, f))
    print("  a counterexample       :",
          is_lip(f) and abs(f[0]-s) <= 1 and band_ok(lv, f)
          and sentence(lv, stop, level, f) and not folds(lv, f))
