#!/usr/bin/env python3
"""gen-audit76.py -- writes HPC/Fold/Audit76.lean and the modules of Audit76Long/ from the
stored witness files and the ExtendsSubBand witnesses found by ext76.py (`LEAN` lines of its
output, collected in ext76-least.log).  Every clause is then checked by the kernel; nothing
generated here is trusted."""
import sys

def hexnum(vals):
    assert all(0 <= v <= 15 for v in vals)
    return '0x' + ''.join('%x' % v for v in reversed(vals))

def rd(path):
    L = open(path).read().split('\n')
    return [int(x) for x in L[1].split()]

def data(path, n):
    rho = rd(path)
    assert len(rho) == n
    return f'''/-- The {n} links of `ρ` of `{path}`, one base-sixteen digit each, link `j` the `j`-th
digit. -/
def rhoNat : ℕ := {hexnum(rho)}

/-- The point sequence of `{path}`. -/
def rho : Fin {n} → ℤ := fun j => (((rhoNat >>> (4 * j.val)) &&& 15 : ℕ) : ℤ)
'''

def wit(name, n, i, L, H, k, Lp, Hp, s, ts, e, doc=''):
    tsl = '[' + ', '.join(map(str, ts)) + ']'
    return f'''/-- The basepoint {i}. -/
def basept{name} : Fin {n} := ⟨{i}, by omega⟩

/-- **The extension law at basepoint {i}** (band `[{L}, {H}]`, least leg count {k}).{doc}
The witness: `L' = {Lp}`, `H' = {Hp}`, `w'` from `{s}` through `{tsl}`, the appended leg to
`{e}`. -/
theorem extendsSubBand{name} : ExtendsSubBand rho basept{name} {L} {H} {k} :=
  extendsSubBand_of_witness {Lp} {Hp} {s} {e} {tsl} (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
'''

def lean_lines(logpath):
    out = {}
    for ln in open(logpath):
        ln = ln.strip()
        if not ln.startswith('LEAN '):
            continue
        a, e = ln.split('|')
        f = a.split()[1:]
        path = f[0]; n, i, L, H, k, Lp, Hp, s = map(int, f[1:9]); ts = list(map(int, f[9:]))
        out[path] = (n, i, L, H, k, Lp, Hp, s, ts, int(e))
    return out

if __name__ == '__main__':
    W = lean_lines(sys.argv[1])
    mode = sys.argv[2]
    if mode == 'long':
        # one data module per pair, one module per basepoint
        groups = {}
        for path, v in W.items():
            groups.setdefault((v[0], rd(path)[:50].__repr__(), tuple(rd(path)[-50:])), []).append((path, v))
        for tag, paths in [(a, b.split(',')) for a, b in (x.split('=') for x in sys.argv[3:])]:
            first = paths[0]
            n = W[first][0]
            hdr = f'''import HPC.Fold.Target76

/-! The data of `{first}` ({n} links) for the kernel checks of `Audit76Long`. -/

namespace HPC.Fold.Audit76.{tag}

{data(first, n)}
end HPC.Fold.Audit76.{tag}
'''
            open(f'Audit76Long/{tag}Data.lean', 'w').write(hdr)
            for j, p in enumerate(paths):
                assert rd(p) == rd(first)
                v = W[p]
                name = f'_{v[1]}'
                src = f'''import Audit76Long.{tag}Data

/-! The extension law at `{p}`, basepoint {v[1]}, put to the kernel. The arms here run to
{max(v[0] - v[1], v[1] + 1)} links, past the default thread stack of the kernel's recursion, which is
why this module is in the library `Audit76Long` (built with a larger thread stack) rather than in
`HPC`. -/

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

namespace HPC.Fold.Audit76.{tag}

{wit(name, *v, doc=' Source: `' + p + '`.')}
end HPC.Fold.Audit76.{tag}
'''
                open(f'Audit76Long/{tag}B{v[1]}.lean', 'w').write(src)
    else:
        print('usage')
