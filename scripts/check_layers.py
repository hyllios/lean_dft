#!/usr/bin/env python3
"""Layering check for lean_dft.

Rules (see docs/ARCHITECTURE.md):
  1. Library order ForMathlib <- QM <- DFT: a module may not import a library that comes after its own.
     PhyslibAlpha (unreviewed) may not be imported at all.
  2. Folder DAG: let the folder of a module be its parent directory. The folder-level import graph must
     have no cycles (a folder may import itself and other folders, but never in a loop).
Exit code 1 on violations unless --report-only.
"""
import os, sys, collections
LIBS = ['ForMathlib', 'QM', 'DFT']
ROOT = os.environ.get('LAYERS_ROOT') or os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
report_only = '--report-only' in sys.argv

mods = {}
for lib in LIBS:
    for dp, _, fs in os.walk(os.path.join(ROOT, lib)):
        for f in fs:
            if f.endswith('.lean'):
                p = os.path.join(dp, f)
                m = os.path.relpath(p, ROOT)[:-5].replace(os.sep, '.')
                imps = []
                for line in open(p, encoding='utf-8'):
                    t = line.split()
                    if t[:1] == ['import'] and len(t) >= 2:
                        imps.append(t[1])
                    elif t[:2] == ['public', 'import'] and len(t) >= 3:
                        imps.append(t[2])
                mods[m] = imps

errors = []
for m, imps in mods.items():
    lm = LIBS.index(m.split('.')[0])
    for i in imps:
        top = i.split('.')[0]
        if top == 'PhyslibAlpha':
            errors.append(f'{m} imports unreviewed PhyslibAlpha module {i}')
        if top in LIBS and LIBS.index(top) > lm:
            errors.append(f'library order: {m} ({LIBS[lm]}) imports {i} ({top})')

folder = lambda m: '.'.join(m.split('.')[:-1])
E = collections.defaultdict(set); witness = {}
for m, imps in mods.items():
    for i in imps:
        if i in mods:
            a, b = folder(m), folder(i)
            if a != b:
                E[a].add(b); witness.setdefault((a, b), f'{m} -> {i}')

sys.setrecursionlimit(100000)
idx, low, st, on, comps, c = {}, {}, [], set(), [], [0]
def dfs(v):
    idx[v] = low[v] = c[0]; c[0] += 1; st.append(v); on.add(v)
    for w in E.get(v, ()):
        if w not in idx: dfs(w); low[v] = min(low[v], low[w])
        elif w in on: low[v] = min(low[v], idx[w])
    if low[v] == idx[v]:
        comp = []
        while True:
            w = st.pop(); on.discard(w); comp.append(w)
            if w == v: break
        comps.append(comp)
for v in sorted(set(E) | {b for s in E.values() for b in s}):
    if v not in idx: dfs(v)
for comp in comps:
    if len(comp) > 1:
        cs = set(comp)
        errors.append('folder cycle: ' + ' , '.join(sorted(comp)))
        for (a, b), w in sorted(witness.items()):
            if a in cs and b in cs: errors.append(f'      {w}')

n_cycles = sum(1 for e in errors if e.startswith('folder cycle'))
if errors:
    print('\n'.join(errors))
print(f'layering: {len(mods)} modules, {n_cycles} folder cycle(s), '
      f'{sum(1 for e in errors if e.startswith("library order") or "PhyslibAlpha" in e)} library-order violation(s)')
sys.exit(0 if (not errors or report_only) else 1)
