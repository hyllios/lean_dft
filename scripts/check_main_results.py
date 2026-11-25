#!/usr/bin/env python3
"""Main results (docs/MAIN_RESULTS.md) must exist and must be referenced in the blueprint.

usage: check_main_results.py [--strict] [--list FILE]
  --list FILE  write the listed names to FILE (one per line) for `lake exe checkdecls FILE` (existence check)
  --strict     also fail if a listed name is not referenced by a \\lean{...} in blueprint/src
"""
import os, re, sys, glob
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
table = open(os.path.join(ROOT, 'docs', 'MAIN_RESULTS.md'), encoding='utf-8').read()
table = table.split('## Names in the README that no longer exist')[0]
names = re.findall(r'^\| `((?:DFT|QM|ForMathlib)\.[^`]+)` \|', table, flags=re.M)
refs = set()
for f in glob.glob(os.path.join(ROOT, 'blueprint', 'src', '**', '*.tex'), recursive=True):
    for m in re.findall(r'\\lean\{([^}]*)\}', open(f, encoding='utf-8').read()):
        refs |= {x.strip() for x in m.split(',') if x.strip()}
if '--list' in sys.argv:
    open(sys.argv[sys.argv.index('--list') + 1], 'w').write(''.join(n + '\n' for n in names))
missing = [n for n in names if n not in refs]
for n in missing: print(f'main result not in blueprint: {n}')
print(f'main results: {len(names)} listed, {len(names) - len(missing)} in the blueprint, {len(missing)} missing')
sys.exit(1 if missing and '--strict' in sys.argv else 0)
