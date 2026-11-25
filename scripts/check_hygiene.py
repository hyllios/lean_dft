#!/usr/bin/env python3
"""Source hygiene checks for lean_dft (see docs/AGENTS.md §3).

Enforced (exit 1):
  * forbidden constructs: `sorry`, `native_decide`, `implemented_by`, `unsafe`, `axiom` declarations, `admit`.
Reported (exit 1 only with --strict, to be switched on once the backlog is cleared):
  * `set_option maxHeartbeats` without a `-- heartbeats: <reason>` comment on the same or the previous line;
  * files without a module docstring (`/-!`).
"""
import os, re, sys
ROOT = os.environ.get('HYGIENE_ROOT') or os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LIBS = ['ForMathlib', 'QM', 'DFT']
strict = '--strict' in sys.argv
FORBID = [(re.compile(r'\bsorry\b'), 'sorry'), (re.compile(r'\bnative_decide\b'), 'native_decide'),
          (re.compile(r'\bimplemented_by\b'), 'implemented_by'), (re.compile(r'^\s*(private\s+|protected\s+)?unsafe\b'), 'unsafe'),
          (re.compile(r'^\s*axiom\s'), 'axiom declaration'), (re.compile(r'\badmit\b'), 'admit')]
def strip_comments(line, in_block):
    out, i = '', 0
    while i < len(line):
        if in_block:
            j = line.find('-/', i)
            if j < 0: return out, True
            in_block, i = False, j + 2
        else:
            if line.startswith('--', i): break
            if line.startswith('/-', i): in_block, i = True, i + 2; continue
            out += line[i]; i += 1
    return out, in_block
errors, hb_missing, no_doc, nfiles = [], [], [], 0
for lib in LIBS:
    for dp, _, fs in os.walk(os.path.join(ROOT, lib)):
        for f in sorted(fs):
            if not f.endswith('.lean'): continue
            p = os.path.join(dp, f); rel = os.path.relpath(p, ROOT); nfiles += 1
            lines = open(p, encoding='utf-8').read().split('\n')
            if not any(l.lstrip().startswith('/-!') for l in lines): no_doc.append(rel)
            in_block = False
            for k, raw in enumerate(lines, 1):
                code, in_block = strip_comments(raw, in_block)
                for rx, what in FORBID:
                    if rx.search(code): errors.append(f'{rel}:{k}: forbidden `{what}`')
                if 'maxHeartbeats' in code and 'set_option' in code:
                    prev = lines[k - 2] if k >= 2 else ''
                    if 'heartbeats:' not in raw and 'heartbeats:' not in prev:
                        hb_missing.append(f'{rel}:{k}')
for e in errors: print(e)
if strict:
    for h in hb_missing: print(f'{h}: maxHeartbeats without `-- heartbeats: <reason>`')
    for d in no_doc: print(f'{d}: no module docstring')
print(f'hygiene: {nfiles} files; {len(errors)} forbidden construct(s); '
      f'{len(hb_missing)} unjustified maxHeartbeats; {len(no_doc)} file(s) without module docstring')
sys.exit(1 if errors or (strict and (hb_missing or no_doc)) else 0)
