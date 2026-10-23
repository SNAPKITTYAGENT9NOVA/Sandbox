# Usage: python3 gen_oeis_tests.py <formal-conjectures>/FormalConjectures/OEIS ../src > TestOeis.mod
# Generates tests/TestOeis.mod from the `theorem a_K : a K = V` statements of the Lean sources.
import re, sys, os
src = sys.argv[1]; srcdir = sys.argv[2]
BOUND = {}                     # documented bounds "n <= N" from the .def comments
def procs(defpath):
    out = {}
    for m in re.finditer(r'PROCEDURE (A\d{6})\w* \(n: LONGCARD; VAR r: (\w+(?:\.T)?)\) : BOOLEAN;([^\n]*)', open(defpath).read()):
        out.setdefault(m.group(1), m.group(2))
        b = re.search(r'\bn <= (\d+)(?:\^(\d+))?', m.group(3))
        if b: BOUND[m.group(1)] = int(b.group(1)) ** int(b.group(2) or 1)
    return out
# Lean-checked values outside the documented capacity of the Modula-2 procedure: FALSE expected
OUTSIDE = {('A358684', 7): 'minFac (fermatNumber 7) = 59649589127497217 is beyond the 2^32 trial bound'}
nat = procs(os.path.join(srcdir, 'OeisNat.def'))
intm = procs(os.path.join(srcdir, 'OeisInt.def'))
lines = []; count = 0; files = 0
for name, mod in sorted(list((k, 'OeisNat') for k in nat) + list((k, 'OeisInt') for k in intm)):
    typ = nat.get(name) if mod == 'OeisNat' else intm.get(name)
    f = os.path.join(src, str(int(name[1:])) + '.lean')
    if not os.path.exists(f): continue
    text = open(f).read()
    tests = re.findall(r'^theorem a_\w+ : a (\d+) = (-?\d+) := by', text, re.M)
    if not tests: continue
    files += 1
    lines.append(f'  (* {os.path.basename(f)} *)')
    for k, v in tests:
        v = int(v); count += 1
        call = f'{mod}.{name}({k}, '
        why = OUTSIDE.get((name, int(k))) or (f'n > {BOUND[name]}' if name in BOUND and int(k) > BOUND[name] else None)
        if why:
            var = {'LONGCARD': 'n', 'LONGINT': 'i'}.get(typ, 'q')
            lines.append(f'  ok := {call}{var});')
            lines.append(f'  Check.Fails("{name}", {k}, ok);   (* Lean value {v}; {why} *)')
            continue
        if typ == 'LONGCARD':
            lines.append(f'  ok := {call}n);')
            if v < 2**64: lines.append(f'  Check.Nat("{name}", {k}, ok, n, {v});')
            else: lines.append(f'  Check.Fails("{name}", {k}, ok);   (* {v} exceeds 2^64 - 1 *)')
        elif typ == 'LONGINT':
            lines.append(f'  ok := {call}i);')
            if -2**63 <= v < 2**63: lines.append(f'  Check.Int("{name}", {k}, ok, i, {v});')
            else: lines.append(f'  Check.Fails("{name}", {k}, ok);')
        else:
            lines.append(f'  ok := {call}q);')
            lines.append(f'  Check.RatInt("{name}", {k}, ok, q, {v});')
body = "\n".join(lines)
print(f'''(* SPDX-License-Identifier: AGPL-3.0-only *)
(* Copyright (C) 2026 SNAPKITTYWEST (Sovereign Kernel Project) *)
MODULE TestOeis;
(* Expected values are the `theorem a_K : a K = V` statements of the corresponding
   FormalConjectures/OEIS/*.lean files ({count} values from {files} files), which Lean checks by
   decide / native_decide / norm_num. A value above 2^64 - 1 must make the procedure return FALSE. *)

IMPORT Check, OeisNat, OeisInt, Rat;

VAR
  n: LONGCARD; i: LONGINT; q: Rat.T; ok: BOOLEAN;

BEGIN
{body}
  Check.Done("TestOeis")
END TestOeis.''')
