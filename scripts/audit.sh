#!/usr/bin/env bash
# Axiom audit for every module of this repository.
# Each file is compiled as a copy that ends with `#print axioms` of every theorem it declares.
# The audit fails on any error or warning, on `sorry`, on a missing axiom report, or on an axiom
# outside propext, Classical.choice and Quot.sound.
# Usage, from the repository root after `lake exe cache get`:   scripts/audit.sh
# Set LEAN to another command that compiles one file if needed (default: `lake env lean`).
set -uo pipefail
cd "$(dirname "$0")/.."
LEAN="${LEAN:-lake env lean}"
mkdir -p .lake/audit
fail=0
for f in $(find OnDemandPrecision -name '*.lean' | sort); do
  ns=$(grep -m1 -oE '^namespace [A-Za-z0-9_.]+' "$f" | cut -d' ' -f2)
  names=$(grep -oE '^theorem [^ :]+' "$f" | awk '{print $2}')
  t=".lake/audit/$(basename "$f")"
  { cat "$f"; echo; for n in $names; do echo "#print axioms ${ns}.${n}"; done; } > "$t"
  out=$($LEAN "$t" 2>&1)
  if grep -qE ':[0-9]+:[0-9]+: (error|warning)' <<<"$out" || grep -q 'sorryAx' <<<"$out"; then
    echo "FAIL $f"; echo "$out" | head -40; fail=1; continue
  fi
  flat=$(tr '\n' ' ' <<<"$out" | tr -s ' ')
  bad=$(grep -oE "depends on axioms: \[[^]]*\]" <<<"$flat" |
    grep -vE "^depends on axioms: \[((propext|Classical\.choice|Quot\.sound)(, )?)*\]$" || true)
  n_rep=$(grep -oE "depends on axioms|does not depend on any axioms" <<<"$flat" | wc -l)
  n_thm=$(wc -w <<<"$names")
  if [ -n "$bad" ] || [ "$n_rep" -ne "$n_thm" ]; then
    echo "FAIL $f (axioms: ${bad:-none}; $n_rep of $n_thm reports)"; fail=1
  else
    echo "OK   $f ($n_thm theorems)"
  fi
done
exit $fail
