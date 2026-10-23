#!/usr/bin/env bash
# Root files (batch 203, commission section 3): every `.lean` file at the repository root, whether
# a `lean_lib` of `lakefile.toml` builds it, and how many times the word `sorry` occurs in it
# (as a whole word, comments included). Also: the `.lean` files under `HPC/` that no `lean_lib`
# builds (not in the import closure of `HPC.lean`, `HPCExtra.lean`, `HPCArchive.lean` or `HPCCensus.lean`, i.e.
# absent from `doc/depcensus/modules.tsv`).
# Run from the repository root after `lake env lean scripts/DepCensus.lean`:
#   bash scripts/rootfiles.sh
set -euo pipefail
out=doc/depcensus/root-files.tsv
# the lean_lib roots of lakefile.toml
roots=$(grep -A2 '^\[\[lean_lib\]\]' lakefile.toml | sed -n 's/^roots = \[\(.*\)\]/\1/p' | tr -d '"' | tr ',' '\n' | tr -d ' ')
{
  printf 'file\tbuilt_by_lean_lib\tsorry\n'
  for f in *.lean; do
    mod=${f%.lean}
    built=no
    for r in $roots; do
      if [ "$r" = "$mod" ]; then built="yes ($r)"; fi
    done
    n=$( (grep -ow 'sorry' "$f" || true) | wc -l | tr -d ' ')
    printf '%s\t%s\t%s\n' "$f" "$built" "$n"
  done
} > "$out"
cat "$out"
# files under HPC/ that no lean_lib builds
out2=doc/depcensus/unbuilt-files.txt
cut -f1 doc/depcensus/modules.tsv | tail -n +2 | sed 's|\.|/|g; s|$|.lean|' | sort > /tmp/built-files.txt
find HPC -name '*.lean' | sort > /tmp/all-files.txt
comm -13 /tmp/built-files.txt /tmp/all-files.txt > "$out2"
echo "files under HPC/ built by no lean_lib: $(wc -l < "$out2")"
