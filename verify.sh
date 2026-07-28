#!/bin/sh
# Typecheck every development and fail if the kernel reports a `sorry` or an error.
#
# `sorry` does not stop Lean from producing a build: it emits a WARNING and leaves
# an unsound theorem behind, and `lean` still exits 0. A script that only checked
# the exit status would therefore pass a file full of admitted proofs -- this one
# did, until a planted `sorry` proved it.
#
# Note the quoting: Lean writes  declaration uses `sorry`  with BACKTICKS. Matching
# on 'sorry' in single quotes silently never fires, which is exactly how the first
# version of this script passed its own negative control.
set -eu
status=0
for f in Bound/*.lean; do
    if ! out=$(lake env lean "$f" 2>&1); then
        printf '  FAIL  %-26s lean exited non-zero\n' "$f"; status=1; continue
    fi
    if printf '%s' "$out" | grep -q "declaration uses"; then
        printf '  FAIL  %-26s uses sorry\n' "$f"; status=1; continue
    fi
    if printf '%s' "$out" | grep -qi "error:"; then
        printf '  FAIL  %-26s has errors\n' "$f"; status=1; continue
    fi
    printf '  ok    %-26s 0 sorry, 0 errors\n' "$f"
done
if [ "$status" -eq 0 ]; then
    printf '\nAll developments typecheck with no admitted proofs.\n'
fi
exit "$status"
