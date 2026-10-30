#!/bin/bash
# Checks the proof export of `Clients.Admin.holds_proof` (`solution.ndjson.zst` beside this script) against the statement in
# the repository STATEMENTS_PROJECT, with Lean's own tools only:
#   1. Lean 4.34.0 builds the challenge `ReleaseChallenges.admin`: the theorem as the repository states
#      it, proved by `sorry`. Lean's warning "declaration uses `sorry`" there is expected.
#   2. LEAN4EXPORT (leanprover/lean4export) exports the challenge's theorem, with every constant its statement uses,
#      from the modules just built.
#   3. Lean 4.35.0's `lake comparator`, configured by `comparator.json` beside this script,
#      checks that the solution proves a theorem of that name with the same statement over the same constants, using
#      no axiom but those `comparator.json` permits (so no `sorry`), and replays the whole solution in Lean's kernel
#      and in the independent kernels `comparator.json` lists (`external_kernels`), which the toolchain ships: its
#      `bin` directory is put first on `PATH` for them.
#      It ends with "Your solution is okay!" and exit status 0 if it accepts.
# With NANODA_BIN set to a nanoda_bin of one's own build, that nanoda runs as a further kernel.
# Further arguments go to `lake comparator` (`lake help comparator`).
set -euo pipefail
if [ "$#" -lt 2 ]; then
  echo "usage: $0 STATEMENTS_PROJECT LEAN4EXPORT [comparator options...]" >&2
  exit 2
fi
here=$(cd "$(dirname "$0")" && pwd)
project=$(cd "$1" && pwd)
exporter=$(realpath "$2")
shift 2
work=$(mktemp -d "$here/.verify-source.XXXXXX")
trap 'rm -rf -- "$work"' EXIT
PATH="$(elan run leanprover/lean4:v4.35.0 lean --print-prefix)/bin:$PATH"
echo '== 1. building the challenge ReleaseChallenges.admin (its warning "declaration uses `sorry`" is expected)'
(
  cd "$project"
  elan run leanprover/lean4:v4.34.0 lake build ReleaseChallenges.admin
)
echo "== 2. exporting the challenge's statement"
(
  cd "$project"
  elan run leanprover/lean4:v4.34.0 lake env "$exporter" ReleaseChallenges.admin -- Clients.Admin.holds_proof Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam propext Quot.sound Classical.choice > "$work/challenge.ndjson"
)
zstd -d -q "$here/solution.ndjson.zst" -o "$work/solution.ndjson"
config="$here/comparator.json"
if [ -n "${NANODA_BIN:-}" ]; then
  # (a nanoda the reader built, as one more kernel besides those `comparator.json` lists: the README's
  # "Independent kernels"; a checker whose name contains "noda" gets nanoda's configuration from the comparator)
  sed "s|\"external_kernels\": {|\"external_kernels\": {\"nanoda-own\": [\"$(realpath "$NANODA_BIN")\"],|" \
    "$here/comparator.json" > "$work/comparator.json"
  config="$work/comparator.json"
fi
echo "== 3. lake comparator: the solution against the challenge"
cd "$here"
elan run leanprover/lean4:v4.35.0 lake comparator --config "$config" "$@" --challenge-from-export "$work/challenge.ndjson" --solution-from-export "$work/solution.ndjson"
