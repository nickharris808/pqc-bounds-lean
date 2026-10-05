# pqc-bounds-lean

[![ci](https://github.com/nickharris808/pqc-bounds-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/nickharris808/pqc-bounds-lean/actions/workflows/ci.yml)
[![license](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)
[![lean](https://img.shields.io/badge/Lean-4.31.0-blueviolet.svg)](lean-toolchain)
[![sorry](https://img.shields.io/badge/sorry-0-brightgreen.svg)](verify.sh)
[![imports](https://img.shields.io/badge/imports-0-brightgreen.svg)](Bound/)
[![mathlib](https://img.shields.io/badge/mathlib-not%20required-brightgreen.svg)](lakefile.toml)

**A machine-checked memory bound whose only trusted base is the Lean kernel.**

Four developments, 20 theorems, **zero `sorry`, zero imports**. No mathlib, no
network, no `lake update`. `lean` typechecks each file in seconds.

**📖 Full documentation, tutorial and conceptual guide: <https://nickharris808.github.io/pqc-toolkit/>**

---

## Why zero imports matters

Most Lean developments import mathlib. That is usually the right call, and it also
means your trusted base is the kernel *plus* a large, fast-moving library. These
files depend only on Lean 4 core — `Nat` arithmetic and the `omega` decision
procedure — so there is nothing between the kernel and the theorem.

That is the whole pitch: a bound you can check yourself, from a clean machine, in
under a minute, with nothing to trust but Lean.

## 30-second quickstart

```bash
git clone https://github.com/nickharris808/pqc-bounds-lean
cd pqc-bounds-lean
./verify.sh
```

```
  ok    Bound/AuthEntropy.lean     0 sorry, 0 errors
  ok    Bound/Bound.lean           0 sorry, 0 errors
  ok    Bound/NonMergeability.lean 0 sorry, 0 errors
  ok    Bound/ReassemblyFloor.lean 0 sorry, 0 errors

All developments typecheck with no admitted proofs.
```

You need [elan](https://github.com/leanprover/elan); `lean-toolchain` pins
4.31.0 and elan fetches it.

## What is proven

**`Bound.lean` — the residency bound.** An unrepaired reassemble-then-verify
datapath retains every admitted byte, so residency grows without limit in the
number of fragments. A gated datapath admits a fragment only when it keeps the
window within `CAP`, and is therefore bounded by `CAP` *for every* fragment
sequence.

| Theorem | Statement |
|---|---|
| `bounded` | gated residency never exceeds `CAP`, for all `n` |
| `naive_unbounded` | for any bound, some `n` exceeds it |
| `gated_le_naive` | gating never retains more than not gating |
| `separation` | the two differ unboundedly |
| `bounded_at_canonical` | the bound at the deployed parameters (`#eval` prints **16384**) |
| `floor_necessary` | a cap below the largest legitimate object rejects honest traffic |
| `window_nonempty` | conditions under which a usable cap exists |
| `window_admits_and_bounded` | such a cap both admits honest objects and stays bounded |

**`ReassemblyFloor.lean`** — `no_third_option`, `buffer_all_covers`,
`gate_covers`: a dichotomy result on covering strategies.

**`NonMergeability.lean`** — `idempotent_not_strict`,
`oneshot_fold_cannot_close_epoch_family`, `disjoint_epoch_families_not_mergeable`
and two more: separate epoch families cannot be collapsed into one fold.

**`AuthEntropy.lean`** — `deception_floor`, `floor_achievable`,
`advantage_exceeds_target`, `movable_but_irreducible`: an entropy floor below
which deception advantage is unavoidable.

## Worked example

`Bound.lean` computes its own headline number rather than asserting it:

```
$ lake env lean Bound/Bound.lean
16384
```

That is `bounded_at_canonical` evaluated at the deployed parameters — the same
16,384-byte cap that [`pqc-sizes`](https://github.com/nickharris808/pqc-sizes)
derives arithmetically and [`farkas-check`](https://github.com/nickharris808/farkas-check)
re-verifies on-device from a certificate.

## Honest scope

**What this proves.** That the stated gated recurrence is bounded by `CAP` for
every input sequence, and that the ungated one is not — as a theorem about the
model, checked by the Lean kernel.

**What it does NOT prove.**

- **Not that your implementation matches the model.** The theorem is about
  `gatedStep`, a four-line recurrence. Whether your reassembly path refines it is
  a separate obligation this repository does not discharge.
- **Not a security proof.** Memory exhaustion is one failure family of 39; see
  [`pqc-mfb`](https://github.com/nickharris808/pqc-mfb).
- **Not a claim about hardware.** A fixed-width implementation additionally needs
  an overflow argument, which is not here.
- **Not peer-reviewed.** It is machine-checked, which is a different and narrower
  thing.

## Why `verify.sh` greps rather than trusting the exit code

`sorry` admits a goal without proving it. Lean emits a *warning* and still exits
**0**, so a script that only checked the exit status would happily pass a file of
admitted proofs — the first version of this one did, until a planted `sorry`
proved it. Lean writes ``declaration uses `sorry` `` with backticks; matching on
`'sorry'` in single quotes never fires.

CI runs the same script, and a planted-`sorry` job asserts it still fails.

## Related

Three independent checks of the same bound:

| Where | How |
|---|---|
| **here** | Lean 4, mathlib-free, kernel-only trusted base |
| [`farkas-check`](https://github.com/nickharris808/farkas-check) | 216 lines of integer C (132 code), on-device, no solver |
| [`pqc-dos-embedded`](https://github.com/nickharris808/pqc-dos-embedded) | the failure and the bound on emulated ARMv7-M |

[`pqc-sizes`](https://github.com/nickharris808/pqc-sizes) ·
[`pqc-mfb`](https://github.com/nickharris808/pqc-mfb) ·
[`pqc-formal-corpus`](https://github.com/nickharris808/pqc-formal-corpus) (these
theorems appear in it by name)

These developments prove *the bound*. Enforcing it across the full post-quantum
migration failure surface is a separate closed codebase, and patent claims have been drafted for relevant subject matter (filing status available on request). For commercial use,
open a GitHub Discussion or an issue.

## License

Apache-2.0. See [LICENSE](LICENSE).
