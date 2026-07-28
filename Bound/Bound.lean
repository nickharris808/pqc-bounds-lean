/-
  Bound.lean — the PQC memory-DoS residency lower bound, machine-checked in Lean 4.

  This is the THIRD independent proof of the SAME bound the repo already establishes
  in z3 (software, an SMT encoding) and Yosys SAT (silicon RTL,
  a synthesizable RTL gate). It is mathlib-free — it depends only on
  Lean 4 core (Nat arithmetic + the `omega` decision procedure) — so it type-checks in
  seconds with no network.

  Headline: one residency lower bound, proven in THREE independent proof systems —
  pure math (Lean 4, here), software (z3), and silicon (Yosys k-induction).

  Model (mirrors the RTL admission FSM and the z3 transition relation):
    * a flood admits fragments of size `S` (> 0), starting from base `K0`;
    * the NAIVE reassemble-then-verify datapath holds every admitted byte:
        naiveResident K0 S n = K0 + n*S                 (grows without bound)
    * the bounded-reassembly GATE admits a fragment only if it keeps the window
      within `CAP`, else drops it (the admission gate):
        gatedStep CAP S r = if r + S ≤ CAP then r + S else r
        gatedResident CAP S (n+1) = gatedStep CAP S (gatedResident CAP S n)
-/
namespace WifiPQC

/-- Naive reassemble-then-verify residency after `n` admitted fragments of size `S`. -/
def naiveResident (K0 S n : Nat) : Nat := K0 + n * S

/-- One step of the bounded-reassembly gate: admit (grow by `S`) iff it stays ≤ CAP. -/
def gatedStep (CAP S r : Nat) : Nat := if r + S ≤ CAP then r + S else r

/-- Gated residency after `n` admit attempts, starting empty. -/
def gatedResident (CAP S : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => gatedStep CAP S (gatedResident CAP S n)

/-- (S1) The bounded-buffer invariant: the gate's window never exceeds `CAP`, for any
    flood length `n` and any fragment size `S`. This is the hardware/SMT `resident ≤ CAP`,
    proven here in pure math by induction on the flood length. -/
theorem bounded (CAP S : Nat) : ∀ n, gatedResident CAP S n ≤ CAP := by
  intro n
  induction n with
  | zero => simp only [gatedResident]; omega
  | succ k ih =>
    simp only [gatedResident, gatedStep]
    by_cases h : gatedResident CAP S k + S ≤ CAP
    · rw [if_pos h]; exact h
    · rw [if_neg h]; exact ih

/-- (DoS) The naive residency exceeds ANY fixed budget `B` once the flood is large
    enough (given a positive fragment size). No fixed-size buffer survives the flood. -/
theorem naive_unbounded (K0 S B : Nat) (hS : 0 < S) :
    ∃ n, naiveResident K0 S n > B := by
  refine ⟨B + 1, ?_⟩
  unfold naiveResident
  have h : (B + 1) * 1 ≤ (B + 1) * S := Nat.mul_le_mul_left (B + 1) hS
  omega

/-- (load-bearing) The gate's residency never exceeds the naive residency it caps:
    the cap genuinely constrains the SAME accumulation — it is not a different, weaker
    system. This is the Lean analog of the z3 "naive_violated" / non-vacuity witness. -/
theorem gated_le_naive (CAP S : Nat) :
    ∀ n, gatedResident CAP S n ≤ naiveResident 0 S n := by
  intro n
  induction n with
  | zero => simp only [gatedResident, naiveResident]; omega
  | succ k ih =>
    simp only [gatedResident, gatedStep, naiveResident] at *
    have hk : (k + 1) * S = k * S + S := Nat.succ_mul k S
    by_cases h : gatedResident CAP S k + S ≤ CAP
    · rw [if_pos h]; omega
    · rw [if_neg h]; omega

/-- (separation) For ANY extra margin `M`, a flood drives the naive demand strictly
    above `CAP + M` while the gate stays ≤ `CAP` — the unbounded-amplification gap that
    motivates the whole mechanism: a fixed budget can be beaten by any margin, the gate
    cannot. -/
theorem separation (CAP S M : Nat) (hS : 0 < S) :
    ∃ n, naiveResident 0 S n > CAP + M ∧ gatedResident CAP S n ≤ CAP := by
  obtain ⟨n, hn⟩ := naive_unbounded 0 S (CAP + M) hS
  exact ⟨n, hn, bounded CAP S n⟩

/-- (canonical) The single DEPLOYED value of the reassembly cap, pinned inside the
    proof-checked environment. The Proof↔Code drift binder (`tools/check_drift_binding.py`)
    reads THIS value out of Lean (via `#eval CAP_CANONICAL` below) and asserts that the
    compiled `libpqc_state` binary enforces the same cap and that every source-fleet site
    agrees on it. `16384` = the 16 KiB per-session reassembly window (the admission gate).
    NOTE: this is DISTINCT from the 65536 (64 KiB) "is-this-flood-unbounded?" threshold
    `BOUNDED_REASSEMBLY_CAP` — do not conflate the two. -/
def CAP_CANONICAL : Nat := 16384

/-- The bounded-buffer invariant specialized to the deployed cap: the gate's window
    never exceeds `16384`, for any flood length and fragment size. This is a
    proof-CARRIED instance of `bounded` at the canonical value — the constant is not
    merely written down, the `resident ≤ 16384` bound is proven to hold there. The
    literal `16384` in the statement is definitionally `CAP_CANONICAL`. -/
theorem bounded_at_canonical (S : Nat) :
    ∀ n, gatedResident CAP_CANONICAL S n ≤ 16384 :=
  bounded CAP_CANONICAL S

/-- The reassembler's acceptance predicate: an object of total size `obj` is admitted iff it
    fits the per-session cap — exactly the real admit guard `incremental_auth.py:136`
    (`buf_len + frag_len ≤ cap`). This is the object the LOWER side of the window reasons over. -/
def admits (cap obj : Nat) : Prop := obj ≤ cap

/-- (feasibility floor — the NEW lower side) A per-session cap STRICTLY BELOW an object's size
    cannot admit it: a legitimate PQC object is dropped. This is the machine-checked
    `buffer < X ⇒ drops legit`, the half the four existing upper-side proofs never stated. -/
theorem floor_necessary (cap obj : Nat) (h : cap < obj) : ¬ admits cap obj := by
  simp only [admits]; omega

/-- (membership) The deployed cap `16384` admits any supported object whose size is ≤ 16384 —
    i.e. 16384 lies on the feasible side of the window for such an object. Together with the
    ceiling this makes 16384 a MEMBER of `[X, Y]`, not a forced unique point. -/
theorem window_nonempty (objMax : Nat) (h : objMax ≤ 16384) : admits 16384 objMax := by
  simp only [admits]; omega

/-- (two-sided, in one statement) For any cap that MEETS the feasibility floor (`cap ≥ objMax`),
    the reassembler admits the object AND — by `bounded` — its gated residency never exceeds
    `cap` under any flood. Feasibility (lower) and DoS-safety (upper) hold together: this is the
    window `objMax ≤ cap` with both guarantees. -/
theorem window_admits_and_bounded (cap objMax S : Nat) (h : objMax ≤ cap) :
    admits cap objMax ∧ ∀ n, gatedResident cap S n ≤ cap := by
  refine ⟨?_, bounded cap S⟩
  simpa only [admits] using h

-- Emit the proof-checked constant on stdout so the drift binder can read it back
-- FROM the Lean environment (not from a source regex): `lean Bound.lean` prints `16384`.
#eval CAP_CANONICAL

end WifiPQC
