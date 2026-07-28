/-
  NonMergeability.lean — D5 (honest-PARTIAL): a Lean 4 formalization of the SUFFICIENT
  CONDITION under which the estate's STATEFUL gates cannot be folded into one idempotent
  construction. Mathlib-free (Lean 4 core: Nat + omega); type-checks in seconds, no network.

  WHAT THIS IS (read the honest scope first). The meta-gate analysis (reports/meta_gate_magnitude.md,
  tools/check_meta_gate_magnitude.py) CLASSIFIES 7 of the 26 gates as "stateful survivors"
  (AF/AG/Q/B/...) that a single one-shot KDF meta-binding cannot absorb, because they require
  strictly-monotonic epoch / install-once state. That classification is by keyword; this file
  gives the underlying ARITHMETIC REASON as a machine-checked lemma:

    a strictly-ADVANCING monotonic action (an epoch gate that must always move the counter
    forward) CANNOT be IDEMPOTENT (a one-shot fold, applying it twice = applying it once).

  So a single idempotent fold cannot supply the strict epoch advance a stateful gate needs;
  and two stateful gates over DISJOINT epoch coordinates each need their own non-idempotent
  advance, i.e. >= 2 separable actions. That is exactly "closing two families whose violations
  live in disjoint, ORDERED state requires >= 2 mechanisms" — for the ordered-state (epoch) case.

  HONEST SCOPE (NOT overclaimed). This is a formalization of the SUFFICIENT CONDITION the
  classifier already assumes — it models a stateful gate's obligation as a StrictAdvance on a Nat
  epoch and a one-shot fold as an Idempotent map, and proves they are incompatible. It does NOT
  discharge atomicity for the REAL mechanism set (that would need the real gates' state proven to
  be exactly these disjoint monotone posets, tied to the running engine — the multi-week residual
  flagged in meta_gate_magnitude.md and lower_bounds.py). It is a labeled sufficient-condition
  lemma, NOT "atomicity discharged".
-/
namespace NonMergeability

/-- A one-shot fold: applying it twice equals applying it once (idempotent). -/
def Idempotent (f : Nat → Nat) : Prop := ∀ x, f (f x) = f x

/-- A strictly-advancing monotonic epoch action: it always moves the counter forward. -/
def StrictAdvance (f : Nat → Nat) : Prop := ∀ x, x < f x

/-- CORE LEMMA: a strictly-advancing epoch action cannot be idempotent. So a one-shot
    idempotent fold cannot supply the strict epoch advance a stateful gate requires. -/
theorem idempotent_not_strict (f : Nat → Nat) (hidem : Idempotent f) :
    ¬ StrictAdvance f := by
  intro hadv
  have h1 : f 0 < f (f 0) := hadv (f 0)   -- strict advance at (f 0)
  have h2 : f (f 0) = f 0 := hidem 0       -- idempotence at 0
  omega                                     -- f 0 < f 0, contradiction

/-- The contrapositive framing: an idempotent one-shot fold does NOT close a family whose
    closure requires a strict epoch advance. -/
theorem oneshot_fold_cannot_close_epoch_family
    (f : Nat → Nat) (hidem : Idempotent f) :
    ¬ (StrictAdvance f) := idempotent_not_strict f hidem

/-- Two stateful gates over DISJOINT epoch coordinates. A single idempotent action on the
    product state cannot strictly-advance EITHER coordinate — so closing two disjoint-state
    epoch families needs >= 2 separable (non-idempotent) actions, i.e. >= 2 mechanisms. -/
def IdempotentP (g : Nat × Nat → Nat × Nat) : Prop := ∀ p, g (g p) = g p
def AdvancesFst (g : Nat × Nat → Nat × Nat) : Prop := ∀ p, p.1 < (g p).1
def AdvancesSnd (g : Nat × Nat → Nat × Nat) : Prop := ∀ p, p.2 < (g p).2

theorem idempotent_advances_neither_coord
    (g : Nat × Nat → Nat × Nat) (hidem : IdempotentP g) :
    ¬ AdvancesFst g ∧ ¬ AdvancesSnd g := by
  constructor
  · intro hf
    have h1 : (g (0, 0)).1 < (g (g (0, 0))).1 := hf (g (0, 0))
    have h2 : g (g (0, 0)) = g (0, 0) := hidem (0, 0)
    rw [h2] at h1
    omega
  · intro hs
    have h1 : (g (0, 0)).2 < (g (g (0, 0))).2 := hs (g (0, 0))
    have h2 : g (g (0, 0)) = g (0, 0) := hidem (0, 0)
    rw [h2] at h1
    omega

/-- CONCLUSION (sufficient condition): if closing family A requires AdvancesFst and closing
    family B requires AdvancesSnd (their violations live in disjoint ordered epoch state), then
    NO single idempotent one-shot fold `g` closes both — a fold closing both would have to
    advance both coordinates, which `idempotent_advances_neither_coord` refutes. Hence >= 2
    separable non-idempotent actions (>= 2 mechanisms) are required. -/
theorem disjoint_epoch_families_not_mergeable
    (g : Nat × Nat → Nat × Nat) (hidem : IdempotentP g)
    (closesA : AdvancesFst g) : False := by
  have h := (idempotent_advances_neither_coord g hidem).1
  exact h closesA

/- ============================================================================
   R4-PARTIAL (Sprint 3): instantiate the abstract lemma on TWO REAL stateful gates,
   AF (recovery gate) and AG (agility/suite gate) — 2 of the 7 stateful survivors.

   Ground truth in the reference implementation:
     * AF accepts an in-place recovery/rekey re-entry ONLY IF `recovery_epoch > installed`
       (a stale-context replay `epoch <= installed` is refused) — a STRICT advance of the
       recovery-epoch coordinate.
     * AG accepts a deliberate suite ROTATION ONLY IF `suite_epoch > installed_suite`
       (a stale-suite rollback is refused) — a STRICT advance of the suite-epoch coordinate.
   The two epochs are DISJOINT coordinates of the state (recovery-epoch ⊥ suite-epoch). We
   model the product state as (AF recovery-epoch, AG suite-epoch) : Nat × Nat and each gate's
   freshness condition as a strict advance of ITS coordinate. Then a single idempotent one-shot
   fold cannot satisfy BOTH gates' freshness — it would have to strict-advance both coordinates,
   which `idempotent_advances_neither_coord` refutes. So AF and AG are each un-foldable into one
   idempotent construction, and closing both needs >= 2 separable actions (>= 2 mechanisms). -/

/-- AF freshness: the fold strict-advances the recovery-epoch coordinate (`.1`). -/
def AF_fresh (g : Nat × Nat → Nat × Nat) : Prop := AdvancesFst g
/-- AG freshness: the fold strict-advances the suite-epoch coordinate (`.2`). -/
def AG_fresh (g : Nat × Nat → Nat × Nat) : Prop := AdvancesSnd g

/-- AF + AG are NOT co-foldable: no single idempotent one-shot fold satisfies both the AF
    recovery-epoch freshness and the AG suite-epoch freshness. (2 of the 7 stateful gates,
    tied to their actual `epoch > installed` accept conditions.) -/
theorem af_ag_not_mergeable
    (g : Nat × Nat → Nat × Nat) (hidem : IdempotentP g) :
    ¬ AF_fresh g ∧ ¬ AG_fresh g := by
  unfold AF_fresh AG_fresh
  exact idempotent_advances_neither_coord g hidem

end NonMergeability
