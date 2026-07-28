/-
  ReassemblyFloor.lean — LAW 1 (Sprint 135): the reassembly memory conservation dichotomy,
  the deployed face of the Naor-Rothblum / CCMT s*t = Omega(N) online-memory-checking floor.
  Mathlib-free (Lean 4 core: Nat + omega); typechecks in seconds, no network, 0 sorry.

  MODEL. An online reassembler covers a substituted symbol's integrity iff the symbol is RESIDENT
  in the buffer at verify time (at most B of the N symbols) OR PER-FRAME AUTHENTICATED (active iff
  A > 0, which covers all N as they stream). So covered <= B + (if A > 0 then N else 0). An
  uncovered symbol (covered < N) can be actively substituted undetected.

  HONEST SCOPE. This is the deployed COVERING dichotomy ("buffer-all OR gate; no third option"),
  the deployed face of Naor-Rothblum FOCS'05 s*t=Omega(N) and CCMT ICALP'09 h*v=Omega(N) (cited).
  The sharper product bound is not re-derived here; this file discharges the no-third-option
  consequence over the covering model. No byte-size or legal claim.
-/
namespace ReassemblyFloor

/-- The information bound on any online reassembler's coverage. -/
def coverBound (covered B A N : Nat) : Prop :=
  covered ≤ B + (if A > 0 then N else 0)

/-- NO THIRD OPTION: a reassembler that neither buffers the whole object (B >= N) nor gates
    (A > 0) necessarily leaves a symbol uncovered — i.e. accepts an active substitution. -/
theorem no_third_option (covered B A N : Nat)
    (bound : coverBound covered B A N) (hB : B < N) (hA : A = 0) :
    covered < N := by
  unfold coverBound at bound
  subst hA
  simp only [Nat.lt_irrefl, if_false, Nat.add_zero, gt_iff_lt] at bound
  omega

/-- BUFFER-ALL corner: retaining the whole object (B >= N) achieves full coverage. -/
theorem buffer_all_covers (B A N : Nat) (hB : N ≤ B) : coverBound N B A N := by
  unfold coverBound; omega

/-- GATE corner: per-frame authentication (A > 0) achieves full coverage with tiny buffer. -/
theorem gate_covers (B A N : Nat) (hA : 0 < A) : coverBound N B A N := by
  unfold coverBound
  simp only [hA, if_true]
  omega

end ReassemblyFloor

-- Emit the canonical object size used by the deployed instance so the CI wrapper can pin it.
#eval "ReassemblyFloor: no_third_option / buffer_all_covers / gate_covers (0 sorry); N=4194304 deployed instance"
