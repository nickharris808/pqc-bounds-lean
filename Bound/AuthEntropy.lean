/-
  AuthEntropy.lean — LAW 2 (Sprint 135): the authentication-entropy conservation floor, the
  counting core of the Gilbert-MacWilliams-Sloane / Simmons deception bound P_d >= 2^{-H(K)/2}.
  Mathlib-free (Lean 4 core: Nat + omega); typechecks in seconds, no network, 0 sorry.

  MODEL. Authentication resistance splits as a+b bits: a = impersonation-resistance bits, b =
  substitution-resistance bits. The GMS/Simmons product constraint is a + b <= H(K) (you cannot
  buy more authentication than the key entropy funds). The deception advantage is 2^{-min(a,b)}.

  HONEST SCOPE. Tier-1 in the ONE-TIME-authentication model (cited: GMS 1974, Simmons CRYPTO'84,
  Stinson J.Crypto'88, Maurer IEEE-IT'00). The GMS product constraint a+b<=H is the CITED theorem;
  this file discharges its counting CONSEQUENCE (H < 2k => min(a,b) < k => deception > 2^{-k}). The
  deployed claim is the conservation law, NOT "short MAC keys are impossible". No byte-size claim.
-/
namespace AuthEntropy

/-- DECEPTION FLOOR: committing fewer than 2k key-entropy bits (a+b <= h < 2k) forces the weaker
    deception leg to have < k bits, i.e. success probability > 2^{-k}. Resisting deception at
    level k is impossible below H(K) = 2k. -/
theorem deception_floor (a b h k : Nat)
    (gms : a + b ≤ h) (under : h < 2 * k) :
    min a b < k := by
  omega

/-- The floor is TIGHT: at H(K) = 2k a balanced code (a = b = k) meets it exactly. -/
theorem floor_achievable (k : Nat) :
    k + k ≤ 2 * k ∧ min k k = k :=
  ⟨by omega, Nat.min_self k⟩

/-- Monotone corollary in the powers: min(a,b) < k gives the strict advantage 2^{min a b} < 2^k
    (so the deception advantage 2^{-min(a,b)} strictly exceeds the target 2^{-k}). -/
theorem advantage_exceeds_target (a b k : Nat) (h : min a b < k) :
    2 ^ (min a b) < 2 ^ k :=
  Nat.pow_lt_pow_right (by omega) h

/-- CONSERVATION: the total funded resistance a+b is packaging-independent — moving entropy
    between the two legs (or across wire/state/rounds) redistributes a,b but cannot raise a+b
    above h. Formally, for any split with a+b <= h, both legs cannot simultaneously reach k
    unless h >= 2k. -/
theorem movable_but_irreducible (a b h k : Nat)
    (gms : a + b ≤ h) (both : k ≤ a ∧ k ≤ b) :
    2 * k ≤ h := by
  omega

end AuthEntropy

#eval "AuthEntropy: deception_floor / floor_achievable / advantage_exceeds_target / movable_but_irreducible (0 sorry)"
