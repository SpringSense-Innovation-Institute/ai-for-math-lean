module

public import LeanProject.ErdosProblems.P732.ProjectivePlane
public import Mathlib.FieldTheory.Finite.GaloisField

@[expose] public section

noncomputable section

namespace ErdosProblems
namespace P732

/-!
Finite-field cardinality helpers for prime powers.

This file is intentionally only a cardinality bridge: it packages mathlib's
`GaloisField p k` construction for the local `PrimePower` predicate without
touching the projective-plane interface.
-/

theorem PrimePower.exists_prime_pow {q : ℕ} (hq : PrimePower q) :
    ∃ p k : ℕ, Nat.Prime p ∧ 0 < k ∧ q = p ^ k :=
  hq

theorem galoisField_nat_card (p k : ℕ) [Fact p.Prime] (hk : k ≠ 0) :
    Nat.card (GaloisField p k) = p ^ k :=
  GaloisField.card p k hk

theorem PrimePower.exists_finite_field {q : ℕ} (hq : PrimePower q) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : DecidableEq F),
      Fintype.card F = q := by
  rcases hq with ⟨p, k, hp, hk, rfl⟩
  haveI : Fact p.Prime := ⟨hp⟩
  let F := GaloisField p k
  haveI : Fintype F := Fintype.ofFinite F
  refine ⟨F, inferInstance, inferInstance, Classical.decEq F, ?_⟩
  rw [Fintype.card_eq_nat_card]
  exact galoisField_nat_card p k hk.ne'

end P732
end ErdosProblems
