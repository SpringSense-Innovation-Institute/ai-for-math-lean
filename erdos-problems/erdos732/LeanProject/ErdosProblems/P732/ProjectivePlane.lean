module

public import LeanProject.ErdosProblems.P732.Basic

@[expose] public section

noncomputable section

namespace ErdosProblems
namespace P732

/-! The projective-plane interface used by Alon's construction. -/

structure ProjectivePlane (q : ℕ) where
  Point : Type
  [instFintypePoint : Fintype Point]
  [instDecidableEqPoint : DecidableEq Point]
  card_points : Fintype.card Point = q ^ 2 + q + 1
  line : Fin (q ^ 2 + q + 1) → Finset Point
  line_card : ∀ i : Fin (q ^ 2 + q + 1), (line i).card = q + 1
  pair_unique_line :
    ∀ ⦃a b : Point⦄, a ≠ b →
      ∃! i : Fin (q ^ 2 + q + 1), a ∈ line i ∧ b ∈ line i

attribute [instance] ProjectivePlane.instFintypePoint
attribute [instance] ProjectivePlane.instDecidableEqPoint

def PrimePower (q : ℕ) : Prop :=
  ∃ p k : ℕ, Nat.Prime p ∧ 0 < k ∧ q = p ^ k

theorem PrimePower.two_le {q : ℕ} (hq : PrimePower q) : 2 ≤ q := by
  rcases hq with ⟨p, k, hp, hk, rfl⟩
  exact hp.two_le.trans (le_self_pow hp.one_le hk.ne')

end P732
end ErdosProblems
