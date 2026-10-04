module

public import LeanProject.ErdosProblems.P732.ProjectivePlane.MathlibGeometry
public import Mathlib.LinearAlgebra.Projectivization.Cardinality

@[expose] public section

noncomputable section

namespace ErdosProblems
namespace P732
namespace PlaneModel

open scoped LinearAlgebra.Projectivization

instance instFintypePoint {F : Type} [Field F] [Fintype F] :
    Fintype (Point F) :=
  Fintype.ofFinite (Point F)

instance instFintypeLine {F : Type} [Field F] [Fintype F] :
    Fintype (Line F) :=
  Fintype.ofFinite (Line F)

theorem natCard_point {F : Type} [Field F] [Fintype F] :
    Nat.card (Point F) = (Fintype.card F) ^ 2 + Fintype.card F + 1 := by
  haveI : Finite F := inferInstance
  have hfinrank : Module.finrank F (Fin 3 → F) = 3 := by
    simp
  have h := Projectivization.card_of_finrank F (Fin 3 → F) hfinrank
  have hsum :
      ∑ i ∈ Finset.range 3, Nat.card F ^ i =
        (Fintype.card F) ^ 2 + Fintype.card F + 1 := by
    rw [Nat.card_eq_fintype_card]
    norm_num [Finset.sum_range_succ, Nat.pow_succ, Nat.mul_assoc, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm]
  exact h.trans hsum

theorem natCard_line {F : Type} [Field F] [Fintype F] :
    Nat.card (Line F) = (Fintype.card F) ^ 2 + Fintype.card F + 1 :=
  natCard_point

theorem fintypeCard_point {F : Type} [Field F] [Fintype F] :
    letI : Fintype (Point F) := Fintype.ofFinite (Point F)
    Fintype.card (Point F) = (Fintype.card F) ^ 2 + Fintype.card F + 1 := by
  letI : Fintype (Point F) := Fintype.ofFinite (Point F)
  rw [← Nat.card_eq_fintype_card]
  exact natCard_point

theorem fintypeCard_line {F : Type} [Field F] [Fintype F] :
    letI : Fintype (Line F) := Fintype.ofFinite (Line F)
    Fintype.card (Line F) = (Fintype.card F) ^ 2 + Fintype.card F + 1 := by
  letI : Fintype (Line F) := Fintype.ofFinite (Line F)
  rw [← Nat.card_eq_fintype_card]
  exact natCard_line

theorem point_card {F : Type} [Field F] [Fintype F] :
    Fintype.card (Point F) = (Fintype.card F) ^ 2 + Fintype.card F + 1 :=
  fintypeCard_point

theorem line_card {F : Type} [Field F] [Fintype F] :
    Fintype.card (Line F) = (Fintype.card F) ^ 2 + Fintype.card F + 1 :=
  fintypeCard_line

theorem quadratic_card_injective {a b : ℕ}
    (h : a ^ 2 + a + 1 = b ^ 2 + b + 1) : a = b := by
  wlog hle : a ≤ b generalizing a b with H
  · exact (H h.symm (Nat.le_of_not_ge hle)).symm
  by_contra hne
  have hlt : a < b := lt_of_le_of_ne hle hne
  have hsquare : a ^ 2 < b ^ 2 :=
    Nat.pow_lt_pow_left hlt (by decide : 2 ≠ 0)
  have hstrict : a ^ 2 + a + 1 < b ^ 2 + b + 1 := by
    omega
  exact (ne_of_lt hstrict) h

end PlaneModel
end P732
end ErdosProblems
