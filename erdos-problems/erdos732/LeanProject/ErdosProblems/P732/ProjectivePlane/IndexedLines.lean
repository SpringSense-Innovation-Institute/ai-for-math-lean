module

public import LeanProject.ErdosProblems.P732.ProjectivePlane.Cardinality

@[expose] public section

noncomputable section

namespace ErdosProblems
namespace P732
namespace PlaneModel

open scoped LinearAlgebra.Projectivization

theorem quad_card_injective {a b : ℕ}
    (h : a ^ 2 + a + 1 = b ^ 2 + b + 1) : a = b := by
  exact quadratic_card_injective h

theorem order_eq_card {F : Type} [Field F] [Fintype F] [DecidableEq F] :
    Configuration.ProjectivePlane.order (Point F) (Line F) = Fintype.card F := by
  classical
  haveI : Fintype (Point F) := Fintype.ofFinite (Point F)
  haveI : Fintype (Line F) := Fintype.ofFinite (Line F)
  have hplane :=
    Configuration.ProjectivePlane.card_points (P := Point F) (L := Line F)
  have hmodel : Fintype.card (Point F) = Fintype.card F ^ 2 + Fintype.card F + 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact natCard_point
  exact quad_card_injective (hplane.symm.trans hmodel)

def lineEquivFin {F : Type} [Field F] [Fintype F] :
    Line F ≃ Fin (Fintype.card F ^ 2 + Fintype.card F + 1) := by
  classical
  haveI : Fintype (Line F) := Fintype.ofFinite (Line F)
  exact Fintype.equivFinOfCardEq (by
    rw [← Nat.card_eq_fintype_card]
    exact natCard_line (F := F))

def indexedLine {F : Type} [Field F] [Fintype F]
    (i : Fin (Fintype.card F ^ 2 + Fintype.card F + 1)) : Line F :=
  (lineEquivFin (F := F)).symm i

def lineSet {F : Type} [Field F] (l : Line F) : Set (Point F) :=
  {p : Point F | p ∈ l}

def lineFinset {F : Type} [Field F] [Fintype F] (l : Line F) :
    Finset (Point F) := by
  classical
  letI : Fintype (Point F) := Fintype.ofFinite (Point F)
  exact (lineSet l).toFinite.toFinset

theorem mem_lineFinset {F : Type} [Field F] [Fintype F]
    (l : Line F) (p : Point F) :
    p ∈ lineFinset l ↔ p ∈ l := by
  classical
  simp [lineFinset, lineSet]

theorem lineFinset_card {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (l : Line F) :
    (lineFinset l).card = Fintype.card F + 1 := by
  classical
  have hcount :=
    Configuration.ProjectivePlane.pointCount_eq (P := Point F) (L := Line F) l
  rw [order_eq_card (F := F)] at hcount
  let s : Set (Point F) := lineSet l
  let hs : s.Finite := s.toFinite
  change hs.toFinset.card = Fintype.card F + 1
  haveI : Fintype s := hs.fintype
  rw [hs.card_toFinset]
  rw [← Nat.card_eq_fintype_card]
  exact hcount

def indexedLineFinset {F : Type} [Field F] [Fintype F]
    (i : Fin (Fintype.card F ^ 2 + Fintype.card F + 1)) :
    Finset (Point F) :=
  lineFinset (indexedLine i)

theorem mem_indexedLineFinset {F : Type} [Field F] [Fintype F]
    (i : Fin (Fintype.card F ^ 2 + Fintype.card F + 1)) (p : Point F) :
    p ∈ indexedLineFinset i ↔ p ∈ indexedLine i := by
  exact mem_lineFinset (indexedLine i) p

theorem indexedLineFinset_card {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (i : Fin (Fintype.card F ^ 2 + Fintype.card F + 1)) :
    (indexedLineFinset i).card = Fintype.card F + 1 :=
  lineFinset_card (indexedLine i)

theorem indexedLine_injective {F : Type} [Field F] [Fintype F] :
    Function.Injective (indexedLine (F := F)) := by
  intro i j h
  exact (lineEquivFin (F := F)).symm.injective h

end PlaneModel
end P732
end ErdosProblems
