module

public import LeanProject.ErdosProblems.P732.FiniteFieldCard
public import LeanProject.ErdosProblems.P732.ProjectivePlane.PairUnique

@[expose] public section

noncomputable section

namespace ErdosProblems
namespace P732

namespace PlaneModel

def projectivePlaneOfField (F : Type) [Field F] [Fintype F] [DecidableEq F] :
    ProjectivePlane (Fintype.card F) where
  Point := PlaneModel.Point F
  instFintypePoint := Fintype.ofFinite (PlaneModel.Point F)
  instDecidableEqPoint := Classical.decEq (PlaneModel.Point F)
  card_points := by
    rw [← Nat.card_eq_fintype_card]
    exact natCard_point (F := F)
  line := indexedLineFinset (F := F)
  line_card := indexedLineFinset_card (F := F)
  pair_unique_line := by
    intro a b hab
    exact indexedLine_unique_of_pair (F := F) hab

end PlaneModel

theorem projectivePlane_of_primePower {q : ℕ} :
    PrimePower q → Nonempty (ProjectivePlane q) := by
  intro hq
  rcases hq.exists_finite_field with ⟨F, instField, instFintype, instDecidable, hcard⟩
  letI : Field F := instField
  letI : Fintype F := instFintype
  letI : DecidableEq F := instDecidable
  exact ⟨hcard ▸ PlaneModel.projectivePlaneOfField F⟩

end P732
end ErdosProblems
