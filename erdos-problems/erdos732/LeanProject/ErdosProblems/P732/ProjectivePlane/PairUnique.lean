module

public import LeanProject.ErdosProblems.P732.ProjectivePlane.IndexedLines

@[expose] public section

noncomputable section

namespace ErdosProblems
namespace P732
namespace PlaneModel

open scoped LinearAlgebra.Projectivization

theorem indexedLine_unique_of_pair
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {a b : Point F} (hab : a ≠ b) :
    ∃! i : Fin (Fintype.card F ^ 2 + Fintype.card F + 1),
      a ∈ indexedLineFinset i ∧ b ∈ indexedLineFinset i := by
  rcases existsUnique_line (F := F) a b hab with ⟨l, hl, huniq⟩
  refine ⟨lineEquivFin l, ?_, ?_⟩
  · simpa [mem_indexedLineFinset, indexedLine]
      using hl
  · intro j hj
    have hline : (lineEquivFin (F := F)).symm j = l := huniq
      ((lineEquivFin (F := F)).symm j) (by
      simpa [mem_indexedLineFinset, indexedLine] using hj)
    apply (lineEquivFin (F := F)).symm.injective
    simp [hline]

end PlaneModel
end P732
end ErdosProblems
