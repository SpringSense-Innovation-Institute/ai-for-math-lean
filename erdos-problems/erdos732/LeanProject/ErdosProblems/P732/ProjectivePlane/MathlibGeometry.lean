module

public import LeanProject.ErdosProblems.P732.ProjectivePlane
public import Mathlib.Combinatorics.Configuration

@[expose] public section

noncomputable section

namespace ErdosProblems
namespace P732
namespace PlaneModel

open scoped LinearAlgebra.Projectivization

/-- The projective points used by mathlib's coordinate projective plane. -/
abbrev Point (F : Type) [Field F] : Type :=
  Projectivization F (Fin 3 → F)

/-- Lines are represented by the dual projective plane, using orthogonality as incidence. -/
abbrev Line (F : Type) [Field F] : Type :=
  Projectivization F (Fin 3 → F)

instance instMembership {F : Type} [Field F] :
    Membership (Point F) (Line F) :=
  inferInstance

theorem mem_iff {F : Type} [Field F] (p : Point F) (l : Line F) :
    p ∈ l ↔ Projectivization.orthogonal p l :=
  Configuration.ofField.mem_iff p l

theorem existsUnique_line
    {F : Type} [Field F] [DecidableEq F] (p₁ p₂ : Point F) (hp : p₁ ≠ p₂) :
    ∃! l : Line F, p₁ ∈ l ∧ p₂ ∈ l :=
  Configuration.HasLines.existsUnique_line (P := Point F) (L := Line F) p₁ p₂ hp

end PlaneModel
end P732
end ErdosProblems
