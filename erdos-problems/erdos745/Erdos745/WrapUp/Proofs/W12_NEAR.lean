module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W12_Near

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section
namespace Erdos745.WrapUp.Proofs.W12_NEAR

open Erdos745.WrapUp.Proofs.Internal.W12_NEAR_Laws

/-- One absolute witness bounds the center error across all barely-supercritical sequences. -/
theorem uniformCenterBound (hR : RateStatement) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : NatSeq, bareSuper M →
      ∀ᶠ n in Filter.atTop, |giantCenter M n - 4 * displacement M n| ≤
        C * (displacement M n ^ 2 / n) :=
  uniform_super_center_bound hR

theorem result
    (hF : FiniteEnumerationStatement)
    (hR : RateStatement)
    (hP : PoissonStatement)
    (hS : SubcriticalExclusionStatement)
    (hC : CyclicStructureStatement)
    (hG : GiantStatement) : RequiredNearAtlasStatement := by
  exact ⟨barelySubcriticalLaw_of_inputs hF hR hP hS hC,
    barelySupercriticalLaw_of_inputs hF hR hP hC hG⟩

end Erdos745.WrapUp.Proofs.W12_NEAR
