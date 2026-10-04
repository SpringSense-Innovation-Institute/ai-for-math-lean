module

public import Erdos745.WrapUp.Contracts
public import Erdos745.WrapUp.Proofs.Internal.Linked.W14_Tails

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section
namespace Erdos745.WrapUp.Proofs.W14_EXPLORATION

open Internal.W14_EXPLORATION_Interpolation Internal.W14_EXPLORATION_PathWeak
open Internal.W14_EXPLORATION_CompletionTail Internal.W14_EXPLORATION_LateTail

/-- The same concrete interpolation supplies weak convergence and both literal tails. -/
theorem result : FiniteEnumerationStatement →
    BrownianFoundationStatement →
    ExplorationStatement := by
  intro hfinite hfoundation
  refine ⟨explorationInterpolation, explorationInterpolation_isInterpolation, ?_⟩
  intro M lam mu hcritical hmu
  exact ⟨critical_weakExploration hfinite M lam hcritical mu hmu,
    lateLarge_eventual_bound hfinite M lam hcritical,
    unfinishedEarly_eventual_bound hfinite hfoundation M lam hcritical mu hmu⟩

end Erdos745.WrapUp.Proofs.W14_EXPLORATION
