module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W15_Final

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section
namespace Erdos745.WrapUp.Proofs.W15_CRITICAL

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W15_CRITICAL_PublicTransfer

/-- Exact conditional public critical target. -/
theorem result : BrownianFoundationStatement →
    ExplorationStatement →
    CriticalStatement := by
  intro hBrownian hExploration
  exact criticalLaw_of_public hBrownian hExploration

end Erdos745.WrapUp.Proofs.W15_CRITICAL
