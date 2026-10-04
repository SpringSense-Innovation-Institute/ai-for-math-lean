module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W05_Analytic

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section
namespace Erdos745.WrapUp.Proofs.W05_SUMS

open Erdos745.WrapUp

theorem result : FiniteEnumerationStatement →
    RateStatement →
    AnalyticSumsStatement := by
  intro hEnum hRate
  exact ⟨
    Internal.W05_SUMS_TreeSeries.result hEnum hRate,
    Internal.W05_SUMS_Tails.powerWeight,
    Internal.W05_SUMS_Tails.fixedTail,
    Internal.W05_SUMS_Tails.movingTail
  ⟩

end Erdos745.WrapUp.Proofs.W05_SUMS
