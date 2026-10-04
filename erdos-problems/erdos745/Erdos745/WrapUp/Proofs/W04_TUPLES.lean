module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W04_Public

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section
namespace Erdos745.WrapUp.Proofs.W04_TUPLES

/-- Component tuple estimates from finite enumeration and exact-rate expansions. -/
theorem result :
    FiniteEnumerationStatement → RateStatement → TupleEstimatesStatement := by
  intro hF _hRate
  exact ⟨
    Internal.W04_TUPLES_Public.globalEventually hF,
    Internal.W04_TUPLES_PublicNear.mixedEventually hF,
    Internal.W04_TUPLES_Compact.compactLocalEventually hF,
    Internal.W04_TUPLES_Public.separatedTailEventually hF
  ⟩

end Erdos745.WrapUp.Proofs.W04_TUPLES
