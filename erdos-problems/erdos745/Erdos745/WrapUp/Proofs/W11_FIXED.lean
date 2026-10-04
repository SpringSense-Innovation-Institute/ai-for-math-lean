module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W11_Fixed

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section
namespace Erdos745.WrapUp.Proofs.W11_FIXED

open Erdos745.WrapUp.Proofs.Internal.W11_FIXED_Laws

theorem result : FiniteEnumerationStatement →
    RateStatement →
    PoissonStatement →
    SubcriticalExclusionStatement →
    CyclicStructureStatement →
    GiantStatement →
    FixedAtlasStatement :=
  fixedAtlasStatement_of_inputs

end Erdos745.WrapUp.Proofs.W11_FIXED
