module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W10_Near
public import Erdos745.WrapUp.Contracts

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section

namespace Erdos745.WrapUp.Proofs.W10_GIANT

open Erdos745.WrapUp.Proofs.Internal.W10_GIANT_Near
open Erdos745.WrapUp.Proofs.Internal.W10_GIANT_Fixed

theorem result : FiniteEnumerationStatement →
    RateStatement →
    TupleEstimatesStatement →
    AnalyticSumsStatement →
    CyclicStructureStatement →
    TreeMassStatement →
    GiantStatement := by
  intro hF hRate hTuple hAnalytic hCyc hTree
  constructor
  · intro M hbare
    exact near_giant_branch hF hRate hTuple hCyc hTree M hbare
  · intro M lam hM hlam hdeg
    exact fixed_giant_branch hF hRate hTuple hCyc hTree M lam hM hlam hdeg

end Erdos745.WrapUp.Proofs.W10_GIANT
