module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W09_FixedFinal
public import Erdos745.WrapUp.Contracts

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section

namespace Erdos745.WrapUp.Proofs.W09_TREE_MASS

open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_NearMean
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_NearVarianceTail
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_FixedMean
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_FixedVariance

theorem result : FiniteEnumerationStatement →
    RateStatement →
    TupleEstimatesStatement →
    AnalyticSumsStatement →
    TreeMassStatement := by
  intro hF hRate hT hA
  constructor
  · intro M hbare
    exact ⟨near_mean_boundedBy hRate hT hA hbare,
      near_variance_boundedBy hF hRate hT hA hbare⟩
  · intro M lam hadm hlam hdeg
    exact ⟨fixed_mean_boundedBy hRate hT hA hadm hlam hdeg,
      fixed_variance_boundedBy hF hRate hT hA hadm hlam hdeg⟩

end Erdos745.WrapUp.Proofs.W09_TREE_MASS
