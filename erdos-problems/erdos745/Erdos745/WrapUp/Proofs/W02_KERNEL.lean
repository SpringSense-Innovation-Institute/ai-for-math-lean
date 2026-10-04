module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W02_Choices
public import Erdos745.WrapUp.Proofs.Internal.Linked.W02_Dense
public import Erdos745.WrapUp.Proofs.Internal.Linked.W02_Sparse

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section
/-!
Connected-graph enumeration bounds from suppression orbits, with separate
sparse and dense estimates.
-/

noncomputable section

namespace Erdos745.WrapUp.Proofs.W02_KERNEL

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Expansion
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Suppression
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Encode
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_ChoiceFamily
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_SparseFinal

/-- Unconditional all-excess connected-graph bound. -/
theorem result (hF : FiniteEnumerationStatement) : KernelBoundStatement := by
  have hchoices : ChoiceSymmetryFamilyStatement :=
    choiceSymmetryFamilyStatement_of_presentations choicePresentationFamilyStatement
  have horbits : SuppressionOrbitStatement :=
    suppressionOrbitStatement_of_symmetry (symmetryOrbitStatement_of_choices hchoices)
  refine ⟨5015306502144, by norm_num, ?_⟩
  intro k r hk hr
  by_cases hsparse : r < k
  · exact (connectedCount_le_expansionMajorant_of_orbits horbits hk hr).trans
      (expansionMajorant_sparse hF k r hk hr hsparse)
  · have hkr : k ≤ r := Nat.le_of_not_gt hsparse
    have hbase : (18 : ℝ) ^ r ≤ (5015306502144 : ℝ) ^ r := by
      gcongr; norm_num
    have hrpow : 0 ≤ Real.rpow (r : ℝ) (-(r : ℝ) / 2) :=
      Real.rpow_nonneg (Nat.cast_nonneg r) _
    have hkpow : 0 ≤ Real.rpow (k : ℝ)
        ((k : ℝ) + (3 * (r : ℝ) - 1) / 2) :=
      Real.rpow_nonneg (Nat.cast_nonneg k) _
    exact
      (Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_DenseFinal.connectedCount_le_dense_target
        k r hk hr hkr).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hbase hrpow) hkpow)

end Erdos745.WrapUp.Proofs.W02_KERNEL
