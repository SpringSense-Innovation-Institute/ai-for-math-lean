module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W08_Mass

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section
namespace Erdos745.WrapUp.Proofs.W08_CYCLIC

noncomputable section
open Filter
open scoped BigOperators Topology
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Analytic
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Finite
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Near
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Complex
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_FixedMass

theorem cyclicStructure
    (hF : FiniteEnumerationStatement)
    (hK : KernelBoundStatement)
    (hR : RateStatement)
    (hT : TupleEstimatesStatement)
    (hA : AnalyticSumsStatement) : CyclicStructureStatement := by
  constructor
  · intro M hbare
    have hmass := barely_unicyclic_bounded hF hT hA M hbare
    refine ⟨hmass,
      barely_small_complex_bounded hF hK hT hA M hbare, ?_⟩
    intro r
    exact barely_cyclic_tail hF hR
      (fun M hM => barely_unicyclic_bounded hF hT hA M hM) M hbare r
  · intro M lam hadm hlam hlam1 hdeg
    obtain ⟨hsum, hmass⟩ := fixed_unicyclic_tendsto hF hR hT M lam
      hadm hlam hlam1 hdeg
    have hnonneg : 0 ≤ unicyclicLimit lam := by
      rw [unicyclicLimit_eq_tsum]
      exact tsum_nonneg fun k => unicyclicLimitTerm_nonneg lam hlam k
    refine ⟨hnonneg, hmass,
      fixed_small_complex_bounded hF hK hR hT M lam hadm hlam hlam1 hdeg, ?_⟩
    intro ns h ell hns hoff
    exact fixed_cyclic_tail hF hR hadm hlam hlam1 hdeg hmass ns h ell hns hoff

/-- Exact conditional W08 producer: all five declared inputs are consumed at
the public contract boundary, and no premise is hidden in the export. -/
theorem result : FiniteEnumerationStatement →
    KernelBoundStatement →
    RateStatement →
    TupleEstimatesStatement →
    AnalyticSumsStatement →
    CyclicStructureStatement := by
  intro hF hK hR hT hA
  exact cyclicStructure hF hK hR hT hA

end
end Erdos745.WrapUp.Proofs.W08_CYCLIC
