module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W01_FiniteCore
public import Erdos745.WrapUp.Proofs.Internal.Linked.W01_Pruefer
public import Erdos745.WrapUp.Proofs.Internal.Linked.W01_Asymptotic
public import Erdos745.WrapUp.Proofs.Internal.Linked.W01_Unicyclic

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section
namespace Erdos745.WrapUp.Proofs.W01_ENUM

open Erdos745.WrapUp.Proofs.Internal

/-- Unconditional assembly of the finite graph laws and exact labelled
enumeration. -/
theorem result : FiniteEnumerationStatement := by
  have hforest := W01_ENUM_Pruefer.rootedForestFormula
  have ht := W01_ENUM_Trees.result hforest
  have hf := W01_ENUM_Finite.result ht.2
  have hunicyclic :=
    W01_ENUM_Unicyclic.unicyclic_formula_of_cycle_forest_decomposition
      hforest W01_ENUM_Decomposition.cycleForestDecomposition
  have ha := W01_ENUM_Asymptotic.result W01_ENUM_Midpoint.result hunicyclic
  exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1,
    hf.2.2.2.2.2.1, hf.2.2.2.2.2.2, ht.1, ht.2, ha.1, ha.2.1,
    ha.2.2.1, ha.2.2.2⟩

end Erdos745.WrapUp.Proofs.W01_ENUM
