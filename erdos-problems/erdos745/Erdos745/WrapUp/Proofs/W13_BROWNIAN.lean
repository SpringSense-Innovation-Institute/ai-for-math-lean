module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W13_Nullity

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section
namespace Erdos745.WrapUp.Proofs.W13_BROWNIAN

noncomputable section
open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

open Internal.W13_BROWNIAN_Law
open Internal.W13_BROWNIAN_Ranks
open Internal.W13_BROWNIAN_Regularity

local instance : MeasurableSpace BrownianPath := borel BrownianPath
local instance : BorelSpace BrownianPath := ⟨rfl⟩

/-- Existence of the Brownian law and positivity, finiteness and measurability of excursion ranks. -/
theorem result : BrownianFoundationStatement := by
  unfold BrownianFoundationStatement
  refine ⟨brownianLaw_existsUnique, ?_⟩
  intro mu hmu lam
  have hgood : ∀ᵐ w ∂mu, GoodExcursionPath w lam :=
    Internal.W13_BROWNIAN_Geometry.ae_goodExcursionPath_of_fixedTime_null_postend_late
      mu hmu lam
      (Internal.W13_BROWNIAN_Nullity.fixedTime_reflected_zero_null mu hmu lam)
      (Internal.W13_BROWNIAN_Minima.ae_postend_descent mu hmu lam)
      (Internal.W13_BROWNIAN_LateExcursions.ae_late_exclusion mu hmu lam)
  refine ⟨hgood, ?_⟩
  intro i hi
  refine ⟨measurable_excursionRankExtended lam i, ?_⟩
  filter_upwards [hgood] with w hw
  exact excursionRankExtended_pos_lt_top_of_good w lam hw i hi

end

end Erdos745.WrapUp.Proofs.W13_BROWNIAN
