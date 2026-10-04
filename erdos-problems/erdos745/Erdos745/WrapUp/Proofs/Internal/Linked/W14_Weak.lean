module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W14_Tightness
public import Erdos745.WrapUp.Proofs.Internal.Linked.W13_Law
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Topology.Bases
public import Erdos745.WrapUp.Proofs.Internal.Linked.W14_Drift
public import Erdos745.WrapUp.Proofs.Internal.Linked.W14_Base
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.MeasureTheory.Measure.Tight

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


/-!
# Same-Brownian-law weak convergence of centered exploration mesh vectors

The finite observation tuple is replaced temporarily by its ordered support.
Increments on that support have the product Gaussian law supplied by the
particular `BrownianLaw mu` argument. The support index maps zero and repeated
times back to the original tuple. The all-index exploration vector laws are
those from `VectorTightness`; they agree eventually with the actual fixed-edge
law. Tightness and characteristic uniqueness identify every cluster point.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_MeshWeak

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Characteristic
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_VectorTightness
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteLaw
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_QueueControl
open Erdos745.WrapUp.Proofs.Internal.W13_BROWNIAN_Law
open Filter MeasureTheory ProbabilityTheory WithLp BoundedContinuousFunction
open scoped BigOperators Topology ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable
local instance : MeasurableSpace BrownianPath := borel BrownianPath
local instance : BorelSpace BrownianPath := ⟨rfl⟩
local instance graphMeasurableSpace (n : ℕ) : MeasurableSpace (Graph n) := ⊤
set_option maxHeartbeats 1000000

private def timeSupport {d : ℕ} (t : Fin d → NNReal) : Finset NNReal :=
  Finset.univ.image t

private def stepCount {d : ℕ} (t : Fin d → NNReal) : ℕ :=
  (insert 0 (timeSupport t)).card - 1

private theorem support_card {d : ℕ} (t : Fin d → NNReal) :
    (insert 0 (timeSupport t)).card = stepCount t + 1 := by
  unfold stepCount
  have h : 0 < (insert 0 (timeSupport t)).card :=
    Finset.card_pos.mpr ⟨0, Finset.mem_insert_self _ _⟩
  omega

private def supportOrder {d : ℕ} (t : Fin d → NNReal) :
    Fin (stepCount t + 1) ≃o {x // x ∈ insert 0 (timeSupport t)} :=
  (insert 0 (timeSupport t)).orderIsoOfFin (support_card t)

private theorem supportOrder_zero {d : ℕ} (t : Fin d → NNReal) :
    ((supportOrder t 0 : {x // x ∈ insert 0 (timeSupport t)}) : NNReal) = 0 := by
  let z : {x // x ∈ insert 0 (timeSupport t)} :=
    ⟨0, Finset.mem_insert_self _ _⟩
  obtain ⟨i, hi⟩ := (supportOrder t).surjective z
  have hle := (supportOrder t).monotone (Fin.zero_le i)
  change ((supportOrder t 0 : {x // x ∈ insert 0 (timeSupport t)}) : NNReal) ≤
    ((supportOrder t i : {x // x ∈ insert 0 (timeSupport t)}) : NNReal) at hle
  rw [hi] at hle
  exact le_antisymm hle (zero_le)

private def orderedTime {d : ℕ} (t : Fin d → NNReal) : ℕ → NNReal :=
  fun k => if hk : k < stepCount t + 1 then
    ((supportOrder t ⟨k, hk⟩ : {x // x ∈ insert 0 (timeSupport t)}) : NNReal)
  else 0

private theorem orderedTime_zero {d : ℕ} (t : Fin d → NNReal) :
    orderedTime t 0 = 0 := by
  rw [orderedTime, dif_pos (by omega)]
  exact supportOrder_zero t

private theorem orderedTime_strict {d : ℕ} (t : Fin d → NNReal) :
    ∀ j < stepCount t, orderedTime t j < orderedTime t (j + 1) := by
  intro j hj
  have h0 : j < stepCount t + 1 := by omega
  have h1 : j + 1 < stepCount t + 1 := by omega
  simp only [orderedTime, dif_pos h0, dif_pos h1]
  exact (supportOrder t).lt_iff_lt.mpr (by simp)

private def timeIndex {d : ℕ} (t : Fin d → NNReal) (i : Fin d) :
    Fin (stepCount t + 1) :=
  (supportOrder t).symm ⟨t i, Finset.mem_insert_of_mem
    (Finset.mem_image_of_mem t (Finset.mem_univ i))⟩

private theorem orderedTime_index {d : ℕ} (t : Fin d → NNReal) (i : Fin d) :
    orderedTime t (timeIndex t i) = t i := by
  rw [orderedTime, dif_pos (timeIndex t i).isLt]
  exact congrArg Subtype.val ((supportOrder t).apply_symm_apply
    ⟨t i, Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem t (Finset.mem_univ i))⟩)

private def increments {d : ℕ} (t : Fin d → NNReal) :
    BrownianPath → Fin (stepCount t) → ℝ :=
  fun w j => w (orderedTime t (j + 1)) - w (orderedTime t j)

private theorem measurable_increments {d : ℕ} (t : Fin d → NNReal) :
    Measurable (increments t) := by
  apply measurable_pi_lambda
  intro j
  exact ((ContinuousEvalConst.continuous_eval_const (orderedTime t (j + 1))).sub
    (ContinuousEvalConst.continuous_eval_const (orderedTime t j))).measurable

private def gaussianSteps {d : ℕ} (t : Fin d → NNReal)
    (j : Fin (stepCount t)) : Measure ℝ :=
  gaussianReal 0 (((orderedTime t (j + 1) : ℝ) -
    (orderedTime t j : ℝ)).toNNReal)

/-- The exact product increment law extracted from the supplied `mu`. -/
private theorem increments_law {d : ℕ} (mu : PathLaw)
    (hmu : BrownianLaw mu) (t : Fin d → NNReal) :
    Measure.map (increments t) mu = Measure.pi (gaussianSteps t) := by
  have h := (incrementLaws_of_brownianLaw mu hmu).2.2
    (stepCount t) (orderedTime t) (orderedTime_strict t)
  change Measure.map (increments t) mu = Measure.pi (gaussianSteps t) at h
  exact h

/-- The finite tuple of evaluations under the *same* path law. -/
def brownianEvaluationVector {d : ℕ} (t : Fin d → NNReal)
    (w : BrownianPath) : EuclideanSpace ℝ (Fin d) :=
  toLp 2 (fun i => w (t i))

theorem measurable_brownianEvaluationVector {d : ℕ} (t : Fin d → NNReal) :
    Measurable (brownianEvaluationVector t) := by
  unfold brownianEvaluationVector
  apply (measurable_toLp 2 _).comp
  apply measurable_pi_lambda
  intro i
  exact (ContinuousEvalConst.continuous_eval_const (t i)).measurable

def brownianEvaluationLaw {d : ℕ} (mu : PathLaw)
    (hmu : BrownianLaw mu) (t : Fin d → NNReal) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) :=
  letI : IsProbabilityMeasure mu := hmu.1
  ⟨Measure.map (brownianEvaluationVector t) mu,
    Measure.isProbabilityMeasure_map
      (measurable_brownianEvaluationVector t).aemeasurable⟩

private def cumulativeVector {d : ℕ} (t : Fin d → NNReal)
    (y : Fin (stepCount t) → ℝ) : EuclideanSpace ℝ (Fin d) :=
  toLp 2 (fun i => ∑ j : Fin (stepCount t),
    if (j : ℕ) < timeIndex t i then y j else 0)

private theorem measurable_cumulativeVector {d : ℕ} (t : Fin d → NNReal) :
    Measurable (cumulativeVector t) := by
  unfold cumulativeVector
  apply (measurable_toLp 2 _).comp
  apply measurable_pi_lambda
  intro i
  apply Finset.measurable_sum
  intro j hj
  split_ifs
  · exact measurable_pi_apply j
  · exact measurable_const

private theorem cumulative_increments {d : ℕ} (t : Fin d → NNReal)
    (w : BrownianPath) (i : Fin d) :
    cumulativeVector t (increments t w) i = w (t i) - w 0 := by
  unfold cumulativeVector increments
  have hindex : (timeIndex t i : ℕ) ≤ stepCount t := by
    have h := (timeIndex t i).isLt
    omega
  have hsum : (∑ j : Fin (stepCount t),
      if (j : ℕ) < timeIndex t i then
        w (orderedTime t (j + 1)) - w (orderedTime t j) else 0) =
      ∑ j ∈ Finset.range (timeIndex t i : ℕ),
        (w (orderedTime t (j + 1)) - w (orderedTime t j)) := by
    calc
      _ = ∑ j ∈ Finset.range (stepCount t),
          if j < (timeIndex t i : ℕ) then
            w (orderedTime t (j + 1)) - w (orderedTime t j) else 0 := by
            simpa using! (Fin.sum_univ_eq_sum_range
              (fun (j : ℕ) => if j < (timeIndex t i : ℕ) then
                w (orderedTime t (j + 1)) - w (orderedTime t j) else 0)
              (stepCount t))
      _ = _ := by
        rw [← Finset.sum_filter]
        have hf : (Finset.range (stepCount t)).filter
            (fun (j : ℕ) => j < (timeIndex t i : ℕ)) =
            Finset.range (timeIndex t i : ℕ) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_range]
          omega
        rw [hf]
  change (∑ j : Fin (stepCount t),
      if (j : ℕ) < timeIndex t i then
        w (orderedTime t (j + 1)) - w (orderedTime t j) else 0) = _
  rw [hsum]
  simpa [orderedTime_index, orderedTime_zero] using!
    (Finset.sum_range_sub (fun j => w (orderedTime t j)) (timeIndex t i : ℕ))

private theorem start_zero_ae (mu : PathLaw) (hmu : BrownianLaw mu) :
    ∀ᵐ w ∂mu, w 0 = 0 := by
  letI : IsProbabilityMeasure mu := hmu.1
  have hset : MeasurableSet {w : BrownianPath | w 0 = 0} :=
    MeasurableSet.preimage (measurableSet_singleton 0)
      (ContinuousEvalConst.continuous_eval_const (0 : NNReal)).measurable
  apply (ae_iff_measure_eq hset.nullMeasurableSet).2
  simpa [measure_univ] using! (incrementLaws_of_brownianLaw mu hmu).2.1

/-- Every tuple, including zero and repeated times, is a deterministic
cumulation of the ordered Gaussian increments. -/
private theorem brownianEvaluationLaw_as_gaussian_map {d : ℕ}
    (mu : PathLaw) (hmu : BrownianLaw mu) (t : Fin d → NNReal) :
    (brownianEvaluationLaw mu hmu t : Measure (EuclideanSpace ℝ (Fin d))) =
      Measure.map (cumulativeVector t) (Measure.pi (gaussianSteps t)) := by
  change Measure.map (brownianEvaluationVector t) mu = _
  rw [← increments_law mu hmu t]
  rw [Measure.map_map (measurable_cumulativeVector t) (measurable_increments t)]
  apply Measure.map_congr
  filter_upwards [start_zero_ae mu hmu] with w hw
  apply PiLp.ext
  intro i
  simp only [Function.comp_apply]
  change w (t i) = cumulativeVector t (increments t w) i
  rw [cumulative_increments, hw, sub_zero]

private def stepWeight {d : ℕ} (t : Fin d → NNReal)
    (z : Fin d → ℝ) (j : Fin (stepCount t)) : ℝ :=
  ∑ i : Fin d, if (j : ℕ) < timeIndex t i then z i else 0

private theorem inner_real_mul (a b : ℝ) : inner ℝ a b = a * b := by
  change b * a = a * b
  ring

private theorem inner_cumulative {d : ℕ} (t : Fin d → NNReal)
    (z : EuclideanSpace ℝ (Fin d)) (y : Fin (stepCount t) → ℝ) :
    inner ℝ (cumulativeVector t y) z =
      inner ℝ (toLp 2 y) (toLp 2 (stepWeight t z)) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [inner_real_mul]
  unfold cumulativeVector stepWeight
  change (∑ i : Fin d,
      (∑ j : Fin (stepCount t), if (j : ℕ) < timeIndex t i then y j else 0) * z i) =
    ∑ j : Fin (stepCount t), y j *
      (∑ i : Fin d, if (j : ℕ) < timeIndex t i then z i else 0)
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> ring

private theorem orderedTime_cast_sub {d : ℕ} (t : Fin d → NNReal)
    (j : Fin (stepCount t)) :
    (orderedTime t (j + 1) : ℝ) - (orderedTime t j : ℝ) =
      (((orderedTime t (j + 1) : ℝ) - (orderedTime t j : ℝ)).toNNReal : ℝ) := by
  have h := orderedTime_strict t j j.isLt
  exact (Real.coe_toNNReal _
    (sub_nonneg.mpr (NNReal.coe_le_coe.mpr h.le))).symm

private theorem covariance_pair {d : ℕ} (t : Fin d → NNReal)
    (i l : Fin d) :
    (∑ j : Fin (stepCount t),
      ((orderedTime t (j + 1) : ℝ) - (orderedTime t j : ℝ)) *
        (if (j : ℕ) < timeIndex t i then (1 : ℝ) else 0) *
        (if (j : ℕ) < timeIndex t l then (1 : ℝ) else 0)) =
      min (t i : ℝ) (t l : ℝ) := by
  have hmin : min (timeIndex t i : ℕ) (timeIndex t l : ℕ) ≤ stepCount t := by
    have hi := (timeIndex t i).isLt
    have hl := (timeIndex t l).isLt
    omega
  have hsum : (∑ j : Fin (stepCount t),
      ((orderedTime t (j + 1) : ℝ) - (orderedTime t j : ℝ)) *
        (if (j : ℕ) < timeIndex t i then (1 : ℝ) else 0) *
        (if (j : ℕ) < timeIndex t l then (1 : ℝ) else 0)) =
      ∑ j ∈ Finset.range (min (timeIndex t i : ℕ) (timeIndex t l : ℕ)),
        ((orderedTime t (j + 1) : ℝ) - (orderedTime t j : ℝ)) := by
    have hpoint (j : Fin (stepCount t)) :
        ((orderedTime t (j + 1) : ℝ) - (orderedTime t j : ℝ)) *
          (if (j : ℕ) < timeIndex t i then (1 : ℝ) else 0) *
          (if (j : ℕ) < timeIndex t l then (1 : ℝ) else 0) =
        if (j : ℕ) < min (timeIndex t i : ℕ) (timeIndex t l : ℕ) then
          ((orderedTime t (j + 1) : ℝ) - (orderedTime t j : ℝ)) else 0 := by
      by_cases hi : (j : ℕ) < timeIndex t i <;>
        by_cases hl : (j : ℕ) < timeIndex t l <;>
        simp [hi, hl]
    simp_rw [hpoint]
    calc
      _ = ∑ j ∈ Finset.range (stepCount t),
          if j < min (timeIndex t i : ℕ) (timeIndex t l : ℕ) then
            (orderedTime t (j + 1) : ℝ) - (orderedTime t j : ℝ) else 0 := by
            simpa using! (Fin.sum_univ_eq_sum_range
              (fun (j : ℕ) => if j < min (timeIndex t i : ℕ) (timeIndex t l : ℕ) then
                (orderedTime t (j + 1) : ℝ) - (orderedTime t j : ℝ) else 0)
              (stepCount t))
      _ = _ := by
        rw [← Finset.sum_filter]
        have hf : (Finset.range (stepCount t)).filter
            (fun (j : ℕ) => j < min (timeIndex t i : ℕ) (timeIndex t l : ℕ)) =
            Finset.range (min (timeIndex t i : ℕ) (timeIndex t l : ℕ)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_range]
          omega
        rw [hf]
  rw [hsum]
  have htel := Finset.sum_range_sub
    (fun j => (orderedTime t j : ℝ))
    (min (timeIndex t i : ℕ) (timeIndex t l : ℕ))
  rw [htel, orderedTime_zero]
  simp only [NNReal.coe_zero, sub_zero]
  rcases le_total (timeIndex t i : ℕ) (timeIndex t l : ℕ) with h | h
  · rw [min_eq_left h, min_eq_left]
    · simp [orderedTime_index]
    · have hh : orderedTime t (timeIndex t i) ≤
          orderedTime t (timeIndex t l) := by
        unfold orderedTime
        simp only [dif_pos (timeIndex t i).isLt,
          dif_pos (timeIndex t l).isLt]
        exact (supportOrder t).monotone (Fin.mk_le_mk.mpr h)
      rw [orderedTime_index, orderedTime_index] at hh
      exact_mod_cast hh
  · rw [min_eq_right h, min_eq_right]
    · simp [orderedTime_index]
    · have hh : orderedTime t (timeIndex t l) ≤
          orderedTime t (timeIndex t i) := by
        unfold orderedTime
        simp only [dif_pos (timeIndex t i).isLt,
          dif_pos (timeIndex t l).isLt]
        exact (supportOrder t).monotone (Fin.mk_le_mk.mpr h)
      rw [orderedTime_index, orderedTime_index] at hh
      exact_mod_cast hh

private theorem covariance_sum {d : ℕ} (t : Fin d → NNReal)
    (z : Fin d → ℝ) :
    (∑ j : Fin (stepCount t),
      ((orderedTime t (j + 1) : ℝ) - (orderedTime t j : ℝ)) *
        stepWeight t z j ^ 2) =
      ∑ i : Fin d, ∑ l : Fin d,
        min (t i : ℝ) (t l : ℝ) * z i * z l := by
  unfold stepWeight
  calc
    _ = ∑ j : Fin (stepCount t), ∑ i : Fin d, ∑ l : Fin d,
      ((orderedTime t (j + 1) : ℝ) - (orderedTime t j : ℝ)) *
        (if (j : ℕ) < timeIndex t i then z i else 0) *
        (if (j : ℕ) < timeIndex t l then z l else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      let a : Fin d → ℝ := fun i =>
        if (j : ℕ) < timeIndex t i then z i else 0
      change ((orderedTime t (j + 1) : ℝ) - (orderedTime t j : ℝ)) *
        (∑ i : Fin d, a i) ^ 2 =
        ∑ i : Fin d, ∑ l : Fin d,
          ((orderedTime t (j + 1) : ℝ) - (orderedTime t j : ℝ)) *
            a i * a l
      calc
        _ = ((orderedTime t (j + 1) : ℝ) - (orderedTime t j : ℝ)) *
            (∑ i : Fin d, ∑ l : Fin d, a i * a l) := by
              rw [pow_two, Finset.sum_mul]
              congr 1
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.mul_sum]
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l hl
          ring
    _ = ∑ i : Fin d, ∑ l : Fin d, ∑ j : Fin (stepCount t),
      ((orderedTime t (j + 1) : ℝ) - (orderedTime t j : ℝ)) *
        (if (j : ℕ) < timeIndex t i then z i else 0) *
        (if (j : ℕ) < timeIndex t l then z l else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro l hl
      have hp : ∀ j : Fin (stepCount t),
          ((orderedTime t (j + 1) : ℝ) - (orderedTime t j : ℝ)) *
            (if (j : ℕ) < timeIndex t i then z i else 0) *
            (if (j : ℕ) < timeIndex t l then z l else 0) =
          (((orderedTime t (j + 1) : ℝ) - (orderedTime t j : ℝ)) *
            (if (j : ℕ) < timeIndex t i then (1 : ℝ) else 0) *
            (if (j : ℕ) < timeIndex t l then (1 : ℝ) else 0)) * z i * z l := by
        intro j
        split_ifs <;> ring
      simp_rw [hp, ← Finset.sum_mul]
      rw [covariance_pair t i l]

/-- The characteristic function of the vector of evaluations of the supplied
Brownian law has exactly the covariance appearing in B04. -/
theorem brownianEvaluationLaw_charFun {d : ℕ} (mu : PathLaw)
    (hmu : BrownianLaw mu) (t : Fin d → NNReal)
    (z : EuclideanSpace ℝ (Fin d)) :
    charFun (brownianEvaluationLaw mu hmu t : Measure _) z =
      Complex.exp ((-(∑ i : Fin d, ∑ l : Fin d,
        min (t i : ℝ) (t l : ℝ) * z i * z l) / 2 : ℝ) : ℂ) := by
  let θ : Fin (stepCount t) → ℝ := stepWeight t z
  have hmap := brownianEvaluationLaw_as_gaussian_map mu hmu t
  rw [hmap]
  have hchar : charFun (Measure.map (cumulativeVector t)
      (Measure.pi (gaussianSteps t))) z =
      charFun ((Measure.pi (gaussianSteps t)).map (toLp 2)) (toLp 2 θ) := by
    unfold charFun
    rw [integral_map (measurable_cumulativeVector t).aemeasurable
      (by fun_prop), integral_map (measurable_toLp 2 _).aemeasurable
      (by fun_prop)]
    apply integral_congr_ae
    filter_upwards [] with y
    rw [inner_cumulative]
  letI (j : Fin (stepCount t)) : IsProbabilityMeasure (gaussianSteps t j) := by
    dsimp [gaussianSteps]
    infer_instance
  rw [hchar, charFun_pi]
  have hterm (j : Fin (stepCount t)) :
      charFun (gaussianSteps t j) (θ j) =
      Complex.exp (((-(((orderedTime t (j + 1) : ℝ) -
        (orderedTime t j : ℝ)) * θ j ^ 2 / 2) : ℝ) : ℂ)) := by
    unfold gaussianSteps
    rw [charFun_gaussianReal]
    rw [← orderedTime_cast_sub t j]
    push_cast
    ring_nf
  simp_rw [hterm]
  have hprod : (∏ j : Fin (stepCount t),
      Complex.exp (((-(((orderedTime t (j + 1) : ℝ) -
        (orderedTime t j : ℝ)) * θ j ^ 2 / 2) : ℝ) : ℂ))) =
      Complex.exp ((-(∑ j : Fin (stepCount t),
        ((orderedTime t (j + 1) : ℝ) - (orderedTime t j : ℝ)) * θ j ^ 2) / 2 : ℝ) : ℂ) := by
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    calc
      (∑ j : Fin (stepCount t),
          -(((orderedTime t (j + 1) : ℂ) -
            (orderedTime t j : ℂ)) * (θ j : ℂ) ^ 2 / 2)) =
          -(∑ j : Fin (stepCount t),
            (((orderedTime t (j + 1) : ℂ) -
              (orderedTime t j : ℂ)) * (θ j : ℂ) ^ 2 / 2)) := by
                rw [Finset.sum_neg_distrib]
      _ = _ := by
        rw [← Finset.sum_div]
        ring
  rw [hprod, covariance_sum t z]

private theorem integral_fixedMeasure_complex (n M : ℕ)
    (hM : M ≤ capacity n) (f : Graph n → ℂ) :
    ∫ G, f G ∂fixedMeasure n M hM = complexExpectM n M f := by
  rw [fixedMeasure, PMF.integral_eq_sum]
  unfold fixedPMF complexExpectM
  simp only [PMF.uniformOfFinset_apply]
  calc
    _ = ∑ x, if x ∈ fixedGraphs n M then
          ((fixedGraphs n M).card : ℂ)⁻¹ * f x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : x ∈ fixedGraphs n M
      · simp only [if_pos h]
        change (((((fixedGraphs n M).card : ENNReal)⁻¹).toReal) • f x) =
          (((fixedGraphs n M).card : ℂ)⁻¹) * f x
        simp [ENNReal.toReal_inv, Complex.real_smul]
      · simp [h]
    _ = ∑ x ∈ fixedGraphs n M,
          ((fixedGraphs n M).card : ℂ)⁻¹ * f x := by
      rw [← Finset.sum_filter]
      simp
    _ = (fixedGraphs n M).sum f / ((fixedGraphs n M).card : ℂ) := by
      rw [← Finset.mul_sum]
      simp only [div_eq_mul_inv]
      ring

private theorem centeredVectorLaw_charFun_eventually {d : ℕ}
    (M : NatSeq) (lam : ℝ) (hcritical : criticalWindow M lam)
    (t : Fin d → NNReal) (z : EuclideanSpace ℝ (Fin d)) :
    (fun n => charFun
      (centeredVectorLaw M t n : Measure (EuclideanSpace ℝ (Fin d))) z) =ᶠ[atTop]
    (fun n => complexExpectM n (M n) (fun G =>
      Complex.exp (Complex.I *
        (((∑ i : Fin d, z i * centeredPartial (M n) G
          (meshIndex n (t i : ℝ))) / n13 n : ℝ) : ℂ)))) := by
  filter_upwards [hcritical.1] with n hM
  rw [centeredVectorLaw_eq_actual M t n hM]
  unfold charFun
  rw [integral_map
    (measurable_from_fixed_graphs (centeredMeshVector (M n) n t)).aemeasurable
    (by fun_prop)]
  rw [integral_fixedMeasure_complex n (M n) hM]
  unfold complexExpectM
  congr 1
  apply Finset.sum_congr rfl
  intro G hG
  congr 1
  rw [PiLp.inner_apply]
  simp only [inner_real_mul,
    centeredMeshVector_apply]
  push_cast
  rw [Finset.sum_div]
  have hsum : (∑ x : Fin d,
      (centeredPartial (M n) G (meshIndex n (t x : ℝ)) : ℂ) *
        (n13 n : ℂ)⁻¹ * (z x : ℂ)) =
      ∑ x : Fin d, (z x : ℂ) *
        (centeredPartial (M n) G (meshIndex n (t x : ℝ)) : ℂ) *
        (n13 n : ℂ)⁻¹ := by
    apply Finset.sum_congr rfl
    intro x hx
    ring
  simp only [div_eq_mul_inv] at *
  rw [hsum]
  ring

/-- The B04 characteristic limit, now stated for the B05 all-index laws. -/
theorem centeredVectorLaw_charFun_tendsto {d : ℕ}
    (hfinite : FiniteEnumerationStatement) (M : NatSeq) (lam T : ℝ)
    (hcritical : criticalWindow M lam) (hT : 0 ≤ T)
    (t : Fin d → NNReal) (ht : ∀ i, (t i : ℝ) ≤ T)
    (z : EuclideanSpace ℝ (Fin d)) :
    Tendsto (fun n => charFun
      (centeredVectorLaw M t n : Measure (EuclideanSpace ℝ (Fin d))) z)
      atTop (𝓝 (Complex.exp ((-(∑ i : Fin d, ∑ l : Fin d,
        min (t i : ℝ) (t l : ℝ) * z i * z l) / 2 : ℝ) : ℂ))) := by
  have hbase := critical_centered_vector_characteristic hfinite M lam T
    hcritical hT (fun i => (t i : ℝ)) (fun i => z i)
    (fun i => (t i).property) ht
  exact hbase.congr' (centeredVectorLaw_charFun_eventually M lam hcritical t z).symm

private theorem charFun_tendsto_of_weak {d : ℕ}
    {ν : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin d))}
    {ξ : ProbabilityMeasure (EuclideanSpace ℝ (Fin d))}
    (hν : Tendsto ν atTop (𝓝 ξ))
    (z : EuclideanSpace ℝ (Fin d)) :
    Tendsto (fun n => charFun (ν n : Measure _) z)
      atTop (𝓝 (charFun (ξ : Measure _) z)) := by
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto
    ℂ).1 hν (innerProbChar z)
  simpa only [charFun_eq_integral_innerProbChar] using! h

/-- The tight all-index laws have exactly one possible cluster point: the
finite evaluation law of the *supplied* Brownian `mu`. -/
theorem centeredVectorLaw_weak {d : ℕ}
    (hfinite : FiniteEnumerationStatement) (M : NatSeq) (lam T : ℝ)
    (hcritical : criticalWindow M lam) (hT : 0 ≤ T)
    (mu : PathLaw) (hmu : BrownianLaw mu)
    (t : Fin d → NNReal) (ht : ∀ i, (t i : ℝ) ≤ T) :
    Tendsto (centeredVectorLaw M t) atTop
      (𝓝 (brownianEvaluationLaw mu hmu t)) := by
  let S : Set (ProbabilityMeasure (EuclideanSpace ℝ (Fin d))) :=
    Set.range (centeredVectorLaw M t)
  have hS : IsTightMeasureSet
      {x : Measure (EuclideanSpace ℝ (Fin d)) | ∃ n,
        (centeredVectorLaw M t n : Measure _) = x} :=
    centeredVectorLaw_tight hfinite M lam T hcritical hT t ht
  have hcompact : IsCompact (closure S) :=
    isCompact_closure_of_isTightMeasureSet (S := S) (by simpa [S] using! hS)
  apply hcompact.tendsto_nhds_of_unique_mapClusterPt
  · exact Filter.Eventually.of_forall (fun n => subset_closure ⟨n, rfl⟩)
  · intro ν hν hcluster
    obtain ⟨φ, hφmono, hφ⟩ :=
      TopologicalSpace.FirstCountableTopology.tendsto_subseq hcluster
    have hφtop : Tendsto φ atTop atTop := hφmono.tendsto_atTop
    have hchar (z : EuclideanSpace ℝ (Fin d)) :
        charFun (ν : Measure _) z =
          charFun (brownianEvaluationLaw mu hmu t : Measure _) z := by
      have hlim := (centeredVectorLaw_charFun_tendsto hfinite M lam T
        hcritical hT t ht z).comp hφtop
      have hlim' := charFun_tendsto_of_weak hφ z
      have htarget := brownianEvaluationLaw_charFun mu hmu t z
      rw [← htarget] at hlim
      exact tendsto_nhds_unique hlim' hlim
    have heq : (ν : Measure (EuclideanSpace ℝ (Fin d))) =
        (brownianEvaluationLaw mu hmu t : Measure _) :=
      Measure.ext_of_charFun (funext hchar)
    exact ProbabilityMeasure.toMeasure_injective heq

/- Every bounded continuous real test of the actual fixed-edge centered
mesh vector converges to the same `mu`'s Brownian evaluation vector. -/
end

end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_MeshWeak


/-!
# Compact-window tightness for the concrete exploration interpolation

The centered and predictable parts are assembled on the same fixed graph.  The
eventual horizon guard is used only for the martingale identification, so the
result remains an actual `explorationInterpolation` statement.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_WindowTightness

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_DyadicCompact
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_DriftCompact
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_DriftFinite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FourthMoment
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Drift
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteHorizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Interpolation
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_QueueControl
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_CriticalBudget
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteLaw
open Filter Set MeasureTheory
open scoped BigOperators Topology

noncomputable section
attribute [local instance] Classical.propDecidable

local instance graphMeasurableSpace (n : ℕ) : MeasurableSpace (Graph n) := ⊤
local instance : MeasurableSpace BrownianPath := borel BrownianPath
local instance : BorelSpace BrownianPath := ⟨rfl⟩

/-- Continuous restriction of a full path to the compact time window. -/
def pathRestriction (T : NNReal) (w : BrownianPath) : C(Window T, ℝ) :=
  w.restrict (Set.Icc 0 T)

theorem continuous_pathRestriction (T : NNReal) : Continuous (pathRestriction T) :=
  ContinuousMap.continuous_restrict (Set.Icc 0 T)

/-- The restriction of the concrete interpolation, including its stationary tail. -/
def explorationRestriction {n : ℕ} (G : Graph n) (T : NNReal) : C(Window T, ℝ) :=
  pathRestriction T (explorationInterpolation n G)

@[simp] theorem explorationRestriction_apply {n : ℕ} (G : Graph n)
    (T : NNReal) (x : Window T) :
    explorationRestriction G T x = explorationInterpolation n G x.1 := rfl

/-- Restriction-event mass for the actual fixed-edge path pushforward. -/
theorem explorationPathMeasure_restriction_toReal (n M : ℕ)
    (hM : M ≤ capacity n) (T : NNReal) (K : Set (C(Window T, ℝ)))
    (hK : IsCompact K) :
    (explorationPathMeasure n M hM {w | pathRestriction T w ∈ K}).toReal =
      probM n M (fun G => explorationRestriction G T ∈ K) := by
  have hmeas : MeasurableSet {w : BrownianPath | pathRestriction T w ∈ K} :=
    (hK.isClosed.preimage (continuous_pathRestriction T)).measurableSet
  unfold explorationPathMeasure
  rw [Measure.map_apply (measurable_explorationInterpolation n) hmeas]
  exact fixedMeasure_apply_toReal n M hM _

private theorem probM_complement_local {n M : ℕ} (hM : M ≤ capacity n)
    (P : Graph n → Prop) :
    probM n M P + probM n M (fun G => ¬ P G) = 1 := by
  classical
  unfold probM
  rw [← add_div, ← Nat.cast_add]
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := fixedGraphs n M) P
  have hcard : ((fixedGraphs n M).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr (fixedGraphs_nonempty hM))
  convert (div_self hcard) using 1
  congr 1
  norm_cast
  convert hpartition using 1
  congr 2
  ext G
  simp

private theorem probM_union_local {n M : ℕ} (P Q : Graph n → Prop) :
    probM n M (fun G => P G ∨ Q G) ≤ probM n M P + probM n M Q := by
  classical
  unfold probM
  have hs : (fixedGraphs n M).filter (fun G => P G ∨ Q G) =
      (fixedGraphs n M).filter P ∪ (fixedGraphs n M).filter Q := by
    ext G
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  have hc := Finset.card_union_le
    ((fixedGraphs n M).filter P) ((fixedGraphs n M).filter Q)
  have hr : (((((fixedGraphs n M).filter P ∪
        (fixedGraphs n M).filter Q).card : ℝ))) ≤
      ((fixedGraphs n M).filter P).card +
        ((fixedGraphs n M).filter Q).card := by exact_mod_cast hc
  have hr' : (((fixedGraphs n M).filter (fun G => P G ∨ Q G)).card : ℝ) ≤
      ((fixedGraphs n M).filter P).card + ((fixedGraphs n M).filter Q).card := by
    rw [hs]
    exact hr
  rw [← add_div]
  convert div_le_div_of_nonneg_right hr' (Nat.cast_nonneg _) using 1
  congr 1
  congr 1
  congr 1
  ext G
  simp

private theorem martingalePartial_eq_centeredPartial
    {n M k : ℕ} (G : Graph n) (hk : k ≤ n) :
    martingalePartial G (fun i => queryMean M G i - 1) k =
      centeredPartial M G k := by
  unfold martingalePartial centeredPartial
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i < n := by
    have hi' : i < k := Finset.mem_range.mp hi
    omega
  rw [actualWalkIncrement_eq_queryCount G i hin]
  ring

/-- Both martingale endpoints are identified only inside the finite exploration. -/
private theorem explorationRestriction_eq_add
    {n M : ℕ} (G : Graph n) (T : NNReal)
    (ha : 1 ≤ n23 n) (hJ : ⌊((T : ℝ) + 1) * n23 n⌋₊ ≤ n) :
    explorationRestriction G T =
      centeredRestriction M G T + polygonalDriftRestriction M G T := by
  ext x
  have hguard := horizon_endpoint_guard n (T : ℝ) x.1
    (NNReal.coe_nonneg _) x.property.2 ha
  have hj1 : ⌊(x.1 : ℝ) * n23 n⌋₊ + 1 ≤ n := hguard.2.trans hJ
  have hj0 : ⌊(x.1 : ℝ) * n23 n⌋₊ ≤ n := by omega
  have hmart0 := martingalePartial_eq_centeredPartial
    (M := M) (k := ⌊(x.1 : ℝ) * n23 n⌋₊) G hj0
  have hmart1 := martingalePartial_eq_centeredPartial
    (M := M) (k := ⌊(x.1 : ℝ) * n23 n⌋₊ + 1) G hj1
  change explorationInterpolation n G x.1 =
    centeredPolygon M G x.1 + polygonalDriftRestriction M G T x
  rw [explorationInterpolation_isInterpolation n G x.1,
    polygonalDriftRestriction_apply G T ha x]
  have hraw := rawExploration_affine_decomposition M G x.1
  dsimp at hraw
  rw [hraw, hmart0, hmart1]
  unfold centeredPolygon linearInterpolation polygonalDrift
  simp only [NNReal.coe_mul, explorationScale_coe]
  ring

private theorem probM_mono_local {n M : ℕ} (P Q : Graph n → Prop)
    (h : ∀ G, P G → Q G) : probM n M P ≤ probM n M Q := by
  classical
  unfold probM
  have hs : (fixedGraphs n M).filter P ⊆ (fixedGraphs n M).filter Q := by
    intro G hG
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hG).1, h G (Finset.mem_filter.mp hG).2⟩
  have hc : (((fixedGraphs n M).filter P).card : ℝ) ≤
      (((fixedGraphs n M).filter Q).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hs
  exact div_le_div_of_nonneg_right hc (Nat.cast_nonneg _)

/-- The same compact set captures every admissible index; the finite initial
support is included explicitly alongside the eventual centered-plus-drift set. -/
theorem critical_explorationRestriction_compact_all
    (hfinite : FiniteEnumerationStatement) (M : NatSeq) (lam T ε : ℝ)
    (hcritical : criticalWindow M lam) (hT : 0 ≤ T) (hε : 0 < ε) :
    ∃ K : Set (C(Window ⟨T, hT⟩, ℝ)), IsCompact K ∧
      ∀ n, M n ≤ capacity n →
        probM n (M n)
          (fun G => explorationRestriction G ⟨T, hT⟩ ∈ K) ≥ 1 - ε := by
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨Kc, hKc, hc⟩ :=
    critical_centeredRestriction_compact hfinite M lam T (ε / 2)
      hcritical hT hε2
  obtain ⟨Kd, hKd, hd⟩ :=
    critical_polygonalDriftRestriction_compact hfinite M lam T (ε / 2)
      hcritical hT hε2
  let K : Set (C(Window ⟨T, hT⟩, ℝ)) := Set.image2 (· + ·) Kc Kd
  have hK : IsCompact K := by
    have hp : IsCompact (Kc ×ˢ Kd) := hKc.prod hKd
    have hcadd : Continuous (fun p : C(Window ⟨T, hT⟩, ℝ) ×
        C(Window ⟨T, hT⟩, ℝ) => p.1 + p.2) :=
      continuous_fst.add continuous_snd
    simpa only [Set.image_prod] using! hp.image hcadd
  have hguard : ∀ᶠ n : ℕ in atTop,
      1 ≤ n23 n ∧ ⌊(T + 1) * n23 n⌋₊ ≤ n := by
    have he := eventually_eighth_horizon (T + 1) (by linarith)
    have hb := n13_tendsto_atTop.eventually_ge_atTop (1 : ℝ)
    filter_upwards [he, hb, eventually_ge_atTop (1 : ℕ)] with n hh hbn hn
    have hn0 : 0 < n := by omega
    have ha : 1 ≤ n23 n := by
      rw [n23_eq_n13_square n hn0]
      nlinarith [sq_nonneg (n13 n - 1)]
    exact ⟨ha, by omega⟩
  have hevent : ∀ᶠ n : ℕ in atTop,
      (probM n (M n) (fun G => centeredRestriction (M n) G ⟨T, hT⟩ ∈ Kc) ≥ 1 - ε / 2) ∧
      (probM n (M n) (fun G => polygonalDriftRestriction (M n) G ⟨T, hT⟩ ∈ Kd) ≥ 1 - ε / 2) ∧
      (1 ≤ n23 n ∧ ⌊(T + 1) * n23 n⌋₊ ≤ n) := by
    filter_upwards [hc, hd, hguard] with n hcn hdn hg
    exact ⟨hcn, hdn, hg⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  let E : Set (C(Window ⟨T, hT⟩, ℝ)) :=
    Set.range (fun p : Σ n : Fin N, Graph (n : ℕ) =>
      explorationRestriction p.2 ⟨T, hT⟩)
  have hE : IsCompact E := (Set.finite_range _).isCompact
  let Kfinal : Set (C(Window ⟨T, hT⟩, ℝ)) := K ∪ E
  have hKfinal : IsCompact Kfinal := hK.union hE
  refine ⟨Kfinal, hKfinal, ?_⟩
  intro n hM
  by_cases hnN : N ≤ n
  · have ⟨hcn, hdn, hg⟩ := hN n hnN
    let A : Graph n → Prop := fun G => centeredRestriction (M n) G ⟨T, hT⟩ ∈ Kc
    let B : Graph n → Prop := fun G => polygonalDriftRestriction (M n) G ⟨T, hT⟩ ∈ Kd
    let C : Graph n → Prop := fun G => explorationRestriction G ⟨T, hT⟩ ∈ Kfinal
    have hbad : probM n (M n) (fun G => ¬ (A G ∧ B G)) ≤ ε := by
      have hu := probM_union_local (n := n) (M := M n) (fun G => ¬ A G) (fun G => ¬ B G)
      have hca := probM_complement_local hM A
      have hcb := probM_complement_local hM B
      have hform : (fun G : Graph n => ¬ (A G ∧ B G)) =
          (fun G => ¬ A G ∨ ¬ B G) := by
        funext G
        apply propext
        tauto
      rw [hform]
      rw [show probM n (M n) (fun G => ¬ A G) =
        1 - probM n (M n) A by linarith [hca]] at hu
      rw [show probM n (M n) (fun G => ¬ B G) =
        1 - probM n (M n) B by linarith [hcb]] at hu
      have hca' : 1 - ε / 2 ≤ probM n (M n) A := by simpa [A] using! hcn
      have hcb' : 1 - ε / 2 ≤ probM n (M n) B := by simpa [B] using! hdn
      linarith
    have hgood : 1 - ε ≤ probM n (M n) (fun G => A G ∧ B G) := by
      have hcpl := probM_complement_local hM (fun G => A G ∧ B G)
      linarith
    have hsubset : ∀ G : Graph n, A G ∧ B G → C G := by
      intro G hG
      have heq := explorationRestriction_eq_add (M := M n) G ⟨T, hT⟩ hg.1 hg.2
      change explorationRestriction G ⟨T, hT⟩ ∈ Kfinal
      rw [heq]
      apply Set.mem_union_left E
      exact Set.mem_image2.mpr ⟨_, hG.1, _, hG.2, rfl⟩
    exact hgood.trans (probM_mono_local _ _ hsubset)
  · have hnlt : n < N := by omega
    let C : Graph n → Prop := fun G => explorationRestriction G ⟨T, hT⟩ ∈ Kfinal
    have hsubset : ∀ G : Graph n, True → C G := by
      intro G _
      apply Set.mem_union_right K
      exact ⟨⟨⟨n, hnlt⟩, G⟩, rfl⟩
    have htrue : probM n (M n) (fun _ => True) = 1 := by
      have hcard : (0 : ℝ) < ((fixedGraphs n (M n)).card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr (fixedGraphs_nonempty hM)
      unfold probM
      simp only [Finset.filter_true]
      exact div_self (ne_of_gt hcard)
    have hprob := probM_mono_local (n := n) (M := M n)
      (fun _ => True) C hsubset
    linarith

/-- Compact-window tightness in the eventual form used by the next block. -/
theorem critical_explorationPathMeasure_window_compact_all
    (hfinite : FiniteEnumerationStatement) (M : NatSeq) (lam T ε : ℝ)
    (hcritical : criticalWindow M lam) (hT : 0 ≤ T) (hε : 0 < ε) :
    ∃ K : Set (C(Window ⟨T, hT⟩, ℝ)), IsCompact K ∧
      ∀ n (hM : M n ≤ capacity n),
        (explorationPathMeasure n (M n) hM
          {w | pathRestriction ⟨T, hT⟩ w ∈ K}).toReal ≥ 1 - ε := by
  obtain ⟨K, hK, hbound⟩ :=
    critical_explorationRestriction_compact_all hfinite M lam T ε
      hcritical hT hε
  refine ⟨K, hK, ?_⟩
  intro n hM
  rw [explorationPathMeasure_restriction_toReal n (M n) hM ⟨T, hT⟩ K hK]
  exact hbound n hM

end

end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_WindowTightness


/-!
# Finite-dimensional law of the actual interpolated BFS exploration

The centered mesh law is transferred on the same fixed-edge graph. The only
random discrepancy is one centered query increment per observation cell and
the polygonal predictable drift. Both use the original graph and edge count.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteDimensional

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Characteristic
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_QueueControl
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Reveal
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Horizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteAtoms
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteMaximal
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_VectorTightness
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_MeshWeak
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteLaw
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Interpolation
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Drift
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_CriticalBudget
open Filter MeasureTheory WithLp BoundedContinuousFunction
open scoped BigOperators Topology ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable
local instance graphMeasurableSpace (n : ℕ) : MeasurableSpace (Graph n) := ⊤
local instance : MeasurableSpace BrownianPath := borel BrownianPath
local instance : BorelSpace BrownianPath := ⟨rfl⟩
set_option maxHeartbeats 1000000

private theorem n23_tendsto_atTop : Tendsto n23 atTop atTop := by
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))

def actualEvaluationVector {d n : ℕ} (t : Fin d → NNReal) (G : Graph n) :
    EuclideanSpace ℝ (Fin d) :=
  toLp 2 (fun i => explorationInterpolation n G (t i))

def deterministicDriftVector {d : ℕ} (lam : ℝ) (t : Fin d → NNReal) :
    EuclideanSpace ℝ (Fin d) :=
  toLp 2 (fun i => driftCurve lam (t i))

def driftedEvaluationVector {d : ℕ} (lam : ℝ) (t : Fin d → NNReal)
    (w : BrownianPath) : EuclideanSpace ℝ (Fin d) :=
  toLp 2 (fun i => driftPath w lam (t i))

def actualVectorLaw {d : ℕ} (M : NatSeq) (t : Fin d → NNReal) (n : ℕ) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) :=
  ⟨Measure.map (actualEvaluationVector t)
      (fixedMeasure n (admissibleEdges M n) (admissibleEdges_le M n)),
    Measure.isProbabilityMeasure_map
      (measurable_from_fixed_graphs (actualEvaluationVector t)).aemeasurable⟩

private def centeredCellVector {d n : ℕ} (M : ℕ) (t : Fin d → NNReal)
    (G : Graph n) : EuclideanSpace ℝ (Fin d) :=
  toLp 2 (fun i =>
    let x := (t i : ℝ) * n23 n
    let j := ⌊x⌋₊
    (x - (j : ℝ)) *
      (centeredPartial M G (j + 1) - centeredPartial M G j) / n13 n)

private def driftErrorVector {d n : ℕ} (M : ℕ) (lam : ℝ)
    (t : Fin d → NNReal) (G : Graph n) : EuclideanSpace ℝ (Fin d) :=
  toLp 2 (fun i => polygonalDrift M G (t i) - driftCurve lam (t i))

private theorem actual_vector_decomposition {d n M : ℕ}
    (t : Fin d → NNReal) (G : Graph n)
    (hguard : ∀ i : Fin d, meshIndex n (t i : ℝ) + 1 ≤ n) (lam : ℝ) :
    actualEvaluationVector t G = centeredMeshVector M n t G +
      deterministicDriftVector lam t + centeredCellVector M t G +
      driftErrorVector M lam t G := by
  ext i
  let x : ℝ := (t i : ℝ) * n23 n
  let j : ℕ := ⌊x⌋₊
  let θ : ℝ := x - (j : ℝ)
  have hj1 : j + 1 ≤ n := by simpa [j, x, meshIndex] using! hguard i
  have hj : j ≤ n := by omega
  have hwj := walk_centered_predictable (M := M) G j hj
  have hwj1 := walk_centered_predictable (M := M) G (j + 1) hj1
  simp only [actualEvaluationVector, centeredMeshVector_apply,
    deterministicDriftVector, centeredCellVector, driftErrorVector,
    PiLp.add_apply, PiLp.toLp_apply]
  change rawExploration G (t i) = _
  change ((1 - ((t i : ℝ) * n23 n -
      (⌊(t i : ℝ) * n23 n⌋₊ : ℝ))) * ((explore G ⌊(t i : ℝ) * n23 n⌋₊).walk : ℝ) +
      ((t i : ℝ) * n23 n - (⌊(t i : ℝ) * n23 n⌋₊ : ℝ)) *
        ((explore G (⌊(t i : ℝ) * n23 n⌋₊ + 1)).walk : ℝ)) / n13 n = _
  rw [hwj, hwj1]
  dsimp [polygonalDrift, meshIndex]
  ring

/-! The one-step conditional square estimate is summed over its history atoms. -/
private theorem centered_step_square_sum_le {n M J : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (hbudget : HorizonBudget n M J 8) (j : ℕ) (hj : j < J) :
    (∑ G ∈ fixedGraphs n M,
      (centeredPartial M G (j + 1) - centeredPartial M G j) ^ 2) ≤
      4 * ((fixedGraphs n M).card : ℝ) := by
  let s := fixedGraphs n M
  let h : Graph n → _ := fun G => revealTrace G j
  let D : Graph n → ℝ := fun G =>
    centeredPartial M G (j + 1) - centeredPartial M G j
  have hmaps : ∀ G ∈ s, h G ∈ s.image h := by
    intro G hG
    exact Finset.mem_image.mpr ⟨G, hG, rfl⟩
  have hfiber : ∀ G ∈ s,
      (∑ H ∈ s with h H = h G, D H ^ 2) ≤
        4 * (((s.filter (fun H => h H = h G)).card : ℝ)) := by
    intro G hG
    have hGc : G.card = M := (Finset.mem_filter.mp hG).2
    simpa only [s, h, D, historyAtom, increment] using!
      centered_atom_square hfinite hM G j hGc hbudget hj
  have hsum :
      (∑ v ∈ s.image h, ∑ H ∈ s with h H = v, D H ^ 2) ≤
      ∑ v ∈ s.image h, 4 * (((s.filter (fun H => h H = v)).card : ℝ)) := by
    apply Finset.sum_le_sum
    intro v hv
    obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hv
    exact hfiber G hG
  have hcard : (∑ v ∈ s.image h,
      (s.filter (fun H => h H = v)).card) = s.card := by
    calc
      _ = ∑ v ∈ s.image h, ∑ H ∈ s with h H = v, (1 : ℕ) := by simp
      _ = ∑ H ∈ s, (1 : ℕ) := Finset.sum_fiberwise_of_maps_to hmaps _
      _ = s.card := by simp
  calc
    (∑ G ∈ fixedGraphs n M,
      (centeredPartial M G (j + 1) - centeredPartial M G j) ^ 2) =
        ∑ G ∈ s, D G ^ 2 := rfl
    _ = ∑ v ∈ s.image h, ∑ H ∈ s with h H = v, D H ^ 2 :=
      (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ v ∈ s.image h, 4 * (((s.filter (fun H => h H = v)).card : ℝ)) := hsum
    _ = 4 * ((fixedGraphs n M).card : ℝ) := by
      rw [← Finset.mul_sum]
      norm_cast
      rw [hcard]

private theorem centered_cell_square_sum_le {d n M J : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (hbudget : HorizonBudget n M J 8) (hn : 0 < n)
    (t : Fin d → NNReal)
    (ht : ∀ i, meshIndex n (t i : ℝ) < J) :
    (∑ G ∈ fixedGraphs n M, ‖centeredCellVector M t G‖ ^ 2) ≤
      (4 * (d : ℝ) / n13 n ^ 2) * ((fixedGraphs n M).card : ℝ) := by
  have hb : 0 < n13 n := by
    unfold n13
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hθ (i : Fin d) :
      0 ≤ (t i : ℝ) * n23 n - (meshIndex n (t i : ℝ) : ℝ) ∧
      (t i : ℝ) * n23 n - (meshIndex n (t i : ℝ) : ℝ) ≤ 1 := by
    have hx : 0 ≤ (t i : ℝ) * n23 n :=
      mul_nonneg (t i).property (n23_pos n hn).le
    have hfloor := Nat.floor_le hx
    have hfloor' := Nat.lt_floor_add_one ((t i : ℝ) * n23 n)
    dsimp [meshIndex]
    constructor <;> linarith
  have hcoord (i : Fin d) :
      (∑ G ∈ fixedGraphs n M,
        (centeredCellVector M t G i) ^ 2) ≤
      (4 / n13 n ^ 2) * ((fixedGraphs n M).card : ℝ) := by
    let j := meshIndex n (t i : ℝ)
    have hs := centered_step_square_sum_le hfinite hM hbudget j (ht i)
    have hpoint : ∀ G ∈ fixedGraphs n M,
        (centeredCellVector M t G i) ^ 2 ≤
          (centeredPartial M G (j + 1) - centeredPartial M G j) ^ 2 /
            n13 n ^ 2 := by
      intro G hG
      have hθ0 := (hθ i).1
      have hθ1 := (hθ i).2
      change (((t i : ℝ) * n23 n - (j : ℝ)) *
        (centeredPartial M G (j + 1) - centeredPartial M G j) / n13 n) ^ 2 ≤ _
      have hθsq : ((t i : ℝ) * n23 n - (j : ℝ)) ^ 2 ≤ 1 := by nlinarith
      have hsq := sq_nonneg (centeredPartial M G (j + 1) - centeredPartial M G j)
      have hmul := mul_le_mul_of_nonneg_right hθsq hsq
      have hnum : (((t i : ℝ) * n23 n - (j : ℝ)) *
          (centeredPartial M G (j + 1) - centeredPartial M G j)) ^ 2 ≤
          (centeredPartial M G (j + 1) - centeredPartial M G j) ^ 2 := by
        nlinarith
      convert div_le_div_of_nonneg_right hnum (sq_nonneg (n13 n)) using 1; ring
    have hsum := Finset.sum_le_sum hpoint
    calc
      _ ≤ ∑ G ∈ fixedGraphs n M,
        (centeredPartial M G (j + 1) - centeredPartial M G j) ^ 2 /
          n13 n ^ 2 := hsum
      _ = (∑ G ∈ fixedGraphs n M,
        (centeredPartial M G (j + 1) - centeredPartial M G j) ^ 2) /
          n13 n ^ 2 := by rw [Finset.sum_div]
      _ ≤ (4 * ((fixedGraphs n M).card : ℝ)) / n13 n ^ 2 :=
        div_le_div_of_nonneg_right hs (sq_nonneg _)
      _ = _ := by ring
  have hnorm (G : Graph n) :
      ‖centeredCellVector M t G‖ ^ 2 =
        ∑ i : Fin d, (centeredCellVector M t G i) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.norm_eq_abs, sq_abs]
  simp_rw [hnorm]
  rw [Finset.sum_comm]
  calc
    (∑ i : Fin d, ∑ G ∈ fixedGraphs n M,
      (centeredCellVector M t G i) ^ 2) ≤
      ∑ _i : Fin d, (4 / n13 n ^ 2) *
        ((fixedGraphs n M).card : ℝ) :=
      Finset.sum_le_sum (fun i hi => hcoord i)
    _ = _ := by simp; ring

private theorem centered_cell_probability {d : ℕ}
    (hfinite : FiniteEnumerationStatement) (M : NatSeq) (lam T δ : ℝ)
    (hcritical : criticalWindow M lam) (hT : 0 ≤ T) (hδ : 0 < δ)
    (t : Fin d → NNReal) (ht : ∀ i, (t i : ℝ) ≤ T) :
    Tendsto (fun n => probM n (M n) (fun G =>
      δ ≤ ‖centeredCellVector (M n) t G‖)) atTop (𝓝 0) := by
  let H : ℝ := T + 1
  have hH : 0 ≤ H := by dsimp [H]; linarith
  have hb : Tendsto (fun n : ℕ => (n13 n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp n13_tendsto_atTop
  have hbound : ∀ᶠ n : ℕ in atTop,
      probM n (M n) (fun G => δ ≤ ‖centeredCellVector (M n) t G‖) ≤
        (4 * (d : ℝ) / δ ^ 2) * ((n13 n)⁻¹) ^ 2 := by
    filter_upwards [hcritical.1,
      eventually_horizonBudget M lam H hcritical hH,
      n23_tendsto_atTop.eventually_ge_atTop (1 : ℝ),
      eventually_ge_atTop (1 : ℕ)] with n hM hbudget ha hn
    let J := meshIndex n H
    have hj (i : Fin d) : meshIndex n (t i : ℝ) < J := by
      have hguard := (horizon_endpoint_guard n T (t i) hT (ht i) ha).2
      simpa only [meshIndex, H, J] using! Nat.lt_of_succ_le hguard
    have hs := centered_cell_square_sum_le hfinite hM hbudget hn t hj
    have hcard : (0 : ℝ) < ((fixedGraphs n (M n)).card : ℝ) := by
      exact_mod_cast (Finset.card_pos.mpr (fixedGraphs_nonempty hM))
    have hpoint : δ ^ 2 *
        (((fixedGraphs n (M n)).filter
          (fun G => δ ≤ ‖centeredCellVector (M n) t G‖)).card : ℝ) ≤
        ∑ G ∈ fixedGraphs n (M n), ‖centeredCellVector (M n) t G‖ ^ 2 := by
      have hle : ∀ G ∈ fixedGraphs n (M n),
          δ ^ 2 * (if δ ≤ ‖centeredCellVector (M n) t G‖ then
            (1 : ℝ) else 0) ≤ ‖centeredCellVector (M n) t G‖ ^ 2 := by
        intro G hG
        split_ifs with hbad
        · simpa using! (sq_le_sq₀ hδ.le (norm_nonneg _)).mpr hbad
        · simp only [mul_zero]
          positivity
      have hh := Finset.sum_le_sum hle
      simpa only [← Finset.mul_sum, ← Finset.sum_filter, Finset.sum_const,
        nsmul_eq_mul, mul_one] using! hh
    have hp : probM n (M n) (fun G => δ ≤ ‖centeredCellVector (M n) t G‖) ≤
        4 * (d : ℝ) / (δ ^ 2 * n13 n ^ 2) := by
      unfold probM
      have hnum : δ ^ 2 * (((fixedGraphs n (M n)).filter
          (fun G => δ ≤ ‖centeredCellVector (M n) t G‖)).card : ℝ) ≤
          (4 * (d : ℝ) / n13 n ^ 2) * ((fixedGraphs n (M n)).card : ℝ) :=
        hpoint.trans hs
      apply (div_le_iff₀ hcard).mpr
      have hbpos : 0 < n13 n := by
        unfold n13
        exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
      have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
      have htarget :
          4 * (d : ℝ) / n13 n ^ 2 *
            ((fixedGraphs n (M n)).card : ℝ) / δ ^ 2 =
          4 * (d : ℝ) / (δ ^ 2 * n13 n ^ 2) *
            ((fixedGraphs n (M n)).card : ℝ) := by ring
      rw [← htarget]
      exact (le_div_iff₀ hδsq).mpr (by simpa only [mul_comm] using! hnum)
    have heq : 4 * (d : ℝ) / (δ ^ 2 * n13 n ^ 2) =
        (4 * (d : ℝ) / δ ^ 2) * ((n13 n)⁻¹) ^ 2 := by ring
    exact hp.trans_eq heq
  have hright : Tendsto (fun n : ℕ =>
      (4 * (d : ℝ) / δ ^ 2) * ((n13 n)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using! (hb.pow 2).const_mul (4 * (d : ℝ) / δ ^ 2)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hright
  · exact Filter.Eventually.of_forall (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · exact hbound

private theorem drift_error_le_sup {n M : ℕ} (G : Graph n)
    (lam T : ℝ) (hT : 0 ≤ T) (t : NNReal) (ht : (t : ℝ) ≤ T)
    (ha : 1 ≤ n23 n) :
    |polygonalDrift M G t - driftCurve lam t| ≤
      polygonalDriftErrorSup M lam T G := by
  unfold polygonalDriftErrorSup
  apply le_csSup
  · let J := meshIndex n (T + 1)
    have hbound : ∀ z ∈ {z : ℝ | ∃ u : NNReal, (u : ℝ) ≤ T ∧
        z = |polygonalDrift M G u - driftCurve lam u|},
        z ≤ gridDriftErrorMax M lam G J + 1 / (2 * n23 n ^ 2) := by
      intro z hz
      obtain ⟨u, hu, rfl⟩ := hz
      have hcell := (horizon_endpoint_guard n T u hT hu ha).2
      exact polygonalDrift_error_le_grid G lam u (by
        have : 0 < n23 n := by linarith
        by_contra hn
        have hz : n = 0 := by omega
        subst n
        norm_num [n23] at ha) (by simpa only [J, meshIndex] using! hcell)
    exact ⟨_, hbound⟩
  · exact ⟨t, ht, rfl⟩

private theorem drift_error_sup_nonneg {n M : ℕ} (G : Graph n)
    (lam T : ℝ) (hT : 0 ≤ T) (ha : 1 ≤ n23 n) :
    0 ≤ polygonalDriftErrorSup M lam T G := by
  have h := drift_error_le_sup (M := M) G lam T hT 0 (by simpa using! hT) ha
  exact (abs_nonneg _).trans h

private theorem drift_error_vector_norm_le {d n M : ℕ}
    (G : Graph n) (lam T : ℝ) (hT : 0 ≤ T)
    (t : Fin d → NNReal) (ht : ∀ i, (t i : ℝ) ≤ T)
    (ha : 1 ≤ n23 n) :
    ‖driftErrorVector M lam t G‖ ≤
      ((d : ℝ) + 1) * polygonalDriftErrorSup M lam T G := by
  let s := polygonalDriftErrorSup M lam T G
  have hs : 0 ≤ s := drift_error_sup_nonneg G lam T hT ha
  have hcoord (i : Fin d) :
      ‖driftErrorVector M lam t G i‖ ≤ s := by
    simpa [driftErrorVector, Real.norm_eq_abs] using!
      drift_error_le_sup G lam T hT (t i) (ht i) ha
  have hsq : ‖driftErrorVector M lam t G‖ ^ 2 ≤ (d : ℝ) * s ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin d, s ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact (sq_le_sq₀ (norm_nonneg _) hs).mpr (hcoord i)
      _ = _ := by simp
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hcross : (d : ℝ) * s ^ 2 ≤ ((d : ℝ) + 1) ^ 2 * s ^ 2 := by
    nlinarith [sq_nonneg ((d : ℝ) * s), sq_nonneg s]
  have hright : 0 ≤ ((d : ℝ) + 1) * s := mul_nonneg (by linarith) hs
  have hsq' := hsq.trans hcross
  apply (sq_le_sq₀ (norm_nonneg _) hright).mp
  convert hsq' using 1; ring

private theorem three_add_sub {α : Type*} [AddCommGroup α]
    (a b c : α) : a + b + c - a = b + c := by
  abel

private theorem actual_vector_distance_of_guard {d n M : ℕ}
    (lam T : ℝ) (hT : 0 ≤ T)
    (t : Fin d → NNReal) (ht : ∀ i, (t i : ℝ) ≤ T)
    (ha : 1 ≤ n23 n) (G : Graph n)
    (hguard : ∀ i : Fin d, meshIndex n (t i : ℝ) + 1 ≤ n) :
    ‖actualEvaluationVector t G -
      (centeredMeshVector M n t G + deterministicDriftVector lam t)‖ ≤
      ‖centeredCellVector M t G‖ +
        ((d : ℝ) + 1) * polygonalDriftErrorSup M lam T G := by
  let B : EuclideanSpace ℝ (Fin d) :=
    centeredMeshVector M n t G + deterministicDriftVector lam t
  let C : EuclideanSpace ℝ (Fin d) := centeredCellVector M t G
  let D : EuclideanSpace ℝ (Fin d) := driftErrorVector M lam t G
  have hid : actualEvaluationVector t G = B + C + D := by
    exact actual_vector_decomposition (M := M) t G hguard lam
  have hsub : actualEvaluationVector t G - B = C + D :=
    (congrArg (fun v => v - B) hid).trans (three_add_sub B C D)
  have hnorm : ‖actualEvaluationVector t G - B‖ = ‖C + D‖ :=
    congrArg norm hsub
  have htri : ‖C + D‖ ≤ ‖C‖ + ‖D‖ := norm_add_le C D
  have hD : ‖D‖ ≤
      ((d : ℝ) + 1) * polygonalDriftErrorSup M lam T G :=
    drift_error_vector_norm_le (M := M) G lam T hT t ht ha
  have hlast : ‖C‖ + ‖D‖ ≤ ‖C‖ +
      ((d : ℝ) + 1) * polygonalDriftErrorSup M lam T G :=
    by simpa only [add_comm] using! add_le_add_left hD ‖C‖
  exact hnorm.le.trans (htri.trans hlast)

private theorem eventual_actual_vector_distance {d : ℕ}
    (M : NatSeq) (lam T : ℝ) (hT : 0 ≤ T)
    (t : Fin d → NNReal) (ht : ∀ i, (t i : ℝ) ≤ T) :
    ∀ᶠ n : ℕ in atTop, ∀ G : Graph n,
      ‖actualEvaluationVector t G -
        (centeredMeshVector (M n) n t G + deterministicDriftVector lam t)‖ ≤
        ‖centeredCellVector (M n) t G‖ +
          ((d : ℝ) + 1) * polygonalDriftErrorSup (M n) lam T G := by
  let H : ℝ := T + 1
  have hH : 0 ≤ H := by dsimp [H]; linarith
  filter_upwards [n23_tendsto_atTop.eventually_ge_atTop (1 : ℝ),
    eventually_eighth_horizon H hH,
    eventually_ge_atTop (8 : ℕ)] with n ha hJ hn G
  let J := meshIndex n H
  have hJn : J + 1 ≤ n := by
    have h8 : 8 * J ≤ n := by simpa only [J, meshIndex, H] using! hJ
    omega
  have hguard (i : Fin d) : meshIndex n (t i : ℝ) + 1 ≤ n := by
    have hh := (horizon_endpoint_guard n T (t i) hT (ht i) ha).2
    have hh' : meshIndex n (t i : ℝ) + 1 ≤ J := by
      simpa only [J, H, meshIndex] using! hh
    omega
  exact actual_vector_distance_of_guard lam T hT t ht ha G hguard

private theorem probM_mono {n M : ℕ} (P Q : Graph n → Prop)
    (h : ∀ G, P G → Q G) : probM n M P ≤ probM n M Q := by
  unfold probM
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (by
    intro G hG
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hG).1, h G (Finset.mem_filter.mp hG).2⟩)

private theorem probM_or_le {n M : ℕ} (P Q : Graph n → Prop) :
    probM n M (fun G => P G ∨ Q G) ≤ probM n M P + probM n M Q := by
  have hc := Finset.card_union_le
    ((fixedGraphs n M).filter P) ((fixedGraphs n M).filter Q)
  have hcr : (((fixedGraphs n M).filter P ∪
      (fixedGraphs n M).filter Q).card : ℝ) ≤
      (((fixedGraphs n M).filter P).card : ℝ) +
        (((fixedGraphs n M).filter Q).card : ℝ) := by exact_mod_cast hc
  unfold probM
  rw [← add_div]
  have hbound := div_le_div_of_nonneg_right hcr
    (Nat.cast_nonneg ((fixedGraphs n M).card))
  convert hbound using 1
  congr 1
  congr 1
  congr 1
  ext G
  simp [and_or_left]

private theorem actual_vector_distance_probability {d : ℕ}
    (hfinite : FiniteEnumerationStatement) (M : NatSeq) (lam T δ : ℝ)
    (hcritical : criticalWindow M lam) (hT : 0 ≤ T) (hδ : 0 < δ)
    (t : Fin d → NNReal) (ht : ∀ i, (t i : ℝ) ≤ T) :
    Tendsto (fun n => probM n (M n) (fun G =>
      δ ≤ ‖actualEvaluationVector t G -
        (centeredMeshVector (M n) n t G + deterministicDriftVector lam t)‖))
      atTop (𝓝 0) := by
  let η : ℝ := δ / (2 * ((d : ℝ) + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  have hhalf : 0 < δ / 2 := by linarith
  have hc := centered_cell_probability hfinite M lam T (δ / 2)
    hcritical hT hhalf t ht
  have hd := critical_polygonal_drift_concentration hfinite M lam T η
    hcritical hT hη
  have hupper : ∀ᶠ n : ℕ in atTop,
      probM n (M n) (fun G => δ ≤ ‖actualEvaluationVector t G -
        (centeredMeshVector (M n) n t G + deterministicDriftVector lam t)‖) ≤
      probM n (M n) (fun G => δ / 2 ≤ ‖centeredCellVector (M n) t G‖) +
      probM n (M n) (fun G => η ≤ polygonalDriftErrorSup (M n) lam T G) := by
    filter_upwards [eventual_actual_vector_distance M lam T hT t ht] with n hdist
    have hcontain : ∀ G : Graph n,
        δ ≤ ‖actualEvaluationVector t G -
          (centeredMeshVector (M n) n t G + deterministicDriftVector lam t)‖ →
        δ / 2 ≤ ‖centeredCellVector (M n) t G‖ ∨
        η ≤ polygonalDriftErrorSup (M n) lam T G := by
      intro G hbad
      by_contra h
      push_neg at h
      have hh := hdist G
      dsimp [η] at h
      have hdpos : (0 : ℝ) < (d : ℝ) + 1 := by positivity
      have hprod : ((d : ℝ) + 1) * polygonalDriftErrorSup (M n) lam T G <
          ((d : ℝ) + 1) * η := by
        have hh := mul_pos hdpos (sub_pos.mpr h.2)
        nlinarith
      have heq : ((d : ℝ) + 1) * η = δ / 2 := by
        dsimp [η]
        field_simp
      rw [heq] at hprod
      linarith
    exact (probM_mono _ _ hcontain).trans (probM_or_le _ _)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (by simpa using! hc.add hd)
  · exact Filter.Eventually.of_forall (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · exact hupper

private theorem actualVectorLaw_integral {d : ℕ} (M : NatSeq)
    (t : Fin d → NNReal) (n : ℕ)
    (F : EuclideanSpace ℝ (Fin d) → ℝ) (hF : Continuous F) :
    ∫ x, F x ∂(actualVectorLaw M t n : Measure _) =
      expectM n (admissibleEdges M n)
        (fun G => F (actualEvaluationVector t G)) := by
  change ∫ x, F x ∂Measure.map (actualEvaluationVector t)
      (fixedMeasure n (admissibleEdges M n) (admissibleEdges_le M n)) = _
  rw [integral_map (measurable_from_fixed_graphs _).aemeasurable
    hF.aestronglyMeasurable]
  exact integral_fixedMeasure n _ (admissibleEdges_le M n) _

private theorem translated_centered_weak {d : ℕ}
    (hfinite : FiniteEnumerationStatement) (M : NatSeq) (lam T : ℝ)
    (hcritical : criticalWindow M lam) (hT : 0 ≤ T)
    (mu : PathLaw) (hmu : BrownianLaw mu)
    (t : Fin d → NNReal) (ht : ∀ i, (t i : ℝ) ≤ T) :
    Tendsto (fun n => (centeredVectorLaw M t n).map
      (fun x : EuclideanSpace ℝ (Fin d) => x + deterministicDriftVector lam t))
      atTop
      (𝓝 ((brownianEvaluationLaw mu hmu t).map
        (fun x : EuclideanSpace ℝ (Fin d) => x + deterministicDriftVector lam t))) := by
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
    (centeredVectorLaw_weak hfinite M lam T hcritical hT mu hmu t ht)
    (by fun_prop)

private theorem drifted_vector_eq (lam : ℝ) {d : ℕ}
    (t : Fin d → NNReal) (w : BrownianPath) :
    brownianEvaluationVector t w + deterministicDriftVector lam t =
      driftedEvaluationVector lam t w := by
  ext i
  simp [brownianEvaluationVector, deterministicDriftVector,
    driftedEvaluationVector, driftPath, drift, driftCurve]
  ring

/-- Every finite tuple, including zero and repeated times, has the actual
interpolated BFS finite-dimensional law of the supplied drifted Brownian path. -/
theorem actualVectorLaw_weak {d : ℕ}
    (hfinite : FiniteEnumerationStatement) (M : NatSeq) (lam T : ℝ)
    (hcritical : criticalWindow M lam) (hT : 0 ≤ T)
    (mu : PathLaw) (hmu : BrownianLaw mu)
    (t : Fin d → NNReal) (ht : ∀ i, (t i : ℝ) ≤ T) :
    Tendsto (actualVectorLaw M t) atTop
      (𝓝 ((brownianEvaluationLaw mu hmu t).map
        (fun x : EuclideanSpace ℝ (Fin d) => x + deterministicDriftVector lam t))) := by
  let ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin d)) :=
    (brownianEvaluationLaw mu hmu t).map
      (fun x : EuclideanSpace ℝ (Fin d) => x + deterministicDriftVector lam t)
  have hbase := translated_centered_weak hfinite M lam T hcritical hT
    mu hmu t ht
  apply (tendsto_iff_forall_lipschitz_integral_tendsto).2
  intro F hbounded hLip
  obtain ⟨C, hC⟩ := hbounded
  obtain ⟨L, hL⟩ := hLip
  have hF : Continuous F := hL.continuous
  let f : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ :=
    ⟨⟨F, hF⟩, ⟨C, hC⟩⟩
  have hbasetest := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto).1
    hbase f
  have hdiff : Tendsto (fun n =>
      (∫ x, F x ∂(actualVectorLaw M t n : Measure _)) -
      (∫ x, F x ∂((centeredVectorLaw M t n).map
        (fun x : EuclideanSpace ℝ (Fin d) => x + deterministicDriftVector lam t) : Measure _)))
      atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    let δ : ℝ := ε / (2 * ((L : ℝ) + 1))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hclose : Tendsto (fun n => probM n (M n) (fun G =>
        δ ≤ dist (actualEvaluationVector t G)
          (centeredMeshVector (M n) n t G + deterministicDriftVector lam t)))
        atTop (𝓝 0) := by
      simpa only [dist_eq_norm] using!
        actual_vector_distance_probability hfinite M lam T δ
          hcritical hT hδ t ht
    have hCpos : 0 ≤ C := by
      have hh := hC (0 : EuclideanSpace ℝ (Fin d)) 0
      simpa using! hh
    have hsmall := hclose.eventually_lt_const
      (by positivity : (0 : ℝ) < ε / (2 * (C + 1)))
    filter_upwards [hcritical.1, hsmall] with n hM hbad
    have hcard : (0 : ℝ) < ((fixedGraphs n (M n)).card : ℝ) := by
      exact_mod_cast (Finset.card_pos.mpr (fixedGraphs_nonempty hM))
    have hbaseint : (∫ x, F x ∂((centeredVectorLaw M t n).map
        (fun x : EuclideanSpace ℝ (Fin d) => x + deterministicDriftVector lam t) : Measure _)) =
        expectM n (M n) (fun G =>
          F (centeredMeshVector (M n) n t G + deterministicDriftVector lam t)) := by
      change ∫ x, F x ∂Measure.map
        (fun x : EuclideanSpace ℝ (Fin d) => x + deterministicDriftVector lam t)
        (centeredVectorLaw M t n : Measure _) = _
      rw [integral_map (by fun_prop : Continuous
        (fun x : EuclideanSpace ℝ (Fin d) => x + deterministicDriftVector lam t)).measurable.aemeasurable
        hF.aestronglyMeasurable]
      rw [centeredVectorLaw_integral M t n
        (fun x => F (x + deterministicDriftVector lam t)) (by fun_prop),
        admissibleEdges_eq_of_le M n hM]
    have hactualint : (∫ x, F x ∂(actualVectorLaw M t n : Measure _)) =
        expectM n (M n) (fun G => F (actualEvaluationVector t G)) := by
      rw [actualVectorLaw_integral M t n F hF,
        admissibleEdges_eq_of_le M n hM]
    rw [Real.dist_eq]
    simp only [sub_zero]
    rw [hactualint, hbaseint]
    let X : Graph n → EuclideanSpace ℝ (Fin d) :=
      fun G => centeredMeshVector (M n) n t G + deterministicDriftVector lam t
    let Y : Graph n → EuclideanSpace ℝ (Fin d) :=
      actualEvaluationVector t
    have hpoint : ∀ G ∈ fixedGraphs n (M n),
        |F (Y G) - F (X G)| ≤ (L : ℝ) * δ +
          C * (if δ ≤ dist (Y G) (X G) then (1 : ℝ) else 0) := by
      intro G hG
      by_cases hb : δ ≤ dist (Y G) (X G)
      · simp only [if_pos hb, mul_one]
        have hh := hC (Y G) (X G)
        have hL0 : (0 : ℝ) ≤ L := by positivity
        rw [Real.dist_eq] at hh
        have hnonneg : (0 : ℝ) ≤ (L : ℝ) * δ := by positivity
        linarith
      · simp only [if_neg hb, mul_zero, add_zero]
        have hh := hL.dist_le_mul (Y G) (X G)
        rw [Real.dist_eq] at hh
        have hL0 : (0 : ℝ) ≤ L := by positivity
        exact hh.trans (mul_le_mul_of_nonneg_left (le_of_not_ge hb) hL0)
    have hsum := Finset.sum_le_sum hpoint
    have hbound : |expectM n (M n) (fun G => F (Y G)) -
        expectM n (M n) (fun G => F (X G))| ≤
        (L : ℝ) * δ + C * probM n (M n) (fun G => δ ≤ dist (Y G) (X G)) := by
      unfold expectM probM
      rw [← sub_div, ← Finset.sum_sub_distrib,
        abs_div, abs_of_pos hcard]
      calc
        |(fixedGraphs n (M n)).sum
          (fun G => F (Y G) - F (X G))| /
            ((fixedGraphs n (M n)).card : ℝ) ≤
          ((fixedGraphs n (M n)).sum
            (fun G => |F (Y G) - F (X G)|)) /
            ((fixedGraphs n (M n)).card : ℝ) :=
          div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hcard.le
        _ ≤ ((fixedGraphs n (M n)).sum (fun G =>
          (L : ℝ) * δ + C * (if δ ≤ dist (Y G) (X G) then 1 else 0))) /
            ((fixedGraphs n (M n)).card : ℝ) :=
          div_le_div_of_nonneg_right hsum hcard.le
        _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          simp only [Finset.sum_const, nsmul_eq_mul]
          rw [← Finset.mul_sum]
          have hs : ((fixedGraphs n (M n)).sum (fun G =>
              if δ ≤ dist (Y G) (X G) then (1 : ℝ) else 0)) =
              (((fixedGraphs n (M n)).filter
                (fun G => δ ≤ dist (Y G) (X G))).card : ℝ) := by simp
          rw [hs]
          field_simp
    have hbad' : probM n (M n) (fun G => δ ≤ dist (Y G) (X G)) <
        ε / (2 * (C + 1)) := hbad
    have hε1 : (L : ℝ) * δ < ε / 2 := by
      have hx : (L : ℝ) / ((L : ℝ) + 1) < 1 := by
        apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (L : ℝ) + 1)).mpr
        linarith
      calc
        (L : ℝ) * δ = ((L : ℝ) / ((L : ℝ) + 1)) * (ε / 2) := by
          dsimp [δ]
          have hden : ((L : ℝ) + 1) ≠ 0 := by positivity
          field_simp
        _ < 1 * (ε / 2) := by
          have hh := mul_pos (sub_pos.mpr hx) (by linarith : 0 < ε / 2)
          nlinarith
        _ = ε / 2 := by ring
    have hε2 : C * probM n (M n)
        (fun G => δ ≤ dist (Y G) (X G)) < ε / 2 := by
      have hh := mul_le_mul_of_nonneg_left hbad'.le hCpos
      have hC1 : C / (C + 1) < 1 := by
        apply (div_lt_iff₀ (by linarith)).mpr
        linarith
      have hstrict : (C / (C + 1)) * (ε / 2) < ε / 2 := by
        have hh := mul_pos (sub_pos.mpr hC1) (by linarith : 0 < ε / 2)
        nlinarith
      have heq : C * (ε / (2 * (C + 1))) = (C / (C + 1)) * (ε / 2) := by
        have hden : C + 1 ≠ 0 := by linarith
        field_simp
      rw [heq] at hh
      linarith
    exact lt_of_le_of_lt hbound (by linarith)
  have hbase' : Tendsto (fun n => ∫ x, F x ∂
      (((centeredVectorLaw M t n).map
        (fun x : EuclideanSpace ℝ (Fin d) => x + deterministicDriftVector lam t)) : Measure _))
      atTop (𝓝 (∫ x, F x ∂(ν : Measure _))) := by
    simpa only [f, ν] using! hbasetest
  have htarget := hdiff.add hbase'
  simpa only [zero_add, sub_add_cancel] using! htarget

/-- The public B05T boundary uses the actual fixed-edge expectation and the
same Brownian witness, for every finite observation tuple. -/
theorem critical_actual_finite_dimensional {d : ℕ}
    (hfinite : FiniteEnumerationStatement) (M : NatSeq) (lam T : ℝ)
    (hcritical : criticalWindow M lam) (hT : 0 ≤ T)
    (mu : PathLaw) (hmu : BrownianLaw mu)
    (t : Fin d → NNReal) (ht : ∀ i, (t i : ℝ) ≤ T)
    (F : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) :
    Tendsto (fun n => expectM n (M n) (fun G =>
      F (actualEvaluationVector t G))) atTop
      (𝓝 (∫ w, F (driftedEvaluationVector lam t w) ∂mu)) := by
  have hweak := actualVectorLaw_weak hfinite M lam T hcritical hT
    mu hmu t ht
  have htest := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto).1
    hweak F
  have hactual : (fun n => ∫ x, F x ∂
      (actualVectorLaw M t n : Measure (EuclideanSpace ℝ (Fin d)))) =ᶠ[atTop]
      (fun n => expectM n (M n) (fun G =>
        F (actualEvaluationVector t G))) := by
    filter_upwards [hcritical.1] with n hM
    rw [actualVectorLaw_integral M t n F F.continuous,
      admissibleEdges_eq_of_le M n hM]
  have htarget : (∫ x, F x ∂
      (((brownianEvaluationLaw mu hmu t).map
        (fun x : EuclideanSpace ℝ (Fin d) => x + deterministicDriftVector lam t)) : Measure _)) =
      ∫ w, F (driftedEvaluationVector lam t w) ∂mu := by
    change ∫ x, F x ∂Measure.map
      (fun x : EuclideanSpace ℝ (Fin d) => x + deterministicDriftVector lam t)
      (brownianEvaluationLaw mu hmu t : Measure _) = _
    rw [integral_map (by fun_prop : Continuous
      (fun x : EuclideanSpace ℝ (Fin d) =>
        x + deterministicDriftVector lam t)).measurable.aemeasurable
        F.continuous.aestronglyMeasurable]
    change ∫ x, F (x + deterministicDriftVector lam t) ∂
      Measure.map (brownianEvaluationVector t) mu = _
    change ∫ x, (F ∘ (fun y : EuclideanSpace ℝ (Fin d) =>
      y + deterministicDriftVector lam t)) x ∂
      Measure.map (brownianEvaluationVector t) mu = _
    rw [integral_map (measurable_brownianEvaluationVector t).aemeasurable
      (F.continuous.comp (by fun_prop : Continuous
        (fun x : EuclideanSpace ℝ (Fin d) =>
          x + deterministicDriftVector lam t))).aestronglyMeasurable]
    congr 1
    funext w
    change F (brownianEvaluationVector t w + deterministicDriftVector lam t) =
      F (driftedEvaluationVector lam t w)
    rw [drifted_vector_eq]
  rw [htarget] at htest
  exact htest.congr' hactual

/-- B08's finite-grid input, with no auxiliary horizon in the public type.
The finite sum bounds every observation time, including the empty tuple. -/
theorem critical_actual_finite_dimensional_all_times {d : ℕ}
    (hfinite : FiniteEnumerationStatement) (M : NatSeq) (lam : ℝ)
    (hcritical : criticalWindow M lam)
    (mu : PathLaw) (hmu : BrownianLaw mu)
    (t : Fin d → NNReal)
    (F : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ) :
    Tendsto (fun n => expectM n (M n) (fun G =>
      F (toLp 2 (fun i => explorationInterpolation n G (t i))))) atTop
      (𝓝 (∫ w, F (toLp 2 (fun i => driftPath w lam (t i))) ∂mu)) := by
  let T : ℝ := ∑ i : Fin d, (t i : ℝ)
  have hT : 0 ≤ T := Finset.sum_nonneg (fun i hi => (t i).property)
  have ht (i : Fin d) : (t i : ℝ) ≤ T :=
    Finset.single_le_sum (fun j hj => (t j).property) (Finset.mem_univ i)
  simpa only [actualEvaluationVector, driftedEvaluationVector] using!
    critical_actual_finite_dimensional hfinite M lam T hcritical hT
      mu hmu t ht F

end

end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteDimensional


/-! Compact-open tightness and finite-grid transfer for the actual exploration law. -/
namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_PathWeak

open Filter Topology MeasureTheory Set NNReal Uniformity
open scoped BigOperators ENNReal
open WithLp
open Erdos745.WrapUp
open W14_EXPLORATION_Interpolation W14_EXPLORATION_FiniteLaw
open W14_EXPLORATION_FiniteDimensional W14_EXPLORATION_WindowTightness
open W14_EXPLORATION_DyadicCompact

noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
local instance : MeasurableSpace BrownianPath := borel BrownianPath
local instance : BorelSpace BrownianPath := ⟨rfl⟩
-- This metrization preserves the compact-convergence uniformity and topology.
local instance : MetricSpace BrownianPath := UniformSpace.metricSpace BrownianPath

private theorem compact_nnreal_interval (T : NNReal) : IsCompact (Icc 0 T) := by
  apply IsCompact.of_isClosed_subset (isCompact_closedBall (0 : NNReal) (T : ℝ)) isClosed_Icc
  intro x hx
  simpa [Metric.mem_closedBall, dist_nndist, NNReal.nndist_zero_eq_val'] using! hx.2

private instance windowCompact (T : NNReal) : CompactSpace (Window T) :=
  isCompact_iff_compactSpace.mp (compact_nnreal_interval T)

/-- Actual fixed-edge laws on admissible indices; a point mass only elsewhere. -/
def criticalPathLaw (M : NatSeq) (n : ℕ) : PathLaw :=
  if h : M n ≤ capacity n then explorationPathMeasure n (M n) h else Measure.dirac 0

instance criticalPathLaw_probability (M : NatSeq) (n : ℕ) :
    IsProbabilityMeasure (criticalPathLaw M n) := by
  unfold criticalPathLaw
  split <;> infer_instance

theorem continuous_driftPath (lam : ℝ) : Continuous (fun w => driftPath w lam) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : BrownianPath × NNReal =>
    p.1 p.2 + lam * (p.2 : ℝ) - (p.2 : ℝ) ^ 2 / 2)
  exact (continuous_eval.add (continuous_const.mul
    (NNReal.continuous_coe.comp continuous_snd))).sub
      (((NNReal.continuous_coe.comp continuous_snd).pow 2).div_const 2)

private theorem compact_times_bounded (S : Set NNReal) (hS : IsCompact S) :
    ∃ r : ℕ, S ⊆ Icc 0 (r : NNReal) := by
  obtain ⟨b, hb⟩ := hS.bddAbove
  obtain ⟨r, hr⟩ := exists_nat_gt (b : ℝ)
  refine ⟨r, fun x hx => ⟨zero_le, ?_⟩⟩
  exact (hb hx).trans (by exact_mod_cast hr.le)

private theorem compact_window_equicontinuous (T : NNReal)
    (K : Set (C(Window T, ℝ))) (hK : IsCompact K) :
    Equicontinuous (fun f : K => (f.1 : Window T → ℝ)) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let E : Window T → C(K, ℝ) := fun x =>
    ⟨fun f => f.1 x, (continuous_eval_const x).comp continuous_subtype_val⟩
  have hE : Continuous E := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact continuous_eval.comp
      ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)
  apply equicontinuous_iff_continuous.mpr
  exact ContinuousMap.isUniformEmbedding_uniformFunOfFun.uniformContinuous.continuous.comp hE

/-- Closed integer-window constraints define a compact family of full continuous paths. -/
theorem compact_of_window_constraints
    (K : (r : ℕ) → Set (C(Window (r : NNReal), ℝ)))
    (hK : ∀ r, IsCompact (K r)) :
    IsCompact {w : BrownianPath | ∀ r, pathRestriction (r : NNReal) w ∈ K r} := by
  let S : Set BrownianPath := {w | ∀ r, pathRestriction (r : NNReal) w ∈ K r}
  have hclosed : IsClosed S := by
    have hS : S = ⋂ r, {w | pathRestriction (r : NNReal) w ∈ K r} := by
      ext w
      simp [S]
    rw [hS]
    exact isClosed_iInter fun r => (hK r).isClosed.preimage (continuous_pathRestriction _)
  have heq : ∀ A : Set NNReal, IsCompact A →
      EquicontinuousOn (fun w : S => (w.1 : NNReal → ℝ)) A := by
    intro A hA
    obtain ⟨r, hr⟩ := compact_times_bounded A hA
    let R : S → K r := fun w => ⟨pathRestriction (r : NNReal) w.1, w.2 r⟩
    have he := (compact_window_equicontinuous _ _ (hK r)).comp R
    have he' : EquicontinuousOn (fun w : S => (w.1 : NNReal → ℝ))
        (Icc 0 (r : NNReal)) :=
      (equicontinuous_restrict_iff _).mp he
    exact he'.mono hr
  have hp : ∀ A : Set NNReal, IsCompact A → ∀ x ∈ A,
      ∃ Q : Set ℝ, IsCompact Q ∧ ∀ w ∈ S, w x ∈ Q := by
    intro A hA x hx
    obtain ⟨r, hr⟩ := compact_times_bounded A hA
    let t : Window (r : NNReal) := ⟨x, hr hx⟩
    refine ⟨(fun f : C(Window (r : NNReal), ℝ) => f t) '' K r,
      (hK r).image (continuous_eval_const t), ?_⟩
    intro w hw
    exact ⟨pathRestriction _ w, hw r, rfl⟩
  letI : T2Space (UniformOnFun NNReal ℝ {A : Set NNReal | IsCompact A}) :=
    UniformOnFun.t2Space_of_covering (by
      apply eq_univ_iff_forall.mpr
      intro x
      exact mem_sUnion_of_mem (mem_singleton x) isCompact_singleton)
  have hc : IsCompact (closure S) :=
    ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun w : BrownianPath => (w : NNReal → ℝ))
      (𝔖 := {A : Set NNReal | IsCompact A}) (fun _ h => h)
      ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
      heq hp
  simpa only [hclosed.closure_eq] using! hc

private theorem window_law_complement (M : NatSeq) (n : ℕ)
    (T : NNReal) (K : Set (C(Window T, ℝ))) (hK : IsCompact K)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hgood : (criticalPathLaw M n {w | pathRestriction T w ∈ K}).toReal ≥ 1 - ε) :
    criticalPathLaw M n {w | pathRestriction T w ∉ K} ≤ ENNReal.ofReal ε := by
  have hm : MeasurableSet {w : BrownianPath | pathRestriction T w ∈ K} :=
    (hK.isClosed.preimage (continuous_pathRestriction T)).measurableSet
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hε).mpr
  change (criticalPathLaw M n).real {w | pathRestriction T w ∈ K}ᶜ ≤ ε
  rw [measureReal_compl (μ := criticalPathLaw M n) hm, probReal_univ]
  change 1 - (criticalPathLaw M n {w | pathRestriction T w ∈ K}).toReal ≤ ε
  linarith

/-- Summable window budgets give tightness of the all-index probability family. -/
theorem criticalPathLaw_tight (hfinite : FiniteEnumerationStatement)
    (M : NatSeq) (lam : ℝ) (hcritical : criticalWindow M lam)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : Set BrownianPath, IsCompact K ∧
      ∀ n, criticalPathLaw M n Kᶜ ≤ ENNReal.ofReal ε := by
  obtain ⟨δ, hδ, hsum⟩ := ENNReal.exists_pos_sum_of_countable
    (ENNReal.ofReal_pos.mpr hε).ne' ℕ
  have hwindow : ∀ r : ℕ, ∃ K : Set (C(Window (r : NNReal), ℝ)),
      IsCompact K ∧ (0 : C(Window (r : NNReal), ℝ)) ∈ K ∧
      ∀ n, criticalPathLaw M n {w | pathRestriction (r : NNReal) w ∉ K} ≤ δ r := by
    intro r
    obtain ⟨K, hK, hb⟩ := critical_explorationPathMeasure_window_compact_all
      hfinite M lam (r : ℝ) (δ r : ℝ) hcritical (Nat.cast_nonneg _)
      (by exact_mod_cast hδ r)
    let L : Set (C(Window (r : NNReal), ℝ)) := K ∪ {0}
    have hL : IsCompact L := hK.union isCompact_singleton
    refine ⟨L, hL, Or.inr rfl, fun n => ?_⟩
    rw [← ENNReal.ofReal_coe_nnreal]
    apply window_law_complement M n _ L hL (δ r) (δ r).property
    unfold criticalPathLaw
    split
    · rename_i hM
      have hm : MeasurableSet {w : BrownianPath | pathRestriction (r : NNReal) w ∈ K} :=
        (hK.isClosed.preimage (continuous_pathRestriction _)).measurableSet
      have hmono : (explorationPathMeasure n (M n) hM
          {w | pathRestriction (r : NNReal) w ∈ K}).toReal ≤
          (explorationPathMeasure n (M n) hM
          {w | pathRestriction (r : NNReal) w ∈ L}).toReal := by
        apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
        exact measure_mono (fun _ hw => Or.inl hw)
      exact (hb n hM).trans hmono
    · have hz : pathRestriction (r : NNReal) (0 : BrownianPath) = 0 := by
        ext x
        rfl
      rw [Measure.dirac_apply_of_mem (show (0 : BrownianPath) ∈
        {w | pathRestriction (r : NNReal) w ∈ L} from Or.inr hz)]
      simp only [ENNReal.toReal_one]
      linarith [(δ r).property]
  choose K hK hzero hb using hwindow
  let S : Set BrownianPath := {w | ∀ r, pathRestriction (r : NNReal) w ∈ K r}
  refine ⟨S, compact_of_window_constraints K hK, fun n => ?_⟩
  have hcompl : Sᶜ = ⋃ r, {w | pathRestriction (r : NNReal) w ∉ K r} := by
    ext w
    simp [S]
  rw [hcompl]
  exact (measure_iUnion_le _).trans ((ENNReal.tsum_le_tsum (hb · n)).trans hsum.le)

/-- A common compact family for the finite laws and the same supplied drifted Brownian law. -/
theorem critical_common_path_compact (hfinite : FiniteEnumerationStatement)
    (M : NatSeq) (lam : ℝ) (hcritical : criticalWindow M lam)
    (mu : PathLaw) (hmu : BrownianLaw mu) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : Set BrownianPath, IsCompact K ∧
      (∀ n, criticalPathLaw M n Kᶜ ≤ ENNReal.ofReal ε) ∧
      (Measure.map (fun w => driftPath w lam) mu) Kᶜ ≤ ENNReal.ofReal ε := by
  letI : IsProbabilityMeasure mu := hmu.1
  let ν : PathLaw := Measure.map (fun w => driftPath w lam) mu
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map
    (continuous_driftPath lam).measurable.aemeasurable
  obtain ⟨K, hK, hb⟩ := criticalPathLaw_tight hfinite M lam hcritical ε hε
  obtain ⟨L, hL, hLmass⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
      (isTightMeasureSet_singleton (μ := ν)) (ENNReal.ofReal ε)
      (ENNReal.ofReal_pos.mpr hε)
  refine ⟨K ∪ L, hK.union hL, fun n => ?_, ?_⟩
  · exact (measure_mono (compl_subset_compl.mpr subset_union_left)).trans (hb n)
  · exact (measure_mono (compl_subset_compl.mpr subset_union_right)).trans
      (hLmass ν (mem_singleton _))

/-! Finite-grid reconstruction. The interpolation is constant past its last grid point. -/
private def clampIndex (m j : ℕ) : Fin (m * m + 1) :=
  ⟨min j (m * m), by omega⟩

/-- The deterministic grid has spacing `1/m` and final time `m`. -/
def gridTime (m : ℕ) (i : Fin (m * m + 1)) : NNReal :=
  (i.val : NNReal) / (m : NNReal)

private def gridBasis (m : ℕ) (i : Fin (m * m + 1)) : BrownianPath :=
  let z : ℕ → ℝ := fun j => if clampIndex m j = i then 1 else 0
  ⟨fun t => linearInterpolation z (t * (m : NNReal)),
    (continuous_linearInterpolation_of_stationary z (m * m) (by
      intro j hj
      simp only [z, clampIndex, min_eq_right hj, min_self])).comp
        (continuous_id.mul continuous_const)⟩

/-- Continuous polygonal reconstruction of the finite Euclidean evaluation vector. -/
def gridReconstruction (m : ℕ)
    (v : EuclideanSpace ℝ (Fin (m * m + 1))) : BrownianPath :=
  ∑ i, (v i) • gridBasis m i

theorem continuous_gridReconstruction (m : ℕ) : Continuous (gridReconstruction m) := by
  apply continuous_finset_sum
  intro i _
  exact (PiLp.continuous_apply 2 (fun _ => ℝ) i).smul continuous_const

private theorem gridReconstruction_apply (m : ℕ)
    (v : EuclideanSpace ℝ (Fin (m * m + 1))) (t : NNReal) :
    gridReconstruction m v t =
      let x := (t : ℝ) * m
      let j := ⌊x⌋₊
      let θ := x - j
      (1 - θ) * v (clampIndex m j) + θ * v (clampIndex m (j + 1)) := by
  simp only [gridReconstruction, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    gridBasis, ContinuousMap.coe_mk, linearInterpolation, NNReal.coe_mul,
    NNReal.coe_natCast, smul_eq_mul]
  simp_rw [mul_add, mul_left_comm (a := _), Finset.sum_add_distrib,
    ← Finset.mul_sum, mul_ite, mul_one, mul_zero]
  simp

/-- The finite vector of path values used by polygonal reconstruction. -/
def gridEvaluation (m : ℕ) (w : BrownianPath) :
    EuclideanSpace ℝ (Fin (m * m + 1)) := toLp 2 (fun i => w (gridTime m i))

theorem continuous_gridEvaluation (m : ℕ) : Continuous (gridEvaluation m) :=
  (PiLp.continuous_toLp 2 (fun _ => ℝ)).comp
    (continuous_pi fun i => continuous_eval_const (gridTime m i))

private theorem compact_eval_modulus (K : Set BrownianPath) (hK : IsCompact K)
    (R : NNReal) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ w ∈ K, ∀ s ∈ Icc 0 R, ∀ t ∈ Icc 0 R,
      dist s t < δ → |w s - w t| < ε := by
  have hu : UniformContinuousOn (fun p : BrownianPath × NNReal => p.1 p.2)
      (K ×ˢ Icc 0 R) :=
    (hK.prod (compact_nnreal_interval R)).uniformContinuousOn_of_continuous continuous_eval.continuousOn
  obtain ⟨δ, hδ, hb⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨δ, hδ, fun w hw s hs t ht hst => ?_⟩
  have hh := hb (w, s) ⟨hw, hs⟩ (w, t) ⟨hw, ht⟩
    (by simpa using! hst)
  simpa only [Real.dist_eq] using! hh

private theorem grid_approx_window (K : Set BrownianPath) (hK : IsCompact K)
    (R : NNReal) (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ ∀ w ∈ K, ∀ t ∈ Icc 0 R,
      |w t - gridReconstruction m (gridEvaluation m w) t| < ε := by
  obtain ⟨δ, hδ, hb⟩ := compact_eval_modulus K hK (R + 1) ε hε
  obtain ⟨m, hm⟩ := exists_nat_gt (max ((R : ℝ) + 1) (max 1 (1 / δ)))
  have hmR : (R : ℝ) + 1 < m := (le_max_left _ _).trans_lt hm
  have hm1 : (1 : ℝ) < m := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hm
  have hmδ : 1 / δ < (m : ℝ) := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hm
  have hm0 : 0 < m := by exact_mod_cast (by linarith : (0 : ℝ) < m)
  have hmpos : (0 : ℝ) < m := by positivity
  have hinv : 1 / (m : ℝ) < δ := by
    apply (div_lt_iff₀ hmpos).mpr
    have hh := (div_lt_iff₀ hδ).mp hmδ
    nlinarith
  refine ⟨m, hm0, fun w hw t ht => ?_⟩
  let x : ℝ := (t : ℝ) * m
  let j : ℕ := ⌊x⌋₊
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hj0 : (j : ℝ) ≤ x := Nat.floor_le hx
  have hj1 : x < (j : ℝ) + 1 := Nat.lt_floor_add_one x
  have hjN : j + 1 ≤ m * m := by
    have hlt : x < (m * m : ℕ) := by
      dsimp [x]
      have htR : (t : ℝ) ≤ R := by exact_mod_cast ht.2
      push_cast
      nlinarith
    have hh : j < m * m := (Nat.floor_lt hx).mpr hlt
    omega
  let s : NNReal := (j : NNReal) / (m : NNReal)
  let u : NNReal := ((j + 1 : ℕ) : NNReal) / (m : NNReal)
  have hscoe : (s : ℝ) = (j : ℝ) / m := by simp [s]
  have hucoe : (u : ℝ) = ((j : ℝ) + 1) / m := by simp [u]
  have hsle : (s : ℝ) ≤ t := by rw [hscoe]; exact (div_le_iff₀ hmpos).mpr hj0
  have htule : (t : ℝ) < u := by rw [hucoe]; exact (lt_div_iff₀ hmpos).mpr hj1
  have hustep : (u : ℝ) - s = 1 / m := by rw [hucoe, hscoe]; ring
  have hsR : s ∈ Icc 0 (R + 1) := by
    refine ⟨zero_le, ?_⟩
    exact_mod_cast (hsle.trans (by exact_mod_cast (ht.2.trans (le_add_of_nonneg_right (zero_le)))))
  have huR : u ∈ Icc 0 (R + 1) := by
    refine ⟨zero_le, ?_⟩
    have htR : (t : ℝ) ≤ R := by exact_mod_cast ht.2
    have hi : 1 / (m : ℝ) ≤ 1 := (div_le_one hmpos).mpr hm1.le
    exact_mod_cast (by linarith : (u : ℝ) ≤ (R : ℝ) + 1)
  have htR : t ∈ Icc 0 (R + 1) := ⟨zero_le, ht.2.trans (le_add_of_nonneg_right (zero_le))⟩
  have hst : dist s t < δ := by
    rw [NNReal.dist_eq, abs_of_nonpos (by linarith)]
    linarith
  have hut : dist u t < δ := by
    rw [NNReal.dist_eq, abs_of_nonneg (by linarith)]
    linarith
  have hs := hb w hw s hsR t htR hst
  have hu := hb w hw u huR t htR hut
  let θ : ℝ := x - j
  have hθ : 0 ≤ θ ∧ θ ≤ 1 := ⟨by dsimp [θ]; linarith, by dsimp [θ]; linarith⟩
  have heq : gridReconstruction m (gridEvaluation m w) t =
      (1 - θ) * w s + θ * w u := by
    rw [gridReconstruction_apply]
    change (1 - θ) * w (gridTime m (clampIndex m j)) +
      θ * w (gridTime m (clampIndex m (j + 1))) = _
    simp only [gridTime, clampIndex, min_eq_left (by omega : j ≤ m * m), min_eq_left hjN]
    rfl
  rw [heq]
  have halg : w t - ((1 - θ) * w s + θ * w u) =
      (1 - θ) * (w t - w s) + θ * (w t - w u) := by ring
  rw [halg]
  calc
    _ ≤ |(1 - θ) * (w t - w s)| + |θ * (w t - w u)| := abs_add_le _ _
    _ = (1 - θ) * |w s - w t| + θ * |w u - w t| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - θ),
        abs_of_nonneg hθ.1, abs_sub_comm (w t) (w s), abs_sub_comm (w t) (w u)]
    _ < ε := by
      have h1 := mul_nonneg (by linarith : 0 ≤ 1 - θ) (by linarith : 0 ≤ ε - |w s - w t|)
      have h2 := mul_nonneg hθ.1 (by linarith : 0 ≤ ε - |w u - w t|)
      by_cases hz : θ = 0
      · simp [hz]; exact hs
      · have hp := mul_pos (lt_of_le_of_ne hθ.1 (Ne.symm hz)) (sub_pos.mpr hu)
        nlinarith

/-- Every compact path family admits a continuous finite-grid approximation for a path test. -/
theorem compact_finite_grid_test_approximation (K : Set BrownianPath) (hK : IsCompact K)
    (F : BoundedContinuousFunction BrownianPath ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ ∀ w ∈ K,
      |F w - F (gridReconstruction m (gridEvaluation m w))| < ε := by
  have hU := hK.uniformContinuousAt_of_continuousAt F
    (fun _ _ => F.continuous.continuousAt) (Metric.dist_mem_uniformity hε)
  obtain ⟨A, V, hA, hV, hAV⟩ :=
    (ContinuousMap.mem_compactConvergence_entourage_iff _).mp hU
  obtain ⟨η, hη, hηV⟩ := Metric.mem_uniformity_dist.mp hV
  obtain ⟨r, hr⟩ := compact_times_bounded A hA
  obtain ⟨m, hm, hb⟩ := grid_approx_window K hK (r : NNReal) η hη
  refine ⟨m, hm, fun w hw => ?_⟩
  have hh := hAV (a := (w, gridReconstruction m (gridEvaluation m w))) (show ∀ x ∈ A,
      (w x, gridReconstruction m (gridEvaluation m w) x) ∈ V from
    fun x hx => hηV (by simpa only [Real.dist_eq] using! hb w hw x (hr hx)))
  simpa only [Real.dist_eq] using! hh hw

private theorem integral_test_error (ν : PathLaw) [IsProbabilityMeasure ν]
    (K : Set BrownianPath) (hK : IsCompact K)
    (F H : BoundedContinuousFunction BrownianPath ℝ)
    (C δ ε : ℝ) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hF : ∀ w, |F w| ≤ C) (hH : ∀ w, |H w| ≤ C)
    (hgood : ∀ w ∈ K, |F w - H w| ≤ δ)
    (hmass : ν Kᶜ ≤ ENNReal.ofReal ε) (hε : 0 ≤ ε) :
    |(∫ w, F w ∂ν) - ∫ w, H w ∂ν| ≤ δ + 2 * C * ε := by
  let D := F - H
  have hint : Integrable (fun w => F w - H w) ν := (F.integrable ν).sub (H.integrable ν)
  rw [← integral_sub (F.integrable ν) (H.integrable ν),
    ← integral_add_compl (μ := ν) hK.isClosed.measurableSet hint]
  have h1 : |∫ w in K, F w - H w ∂ν| ≤ δ := by
    have hh := norm_setIntegral_le_of_norm_le_const (measure_lt_top ν K)
      (fun w hw => (show ‖F w - H w‖ ≤ δ from by simpa only [Real.norm_eq_abs] using! hgood w hw))
    exact hh.trans (mul_le_of_le_one_right hδ measureReal_le_one)
  have h2 : |∫ w in Kᶜ, F w - H w ∂ν| ≤ 2 * C * ε := by
    have hh := norm_setIntegral_le_of_norm_le_const (measure_lt_top ν Kᶜ)
      (fun w _ => (show ‖F w - H w‖ ≤ 2 * C from by
        rw [Real.norm_eq_abs]
        exact (abs_sub _ _).trans (by linarith [hF w, hH w])))
    have hm : ν.real Kᶜ ≤ ε :=
      (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hε).mp hmass
    exact hh.trans (mul_le_mul_of_nonneg_left hm (by positivity))
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- Full-path bounded-continuous convergence for the concrete interpolation and supplied law. -/
theorem critical_weakExploration (hfinite : FiniteEnumerationStatement)
    (M : NatSeq) (lam : ℝ) (hcritical : criticalWindow M lam)
    (mu : PathLaw) (hmu : BrownianLaw mu) :
    WeakExploration M explorationInterpolation lam mu := by
  intro F hF hbound
  obtain ⟨C, hCbound⟩ := hbound
  have hC : 0 ≤ C := (abs_nonneg (F 0)).trans (hCbound 0)
  let f : BoundedContinuousFunction BrownianPath ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨F, hF⟩ (2 * C) (by
      intro w v
      rw [Real.dist_eq]
      change |F w - F v| ≤ 2 * C
      exact (abs_sub _ _).trans (by linarith [hCbound w, hCbound v]))
  letI : IsProbabilityMeasure mu := hmu.1
  let ν : PathLaw := Measure.map (fun w => driftPath w lam) mu
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map
    (continuous_driftPath lam).measurable.aemeasurable
  have hlim : Tendsto (fun n => ∫ w, f w ∂criticalPathLaw M n) atTop
      (𝓝 (∫ w, f w ∂ν)) := by
    apply Metric.tendsto_nhds.mpr
    intro e he
    let ε : ℝ := e / (16 * (C + 1))
    have hε : 0 < ε := by dsimp [ε]; positivity
    obtain ⟨K, hK, hmass, hνmass⟩ :=
      critical_common_path_compact hfinite M lam hcritical mu hmu ε hε
    obtain ⟨m, hm, happrox⟩ := compact_finite_grid_test_approximation K hK f (e / 8) (by positivity)
    let Hvec : BoundedContinuousFunction (EuclideanSpace ℝ (Fin (m * m + 1))) ℝ :=
      f.compContinuous ⟨gridReconstruction m, continuous_gridReconstruction m⟩
    let H : BoundedContinuousFunction BrownianPath ℝ :=
      Hvec.compContinuous ⟨gridEvaluation m, continuous_gridEvaluation m⟩
    have hH : ∀ w, |H w| ≤ C := fun w => hCbound _
    have hgood : ∀ w ∈ K, |f w - H w| ≤ e / 8 := fun w hw => (happrox w hw).le
    have hsmall : e / 8 + 2 * C * ε < e / 4 := by
      dsimp [ε]
      have hp : 0 < 16 * (C + 1) := by positivity
      have hh : 2 * C * (e / (16 * (C + 1))) < e / 8 := by
        apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
        field_simp
        nlinarith
      linarith
    have hfin := critical_actual_finite_dimensional_all_times
      hfinite M lam hcritical mu hmu (gridTime m) Hvec
    have heq : ∀ᶠ n in atTop,
        (∫ w, H w ∂criticalPathLaw M n) =
          expectM n (M n) (fun G =>
            Hvec (toLp 2 (fun i => explorationInterpolation n G (gridTime m i)))) := by
      filter_upwards [hcritical.1] with n hM
      rw [criticalPathLaw, dif_pos hM, explorationPathMeasure_integral n (M n) hM H H.continuous]
      rfl
    have hνH : (∫ w, H w ∂ν) =
        ∫ w, Hvec (toLp 2 (fun i => driftPath w lam (gridTime m i))) ∂mu := by
      calc
        _ = ∫ w, H (driftPath w lam) ∂mu :=
          integral_map (μ := mu) (f := fun w => H w)
            (continuous_driftPath lam).measurable.aemeasurable H.continuous.aestronglyMeasurable
        _ = _ := rfl
    have hmiddle : Tendsto (fun n => ∫ w, H w ∂criticalPathLaw M n) atTop
        (𝓝 (∫ w, H w ∂ν)) := by
      rw [hνH]
      apply hfin.congr'
      filter_upwards [heq] with n hn
      exact hn.symm
    have hmid := Metric.tendsto_nhds.mp hmiddle (e / 4) (by positivity)
    filter_upwards [hmid] with n hn
    have hnerr := integral_test_error (criticalPathLaw M n) K hK f H C (e / 8) ε
      hC (by positivity) hCbound hH hgood (hmass n) hε.le
    have hνerr := integral_test_error ν K hK f H C (e / 8) ε
      hC (by positivity) hCbound hH hgood hνmass hε.le
    rw [Real.dist_eq] at hn ⊢
    have ht1 := abs_sub_le (∫ w, f w ∂criticalPathLaw M n)
      (∫ w, H w ∂criticalPathLaw M n) (∫ w, f w ∂ν)
    have ht2 := abs_sub_le (∫ w, H w ∂criticalPathLaw M n)
      (∫ w, H w ∂ν) (∫ w, f w ∂ν)
    rw [abs_sub_comm (∫ w, H w ∂ν) (∫ w, f w ∂ν)] at ht2
    linarith
  have hνf : (∫ w, f w ∂ν) = ∫ w, F (driftPath w lam) ∂mu := by
    calc
      _ = ∫ w, f (driftPath w lam) ∂mu :=
        integral_map (μ := mu) (f := fun w => f w)
          (continuous_driftPath lam).measurable.aemeasurable f.continuous.aestronglyMeasurable
      _ = _ := rfl
  rw [hνf] at hlim
  apply hlim.congr'
  filter_upwards [hcritical.1] with n hM
  rw [criticalPathLaw, dif_pos hM, explorationPathMeasure_integral n (M n) hM f f.continuous]
  rfl

end
end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_PathWeak
