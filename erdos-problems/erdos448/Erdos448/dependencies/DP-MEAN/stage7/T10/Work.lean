module

import all Mathlib.Basic.Real.Basic
public import Erdos448.dependencies.«DP-MEAN».stage6.shared.TaskInterfaces

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.DPMean.TaskT10

@[expose] abbrev PublicTarget : Prop := Erdos448.DPMean.S6.T10PackageTarget

open Erdos448.DPMean

noncomputable section

lemma localSeriesSummable
    {lambda1 lambda2 : ℝ} (range : ParameterRange lambda1 lambda2)
    (h : ArithmeticFunction) (hgeom : PrimePowerGeometricBound h lambda1 lambda2)
    (p : ℕ) (hp : Nat.Prime p) :
    Summable (fun j : ℕ => eulerTerm h p j) := by
  have hp_real : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp_pos : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hp_real
  have ratio_nonneg : 0 ≤ lambda2 / (p : ℝ) :=
    div_nonneg range.lambda2_nonnegative hp_pos.le
  have ratio_lt_one : lambda2 / (p : ℝ) < 1 := by
    apply (div_lt_one hp_pos).2
    exact lt_of_lt_of_le range.lambda2_lt_two hp_real
  apply Summable.of_nonneg_of_le
      (f := fun j : ℕ => lambda1 * (lambda2 / (p : ℝ)) ^ j)
  · intro j
    exact div_nonneg (hgeom p hp j).1 (pow_nonneg hp_pos.le j)
  · intro j
    calc
      eulerTerm h p j
          ≤ (lambda1 * lambda2 ^ j) / (p : ℝ) ^ j :=
            div_le_div_of_nonneg_right (hgeom p hp j).2 (pow_nonneg hp_pos.le j)
      _ = lambda1 * (lambda2 / (p : ℝ)) ^ j := by
        rw [div_pow]
        ring
  · exact (summable_geometric_of_lt_one ratio_nonneg ratio_lt_one).mul_left lambda1

lemma firstPowerConstant_nonneg
    {lambda1 lambda2 : ℝ} (range : ParameterRange lambda1 lambda2) :
    0 ≤ firstPowerConstant lambda1 lambda2 := by
  unfold firstPowerConstant chebyshevConstant
  have hlog : 0 ≤ Real.log (2 : ℝ) := (Real.log_pos (by norm_num)).le
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hlog) range.lambda1_nonnegative)
    range.lambda2_nonnegative

lemma higherPowerTerm_nonneg
    {lambda2 : ℝ} (hlambda2 : 0 ≤ lambda2) (p r : ℕ) :
    0 ≤ higherPowerTerm lambda2 p r := by
  unfold higherPowerTerm
  split_ifs with hpr
  · have hp_one : (1 : ℝ) ≤ p := by exact_mod_cast hpr.1.one_le
    have hp_pos : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hp_one
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg r) (Real.log_nonneg hp_one))
      (pow_nonneg (div_nonneg hlambda2 hp_pos.le) r)
  · exact le_rfl

lemma higherPowerConstant_nonneg
    {lambda1 lambda2 : ℝ} (range : ParameterRange lambda1 lambda2) :
    0 ≤ higherPowerConstant lambda1 lambda2 := by
  unfold higherPowerConstant
  exact mul_nonneg range.lambda1_nonnegative
    (tsum_nonneg (fun p => tsum_nonneg (higherPowerTerm_nonneg range.lambda2_nonnegative p)))

lemma coefficient_positive
    {lambda1 lambda2 : ℝ} (range : ParameterRange lambda1 lambda2) :
    0 < firstPowerConstant lambda1 lambda2 +
      higherPowerConstant lambda1 lambda2 + 1 := by
  have hA := firstPowerConstant_nonneg range
  have hB := higherPowerConstant_nonneg range
  linarith

lemma strictMean_eq_inclusiveMean
    {h : ArithmeticFunction} {X : ℝ}
    (transport : DEF021Interface X) :
    strictMean h X = inclusiveMean h (DEF005Interface X) := by
  apply Finset.sum_congr
  · ext n
    by_cases hn : 0 < n
    · simp only [strictNatDomain, inclusiveNatDomain, Finset.mem_filter,
        Finset.mem_range, strictMean, inclusiveMean]
      simp only [hn, and_true]
      rw [Nat.lt_ceil]
      rw [transport n hn]
      simp [DEF005Interface, strictCutoff]
    · simp [strictNatDomain, inclusiveNatDomain, hn]
  · intro n hn
    rfl

lemma strictEulerProduct_eq_inclusiveEulerProduct
    {h : ArithmeticFunction} {X : ℝ}
    (transport : DEF022Interface X) :
    strictEulerProduct h X = inclusiveEulerProduct h (DEF005Interface X) := by
  apply Finset.prod_congr
  · ext p
    by_cases hp : Nat.Prime p
    · have hp_pos : 0 < p := hp.pos
      simp only [strictPrimeDomain, inclusivePrimeDomain, strictNatDomain,
        inclusiveNatDomain, Finset.mem_filter, Finset.mem_range]
      simp only [hp, hp_pos, and_true]
      rw [Nat.lt_ceil]
      rw [transport p hp]
      simp [DEF005Interface, strictCutoff]
    · simp [strictPrimeDomain, inclusivePrimeDomain, hp]
  · intro p hp
    rfl

lemma reciprocalMean_nonneg
    {h : ArithmeticFunction} (hnonneg : Nonnegative h) (x : ℝ) :
    0 ≤ reciprocalMean h x := by
  unfold reciprocalMean
  apply Finset.sum_nonneg
  intro n hn
  exact div_nonneg (hnonneg n (Finset.mem_filter.1 hn).2) (Nat.cast_nonneg n)

lemma inclusiveEulerProduct_nonneg
    {h : ArithmeticFunction} (hnonneg : Nonnegative h) (x : ℝ) :
    0 ≤ inclusiveEulerProduct h x := by
  unfold inclusiveEulerProduct
  apply Finset.prod_nonneg
  intro p hp
  apply tsum_nonneg
  intro j
  unfold eulerTerm
  exact div_nonneg (hnonneg _ (pow_pos (Nat.Prime.pos (by
    exact (Finset.mem_filter.1 hp).2)) _)) (pow_nonneg (Nat.cast_nonneg p) j)

lemma strictBranch
    (p010 : P010Statement) (p011 : P011Statement)
    (p012_full : P012FullStatement)
    {lambda1 lambda2 : ℝ} (range : ParameterRange lambda1 lambda2)
    (h : ArithmeticFunction) (hnm : NonnegativeMultiplicative h)
    (hgeom : PrimePowerGeometricBound h lambda1 lambda2)
    {X : ℝ} (hX : 2 < X) :
    MeanBoundAt lambda1 lambda2 (meanThreshold lambda1 lambda2) h X := by
  let N : ℝ := DEF005Interface X
  let assumptions : MeanAssumptions h lambda1 lambda2 :=
    { h_nonnegative_multiplicative := hnm
      parameter_range := range
      prime_power_geometric_bound := hgeom }
  have weakX : 2 ≤ X := hX.le
  have endpoints := p012_full X weakX
  have N_two : 2 ≤ N := endpoints.strict_cutoff_at_least_two hX
  have N_one : 1 ≤ N := le_trans (by norm_num) N_two
  have coarse := p010 h lambda1 lambda2 N assumptions N_two
  have euler := p011 h lambda1 lambda2 N assumptions N_one
  have factor := endpoints.strict_factor_comparison hX
  have mean_transport := strictMean_eq_inclusiveMean (h := h)
    endpoints.integer_endpoint_transport
  have product_transport := strictEulerProduct_eq_inclusiveEulerProduct (h := h)
    endpoints.prime_endpoint_transport
  have reciprocal_nonneg : 0 ≤ reciprocalMean h N :=
    reciprocalMean_nonneg hnm.nonnegative N
  have product_nonneg : 0 ≤ inclusiveEulerProduct h N :=
    inclusiveEulerProduct_nonneg hnm.nonnegative N
  have coeff_pos := coefficient_positive range
  have threshold_ge :
      2 * (firstPowerConstant lambda1 lambda2 +
        higherPowerConstant lambda1 lambda2 + 1) ≤
        meanThreshold lambda1 lambda2 := by
    unfold meanThreshold
    exact le_max_right _ _
  unfold MeanBoundAt
  rw [mean_transport, product_transport]
  calc
    inclusiveMean h N ≤
        (firstPowerConstant lambda1 lambda2 +
          higherPowerConstant lambda1 lambda2 + 1) *
          (N / Real.log N) * reciprocalMean h N := coarse
    _ ≤ (firstPowerConstant lambda1 lambda2 +
          higherPowerConstant lambda1 lambda2 + 1) *
          (N / Real.log N) * inclusiveEulerProduct h N := by
      gcongr
      exact mul_nonneg coeff_pos.le (by
        have logN_pos : 0 < Real.log N := Real.log_pos (lt_of_lt_of_le (by norm_num) N_two)
        positivity)
      exact euler.domination
    _ ≤ (firstPowerConstant lambda1 lambda2 +
          higherPowerConstant lambda1 lambda2 + 1) *
          (2 * (X / Real.log X)) * inclusiveEulerProduct h N := by
      gcongr
      exact factor
    _ = (2 * (firstPowerConstant lambda1 lambda2 +
          higherPowerConstant lambda1 lambda2 + 1)) *
          (X / Real.log X) * inclusiveEulerProduct h N := by ring
    _ ≤ meanThreshold lambda1 lambda2 *
          (X / Real.log X) * inclusiveEulerProduct h N := by
      gcongr
      have logX_pos : 0 < Real.log X := Real.log_pos (by linarith)
      positivity

lemma endpointTwo
    {lambda1 lambda2 : ℝ} (range : ParameterRange lambda1 lambda2)
    (h : ArithmeticFunction) (hnm : NonnegativeMultiplicative h) :
    MeanBoundAt lambda1 lambda2 (meanThreshold lambda1 lambda2) h 2 := by
  have threshold_one : 1 ≤ meanThreshold lambda1 lambda2 := by
    unfold meanThreshold
    exact le_max_left _ _
  have log_two_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have log_two_le_one : Real.log (2 : ℝ) ≤ 1 := by
    nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have factor_ge_one : 1 ≤ (2 : ℝ) / Real.log 2 := by
    apply (le_div_iff₀ log_two_pos).2
    linarith
  have h_one : h 1 = 1 := hnm.multiplicative.1
  have nat_domain_two : strictNatDomain 2 = {1} := by
    ext n
    simp [strictNatDomain]
    omega
  have prime_domain_two : strictPrimeDomain 2 = ∅ := by
    ext p
    simp only [strictPrimeDomain, Finset.mem_filter, nat_domain_two,
      Finset.mem_singleton, Finset.notMem_empty, iff_false]
    intro hp
    rcases hp with ⟨rfl, hp⟩
    norm_num at hp
  have strict_mean_two : strictMean h 2 = 1 := by
    simp [strictMean, nat_domain_two, h_one]
  have strict_product_two : strictEulerProduct h 2 = 1 := by
    simp [strictEulerProduct, prime_domain_two]
  unfold MeanBoundAt
  rw [strict_mean_two, strict_product_two, mul_one]
  nlinarith

theorem publicTarget : PublicTarget := by
  rintro ⟨_, p010⟩ p011 p012_full lambda1 lambda2 range
  refine ⟨{
    C := meanThreshold lambda1 lambda2
    C_positive := ?_
    threshold_le_C := le_rfl
    local_series_summable := ?_
    bound := ?_
  }⟩
  · exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  · intro h hgeom p hp
    exact localSeriesSummable range h hgeom p hp
  · intro h hnm hgeom X hX
    rcases hX.eq_or_lt with rfl | hX
    · exact endpointTwo range h hnm
    · exact strictBranch p010 p011 p012_full range h hnm hgeom hX

end

end Erdos448.DPMean.TaskT10
