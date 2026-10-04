module

import all Mathlib.Basic.Real.Basic
public import Erdos448.dependencies.«DP-MERTENS».stage6.FrozenTaskContracts
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.NumberTheory.AbelSummation

public section

set_option backward.isDefEq.respectTransparency false

open Filter Finset Set MeasureTheory
open scoped BigOperators Topology Interval

namespace Erdos448.DPMertens.Tasks.MSCTail

noncomputable section

local instance : ContinuousInv₀ ℝ :=
  NormedDivisionRing.to_continuousInv₀

open Erdos448.DPMertens
open Erdos448.DPMertens.Lowering

@[expose] def primeCoeff (p : ℕ) : ℝ :=
  if p.Prime then Real.log p / p else 0

@[expose] def remainder (t : ℝ) : ℝ :=
  weightedPrimeSum t - Real.log t

@[expose] def kernelDeriv (rho t : ℝ) : ℝ :=
  (-rho * t ^ (-rho - 1) * Real.log t - t ^ (-rho) * t⁻¹) /
    (Real.log t) ^ 2

@[expose] def mainIntegrand (rho t : ℝ) : ℝ :=
  t ^ (-(1 + rho)) / Real.log t

lemma weightedPrimeSum_nat (n : ℕ) :
    weightedPrimeSum n = ∑ k ∈ Icc 0 n, primeCoeff k := by
  unfold weightedPrimeSum primesLE primeCoeff
  rw [Nat.range_succ_eq_Icc_zero]
  simp [Finset.sum_filter]

lemma hasDerivAt_tailKernel {rho t : ℝ} (ht : 1 < t) :
    HasDerivAt (tailKernel rho) (kernelDeriv rho t) t := by
  have ht0 : t ≠ 0 := ne_of_gt (by linarith)
  have hlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hp := Real.hasDerivAt_rpow_const (Or.inl ht0) (p := -rho)
  have hl := Real.hasDerivAt_log ht0
  unfold tailKernel kernelDeriv
  convert hp.div hl hlog using 1 <;> field_simp <;> ring

lemma kernelDeriv_nonpos {rho t : ℝ} (hrho : 0 < rho) (ht : 1 < t) :
    kernelDeriv rho t ≤ 0 := by
  have ht0 : 0 < t := by linarith
  have hlog : 0 < Real.log t := Real.log_pos ht
  unfold kernelDeriv
  have hp1 : 0 < t ^ (-rho - 1) := Real.rpow_pos_of_pos ht0 _
  have hp2 : 0 < t ^ (-rho) := Real.rpow_pos_of_pos ht0 _
  have hinv : 0 < t⁻¹ := inv_pos.mpr ht0
  have hnum : -rho * t ^ (-rho - 1) * Real.log t - t ^ (-rho) * t⁻¹ < 0 := by
    have : -rho * t ^ (-rho - 1) * Real.log t < 0 := by
      exact mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (neg_neg_of_pos hrho) hp1) hlog
    linarith [mul_pos hp2 hinv]
  exact div_nonpos_of_nonpos_of_nonneg hnum.le (sq_nonneg _)

lemma tendsto_tailKernel (rho : ℝ) (hrho : 0 < rho) :
    Tendsto (tailKernel rho) atTop (𝓝 0) := by
  have hp : Tendsto (fun t : ℝ ↦ t ^ (-rho)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop hrho
  have hl : Tendsto (fun t : ℝ ↦ (Real.log t)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  unfold tailKernel
  simpa only [div_eq_mul_inv, mul_zero] using hp.mul hl

lemma integrable_kernelDeriv {G : ℝ} (hG : 2 ≤ G)
    {rho : ℝ} (hrho : 0 < rho) :
    IntegrableOn (kernelDeriv rho) (Ioi G) := by
  apply integrableOn_Ioi_deriv_of_nonpos'
      (g := tailKernel rho) (l := 0)
  · intro t ht
    exact hasDerivAt_tailKernel (lt_of_lt_of_le (by linarith) ht)
  · intro t ht
    exact kernelDeriv_nonpos hrho (lt_of_lt_of_le (by linarith) ht.le)
  · exact tendsto_tailKernel rho hrho

lemma integral_neg_kernelDeriv {G : ℝ} (hG : 2 ≤ G)
    {rho : ℝ} (hrho : 0 < rho) :
    ∫ t in Ioi G, -kernelDeriv rho t = tailKernel rho G := by
  have hderiv : ∀ t ∈ Ici G,
      HasDerivAt (tailKernel rho) (kernelDeriv rho t) t := by
    intro t ht
    exact hasDerivAt_tailKernel (lt_of_lt_of_le (by linarith) ht)
  have hftc := integral_Ioi_of_hasDerivAt_of_nonpos'
    (g := tailKernel rho) (g' := kernelDeriv rho) (a := G) (l := 0) hderiv
    (fun t ht ↦ kernelDeriv_nonpos hrho
      (lt_of_lt_of_le (by linarith) ht.le))
    (tendsto_tailKernel rho hrho)
  rw [integral_neg, hftc]
  ring

lemma mainIntegrand_eq {rho t : ℝ} (ht : 0 < t) :
    mainIntegrand rho t = 1 / (Real.rpow t (1 + rho) * Real.log t) := by
  unfold mainIntegrand
  rw [Real.rpow_neg (le_of_lt ht)]
  rw [div_eq_mul_inv]
  simpa [mul_comm]

lemma integrable_mainIntegrand {G rho : ℝ}
    (hG : 2 ≤ G) (hrho : 0 < rho) :
    IntegrableOn (mainIntegrand rho) (Ioi G) := by
  have hbase : IntegrableOn (fun t : ℝ ↦ t ^ (-(1 + rho))) (Ioi G) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith)
  have hlogG : 0 < Real.log G := Real.log_pos (by linarith)
  have hdom : IntegrableOn
      (fun t : ℝ ↦ (Real.log G)⁻¹ * t ^ (-(1 + rho))) (Ioi G) :=
    hbase.const_mul _
  have hcont : ContinuousOn (mainIntegrand rho) (Ioi G) := by
    have hp : ContinuousOn (fun t : ℝ => t ^ (-(1 + rho))) (Ioi G) :=
      fun t ht => (Real.continuousAt_rpow_const t (-(1 + rho))
        (Or.inl (ne_of_gt (show 0 < t by linarith [hG, mem_Ioi.mp ht])))).continuousWithinAt
    have hl := Real.continuousOn_log.mono (by
      intro t ht
      change G < t at ht
      exact ne_of_gt (by change 0 < t; linarith [hG, ht]))
    exact hp.div hl (fun t ht => by
      change G < t at ht
      exact (Real.log_pos (show 1 < t by linarith [hG, ht])).ne')
  apply hdom.mono'
  · exact hcont.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := by linarith [hG, mem_Ioi.mp ht]
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith [hG, mem_Ioi.mp ht])
    have hlogle : Real.log G ≤ Real.log t :=
      Real.log_le_log (by linarith) ht.le
    have hinv : (Real.log t)⁻¹ ≤ (Real.log G)⁻¹ :=
      (inv_le_inv₀ hlogt hlogG).2 hlogle
    have hrpow : 0 ≤ t ^ (-(1 + rho)) := Real.rpow_nonneg htpos.le _
    simp only [mainIntegrand, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hrpow hlogt.le)]
    rw [div_eq_mul_inv]
    calc
      t ^ (-(1 + rho)) * (Real.log t)⁻¹ ≤
          t ^ (-(1 + rho)) * (Real.log G)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv hrpow
      _ = (Real.log G)⁻¹ * t ^ (-(1 + rho)) := by ring

lemma remainder_bound
    (first : FirstLemmaOutput)
    {t : ℝ} (ht : 2 ≤ t) : |remainder t| ≤ first.C_A := by
  exact first.first_lemma t ht

lemma measurable_remainder : Measurable remainder := by
  have hfloor : ∀ t : ℝ,
      weightedPrimeSum t = weightedPrimeSum (Nat.floor t : ℝ) := by
    intro t
    unfold weightedPrimeSum primesLE
    simp
  have hweighted : Measurable weightedPrimeSum := by
    rw [show weightedPrimeSum =
        fun t : ℝ ↦ weightedPrimeSum (Nat.floor t : ℝ) by
      funext t
      exact hfloor t]
    exact (measurable_of_countable (fun n : ℕ => weightedPrimeSum (n : ℝ))).comp
      Nat.measurable_floor
  exact hweighted.sub Real.measurable_log

lemma integrable_error
    (first : FirstLemmaOutput)
    {G : ℝ} (hG : 2 ≤ G) {rho : ℝ} (hrho : 0 < rho) :
    IntegrableOn (fun t ↦ kernelDeriv rho t * remainder t) (Ioi G) := by
  have hk := integrable_kernelDeriv hG hrho
  have hdom : IntegrableOn
      (fun t ↦ first.C_A * (-kernelDeriv rho t)) (Ioi G) :=
    hk.neg.const_mul first.C_A
  have hcontk : ContinuousOn (kernelDeriv rho) (Ioi G) := by
    have hp1 : ContinuousOn (fun t : ℝ => t ^ (-rho - 1)) (Ioi G) := fun t ht =>
      (Real.continuousAt_rpow_const t (-rho - 1)
        (Or.inl (ne_of_gt (show 0 < t by linarith [hG, mem_Ioi.mp ht])))).continuousWithinAt
    have hp2 : ContinuousOn (fun t : ℝ => t ^ (-rho)) (Ioi G) := fun t ht =>
      (Real.continuousAt_rpow_const t (-rho)
        (Or.inl (ne_of_gt (show 0 < t by linarith [hG, mem_Ioi.mp ht])))).continuousWithinAt
    have hi : ContinuousOn (fun t : ℝ => t⁻¹) (Ioi G) :=
      continuousOn_id.inv₀ (fun t ht =>
        ne_of_gt (show 0 < t by linarith [hG, mem_Ioi.mp ht]))
    have hl := Real.continuousOn_log.mono (by
      intro t ht
      change G < t at ht
      exact ne_of_gt (by change 0 < t; linarith [hG, ht]))
    have hnum : ContinuousOn
        (fun t : ℝ => -rho * t ^ (-rho - 1) * Real.log t -
          t ^ (-rho) * t⁻¹) (Ioi G) :=
      ((continuousOn_const.mul hp1).mul hl).sub (hp2.mul hi)
    exact hnum.div (hl.pow 2) (fun t ht => by
      change G < t at ht
      exact pow_ne_zero 2
        (Real.log_pos (show 1 < t by linarith [hG, ht])).ne')
  apply hdom.mono'
  · exact ((hcontk.aestronglyMeasurable measurableSet_Ioi).mul
      measurable_remainder.aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht2 : 2 ≤ t := hG.trans ht.le
    have hkneg := kernelDeriv_nonpos hrho (by linarith [ht2])
    have hR := remainder_bound first ht2
    have hCA := first.C_A_pos.le
    rw [Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonpos hkneg]
    have hnon : 0 ≤ -kernelDeriv rho t := by linarith
    have := mul_le_mul_of_nonneg_left hR hnon
    simpa [abs_of_nonpos hkneg, mul_comm, mul_left_comm, mul_assoc] using this

lemma error_integral_bound
    (first : FirstLemmaOutput)
    {G : ℝ} (hG : 2 ≤ G) {rho : ℝ} (hrho : 0 < rho) :
    |∫ t in Ioi G, kernelDeriv rho t * remainder t| ≤
      first.C_A * tailKernel rho G := by
  have herr := integrable_error first hG hrho
  have hdom := (integrable_kernelDeriv hG hrho).neg.const_mul first.C_A
  calc
    |∫ t in Ioi G, kernelDeriv rho t * remainder t| ≤
        ∫ t in Ioi G, |kernelDeriv rho t * remainder t| :=
      (by simpa [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm
          (f := fun t : ℝ => kernelDeriv rho t * remainder t)
          (μ := volume.restrict (Ioi G))))
    _ ≤ ∫ t in Ioi G, first.C_A * (-kernelDeriv rho t) := by
      apply integral_mono_ae herr.norm hdom
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht2 : 2 ≤ t := hG.trans ht.le
      have hkneg := kernelDeriv_nonpos hrho (by linarith [ht2])
      have hR := remainder_bound first ht2
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |kernelDeriv rho t| * |remainder t| =
            (-kernelDeriv rho t) * |remainder t| := by
              rw [abs_of_nonpos hkneg]
        _ ≤ (-kernelDeriv rho t) * first.C_A :=
          mul_le_mul_of_nonneg_left hR (by linarith)
        _ = first.C_A * (-kernelDeriv rho t) := by ring
    _ = first.C_A * tailKernel rho G := by
      calc
        (∫ t in Ioi G, first.C_A * (-kernelDeriv rho t)) =
            first.C_A * (∫ t in Ioi G, -kernelDeriv rho t) := by
              simpa using (MeasureTheory.integral_const_mul first.C_A
                (fun t : ℝ => -kernelDeriv rho t)
                (μ := volume.restrict (Ioi G)))
        _ = first.C_A * tailKernel rho G := by
          rw [integral_neg_kernelDeriv hG hrho]

lemma finite_tail_identity
    (first : FirstLemmaOutput)
    {G N : ℕ} (hG : 2 ≤ G) (hGN : G ≤ N)
    {rho : ℝ} (hrho : 0 < rho) :
    (∑ p ∈ Ioc G N,
        if p.Prime then Real.rpow p (-(1 + rho)) else 0) =
      (∫ t in Ioc (G : ℝ) N, mainIntegrand rho t) +
        (tailKernel rho N * remainder N -
          tailKernel rho G * remainder G -
          ∫ t in Ioc (G : ℝ) N, kernelDeriv rho t * remainder t) := by
  have hGreal : (2 : ℝ) ≤ G := by exact_mod_cast hG
  have hGNreal : (G : ℝ) ≤ N := by exact_mod_cast hGN
  have hG1 : (1 : ℝ) < G := by linarith
  have hN1 : (1 : ℝ) < N := lt_of_lt_of_le hG1 hGNreal
  have hdiff : ∀ t ∈ Icc (G : ℝ) N,
      DifferentiableAt ℝ (tailKernel rho) t := by
    intro t ht
    exact (hasDerivAt_tailKernel (lt_of_lt_of_le hG1 ht.1)).differentiableAt
  have hkint : IntegrableOn (kernelDeriv rho) (Icc (G : ℝ) N) := by
    have hkcont : ContinuousOn (kernelDeriv rho) (Ioi (1 : ℝ)) := by
      have hp1 : ContinuousOn (fun t : ℝ => t ^ (-rho - 1)) (Ioi (1 : ℝ)) := fun t ht =>
        (Real.continuousAt_rpow_const t (-rho - 1)
          (Or.inl (ne_of_gt (show 0 < t by linarith [mem_Ioi.mp ht])))).continuousWithinAt
      have hp2 : ContinuousOn (fun t : ℝ => t ^ (-rho)) (Ioi (1 : ℝ)) := fun t ht =>
        (Real.continuousAt_rpow_const t (-rho)
          (Or.inl (ne_of_gt (show 0 < t by linarith [mem_Ioi.mp ht])))).continuousWithinAt
      have hi : ContinuousOn (fun t : ℝ => t⁻¹) (Ioi (1 : ℝ)) :=
        continuousOn_id.inv₀ (fun t ht =>
          ne_of_gt (show 0 < t by linarith [mem_Ioi.mp ht]))
      have hl := Real.continuousOn_log.mono (by
        intro t ht
        change (1 : ℝ) < t at ht
        exact ne_of_gt (by linarith))
      have hnum : ContinuousOn
          (fun t : ℝ => -rho * t ^ (-rho - 1) * Real.log t -
            t ^ (-rho) * t⁻¹) (Ioi (1 : ℝ)) :=
        ((continuousOn_const.mul hp1).mul hl).sub (hp2.mul hi)
      exact hnum.div (hl.pow 2) (fun t ht => by
        have ht1 : (1 : ℝ) < t := mem_Ioi.mp ht
        exact pow_ne_zero 2 (Real.log_pos ht1).ne')
    have hsub : Icc (G : ℝ) N ⊆ Ioi (1 : ℝ) := by
      intro t ht
      show t ∈ Set.Ioi (1 : ℝ)
      exact lt_of_lt_of_le hG1 ht.1
    exact (hkcont.mono hsub).integrableOn_Icc
  have hderiv_eq : ∀ t ∈ Icc (G : ℝ) N,
      deriv (tailKernel rho) t = kernelDeriv rho t := by
    intro t ht
    exact (hasDerivAt_tailKernel (lt_of_lt_of_le hG1 ht.1)).deriv
  have habel := sum_mul_eq_sub_sub_integral_mul'
    (c := primeCoeff) (f := tailKernel rho) hGN hdiff
      (hkint.congr_fun (fun t ht => (hderiv_eq t ht).symm) measurableSet_Icc)
  have hsum : (∑ p ∈ Ioc G N, tailKernel rho p * primeCoeff p) =
      ∑ p ∈ Ioc G N,
        if p.Prime then Real.rpow p (-(1 + rho)) else 0 := by
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hprime : p.Prime
    · have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
      have hlog : Real.log (p : ℝ) ≠ 0 := (Real.log_pos hp1).ne'
      simp only [primeCoeff, hprime, if_true, tailKernel]
      rw [div_mul_eq_mul_div]
      field_simp [hlog]
      rw [show (-rho) = 1 + (-(1 + rho)) by ring,
        Real.rpow_add (by positivity)]
      simp [Real.rpow_one]
    · simp [primeCoeff, hprime]
  have hA (n : ℕ) :
      ∑ k ∈ Icc 0 n, primeCoeff k = Real.log n + remainder n := by
    rw [← weightedPrimeSum_nat]
    unfold remainder
    ring
  have hmain :
      tailKernel rho N * Real.log N - tailKernel rho G * Real.log G -
          ∫ t in Ioc (G : ℝ) N, kernelDeriv rho t * Real.log t =
        ∫ t in Ioc (G : ℝ) N, mainIntegrand rho t := by
    have hkI : IntervalIntegrable (kernelDeriv rho) volume G N := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hGNreal]
      exact hkint
    have hlogI : IntervalIntegrable (fun t : ℝ ↦ t⁻¹) volume G N := by
      exact (continuousOn_id.inv₀ (fun t ht => by
        have ht' : t ∈ Icc (G : ℝ) N := by
          simpa [uIcc_of_le hGNreal] using ht
        change t ≠ 0
        exact ne_of_gt (by linarith [hG1, ht'.1]))).intervalIntegrable
    have hibp := intervalIntegral.integral_deriv_mul_eq_sub
      (u := tailKernel rho) (v := Real.log)
      (u' := kernelDeriv rho) (v' := fun t ↦ t⁻¹)
      (fun t ht ↦ by
        have ht' : t ∈ Icc (G : ℝ) N := by
          simpa [uIcc_of_le hGNreal] using ht
        exact hasDerivAt_tailKernel (lt_of_lt_of_le hG1 ht'.1))
      (fun t ht ↦ by
        have ht' : t ∈ Icc (G : ℝ) N := by
          simpa [uIcc_of_le hGNreal] using ht
        exact Real.hasDerivAt_log (ne_of_gt (by linarith [ht'.1])))
      hkI hlogI
    have hlogC : ContinuousOn Real.log [[(G : ℝ), N]] := by
      intro t ht
      have ht' : t ∈ Icc (G : ℝ) N := by
        simpa [uIcc_of_le hGNreal] using ht
      exact (Real.continuousAt_log (ne_of_gt (by linarith [ht'.1]))).continuousWithinAt
    have htailC : ContinuousOn (tailKernel rho) [[(G : ℝ), N]] := by
      intro t ht
      have ht' : t ∈ Icc (G : ℝ) N := by
        simpa [uIcc_of_le hGNreal] using ht
      exact (hasDerivAt_tailKernel (lt_of_lt_of_le hG1 ht'.1)).continuousAt.continuousWithinAt
    rw [intervalIntegral.integral_add (hkI.mul_continuousOn hlogC)
      (hlogI.continuousOn_mul htailC)] at hibp
    simp_rw [intervalIntegral.integral_of_le hGNreal] at hibp
    have hpoint : ∀ t ∈ Ioc (G : ℝ) N,
        tailKernel rho t * t⁻¹ = mainIntegrand rho t := by
      intro t ht
      unfold tailKernel mainIntegrand
      rw [div_eq_mul_inv]
      have htpos : 0 < t := by linarith [ht.1]
      rw [show (-rho) = 1 + (-(1 + rho)) by ring,
        Real.rpow_add htpos]
      rw [Real.rpow_one]
      field_simp [htpos.ne']
    have hpoint_int :
        (∫ t in Ioc (G : ℝ) N, tailKernel rho t * t⁻¹) =
          ∫ t in Ioc (G : ℝ) N, mainIntegrand rho t := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hpoint t ht
    have hpoint_int' :
        (∫ t in Ioc (G : ℝ) N, tailKernel rho t * (fun s : ℝ => s⁻¹) t) =
          ∫ t in Ioc (G : ℝ) N, mainIntegrand rho t := by
      simpa using hpoint_int
    have hibp' :
        (∫ t in Ioc (G : ℝ) N, kernelDeriv rho t * Real.log t) +
          (∫ t in Ioc (G : ℝ) N, tailKernel rho t * t⁻¹) =
          tailKernel rho N * Real.log N - tailKernel rho G * Real.log G := by
      simpa using hibp
    rw [hpoint_int] at hibp'
    linarith
  have hderiv_int :
      (∫ t in Ioc (G : ℝ) N,
        deriv (tailKernel rho) t * ∑ k ∈ Icc 0 (Nat.floor t), primeCoeff k) =
      ∫ t in Ioc (G : ℝ) N,
        kernelDeriv rho t * ∑ k ∈ Icc 0 (Nat.floor t), primeCoeff k := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [hderiv_eq t (by exact ⟨le_of_lt ht.1, ht.2⟩)]
  rw [hderiv_int] at habel
  rw [hsum] at habel
  rw [hA N, hA G] at habel
  have hsum_int :
      (∫ t in Ioc (G : ℝ) N,
        kernelDeriv rho t * ∑ k ∈ Icc 0 (Nat.floor t), primeCoeff k) =
      ∫ t in Ioc (G : ℝ) N,
        kernelDeriv rho t * (Real.log t + remainder t) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hw : (∑ k ∈ Icc 0 (Nat.floor t), primeCoeff k) = weightedPrimeSum t := by
      unfold weightedPrimeSum primesLE
      rw [Nat.range_succ_eq_Icc_zero]
      simp [primeCoeff, Finset.sum_filter]
    rw [hw]
    unfold remainder
    ring
  rw [hsum_int] at habel
  have hklogInt : IntegrableOn
      (fun t : ℝ => kernelDeriv rho t * Real.log t) (Ioc (G : ℝ) N) := by
    apply (hkint.mul_continuousOn ?_ isCompact_Icc).mono_set Ioc_subset_Icc_self
    intro t ht
    exact (Real.continuousAt_log (ne_of_gt (by linarith [hG1, ht.1]))).continuousWithinAt
  have hkremInt : IntegrableOn
      (fun t : ℝ => kernelDeriv rho t * remainder t) (Ioc (G : ℝ) N) :=
    (integrable_error first hGreal hrho).mono_set (by
      intro t ht
      exact mem_Ioi.mpr ht.1)
  have hsplit :
      (∫ t in Ioc (G : ℝ) N,
        kernelDeriv rho t * (Real.log t + remainder t)) =
      (∫ t in Ioc (G : ℝ) N, kernelDeriv rho t * Real.log t) +
        ∫ t in Ioc (G : ℝ) N, kernelDeriv rho t * remainder t := by
    simp_rw [mul_add]
    exact integral_add hklogInt hkremInt
  rw [hsplit] at habel
  rw [habel]
  rw [← hmain]
  ring

lemma summable_prime_tail (G : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    Summable (fun p : ℕ ↦
      if p.Prime ∧ G < p then Real.rpow p (-(1 + rho)) else 0) := by
  have hs : Summable (fun p : ℕ => Real.rpow p (-(1 + rho))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  apply hs.of_norm_bounded (g := fun p : ℕ => Real.rpow p (-(1 + rho)))
  intro p
  by_cases hp : p.Prime ∧ G < p
  · simp only [hp, if_true]
    exact le_of_eq (abs_of_nonneg (Real.rpow_nonneg (by positivity) _))
  · simp [hp, Real.rpow_nonneg]

lemma tendsto_finite_prime_tail (G : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    Tendsto (fun N : ℕ ↦ ∑ p ∈ Ioc G N,
      if p.Prime then Real.rpow p (-(1 + rho)) else 0) atTop
      (𝓝 (∑' p : ℕ,
        if p.Prime ∧ G < p then Real.rpow p (-(1 + rho)) else 0)) := by
  let a : ℕ → ℝ := fun p ↦
    if p.Prime ∧ G < p then Real.rpow p (-(1 + rho)) else 0
  have ha : Summable a := summable_prime_tail G hrho
  have ht := ha.tendsto_sum_tsum_nat.comp
    (Filter.tendsto_add_atTop_nat 1)
  apply ht.congr'
  filter_upwards with N
  unfold a
  change (∑ p ∈ range (N + 1),
      if p.Prime ∧ G < p then Real.rpow p (-(1 + rho)) else 0) =
    ∑ p ∈ Ioc G N, if p.Prime then Real.rpow p (-(1 + rho)) else 0
  symm
  calc
    (∑ p ∈ Ioc G N, if p.Prime then Real.rpow p (-(1 + rho)) else 0) =
        ∑ p ∈ Ioc G N,
          if p.Prime ∧ G < p then Real.rpow p (-(1 + rho)) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      simp [mem_Ioc.mp hp |>.1]
    _ = ∑ p ∈ range (N + 1),
          if p.Prime ∧ G < p then Real.rpow p (-(1 + rho)) else 0 := by
      apply Finset.sum_subset (show Finset.Ioc G N ⊆ range (N + 1) by
        intro p hp
        have hpN : p ≤ N := (Finset.mem_Ioc.mp hp).2
        apply Finset.mem_range.mpr
        omega)
      intro p hp hnot
      simp only [Finset.mem_range] at hp
      simp only [ite_eq_right_iff]
      intro hprime
      have : p ∈ Finset.Ioc G N := by
        simp only [Finset.mem_Ioc]
        exact ⟨hprime.2, by omega⟩
      exact (hnot this).elim

lemma tendsto_kernel_mul_remainder
    (first : FirstLemmaOutput)
    {rho : ℝ} (hrho : 0 < rho) :
    Tendsto (fun N : ℕ ↦ tailKernel rho N * remainder N)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm'
      (a := fun N : ℕ ↦ first.C_A * |tailKernel rho N|)
  · filter_upwards [eventually_ge_atTop 2] with N hN
    rw [Real.norm_eq_abs, abs_mul]
    have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    simpa [mul_comm] using mul_le_mul_of_nonneg_left
      (remainder_bound first hNreal) (abs_nonneg (tailKernel rho N))
  · have hk : Tendsto (fun N : ℕ ↦ tailKernel rho N) atTop (𝓝 0) :=
      (tendsto_tailKernel rho hrho).comp tendsto_natCast_atTop_atTop
    simpa using (tendsto_const_nhds.mul hk.abs)

lemma tail_formula_and_bound
    (first : FirstLemmaOutput)
    (G : ℕ) (hG : 2 ≤ G) (rho : ℝ) (hrho : 0 < rho) :
    let E := -tailKernel rho G * remainder G -
      ∫ t in Ioi (G : ℝ), kernelDeriv rho t * remainder t
    (∑' p : ℕ, if p.Prime ∧ G < p then Real.rpow p (-(1 + rho)) else 0) =
        primeTailIntegral G rho + E ∧
      |E| ≤ 2 * first.C_A / Real.log G := by
  dsimp only
  have hGreal : (2 : ℝ) ≤ G := by exact_mod_cast hG
  have hmainInt := integrable_mainIntegrand hGreal hrho
  have herrInt := integrable_error first hGreal hrho
  have hfinite := fun N (hGN : G ≤ N) ↦ finite_tail_identity first hG hGN hrho
  have htail := tendsto_finite_prime_tail G hrho
  have hmain : Tendsto
      (fun N : ℕ ↦ ∫ t in Ioc (G : ℝ) N, mainIntegrand rho t)
      atTop (𝓝 (∫ t in Ioi (G : ℝ), mainIntegrand rho t)) := by
    have hi := intervalIntegral_tendsto_integral_Ioi (G : ℝ)
      hmainInt tendsto_natCast_atTop_atTop
    apply hi.congr'
    filter_upwards [eventually_ge_atTop G] with N hN
    have hNreal : (G : ℝ) ≤ N := by exact_mod_cast hN
    rw [intervalIntegral.integral_of_le hNreal]
  have herr : Tendsto
      (fun N : ℕ ↦ ∫ t in Ioc (G : ℝ) N,
        kernelDeriv rho t * remainder t)
      atTop (𝓝 (∫ t in Ioi (G : ℝ),
        kernelDeriv rho t * remainder t)) := by
    have hi := intervalIntegral_tendsto_integral_Ioi (G : ℝ)
      herrInt tendsto_natCast_atTop_atTop
    apply hi.congr'
    filter_upwards [eventually_ge_atTop G] with N hN
    have hNreal : (G : ℝ) ≤ N := by exact_mod_cast hN
    rw [intervalIntegral.integral_of_le hNreal]
  have hkR := tendsto_kernel_mul_remainder first hrho
  have hconst : Tendsto
      (fun _ : ℕ => tailKernel rho G * remainder G) atTop
      (𝓝 (tailKernel rho G * remainder G)) := tendsto_const_nhds
  have hrhs := hmain.add
    ((hkR.sub hconst).sub herr)
  have heq :
      (∑' p : ℕ, if p.Prime ∧ G < p then
          Real.rpow p (-(1 + rho)) else 0) =
        (∫ t in Ioi (G : ℝ), mainIntegrand rho t) +
          (-tailKernel rho G * remainder G -
            ∫ t in Ioi (G : ℝ), kernelDeriv rho t * remainder t) := by
    apply tendsto_nhds_unique htail
    have hrhs' : Tendsto
        (fun N : ℕ =>
          (∫ t in Ioc (G : ℝ) N, mainIntegrand rho t) +
            (tailKernel rho N * remainder N -
              tailKernel rho G * remainder G -
              ∫ t in Ioc (G : ℝ) N,
                kernelDeriv rho t * remainder t)) atTop
        (𝓝 ((∫ t in Ioi (G : ℝ), mainIntegrand rho t) +
          (-tailKernel rho G * remainder G -
            ∫ t in Ioi (G : ℝ),
              kernelDeriv rho t * remainder t))) := by
      convert hrhs using 1 <;> ring
    apply hrhs'.congr'
    filter_upwards [eventually_ge_atTop G] with N hN
    rw [hfinite N hN]
  have hmainFrozen :
      (∫ t in Ioi (G : ℝ), mainIntegrand rho t) =
        primeTailIntegral G rho := by
    unfold primeTailIntegral
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mainIntegrand_eq (by linarith [hGreal, mem_Ioi.mp ht])
  refine ⟨by simpa [hmainFrozen] using heq, ?_⟩
  have hRend := remainder_bound first hGreal
  have hkG0 : 0 ≤ tailKernel rho G := by
    unfold tailKernel
    exact div_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ G by omega)))
  have hint := error_integral_bound first hGreal hrho
  have hE :
      abs (-tailKernel rho G * remainder G -
          ∫ t in Ioi (G : ℝ), kernelDeriv rho t * remainder t) ≤
        2 * first.C_A * tailKernel rho G := by
    calc
      abs (-tailKernel rho G * remainder G -
          ∫ t in Ioi (G : ℝ), kernelDeriv rho t * remainder t) ≤
          abs (tailKernel rho G * remainder G) +
          abs (∫ t in Ioi (G : ℝ), kernelDeriv rho t * remainder t) := by
        rw [show -tailKernel rho G * remainder G -
          (∫ t in Ioi (G : ℝ), kernelDeriv rho t * remainder t) =
          -(tailKernel rho G * remainder G +
            ∫ t in Ioi (G : ℝ), kernelDeriv rho t * remainder t) by ring,
          abs_neg]
        exact abs_add_le _ _
      _ ≤ first.C_A * tailKernel rho G +
          first.C_A * tailKernel rho G := by
        gcongr
        rw [abs_mul, abs_of_nonneg hkG0]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hRend hkG0
      _ = 2 * first.C_A * tailKernel rho G := by ring
  have hlogG : 0 < Real.log (G : ℝ) := Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by omega) hG))
  have hrpow_le : (G : ℝ) ^ (-rho) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast (show 1 ≤ G by omega)) (by linarith)
  have hk_le : tailKernel rho G ≤ 1 / Real.log G := by
    unfold tailKernel
    exact div_le_div_of_nonneg_right hrpow_le hlogG.le
  calc
    abs (-tailKernel rho G * remainder G -
      ∫ t in Ioi (G : ℝ), kernelDeriv rho t * remainder t) ≤
      2 * first.C_A * tailKernel rho G := hE
    _ ≤ 2 * first.C_A * (1 / Real.log G) := by
      exact mul_le_mul_of_nonneg_left hk_le
        (mul_nonneg (by norm_num) first.C_A_pos.le)
    _ = 2 * first.C_A / Real.log G := by ring

/-- P-MSC-04: the open prime tail, uniformly in every positive `rho`, with
the inherited first-lemma constant unchanged. -/
@[expose] def result : TASK_MSC_TAIL_Target := fun first => {
  first := first
  tail := {
    mathcalE := fun G rho ↦
      -tailKernel rho G * remainder G -
        ∫ t in Ioi (G : ℝ), kernelDeriv rho t * remainder t
    formula := by
      intro G hG rho hrho
      exact (tail_formula_and_bound first G hG rho hrho).1
    uniform_bound := by
      intro G hG rho hrho
      exact (tail_formula_and_bound first G hG rho hrho).2
  }
}

end

end Erdos448.DPMertens.Tasks.MSCTail
