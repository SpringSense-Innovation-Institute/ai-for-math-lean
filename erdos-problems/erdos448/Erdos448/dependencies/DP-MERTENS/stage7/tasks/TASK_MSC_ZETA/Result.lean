module

import all Mathlib.Basic.Real.Basic
public import Erdos448.dependencies.«DP-MERTENS».stage6.FrozenTaskContracts
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

public section

set_option backward.isDefEq.respectTransparency false

open Filter Set
open scoped Topology Interval

namespace Erdos448.DPMertens.Tasks.MSCZeta

open Erdos448.DPMertens
open Erdos448.DPMertens.Lowering

noncomputable section

lemma zetaOnePlus_eq_re_riemannZeta (rho : ℝ) (hrho : 0 < rho) :
    zetaOnePlus rho = (riemannZeta (1 + rho : ℝ)).re := by
  have hs : 1 < ((1 + rho : ℝ) : ℂ).re := by simpa using hrho
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  rw [Complex.re_tsum (Complex.summable_one_div_nat_cpow.mpr hs)]
  unfold zetaOnePlus
  apply tsum_congr
  intro n
  by_cases hn : 1 ≤ n
  · simp only [if_pos hn]
    calc
      (n : ℝ).rpow (-(1 + rho)) =
          (((n : ℝ).rpow (-(1 + rho)) : ℝ) : ℂ).re := by simp
      _ = ((n : ℂ) ^ ((-(1 + rho) : ℝ) : ℂ)).re := by
        exact congrArg Complex.re (Complex.ofReal_cpow (Nat.cast_nonneg n) (-(1 + rho)))
      _ = (1 / (n : ℂ) ^ ((1 + rho : ℝ) : ℂ)).re := by
        exact congrArg Complex.re (by
          simpa only [Complex.ofReal_neg, one_div] using
            Complex.cpow_neg (n : ℂ) ((1 + rho : ℝ) : ℂ))
  · have hn0 : n = 0 := by omega
    subst n
    simp only [if_neg (by omega : ¬ 1 ≤ 0), Nat.cast_zero]
    rw [Complex.zero_cpow (by
      exact Complex.ofReal_ne_zero.mpr (by linarith : (1 + rho : ℝ) ≠ 0))]
    simp

lemma tendsto_one_add_rho :
    Tendsto (fun rho : ℝ ↦ 1 + rho) rhoDownZero
      (nhdsWithin (1 : ℝ) (Ioi 1)) := by
  unfold rhoDownZero
  change map (fun rho : ℝ ↦ 1 + rho) (nhdsWithin 0 (Ioi 0)) ≤
    nhdsWithin 1 (Ioi 1)
  exact le_of_eq (by simpa using
    (Filter.map_add_left_nhdsGT (H := ℝ) (c := (1 : ℝ)) (a := (0 : ℝ))))

theorem poleNormalization : ZetaPoleNormalization := by
  have hpoleComplex :=
    ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_nhds_right.comp
      tendsto_one_add_rho
  have hpoleRe :=
    (Complex.continuous_re.tendsto (Real.eulerMascheroniConstant : ℂ)).comp hpoleComplex
  have hpole : Tendsto (fun rho : ℝ ↦ zetaOnePlus rho - rho⁻¹)
      rhoDownZero (nhds Real.eulerMascheroniConstant) := by
    apply hpoleRe.congr'
    filter_upwards [self_mem_nhdsWithin] with rho hrho
    have hrho0 : 0 < rho := hrho
    rw [zetaOnePlus_eq_re_riemannZeta rho hrho0]
    simp
  refine ⟨by simpa only [zpow_neg_one] using hpole, ?_⟩
  have hrhoZero : Tendsto (fun rho : ℝ ↦ rho) rhoDownZero (nhds 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hscaled : Tendsto (fun rho : ℝ ↦ rho * zetaOnePlus rho)
      rhoDownZero (nhds 1) := by
    have hone : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) rhoDownZero (nhds 1) :=
      tendsto_const_nhds
    have h := (hrhoZero.mul hpole).add hone
    simpa using h.congr' (by
      filter_upwards [self_mem_nhdsWithin] with rho hrho
      have hrho0 : 0 < rho := hrho
      field_simp
      ring)
  have hlog : Tendsto (fun rho : ℝ ↦ Real.log (rho * zetaOnePlus rho))
      rhoDownZero (nhds 0) := by
    simpa [Function.comp_def] using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hscaled
  apply hlog.congr'
  filter_upwards [self_mem_nhdsWithin] with rho hrho
  have hrho0 : 0 < rho := hrho
  have hzeta : 0 < zetaOnePlus rho := by
    rw [zetaOnePlus_eq_re_riemannZeta rho hrho0]
    exact riemannZeta_re_pos_of_one_lt (by linarith)
  rw [Real.log_mul (ne_of_gt hrho0) (ne_of_gt hzeta), zpow_neg_one,
    Real.log_inv]
  ring

@[expose] def rhoCorrection (rho : ℝ) (p : ℕ) : ℝ :=
  if p.Prime then
    -Real.log (1 - (p : ℝ).rpow (-(1 + rho))) -
      (p : ℝ).rpow (-(1 + rho))
  else 0

lemma rhoCorrection_tendsto (p : ℕ) :
    Tendsto (fun rho : ℝ ↦ rhoCorrection rho p) rhoDownZero
      (nhds (correctionSeq p)) := by
  by_cases hp : p.Prime
  · have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hx : ContinuousAt (fun rho : ℝ ↦ (p : ℝ).rpow (-(1 + rho))) 0 := by
      exact (Real.continuousAt_const_rpow hp0).comp
        ((continuousAt_const.add continuousAt_id).neg)
    have harg : 1 - (p : ℝ).rpow (-(1 + (0 : ℝ))) ≠ 0 := by
      have hpow : (p : ℝ).rpow (-(1 + (0 : ℝ))) = (p : ℝ)⁻¹ := by
        rw [show -(1 + (0 : ℝ)) = (-1 : ℝ) by ring]
        exact Real.rpow_neg_one _
      rw [hpow]
      have : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
      linarith
    have hcont : ContinuousAt (fun rho : ℝ ↦
        -Real.log (1 - (p : ℝ).rpow (-(1 + rho))) -
          (p : ℝ).rpow (-(1 + rho))) 0 := by
      have hsub : ContinuousAt (fun rho : ℝ ↦
          1 - (p : ℝ).rpow (-(1 + rho))) 0 :=
        (continuousAt_const : ContinuousAt (fun _ : ℝ ↦ (1 : ℝ)) 0).sub hx
      have hlog : ContinuousAt (fun rho : ℝ ↦
          Real.log (1 - (p : ℝ).rpow (-(1 + rho)))) 0 := by
        fun_prop (disch := assumption)
      exact hlog.neg.sub hx
    simpa [rhoDownZero, rhoCorrection, correctionSeq, correction, hp,
      Real.rpow_neg_one] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  · simpa [rhoCorrection, correctionSeq, hp] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (0 : ℝ)) rhoDownZero (nhds 0))

lemma correctionScalar_nonneg_mono {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y < 1) :
    0 ≤ -Real.log (1 - x) - x ∧
      -Real.log (1 - x) - x ≤ -Real.log (1 - y) - y := by
  have hx1 : x < 1 := hxy.trans_lt hy
  have hxpos : 0 < 1 - x := sub_pos.mpr hx1
  have hypos : 0 < 1 - y := sub_pos.mpr hy
  constructor
  · linarith [Real.log_le_sub_one_of_pos hxpos]
  · have hqpos : 0 < (1 - x) / (1 - y) := div_pos hxpos hypos
    have hlog := Real.one_sub_inv_le_log_of_pos hqpos
    have hfrac : y - x ≤ 1 - ((1 - x) / (1 - y))⁻¹ := by
      rw [inv_div]
      have heq : 1 - (1 - y) / (1 - x) = (y - x) / (1 - x) := by
        field_simp
        ring
      rw [heq, le_div_iff₀ hxpos]
      nlinarith
    rw [Real.log_div hxpos.ne' hypos.ne'] at hlog
    linarith

lemma primeZetaCorrection_nonneg_le (rho : ℝ) (hrho : 0 < rho) (p : ℕ) :
    0 ≤ primeZetaCorrection rho p ∧
      primeZetaCorrection rho p ≤ correctionSeq p := by
  by_cases hp : p.Prime
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hp1 : (1 : ℝ) ≤ p := one_le_two.trans hp2
    have hp0 : 0 < (p : ℝ) := lt_of_lt_of_le zero_lt_two hp2
    have hx0 : 0 ≤ (p : ℝ).rpow (-(1 + rho)) :=
      Real.rpow_nonneg (le_of_lt hp0) _
    have hxy : (p : ℝ).rpow (-(1 + rho)) ≤ (p : ℝ)⁻¹ := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    have hy : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    simpa [primeZetaCorrection, correctionSeq, correction, hp] using
      correctionScalar_nonneg_mono hx0 hxy hy
  · simp [primeZetaCorrection, correctionSeq, hp]

lemma primeZetaCorrection_tendsto (p : ℕ) :
    Tendsto (fun rho : ℝ ↦ primeZetaCorrection rho p) rhoDownZero
      (nhds (correctionSeq p)) := by
  simpa [rhoCorrection, primeZetaCorrection] using rhoCorrection_tendsto p

lemma primeZetaCorrection_dominated (rho : ℝ) (hrho : 0 < rho) (p : ℕ) :
    ‖primeZetaCorrection rho p‖ ≤ ‖correctionSeq p‖ := by
  have h := primeZetaCorrection_nonneg_le rho hrho p
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h.1]
  exact h.2.trans_eq (abs_of_nonneg (h.1.trans h.2)).symm

lemma zetaOnePlus_coe_eq_riemannZeta (rho : ℝ) (hrho : 0 < rho) :
    (zetaOnePlus rho : ℂ) = riemannZeta (1 + rho : ℝ) := by
  have hs : 1 < ((1 + rho : ℝ) : ℂ).re := by simpa using hrho
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  unfold zetaOnePlus
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  by_cases hn : 1 ≤ n
  · simp only [if_pos hn]
    calc
      ((n : ℝ).rpow (-(1 + rho)) : ℂ) =
          (n : ℂ) ^ ((-(1 + rho) : ℝ) : ℂ) :=
        Complex.ofReal_cpow (Nat.cast_nonneg n) (-(1 + rho))
      _ = 1 / (n : ℂ) ^ ((1 + rho : ℝ) : ℂ) := by
        simpa only [Complex.ofReal_neg, one_div] using
          Complex.cpow_neg (n : ℂ) ((1 + rho : ℝ) : ℂ)
  · have hn0 : n = 0 := by omega
    subst n
    simp only [if_neg (by omega : ¬ 1 ≤ 0), Nat.cast_zero, Complex.ofReal_zero]
    rw [Complex.zero_cpow (by
      exact Complex.ofReal_ne_zero.mpr (by linarith : (1 + rho : ℝ) ≠ 0))]
    simp

lemma primeSeries_norm_summable (rho : ℝ) (hrho : 0 < rho) :
    Summable (fun p : ℕ ↦
      ‖if p.Prime then Real.rpow p (-(1 + rho)) else 0‖) := by
  have hsum : Summable (fun p : ℕ ↦ (p : ℝ).rpow (-(1 + rho))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  refine hsum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) ?_
  intro p
  by_cases hp : p.Prime
  · simp only [if_pos hp]
    have ha := abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) (-(1 + rho)))
    simpa only [Real.norm_eq_abs, Real.rpow_eq_pow] using ha.le
  · simp [hp, Real.rpow_nonneg]

lemma tsum_primes_eq_indicator (f : ℕ → ℝ) :
    (∑' p : Nat.Primes, f p) = ∑' p : ℕ, if p.Prime then f p else 0 := by
  unfold Nat.Primes
  calc
    (∑' p : {p : ℕ // p.Prime}, f p) =
        ∑' p : ℕ, ({p : ℕ | p.Prime} : Set ℕ).indicator f p :=
      tsum_subtype _ _
    _ = ∑' p : ℕ, if p.Prime then f p else 0 := by
      apply tsum_congr
      intro p
      simp [Set.indicator]

lemma eulerIdentityAt (corr : CorrectionOutput) (rho : ℝ) (hrho : 0 < rho) :
    PrimeZetaEulerIdentityAt rho := by
  have hzeta : 0 < zetaOnePlus rho := by
    rw [zetaOnePlus_eq_re_riemannZeta rho hrho]
    exact riemannZeta_re_pos_of_one_lt (by linarith)
  have hprime := primeSeries_norm_summable rho hrho
  have hcorr : Summable (fun p : ℕ ↦ ‖primeZetaCorrection rho p‖) :=
    corr.convergence.1.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (primeZetaCorrection_dominated rho hrho)
  refine ⟨hrho, hzeta, hprime, hcorr, ?_⟩
  let x : ℕ → ℝ := fun p ↦ (p : ℝ).rpow (-(1 + rho))
  have hx0 (p : Nat.Primes) : 0 ≤ x p := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hxlt (p : Nat.Primes) : x p < 1 := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
    exact (Real.rpow_lt_one_iff_of_pos (by positivity)).2
      (Or.inl ⟨hp1, by linarith⟩)
  have hterm (p : Nat.Primes) :
      -Complex.log (1 - (p : ℂ) ^ (-((1 + rho : ℝ) : ℂ))) =
        ((-Real.log (1 - x p) : ℝ) : ℂ) := by
    have hpow : (p : ℂ) ^ (-((1 + rho : ℝ) : ℂ)) = (x p : ℂ) := by
      simpa [x, Complex.ofReal_neg] using
        (Complex.ofReal_cpow (Nat.cast_nonneg (p : ℕ)) (-(1 + rho))).symm
    rw [hpow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      ← Complex.ofReal_log (by linarith [hxlt p]), Complex.ofReal_neg]
  have hEuler := riemannZeta_eulerProduct_exp_log
    (s := ((1 + rho : ℝ) : ℂ)) (by simpa using hrho)
  have hEulerReal :
      Real.exp (∑' p : Nat.Primes, -Real.log (1 - x p)) = zetaOnePlus rho := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_exp]
    calc
      Complex.exp ((∑' p : Nat.Primes, -Real.log (1 - x p) : ℝ) : ℂ) =
          Complex.exp (∑' p : Nat.Primes,
            -Complex.log (1 - (p : ℂ) ^ (-((1 + rho : ℝ) : ℂ)))) := by
        congr 1
        rw [Complex.ofReal_tsum]
        exact tsum_congr fun p ↦ (hterm p).symm
      _ = riemannZeta (1 + rho : ℝ) := hEuler
      _ = (zetaOnePlus rho : ℂ) := (zetaOnePlus_coe_eq_riemannZeta rho hrho).symm
  have hlogFull :
      Real.log (zetaOnePlus rho) = ∑' p : Nat.Primes, -Real.log (1 - x p) := by
    rw [← hEulerReal, Real.log_exp]
  have hfull :
      (∑' p : Nat.Primes, -Real.log (1 - x p)) =
        primeZetaOnePlus rho + ∑' p : ℕ, primeZetaCorrection rho p := by
    calc
      (∑' p : Nat.Primes, -Real.log (1 - x p)) =
          ∑' p : ℕ, if p.Prime then -Real.log (1 - x p) else 0 :=
        tsum_primes_eq_indicator (fun p : ℕ ↦ -Real.log (1 - x p))
      _ = primeZetaOnePlus rho + ∑' p : ℕ, primeZetaCorrection rho p := by
        unfold primeZetaOnePlus
        rw [← hprime.of_norm.tsum_add hcorr.of_norm]
        apply tsum_congr
        intro p
        by_cases hp : p.Prime
        · simp [primeZetaOnePlus, primeZetaCorrection, hp, x]
        · simp [primeZetaOnePlus, primeZetaCorrection, hp]
  exact hlogFull.trans hfull

@[expose] def analyticBridge (corr : CorrectionOutput) : PrimeZetaAnalyticBridge corr.H where
  at_positive := eulerIdentityAt corr
  correction_pointwise := primeZetaCorrection_tendsto
  correction_dominated := primeZetaCorrection_dominated
  correction_tsum_tendsto := by
    have h := tendsto_tsum_of_dominated_convergence corr.convergence.1
      primeZetaCorrection_tendsto (by
        filter_upwards [self_mem_nhdsWithin] with rho hrho
        exact primeZetaCorrection_dominated rho hrho)
    simpa only [corr.convergence.2.1.tsum_eq] using h

@[expose] def epsilon0Fn (corr : CorrectionOutput) (rho : ℝ) : ℝ :=
  (Real.log (zetaOnePlus rho) - Real.log (rho ^ (-1 : ℤ))) -
    ((∑' p : ℕ, primeZetaCorrection rho p) - corr.H)

@[expose] def primeZetaResult (corr : CorrectionOutput) : PrimeZetaOutput corr.H where
  pole_normalization := poleNormalization
  epsilon0 := epsilon0Fn corr
  formula := by
    intro rho hrho
    have hEuler := (analyticBridge corr).at_positive rho hrho |>.euler_log_identity
    unfold epsilon0Fn
    linarith
  epsilon0_tendsto := by
    have hpole := poleNormalization.2
    have hcorr := (analyticBridge corr).correction_tsum_tendsto.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ corr.H) rhoDownZero (nhds corr.H))
    change Tendsto (fun rho : ℝ ↦
      (Real.log (zetaOnePlus rho) - Real.log (rho ^ (-1 : ℤ))) -
        ((∑' p : ℕ, primeZetaCorrection rho p) - corr.H)) rhoDownZero (nhds 0)
    simpa only [sub_self, sub_zero] using hpole.sub hcorr

@[expose] def result : Erdos448.DPMertens.Lowering.TASK_MSC_ZETA_Target := fun corr ↦
  { corr := corr
    analytic_bridge := analyticBridge corr
    pole := poleNormalization
    prime_zeta := primeZetaResult corr }

end

end Erdos448.DPMertens.Tasks.MSCZeta
