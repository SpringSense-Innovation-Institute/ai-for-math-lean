module

import all Mathlib.Basic.Real.Basic
public import Erdos448.dependencies.«DP-MERTENS».stage6.FrozenTaskContracts

public section

set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory Real Asymptotics Complex
open scoped Topology

namespace Erdos448.DPMertens.Tasks.MSCExpInt

noncomputable section

open Erdos448.DPMertens
open Erdos448.DPMertens.Lowering

@[expose] def expTail (z : ℝ) : ℝ :=
  ∫ x : ℝ in Ioi z, Real.exp (-x) / x

lemma integrableOn_log_mul_exp_neg :
    IntegrableOn (fun t : ℝ => Real.log t * Real.exp (-t)) (Ioi 0) := by
  have hc : MellinConvergent
      (fun t : ℝ => Real.log t • (Real.exp (-t) : ℂ)) (1 : ℂ) := by
    refine (mellin_hasDerivAt_of_isBigO_rpow (E := ℂ) (a := 2) (b := 0)
      ?_ ?_ (by norm_num) ?_ (by norm_num)).1
    · refine (Continuous.continuousOn ?_).locallyIntegrableOn measurableSet_Ioi
      exact continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)
    · rw [← isBigO_norm_left]
      simp_rw [norm_real, isBigO_norm_left]
      simpa only [neg_one_mul] using
        (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one _).isBigO
    · simp_rw [neg_zero, Real.rpow_zero]
      refine isBigO_const_of_tendsto
        (?_ : Tendsto _ _ (𝓝 (1 : ℂ))) one_ne_zero
      rw [(by simp : (1 : ℂ) = Real.exp (-0))]
      exact (continuous_ofReal.comp
        (Real.continuous_exp.comp continuous_neg)).continuousWithinAt
  rw [MellinConvergent] at hc
  have hc' : IntegrableOn
      (fun t : ℝ => ((Real.log t * Real.exp (-t) : ℝ) : ℂ)) (Ioi 0) := by
    simpa using hc
  change Integrable (fun t : ℝ => Real.log t * Real.exp (-t))
    (volume.restrict (Ioi 0))
  simpa only [IntegrableOn, RCLike.re_eq_complex_re, Complex.ofReal_re] using hc'.re

lemma integral_log_mul_exp_neg :
    (∫ t : ℝ in Ioi 0, Real.log t * Real.exp (-t)) =
      -Real.eulerMascheroniConstant := by
  have hGI := Complex.hasDerivAt_GammaIntegral
    (s := (1 : ℂ)) (by norm_num)
  have heq : Complex.Gamma =ᶠ[𝓝 (1 : ℂ)] Complex.GammaIntegral := by
    have hre : Tendsto Complex.re (𝓝 (1 : ℂ)) (𝓝 ((1 : ℂ).re)) :=
      Complex.continuous_re.continuousAt
    have hzpos : ∀ᶠ z in 𝓝 (1 : ℂ), z.re ∈ Ioi (0 : ℝ) :=
      hre.eventually (Ioi_mem_nhds (by norm_num))
    filter_upwards [hzpos] with z hz
    exact Complex.Gamma_eq_integral hz
  have hu := (hGI.congr_of_eventuallyEq heq).unique
    Complex.hasDerivAt_Gamma_one
  norm_num at hu
  have hur := congrArg Complex.re hu
  have hreal := integrableOn_log_mul_exp_neg
  have hcu : Integrable
      (fun t : ℝ => ((t : ℂ) ^ (0 : ℂ) *
        ((Real.log t : ℂ) * Complex.exp (-(t : ℂ)))))
      (volume.restrict (Ioi 0)) := by
    have hof : Integrable
        (fun t : ℝ => ((Real.log t * Real.exp (-t) : ℝ) : ℂ))
        (volume.restrict (Ioi 0)) := hreal.ofReal
    refine hof.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Complex.cpow_zero, one_mul, ← Complex.ofReal_neg, ← Complex.ofReal_exp]
    norm_cast
  calc
    _ = ∫ t : ℝ, Complex.re ((t : ℂ) ^ (0 : ℂ) *
        ((Real.log t : ℂ) * Complex.exp (-(t : ℂ))))
        ∂volume.restrict (Ioi 0) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          rw [Complex.cpow_zero, one_mul, Complex.mul_re]
          simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
          rw [← Complex.ofReal_neg, Complex.exp_ofReal_re]
    _ = Complex.re (∫ t : ℝ, (t : ℂ) ^ (0 : ℂ) *
        ((Real.log t : ℂ) * Complex.exp (-(t : ℂ)))
        ∂volume.restrict (Ioi 0)) := integral_re hcu
    _ = _ := by simpa only [Complex.cpow_zero, one_mul, Complex.neg_re, Complex.ofReal_re] using hur

lemma integrableOn_exp_neg_div {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun x : ℝ => Real.exp (-x) / x) (Ioi z) := by
  refine integrable_of_isBigO_exp_neg one_pos ?_ ?_
  · refine (Real.continuous_exp.comp continuous_neg).continuousOn.div
      continuousOn_id ?_
    intro x hx
    exact (hz.trans_le (mem_Ici.mp hx)).ne'
  · rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := zero_lt_one.trans_le hx
    simp only [norm_eq_abs, one_mul, one_mul]
    rw [abs_div, abs_of_pos (Real.exp_pos _), abs_of_pos hx0,
      abs_of_pos (Real.exp_pos _)]
    simpa only [one_mul, neg_mul] using
      (div_le_self (Real.exp_pos (-x)).le (show 1 ≤ x from hx))

lemma tendsto_log_mul_neg_exp_atTop :
    Tendsto (fun x : ℝ => Real.log x * (-Real.exp (-x))) atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x ^ (1 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop one_pos).tendsto_div_nhds_zero
  have hexp := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 1 one_pos
  have hprod := hlog.mul hexp
  rw [zero_mul] at hprod
  have heq : (fun x : ℝ => Real.log x * (-Real.exp (-x))) =ᶠ[atTop]
      (fun x : ℝ => -((Real.log x / x ^ (1 : ℝ)) *
        (x ^ (1 : ℝ) * Real.exp (-1 * x)))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp only [Real.rpow_one, one_mul]
    field_simp
  simpa only [neg_zero] using hprod.neg.congr' heq.symm

lemma expTail_normalized_eq {z : ℝ} (hz : 0 < z) :
    expTail z + Real.log z =
      (∫ x : ℝ in Ioi z, Real.log x * Real.exp (-x)) +
        (1 - Real.exp (-z)) * Real.log z := by
  have hlogexp : IntegrableOn (fun x : ℝ => Real.log x * Real.exp (-x)) (Ioi z) :=
    integrableOn_log_mul_exp_neg.mono_set fun x hx => hz.trans (mem_Ioi.mp hx)
  have htail := integrableOn_exp_neg_div hz
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := z) (a' := Real.log z * (-Real.exp (-z))) (b' := 0)
    (u := Real.log) (u' := fun x : ℝ => x⁻¹)
    (v := fun x : ℝ => -Real.exp (-x)) (v' := fun x : ℝ => Real.exp (-x))
    (fun x hx => Real.hasDerivAt_log (hz.trans (mem_Ioi.mp hx)).ne')
    (fun x _ => by simpa [Function.comp_def, Pi.neg_def] using (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x) |>.neg)
    (by simpa only [Pi.mul_def] using hlogexp)
    (by
      have hn := htail.neg
      apply hn.congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      dsimp
      field_simp)
    (by
      exact (((Real.continuousAt_log hz.ne').mul
        ((Real.continuous_exp.comp continuous_neg).continuousAt.neg)).tendsto).mono_left
          inf_le_left)
    tendsto_log_mul_neg_exp_atTop
  have hnegint : (∫ x : ℝ in Ioi z, x⁻¹ * (-Real.exp (-x))) = -expTail z := by
    unfold expTail
    change (∫ x : ℝ, x⁻¹ * (-Real.exp (-x)) ∂volume.restrict (Ioi z)) =
      -(∫ x : ℝ, Real.exp (-x) / x ∂volume.restrict (Ioi z))
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with x
    rw [div_eq_mul_inv]
    ring
  rw [hnegint] at hibp
  rw [hibp]
  ring

lemma tendsto_integral_log_exp_Ioi :
    Tendsto (fun z : ℝ => ∫ x : ℝ in Ioi z,
      Real.log x * Real.exp (-x)) rhoDownZero
      (𝓝 (-Real.eulerMascheroniConstant)) := by
  have hmeasure : Tendsto (volume ∘ fun z : ℝ => Ioc 0 z)
      rhoDownZero (𝓝 0) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.mono_left
      (show rhoDownZero ≤ 𝓝 (0 : ℝ) by exact inf_le_left)
    simpa [Function.comp_def, Real.volume_Ioc] using h
  let f : ℝ → ℝ := fun x => Real.log x * Real.exp (-x)
  have hind : Integrable (indicator (Ioi (0 : ℝ)) f) volume := by
    rw [integrable_indicator_iff measurableSet_Ioi]
    exact integrableOn_log_mul_exp_neg
  have hsmallInd := hind.tendsto_setIntegral_nhds_zero hmeasure
  have hsmall : Tendsto (fun z : ℝ => ∫ x : ℝ in Ioc 0 z,
      Real.log x * Real.exp (-x)) rhoDownZero (𝓝 0) := by
    apply hsmallInd.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    symm
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    simp [f, mem_Ioi.mpr hx.1]
  have htotal : Tendsto (fun _ : ℝ => ∫ x : ℝ in Ioi (0 : ℝ),
      Real.log x * Real.exp (-x)) rhoDownZero
      (𝓝 (∫ x : ℝ in Ioi (0 : ℝ), Real.log x * Real.exp (-x))) :=
    tendsto_const_nhds
  have hlim := htotal.sub hsmall
  rw [integral_log_mul_exp_neg, sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hzpos : 0 < z := hz
  have hsubset : Ioc 0 z ⊆ Ioi (0 : ℝ) := fun _ hx => hx.1
  have hdiff := integral_diff measurableSet_Ioc integrableOn_log_mul_exp_neg hsubset
  have hset : Ioi (0 : ℝ) \ Ioc 0 z = Ioi z := by
    ext x
    simp only [mem_diff, mem_Ioi, mem_Ioc, not_and_or, not_lt, not_le]
    constructor
    · rintro ⟨hx0, hxle | hxgt⟩
      · exact (not_lt_of_ge hxle hx0).elim
      · exact hxgt
    · intro hx
      exact ⟨hzpos.trans hx, Or.inr hx⟩
  rw [hset] at hdiff
  rw [integral_log_mul_exp_neg] at hdiff
  exact hdiff.symm

lemma tendsto_exp_correction :
    Tendsto (fun z : ℝ => (1 - Real.exp (-z)) * Real.log z)
      rhoDownZero (𝓝 0) := by
  have hslope := (((hasDerivAt_id (0 : ℝ)).neg.exp).tendsto_slope_zero_right).neg
  have hratio : Tendsto (fun z : ℝ => (1 - Real.exp (-z)) / z)
      rhoDownZero (𝓝 1) := by
    have hslope' : Tendsto (fun z : ℝ => -(z⁻¹ * (Real.exp (-z) - 1)))
        rhoDownZero (𝓝 1) := by
      simpa [slope, rhoDownZero] using hslope
    have heq : (fun z : ℝ => -(z⁻¹ * (Real.exp (-z) - 1))) =ᶠ[rhoDownZero]
        (fun z : ℝ => (1 - Real.exp (-z)) / z) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      field_simp [(mem_Ioi.mp hz).ne']
      ring
    exact hslope'.congr' heq
  have hlogz : Tendsto (fun z : ℝ => z * Real.log z)
      rhoDownZero (𝓝 0) := by
    simpa [rhoDownZero, mul_comm] using
      (tendsto_log_mul_rpow_nhdsGT_zero (r := 1) one_pos)
  have hp := hratio.mul hlogz
  rw [one_mul] at hp
  apply hp.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  field_simp [(mem_Ioi.mp hz).ne']

lemma tendsto_expTail_normalized :
    Tendsto (fun z : ℝ => expTail z + Real.log z)
      rhoDownZero (𝓝 (-Real.eulerMascheroniConstant)) := by
  have hsum := tendsto_integral_log_exp_Ioi.add tendsto_exp_correction
  rw [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (expTail_normalized_eq hz).symm

lemma exp_image_Ioi_log {G : ℝ} (hG : 0 < G) :
    Real.exp '' Ioi (Real.log G) = Ioi G := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [mem_Ioi, ← Real.exp_log hG, Real.exp_lt_exp]
    exact mem_Ioi.mp hu
  · intro ht
    have htG : G < t := mem_Ioi.mp ht
    have ht0 : 0 < t := hG.trans htG
    refine ⟨Real.log t, ?_, Real.exp_log ht0⟩
    exact Real.strictMonoOn_log hG ht0 htG

lemma primeTailIntegral_eq_logIntegral {G rho : ℝ} (hG : 1 < G) :
    primeTailIntegral G rho =
      ∫ u : ℝ in Ioi (Real.log G), Real.exp (-rho * u) / u := by
  unfold primeTailIntegral
  rw [← exp_image_Ioi_log (zero_lt_one.trans hG)]
  rw [integral_image_eq_integral_abs_deriv_smul
    (f := Real.exp) (f' := Real.exp) measurableSet_Ioi
    (fun u _ => Real.hasDerivAt_exp u |>.hasDerivWithinAt)
    (fun _ _ _ _ h => Real.exp_eq_exp.mp h)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  have hlogG : 0 < Real.log G := Real.log_pos (by linarith)
  have hu0 : 0 < u := hlogG.trans (mem_Ioi.mp hu)
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos u), smul_eq_mul]
  change Real.exp u * (1 / ((Real.exp u) ^ (1 + rho) * Real.log (Real.exp u))) =
    Real.exp (-rho * u) / u
  rw [Real.rpow_def_of_pos (Real.exp_pos u) (1 + rho), Real.log_exp]
  field_simp [hu0.ne', Real.exp_ne_zero]
  rw [← Real.exp_add]
  congr 1
  ring

lemma logIntegral_eq_expTail {G rho : ℝ} (hG : 1 < G) (hrho : 0 < rho) :
    (∫ u : ℝ in Ioi (Real.log G), Real.exp (-rho * u) / u) =
      expTail (rho * Real.log G) := by
  unfold expTail
  have himage : (fun u : ℝ => rho * u) '' Ioi (Real.log G) =
      Ioi (rho * Real.log G) := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hp := mul_pos hrho (sub_pos.mpr (mem_Ioi.mp hu))
      rw [mul_sub] at hp
      exact mem_Ioi.mpr (by linarith)
    · intro hv
      have hcancel : rho * (rho⁻¹ * v) = v := by field_simp
      refine ⟨rho⁻¹ * v, ?_, ?_⟩
      · rw [mem_Ioi]
        have hp := mul_pos (inv_pos.mpr hrho) (sub_pos.mpr (mem_Ioi.mp hv))
        field_simp [hrho.ne'] at hp
        nlinarith
      · exact hcancel
  rw [← himage]
  symm
  rw [integral_image_eq_integral_abs_deriv_smul
    (f := fun u : ℝ => rho * u) (f' := fun _ : ℝ => rho) measurableSet_Ioi
    (fun u _ => by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id u).const_mul rho).hasDerivWithinAt)
    (fun x _ y _ hxy => by
      change rho * x = rho * y at hxy
      calc
        x = rho⁻¹ * (rho * x) := by field_simp
        _ = rho⁻¹ * (rho * y) := by rw [hxy]
        _ = y := by field_simp)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  have hlogG : 0 < Real.log G := Real.log_pos hG
  have hu0 : 0 < u := hlogG.trans (mem_Ioi.mp hu)
  simp only [abs_of_pos hrho, smul_eq_mul]
  field_simp [hrho.ne', hu0.ne']

lemma primeTailIntegral_eq_expTail {G rho : ℝ}
    (hG : 1 < G) (hrho : 0 < rho) :
    primeTailIntegral G rho = expTail (rho * Real.log G) := by
  rw [primeTailIntegral_eq_logIntegral hG,
    logIntegral_eq_expTail hG hrho]

/-- The P-MSC-05 exponential-integral endpoint, with `G` fixed before the
one-sided limit in `rho`. -/
@[expose] def result : TASK_MSC_EXPINT_Target where
  epsilonG := fun G rho =>
    expTail (rho * Real.log G) + Real.log (rho * Real.log G) +
      Real.eulerMascheroniConstant
  formula := by
    intro G hG rho hrho
    have hG1 : 1 < G := by linarith
    have hlogG : 0 < Real.log G := Real.log_pos hG1
    rw [primeTailIntegral_eq_expTail hG1 hrho]
    rw [Real.log_mul hrho.ne' hlogG.ne']
    rw [show rho ^ (-1 : ℤ) = rho⁻¹ by simp, Real.log_inv]
    ring
  epsilonG_tendsto := by
    intro G hG
    have hG1 : 1 < G := by linarith
    have hlogG : 0 < Real.log G := Real.log_pos hG1
    have hscale : Tendsto (fun rho : ℝ => rho * Real.log G)
        rhoDownZero rhoDownZero := by
      unfold rhoDownZero
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have h : Tendsto (fun rho : ℝ => rho * Real.log G)
            (𝓝 0) (𝓝 0) := by
          simpa only [zero_mul, id_eq] using
            (tendsto_id.mul (tendsto_const_nhds :
              Tendsto (fun _ : ℝ => Real.log G) (𝓝 0) (𝓝 (Real.log G))))
        exact h.mono_left inf_le_left
      · filter_upwards [self_mem_nhdsWithin] with rho hrho
        exact mul_pos (mem_Ioi.mp hrho) hlogG
    have hn := tendsto_expTail_normalized.comp hscale
    have hout := hn.add_const Real.eulerMascheroniConstant
    simpa [Function.comp_def, add_assoc] using hout

end

end Erdos448.DPMertens.Tasks.MSCExpInt
