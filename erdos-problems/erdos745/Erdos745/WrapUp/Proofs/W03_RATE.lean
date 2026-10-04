module

public import Erdos745.WrapUp.Contracts

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section

namespace Erdos745.WrapUp.Proofs.W03_RATE

open Filter
open scoped Topology

noncomputable section

private def curve (x : ℝ) : ℝ := x * Real.exp (-x)

private def smallInv (z : ℝ) : ℝ :=
  sSup {x : ℝ | 0 ≤ x ∧ x ≤ 1 ∧ curve x ≤ z}

private lemma curve_deriv (x : ℝ) :
    HasStrictDerivAt curve (Real.exp (-x) * (1 - x)) x := by
  unfold curve
  convert (hasStrictDerivAt_id x).mul
    ((Real.hasStrictDerivAt_exp (-x)).comp x (hasStrictDerivAt_id x).neg) using 1 <;>
      simp [Function.comp_apply] <;> ring

private lemma curve_continuous : Continuous curve :=
  continuous_id.mul (Real.continuous_exp.comp continuous_neg)

private lemma curve_strictMono : StrictMonoOn curve (Set.Icc (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) curve_continuous.continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rcases hx with ⟨hx0, hx1⟩
  change 0 < deriv curve x
  rw [(curve_deriv x).hasDerivAt.deriv]
  exact mul_pos (Real.exp_pos _) (by linarith)

private lemma curve_strictAnti : StrictAntiOn curve (Set.Ici (1 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 1) curve_continuous.continuousOn
  intro x hx
  rw [interior_Ici] at hx
  have hx' : 1 < x := hx
  change deriv curve x < 0
  rw [(curve_deriv x).hasDerivAt.deriv]
  exact mul_neg_of_pos_of_neg (Real.exp_pos _) (by linarith)

private lemma curve_root (lam : ℝ) (hlam : 1 < lam) :
    ∃! y : ℝ, y ∈ Set.Ioo 0 1 ∧ curve y = curve lam := by
  have hpos : 0 < curve lam := mul_pos (by linarith) (Real.exp_pos _)
  have hlt : curve lam < curve 1 :=
    curve_strictAnti
      (show 1 ∈ Set.Ici (1 : ℝ) by exact (show (1 : ℝ) ≤ 1 from le_rfl))
      (show lam ∈ Set.Ici (1 : ℝ) by exact hlam.le) hlam
  have hc : curve lam ∈ Set.Icc (curve 0) (curve 1) := by
    constructor
    · simpa [curve] using! hpos.le
    · exact hlt.le
  rcases (intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
      curve_continuous.continuousOn hc) with ⟨y, hy, heq⟩
  have hy0 : 0 < y := by
    by_contra hn
    have : y = 0 := le_antisymm (not_lt.mp hn) hy.1
    subst y
    simp [curve] at heq
    linarith
  have hy1 : y < 1 := by
    by_contra hn
    have : y = 1 := le_antisymm hy.2 (not_lt.mp hn)
    subst y
    exact (ne_of_lt hlt) heq.symm
  refine ⟨y, ⟨⟨hy0, hy1⟩, heq⟩, ?_⟩
  intro z hz
  exact curve_strictMono.injOn ⟨hz.1.1.le, hz.1.2.le⟩
    ⟨hy0.le, hy1.le⟩ (hz.2.trans heq.symm)

private lemma smallInv_curve {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    smallInv (curve x) = x := by
  have hS : {z : ℝ | 0 ≤ z ∧ z ≤ 1 ∧ curve z ≤ curve x} = Set.Icc 0 x := by
    ext z
    constructor
    · intro hz
      exact ⟨hz.1, (curve_strictMono.le_iff_le ⟨hz.1, hz.2.1⟩
        ⟨hx.1.le, hx.2.le⟩).mp hz.2.2⟩
    · intro hz
      refine ⟨hz.1, hz.2.trans hx.2.le, ?_⟩
      exact curve_strictMono.monotoneOn ⟨hz.1, hz.2.trans hx.2.le⟩
        ⟨hx.1.le, hx.2.le⟩ hz.2
  unfold smallInv
  rw [hS]
  exact (isGreatest_Icc hx.1.le).csSup_eq

private lemma conjugate_eq_smallInv (lam : ℝ) :
    conjugate lam = smallInv (curve lam) := rfl

private lemma conjugate_spec (lam : ℝ) (hlam : 1 < lam) :
    0 < conjugate lam ∧ conjugate lam < 1 ∧
      curve (conjugate lam) = curve lam ∧
      ∀ y : ℝ, 0 < y → y < 1 → curve y = curve lam → y = conjugate lam := by
  rcases curve_root lam hlam with ⟨y, ⟨hy, heq⟩, huniq⟩
  have hconj : conjugate lam = y := by
    rw [conjugate_eq_smallInv, ← heq]
    exact smallInv_curve hy
  refine ⟨hconj.symm ▸ hy.1, hconj.symm ▸ hy.2, ?_, ?_⟩
  · simpa [hconj] using! heq
  · intro z hz0 hz1 hz
    have : z = y := huniq z ⟨⟨hz0, hz1⟩, hz⟩
    exact this.trans hconj.symm

private lemma rate_positive (x : ℝ) (hx : 0 < x) (hx1 : x ≠ 1) :
    0 < rate x := by
  unfold rate
  linarith [Real.log_lt_sub_one_of_pos hx hx1]

private lemma rate_eq_of_curve_eq {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : curve x = curve y) : rate x = rate y := by
  unfold rate
  have hl : Real.log x - x = Real.log y - y := by
    have hlog := congrArg Real.log h
    simp only [curve] at hlog
    rw [Real.log_mul hx.ne' (Real.exp_ne_zero _),
      Real.log_mul hy.ne' (Real.exp_ne_zero _), Real.log_exp, Real.log_exp] at hlog
    linarith
  linarith

private lemma rate_deriv {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt rate (1 - x⁻¹) x := by
  unfold rate
  convert! ((hasDerivAt_id x).sub (hasDerivAt_const x 1)).sub
    (Real.hasDerivAt_log hx) using 1 <;> ring

private lemma rate_strictAnti : StrictAntiOn rate (Set.Ioc (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 1)
  · unfold rate
    exact (continuousOn_id.sub continuousOn_const).sub
      ((Real.contDiffOn_log (n := (1 : WithTop ℕ∞))).continuousOn.mono
        (by intro x hx; exact hx.1.ne'))
  · intro x hx
    rw [interior_Ioc] at hx
    rcases hx with ⟨hx0, hx1⟩
    change deriv rate x < 0
    rw [(rate_deriv hx0.ne').deriv]
    exact sub_neg.mpr ((one_lt_inv₀ hx0).2 hx1)

private lemma rate_plus_bound (e : ℝ) (he0 : 0 ≤ e) (he1 : e < 1) :
    |rate (1 + e) - (e ^ 2 / 2 - e ^ 3 / 3)| ≤ e ^ 4 / (4 * (1 - e)) := by
  have heabs : ‖(e : ℂ)‖ = e := by
    simp [Complex.norm_real, abs_of_nonneg he0, Real.norm_eq_abs]
  have hnorm : ‖(e : ℂ)‖ < 1 := by rw [heabs]; exact he1
  have hpos : 0 ≤ 1 + e := by linarith
  have h := Complex.norm_log_sub_logTaylor_le 3 (z := (e : ℂ)) hnorm
  have hcast : 1 + (e : ℂ) = ((1 + e : ℝ) : ℂ) := by norm_num
  rw [hcast, ← Complex.ofReal_log hpos] at h
  norm_num [Complex.logTaylor, Finset.sum_range_succ, abs_of_nonneg he0] at h
  have hc : ((Real.log (1 + e) - (e - e ^ 2 / 2 + e ^ 3 / 3) : ℝ) : ℂ) =
      (Real.log (1 + e) : ℂ) -
        (1 * (e : ℂ) + -(e : ℂ) ^ 2 / 2 + 1 * (e : ℂ) ^ 3 / 3) := by
    push_cast
    ring
  have h' : |Real.log (1 + e) - (e - e ^ 2 / 2 + e ^ 3 / 3)| ≤
      e ^ 4 * (1 - e)⁻¹ / 4 := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hc]
    simpa only [one_mul] using! h
  rw [show rate (1 + e) - (e ^ 2 / 2 - e ^ 3 / 3) =
      -(Real.log (1 + e) - (e - e ^ 2 / 2 + e ^ 3 / 3)) by
        unfold rate; ring, abs_neg]
  convert h' using 1 <;> field_simp

private lemma rate_minus_bound (e : ℝ) (he0 : 0 ≤ e) (he1 : e < 1) :
    |rate (1 - e) - (e ^ 2 / 2 + e ^ 3 / 3)| ≤ e ^ 4 / (4 * (1 - e)) := by
  have heabs : ‖((-e : ℝ) : ℂ)‖ = e := by
    simp [Complex.norm_real, abs_of_nonneg he0, Real.norm_eq_abs]
  have hnorm : ‖((-e : ℝ) : ℂ)‖ < 1 := by rw [heabs]; exact he1
  have hpos : 0 ≤ 1 - e := by linarith
  have h := Complex.norm_log_sub_logTaylor_le 3 (z := ((-e : ℝ) : ℂ)) hnorm
  have hcast : 1 + ((-e : ℝ) : ℂ) = ((1 - e : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, ← Complex.ofReal_log hpos] at h
  norm_num [Complex.logTaylor, Finset.sum_range_succ, abs_of_nonneg he0] at h
  have hc : ((Real.log (1 - e) - (-e - e ^ 2 / 2 - e ^ 3 / 3) : ℝ) : ℂ) =
      (Real.log (1 - e) : ℂ) -
        (-(1 * (e : ℂ)) + -(e : ℂ) ^ 2 / 2 + 1 * (-(e : ℂ)) ^ 3 / 3) := by
    push_cast
    ring
  have h' : |Real.log (1 - e) - (-e - e ^ 2 / 2 - e ^ 3 / 3)| ≤
      e ^ 4 * (1 - e)⁻¹ / 4 := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, hc]
    simpa only [one_mul] using! h
  rw [show rate (1 - e) - (e ^ 2 / 2 + e ^ 3 / 3) =
      -(Real.log (1 - e) - (-e - e ^ 2 / 2 - e ^ 3 / 3)) by
        unfold rate; ring, abs_neg]
  convert h' using 1 <;> field_simp

private lemma remainder_unit_bound {e : ℝ} (he0 : 0 ≤ e) (he : e < 1 / 8) :
    e ^ 4 / (4 * (1 - e)) ≤ e ^ 4 := by
  have hden : 0 < 4 * (1 - e) := by linarith
  rw [div_le_iff₀ hden]
  nlinarith [pow_nonneg he0 4]

private lemma compare_rates (e : ℝ) (he0 : 0 < e) (he : e < 1 / 8) :
    rate (1 + e) < rate (1 - e) ∧ rate (1 - e / 2) < rate (1 + e) := by
  have he1 : e < 1 := lt_trans he (by norm_num)
  have hehalf1 : e / 2 < 1 := by linarith
  have hp := (rate_plus_bound e he0.le he1).trans (remainder_unit_bound he0.le he)
  have hm := (rate_minus_bound e he0.le he1).trans (remainder_unit_bound he0.le he)
  have hmh := (rate_minus_bound (e / 2) (by positivity) hehalf1).trans
    (remainder_unit_bound (by positivity) (by linarith))
  rw [abs_le] at hp hm hmh
  have hdiff : 0 < e ^ 3 * (2 / 3 - 2 * e) :=
    mul_pos (pow_pos he0 3) (by norm_num at he ⊢; linarith)
  have hdiff2 : 0 < e ^ 2 * (3 / 8 - (3 / 8) * e - (17 / 16) * e ^ 2) := by
    apply mul_pos (pow_pos he0 2)
    have hconst : 0 < (3 / 8 : ℝ) - (3 / 8) * (1 / 8) - (17 / 16) * (1 / 8) ^ 2 := by
      norm_num
    nlinarith [sq_nonneg (e - 1 / 8)]
  constructor <;> nlinarith

set_option maxHeartbeats 800000 in
private lemma delta_algebra (e d Ap Am : ℝ) (he0 : 0 < e) (he : e < 1 / 8)
    (hdlo : e / 2 ≤ d) (hdhi : d ≤ e)
    (hp : |Ap - (e ^ 2 / 2 - e ^ 3 / 3)| ≤ e ^ 4)
    (hm : |Am - (d ^ 2 / 2 + d ^ 3 / 3)| ≤ d ^ 4) (heq : Am = Ap) :
    |d - e| ≤ 2 * e ^ 2 ∧ |d - e + 2 * e ^ 2 / 3| ≤ 6 * e ^ 3 := by
  have hd0 : 0 < d := lt_of_lt_of_le (half_pos he0) hdlo
  rw [abs_le] at hp hm
  have hd2 : d ^ 2 ≤ e ^ 2 := by nlinarith
  have hd3 : d ^ 3 ≤ e ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg d) (sub_nonneg.mpr hdhi)]
  have hd4 : d ^ 4 ≤ e ^ 4 := by nlinarith [sq_nonneg (d ^ 2 - e ^ 2)]
  let rp := Ap - (e ^ 2 / 2 - e ^ 3 / 3)
  let rm := Am - (d ^ 2 / 2 + d ^ 3 / 3)
  have hrp : -e ^ 4 ≤ rp ∧ rp ≤ e ^ 4 := hp
  have hrm : -d ^ 4 ≤ rm ∧ rm ≤ d ^ 4 := hm
  have hid : (d ^ 2 - e ^ 2) / 2 + (d ^ 3 + e ^ 3) / 3 + rm - rp = 0 := by
    dsimp [rp, rm]
    linarith
  have he3 : 0 < e ^ 3 := pow_pos he0 3
  have hmain : e ^ 2 - d ^ 2 ≤ 2 * e ^ 3 := by
    have hcoef : 0 ≤ e ^ 3 * (2 - (4 / 3 + 2 * e)) := by
      apply mul_nonneg he3.le
      norm_num at he ⊢
      linarith
    nlinarith
  have hu_nonneg : 0 ≤ e - d := sub_nonneg.mpr hdhi
  have hu : e - d ≤ (4 / 3) * e ^ 2 := by
    have hprod : (e - d) * (e + d) ≤ 2 * e ^ 3 := by nlinarith
    have hsum : 3 * e / 2 ≤ e + d := by linarith
    nlinarith [mul_nonneg hu_nonneg (sub_nonneg.mpr hsum)]
  constructor
  · rw [abs_of_nonpos (sub_nonpos.mpr hdhi)]
    nlinarith
  · have hu2 : (d - e) ^ 2 ≤ (16 / 9) * e ^ 4 := by nlinarith
    have hcubediff : |d ^ 3 - e ^ 3| ≤ 4 * e ^ 4 := by
      rw [abs_of_nonpos (sub_nonpos.mpr hd3)]
      nlinarith
    rw [abs_le] at hcubediff ⊢
    have he5 : e ^ 5 ≤ e ^ 4 / 8 := by
      have hnon := mul_nonneg (pow_nonneg he0.le 4)
        (sub_nonneg.mpr (le_of_lt he))
      nlinarith
    have hid2 : e * (d - e + 2 * e ^ 2 / 3) =
        -(d - e) ^ 2 / 2 - (d ^ 3 - e ^ 3) / 3 - (rm - rp) := by
      nlinarith [hid]
    constructor
    · have hlow : -6 * e ^ 4 ≤ e * (d - e + 2 * e ^ 2 / 3) := by nlinarith
      nlinarith [mul_pos he0 (pow_pos he0 3)]
    · have hupp : e * (d - e + 2 * e ^ 2 / 3) ≤ 6 * e ^ 4 := by nlinarith
      nlinarith [mul_pos he0 (pow_pos he0 3)]

private lemma delta_estimates (e : ℝ) (he0 : 0 < e) (he : e < 1 / 8) :
    let d := 1 - conjugate (1 + e)
    e / 2 ≤ d ∧ d ≤ e ∧ |d - e| ≤ 2 * e ^ 2 ∧
      |d - e + 2 * e ^ 2 / 3| ≤ 6 * e ^ 3 := by
  let d := 1 - conjugate (1 + e)
  have hlam : 1 < 1 + e := by linarith
  obtain ⟨hy0, hy1, hcurve, _⟩ := conjugate_spec (1 + e) hlam
  have hd0 : 0 < d := by dsimp [d]; linarith
  have hd1 : d < 1 := by dsimp [d]; linarith
  have hrate : rate (1 - d) = rate (1 + e) := by
    have hpos : 0 < 1 + e := by linarith
    have := rate_eq_of_curve_eq hy0 hpos hcurve
    simpa [d] using! this
  have hcmp := compare_rates e he0 he
  have hdhi : d ≤ e := by
    by_contra hn
    have hde : e < d := lt_of_not_ge hn
    have hye : 1 - d < 1 - e := by linarith
    have hleft : 1 - d ∈ Set.Ioc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hright : 1 - e ∈ Set.Ioc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hr := rate_strictAnti hleft hright hye
    linarith
  have hdlo : e / 2 ≤ d := by
    by_contra hn
    have hde : d < e / 2 := lt_of_not_ge hn
    have hleft : 1 - e / 2 ∈ Set.Ioc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hright : 1 - d ∈ Set.Ioc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hr := rate_strictAnti hleft hright (by linarith)
    linarith
  have he1 : e < 1 := lt_trans he (by norm_num)
  have hdsmall : d < 1 / 8 := lt_of_le_of_lt hdhi he
  have hp := (rate_plus_bound e he0.le he1).trans (remainder_unit_bound he0.le he)
  have hm := (rate_minus_bound d hd0.le hd1).trans
    (remainder_unit_bound hd0.le hdsmall)
  have halg := delta_algebra e d (rate (1 + e)) (rate (1 - d))
    he0 he hdlo hdhi hp hm hrate
  exact ⟨hdlo, hdhi, halg.1, halg.2⟩

private lemma smallInv_deriv {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasStrictDerivAt smallInv (Real.exp (-x) * (1 - x))⁻¹ (curve x) := by
  apply (curve_deriv x).to_local_left_inverse
  · exact mul_ne_zero (Real.exp_ne_zero _) (by linarith [hx.2])
  · filter_upwards [isOpen_Ioo.eventually_mem hx] with z hz
    exact smallInv_curve hz

private lemma simplify_conjugate_deriv {lam y : ℝ} (hlam : 1 < lam)
    (hy0 : 0 < y) (hy1 : y < 1) (hcurve : curve y = curve lam) :
    (Real.exp (-y) * (1 - y))⁻¹ * (Real.exp (-lam) * (1 - lam)) =
      y * (1 - lam) / (lam * (1 - y)) := by
  have hlam0 : lam ≠ 0 := ne_of_gt (lt_trans zero_lt_one hlam)
  have hyden : Real.exp (-y) * (1 - y) ≠ 0 :=
    mul_ne_zero (Real.exp_ne_zero _) (by linarith)
  have hexp : Real.exp (-lam) = y * Real.exp (-y) / lam := by
    apply (eq_div_iff hlam0).2
    unfold curve at hcurve
    linarith
  rw [hexp]
  field_simp

private lemma conjugate_hasStrictDerivAt (lam : ℝ) (hlam : 1 < lam) :
    HasStrictDerivAt conjugate
      (conjugate lam * (1 - lam) / (lam * (1 - conjugate lam))) lam := by
  obtain ⟨hy0, hy1, hcurve, _⟩ := conjugate_spec lam hlam
  rw [show conjugate = fun z => smallInv (curve z) by funext z; rfl]
  have hs : HasStrictDerivAt smallInv
      (Real.exp (-conjugate lam) * (1 - conjugate lam))⁻¹ (curve lam) := by
    simpa only [hcurve] using! smallInv_deriv ⟨hy0, hy1⟩
  convert! hs.comp lam (curve_deriv lam) using 1
  rw [conjugate_eq_smallInv]
  exact (simplify_conjugate_deriv hlam hy0 hy1 hcurve).symm

private def giantSlope (lam : ℝ) : ℝ :=
  conjugate lam * (lam - conjugate lam) / (lam ^ 2 * (1 - conjugate lam))

private lemma giant_hasStrictDerivAt (lam : ℝ) (hlam : 1 < lam) :
    HasStrictDerivAt giantFraction (giantSlope lam) lam := by
  obtain ⟨hy0, hy1, _, _⟩ := conjugate_spec lam hlam
  have hlam0 : lam ≠ 0 := by linarith
  have hyden : 1 - conjugate lam ≠ 0 := by linarith
  unfold giantFraction giantSlope
  convert! (hasStrictDerivAt_const lam 1).sub
    ((conjugate_hasStrictDerivAt lam hlam).div (hasStrictDerivAt_id lam) hlam0) using 1
  simp only [id_eq]
  field_simp
  ring

private lemma giant_differentiableOn : DifferentiableOn ℝ giantFraction (Set.Ioi 1) := by
  intro lam hlam
  exact (giant_hasStrictDerivAt lam hlam).hasDerivAt.differentiableAt.differentiableWithinAt

private lemma conjugate_continuousOn : ContinuousOn conjugate (Set.Ioi (1 : ℝ)) := by
  intro lam hlam
  exact (conjugate_hasStrictDerivAt lam hlam).hasDerivAt.continuousAt.continuousWithinAt

private lemma giantSlope_continuousOn : ContinuousOn giantSlope (Set.Ioi (1 : ℝ)) := by
  unfold giantSlope
  apply (conjugate_continuousOn.mul (continuousOn_id.sub conjugate_continuousOn)).div
    ((continuousOn_id.pow 2).mul (continuousOn_const.sub conjugate_continuousOn))
  intro x hx
  have hx' : 1 < x := hx
  have hx0 : id x ≠ 0 := by
    simpa only [id_eq] using! ne_of_gt (lt_trans zero_lt_one hx')
  have hy1 := (conjugate_spec x hx').2.1
  apply mul_ne_zero (pow_ne_zero _ hx0)
  simpa only [Pi.sub_apply] using! ne_of_gt (sub_pos.mpr hy1)

private lemma giant_deriv_continuousOn :
    ContinuousOn (deriv giantFraction) (Set.Ioi (1 : ℝ)) := by
  apply giantSlope_continuousOn.congr
  intro lam hlam
  exact (giant_hasStrictDerivAt lam hlam).hasDerivAt.deriv

private lemma giant_algebra_bound (e d : ℝ) (he0 : 0 < e) (he : e < 1 / 8)
    (hw : |d - e + 2 * e ^ 2 / 3| ≤ 6 * e ^ 3) :
    |(e + d) / (1 + e) - (2 * e - 8 * e ^ 2 / 3)| ≤ 9 * e ^ 3 := by
  have hden : 0 < 1 + e := by linarith
  have hid : (e + d) / (1 + e) - (2 * e - 8 * e ^ 2 / 3) =
      (d - e + 2 * e ^ 2 / 3 + 8 * e ^ 3 / 3) / (1 + e) := by
    field_simp
    ring
  rw [hid, abs_le] at ⊢
  rw [abs_le] at hw
  constructor
  · rw [le_div_iff₀ hden]
    nlinarith [mul_pos he0 (pow_pos he0 2)]
  · rw [div_le_iff₀ hden]
    nlinarith [mul_pos he0 (pow_pos he0 2)]

private lemma ratio_bound (e d : ℝ) (he : 0 < e) (hd : e / 2 ≤ d)
    (h : |d - e| ≤ 2 * e ^ 2) : |e / d - 1| ≤ 4 * e := by
  have hd0 : 0 < d := lt_of_lt_of_le (half_pos he) hd
  have hid : e / d - 1 = (e - d) / d := by field_simp
  rw [hid, abs_div, abs_of_pos hd0]
  rw [div_le_iff₀ hd0]
  have hab : |e - d| ≤ 2 * e ^ 2 := by simpa [abs_sub_comm] using! h
  nlinarith

private lemma giant_deriv_tendsto :
    Tendsto (fun e : ℝ => deriv giantFraction (1 + e))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 2) := by
  let d : ℝ → ℝ := fun e => 1 - conjugate (1 + e)
  have hsmall : ∀ᶠ e : ℝ in nhdsWithin 0 (Set.Ioi 0), e < 1 / 8 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 8 by norm_num)).filter_mono inf_le_left
  have hpos : ∀ᶠ e : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < e := self_mem_nhdsWithin
  have hest : ∀ᶠ e : ℝ in nhdsWithin 0 (Set.Ioi 0),
      e / 2 ≤ d e ∧ d e ≤ e ∧ |d e - e| ≤ 2 * e ^ 2 := by
    filter_upwards [hsmall, hpos] with e he he0
    exact ⟨(delta_estimates e he0 he).1, (delta_estimates e he0 he).2.1,
      (delta_estimates e he0 he).2.2.1⟩
  have he_tendsto : Tendsto (fun e : ℝ => e) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) :=
    tendsto_id'.2 inf_le_left
  have hd_tendsto : Tendsto d (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    apply squeeze_zero'
    · filter_upwards [hest, hpos] with e he _
      linarith
    · filter_upwards [hest] with e he
      exact he.2.1
    · exact he_tendsto
  have hratio : Tendsto (fun e => e / d e) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero_norm'
    · filter_upwards [hest, hpos] with e he he0
      simpa [Real.norm_eq_abs] using! ratio_bound e (d e) he0 he.1 he.2.2
    · simpa using! (he_tendsto.const_mul 4)
  have hfirst : Tendsto (fun e => (1 - d e) / (1 + e) ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 1) := by
    simpa using! ((tendsto_const_nhds.sub hd_tendsto).div
      ((tendsto_const_nhds.add he_tendsto).pow 2)
      (by norm_num : (1 + (0 : ℝ)) ^ 2 ≠ 0))
  have hsecond : Tendsto (fun e => 1 + e / d e)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 2) := by
    convert tendsto_const_nhds.add hratio using 1 <;> norm_num
  have hformula : ∀ᶠ e : ℝ in nhdsWithin 0 (Set.Ioi 0),
      deriv giantFraction (1 + e) =
        ((1 - d e) / (1 + e) ^ 2) * (1 + e / d e) := by
    filter_upwards [hest, hpos] with e he he0
    have hd0 : d e ≠ 0 := ne_of_gt (lt_of_lt_of_le (half_pos he0) he.1)
    have hcden : 1 - conjugate (1 + e) ≠ 0 := by simpa [d] using! hd0
    have hslope := (giant_hasStrictDerivAt (1 + e) (by linarith)).hasDerivAt.deriv
    rw [hslope]
    unfold giantSlope d
    field_simp [hcden]
    ring
  simpa using! (hfirst.mul hsecond).congr' (Filter.EventuallyEq.symm hformula)

private lemma uniform_bounds :
    ∃ C e0 : ℝ, 0 < C ∧ 0 < e0 ∧ e0 < 1 ∧
      ∀ e : ℝ, 0 < e → e < e0 →
        |rate (1 + e) - (e ^ 2 / 2 - e ^ 3 / 3)| ≤ C * e ^ 4 ∧
        |rate (1 - e) - (e ^ 2 / 2 + e ^ 3 / 3)| ≤ C * e ^ 4 ∧
        |conjugate (1 + e) - (1 - e + 2 * e ^ 2 / 3)| ≤ C * e ^ 3 ∧
        |giantFraction (1 + e) - (2 * e - 8 * e ^ 2 / 3)| ≤ C * e ^ 3 := by
  refine ⟨9, 1 / 8, by norm_num, by norm_num, by norm_num, ?_⟩
  intro e he0 he
  have he1 : e < 1 := lt_trans he (by norm_num)
  have hp := (rate_plus_bound e he0.le he1).trans (remainder_unit_bound he0.le he)
  have hm := (rate_minus_bound e he0.le he1).trans (remainder_unit_bound he0.le he)
  let d := 1 - conjugate (1 + e)
  have hdelta := delta_estimates e he0 he
  have hconj : |conjugate (1 + e) - (1 - e + 2 * e ^ 2 / 3)| ≤ 9 * e ^ 3 := by
    have hid : conjugate (1 + e) - (1 - e + 2 * e ^ 2 / 3) =
        -(d - e + 2 * e ^ 2 / 3) := by dsimp [d]; ring
    rw [hid, abs_neg]
    exact hdelta.2.2.2.trans (by nlinarith [pow_pos he0 3])
  have hgiant : |giantFraction (1 + e) - (2 * e - 8 * e ^ 2 / 3)| ≤ 9 * e ^ 3 := by
    have hid : giantFraction (1 + e) = (e + d) / (1 + e) := by
      unfold giantFraction
      dsimp [d]
      field_simp
      ring
    rw [hid]
    exact giant_algebra_bound e d he0 he hdelta.2.2.2
  exact ⟨hp.trans (by nlinarith [pow_nonneg he0.le 4]),
    hm.trans (by nlinarith [pow_nonneg he0.le 4]), hconj, hgiant⟩

theorem result : RateStatement := by
  refine ⟨rate_positive, ?_, giant_differentiableOn, giant_deriv_continuousOn,
    giant_deriv_tendsto, uniform_bounds⟩
  intro lam hlam
  obtain ⟨hy0, hy1, hcurve, huniq⟩ := conjugate_spec lam hlam
  have hrate := rate_eq_of_curve_eq hy0 (lt_trans zero_lt_one hlam) hcurve
  exact ⟨hy0, hy1, hcurve, hrate, huniq⟩

end

end Erdos745.WrapUp.Proofs.W03_RATE
