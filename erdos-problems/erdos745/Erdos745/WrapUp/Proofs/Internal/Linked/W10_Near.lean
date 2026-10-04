module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W10_Fixed

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


namespace Erdos745.WrapUp.Proofs.Internal.W10_GIANT_Near

noncomputable section
open Filter
open scoped Topology BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

open W10_GIANT_Numerics
open W10_GIANT_Coupling
open W10_GIANT_Concentration
open W10_GIANT_Exclusions
open W10_GIANT_Trees
open W10_GIANT_Sprinkling
open W10_GIANT_Bridges
open Erdos745.WrapUp.Proofs.W06_POISSON

private lemma near_cutoff_div_ne_zero {M : NatSeq} (hbare : bareSuper M) :
    Tendsto (fun n => (largeCutoff n : ℝ) /
      ((n : ℝ) * epsilon M n)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n =>
      (widthParameter M n) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      hbare.2.2.2
  have hupper : Tendsto (fun n =>
      2 * (widthParameter M n) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
    simpa using! hpow.const_mul 2
  apply squeeze_zero'
  · filter_upwards [bare_epsilon_pos (Or.inr hbare)] with n he
    positivity
  · filter_upwards [bare_epsilon_pos (Or.inr hbare),
      eventually_ge_atTop 1] with n he hn
    have hnpos : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h23pos : 0 < n23 n := n23_pos hnpos
    have h23cube := n23_cube hnpos
    have h23one : (1 : ℝ) ≤ n23 n := by nlinarith [sq_nonneg (n23 n - 1)]
    have hceil : (largeCutoff n : ℝ) ≤ n23 n + 1 :=
      (Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity) _)).le
    have hcut : (largeCutoff n : ℝ) ≤ 2 * n23 n := by linarith
    have hwpos : 0 < widthParameter M n := by
      dsimp [widthParameter]
      positivity
    have hbase : n23 n / ((n : ℝ) * epsilon M n) =
        (widthParameter M n) ^ (-(1 / 3 : ℝ)) := by
      calc
        n23 n / ((n : ℝ) * epsilon M n) =
            (n23 n * epsilon M n ^ 2) / widthParameter M n := by
          dsimp [widthParameter]
          field_simp [hnR.ne', he.ne']
        _ = (widthParameter M n) ^ (2 / 3 : ℝ) /
            widthParameter M n := by
              rw [← width_rpow_two_thirds hnpos he, Real.rpow_eq_pow]
        _ = (widthParameter M n) ^ ((2 / 3 : ℝ) - 1) := by
          rw [Real.rpow_sub hwpos, Real.rpow_one]
        _ = (widthParameter M n) ^ (-(1 / 3 : ℝ)) := by norm_num
    have hdiv := div_le_div_of_nonneg_right hcut
      (mul_nonneg hnR.le he.le)
    calc
      (largeCutoff n : ℝ) / ((n : ℝ) * epsilon M n) ≤
          (2 * n23 n) / ((n : ℝ) * epsilon M n) := hdiv
      _ = 2 * (widthParameter M n) ^ (-(1 / 3 : ℝ)) := by
        rw [← hbase]
        ring
  · exact hupper

private lemma near_sprinkle_correction_zero {M : NatSeq}
    (hbare : bareSuper M) :
    Tendsto (fun n => 2 * (sprinkleTime (1 / 16) n : ℝ) /
      ((n : ℝ) * epsilon M n)) atTop (𝓝 0) := by
  have hq := near_cutoff_div_ne_zero hbare
  have hu : Tendsto (fun n =>
      (1 / 8 : ℝ) * ((largeCutoff n : ℝ) /
        ((n : ℝ) * epsilon M n))) atTop (𝓝 0) := by
    simpa using! hq.const_mul (1 / 8 : ℝ)
  apply squeeze_zero'
  · filter_upwards [bare_epsilon_pos (Or.inr hbare)] with n he
    positivity
  · filter_upwards [bare_epsilon_pos (Or.inr hbare),
      eventually_gt_atTop 0] with n he hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have htime := sprinkleTime_le (1 / 16) (by norm_num) n
    have hden : 0 < (n : ℝ) * epsilon M n := mul_pos hnR he
    have hdiv := div_le_div_of_nonneg_right htime hden.le
    calc
      2 * (sprinkleTime (1 / 16) n : ℝ) /
          ((n : ℝ) * epsilon M n) =
          2 * ((sprinkleTime (1 / 16) n : ℝ) /
            ((n : ℝ) * epsilon M n)) := by ring
      _ ≤ 2 * (((1 / 16 : ℝ) * (largeCutoff n : ℝ)) /
          ((n : ℝ) * epsilon M n)) := by
        exact mul_le_mul_of_nonneg_left hdiv (by norm_num)
      _ = (1 / 8 : ℝ) * ((largeCutoff n : ℝ) /
          ((n : ℝ) * epsilon M n)) := by ring
  · exact hu

private lemma near_old_degree {M : NatSeq} (hbare : bareSuper M) :
    Tendsto (degree (fun n => M n - sprinkleTime (1 / 16) n))
      atTop (𝓝 1) := by
  have ht := sprinkleTime_div_n_tendsto_zero (1 / 16) (by norm_num)
  have hdiff : Tendsto
      (fun n => degree M n -
        2 * ((sprinkleTime (1 / 16) n : ℝ) / (n : ℝ)))
      atTop (𝓝 1) := by
    simpa using! hbare.2.2.1.sub (ht.const_mul 2)
  apply hdiff.congr'
  filter_upwards [sprinkleTime_le_M_eventually (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) ≤ 1 / 16) hbare.2.2.1] with n hle
  unfold degree
  rw [Nat.cast_sub hle]
  ring

private lemma near_old_excess_ratio {M : NatSeq} (hbare : bareSuper M) :
    Tendsto (fun n =>
      epsilon (fun j => M j - sprinkleTime (1 / 16) j) n /
        epsilon M n) atTop (𝓝 1) := by
  let M₀ : NatSeq := fun n => M n - sprinkleTime (1 / 16) n
  have hc := near_sprinkle_correction_zero hbare
  have hlim : Tendsto (fun n =>
      1 - 2 * (sprinkleTime (1 / 16) n : ℝ) /
        ((n : ℝ) * epsilon M n)) atTop (𝓝 1) := by
    simpa using! tendsto_const_nhds.sub hc
  apply hlim.congr'
  have hsmall := (tendsto_order.1 hc).2 (1 / 2) (by norm_num)
  filter_upwards [hsmall, bare_epsilon_pos (Or.inr hbare),
    hbare.2.1, sprinkleTime_le_M_eventually
      (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) ≤ 1 / 16) hbare.2.2.1,
    eventually_gt_atTop 0] with n hs he hd hle hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdeg : degree M₀ n =
      degree M n - 2 * (sprinkleTime (1 / 16) n : ℝ) / (n : ℝ) := by
    dsimp [M₀, degree]
    rw [Nat.cast_sub hle]
    ring
  have hdelta : degree M n - 1 = epsilon M n := by
    rw [epsilon, abs_of_pos (sub_pos.mpr hd)]
  have hpos : 1 < degree M₀ n := by
    have ht := (div_lt_iff₀ (mul_pos hnR he)).mp hs
    rw [hdeg]
    have htdiv : 2 * (sprinkleTime (1 / 16) n : ℝ) / (n : ℝ) <
        epsilon M n / 2 := by
      apply (div_lt_iff₀ hnR).2
      nlinarith
    linarith
  have hdelta0 : epsilon M₀ n = degree M₀ n - 1 := by
    rw [epsilon, abs_of_pos (sub_pos.mpr hpos)]
  dsimp [M₀] at hdelta0
  rw [hdelta0, hdeg]
  rw [← hdelta]
  field_simp [hnR.ne', (sub_pos.mpr hd).ne']
  ring

private lemma near_old_bare {M : NatSeq} (hbare : bareSuper M) :
    bareSuper (fun n => M n - sprinkleTime (1 / 16) n) := by
  let M₀ : NatSeq := fun n => M n - sprinkleTime (1 / 16) n
  have hr := near_old_excess_ratio hbare
  have hc := near_sprinkle_correction_zero hbare
  have hsmall := (tendsto_order.1 hc).2 (1 / 2) (by norm_num)
  have hpos : ∀ᶠ n : ℕ in atTop, 1 < degree M₀ n := by
    filter_upwards [hsmall, bare_epsilon_pos (Or.inr hbare),
      hbare.2.1, sprinkleTime_le_M_eventually
        (by norm_num : (0 : ℝ) < 1)
        (by norm_num : (0 : ℝ) ≤ 1 / 16) hbare.2.2.1,
      eventually_gt_atTop 0] with n hs he hd hle hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hdeg : degree M₀ n =
        degree M n - 2 * (sprinkleTime (1 / 16) n : ℝ) / (n : ℝ) := by
      dsimp [M₀, degree]
      rw [Nat.cast_sub hle]
      ring
    have hdelta : degree M n - 1 = epsilon M n := by
      rw [epsilon, abs_of_pos (sub_pos.mpr hd)]
    have ht := (div_lt_iff₀ (mul_pos hnR he)).mp hs
    rw [hdeg]
    have htdiv : 2 * (sprinkleTime (1 / 16) n : ℝ) / (n : ℝ) <
        epsilon M n / 2 := by
      apply (div_lt_iff₀ hnR).2
      nlinarith
    linarith
  have hwlim : Tendsto (fun n =>
      (epsilon M₀ n / epsilon M n) ^ 3 * widthParameter M n)
      atTop atTop :=
    (hr.pow 3).pos_mul_atTop (by norm_num) hbare.2.2.2
  have hwidth : Tendsto (widthParameter M₀) atTop atTop := by
    apply hwlim.congr'
    filter_upwards [bare_epsilon_pos (Or.inr hbare)] with n he
    dsimp [widthParameter]
    field_simp [he.ne']
  refine ⟨?_, hpos, ?_, hwidth⟩
  · filter_upwards [hbare.1] with n hn
    exact (Nat.sub_le _ _).trans hn
  · exact near_old_degree hbare

private lemma near_noise_div_cutoff_zero {M : NatSeq}
    (hbare : bareSuper M) :
    Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) / epsilon M n) /
      (largeCutoff n : ℝ)) atTop (𝓝 0) := by
  have hq := near_cutoff_div_ne_zero hbare
  have hsqrt : Tendsto (fun n =>
      Real.sqrt ((largeCutoff n : ℝ) /
        ((n : ℝ) * epsilon M n))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using!
      Real.continuous_sqrt.continuousAt.tendsto.comp hq
  apply squeeze_zero' (g := fun n : ℕ =>
    Real.sqrt ((largeCutoff n : ℝ) / ((n : ℝ) * epsilon M n)))
  · filter_upwards with n
    positivity
  · filter_upwards [bare_epsilon_pos (Or.inr hbare),
      largeCutoff_eventually_pos, eventually_gt_atTop 0]
      with n he hh hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hhR : (0 : ℝ) < largeCutoff n := by exact_mod_cast hh
    have hcube := cutoff_cube_ge_square hn
    apply (Real.le_sqrt (by positivity) (by positivity)).2
    rw [div_pow, Real.sq_sqrt (by positivity)]
    apply (div_le_div_iff₀ (sq_pos_of_pos hhR)
      (mul_pos hnR he)).2
    have hmul : ((n : ℝ) / epsilon M n) *
        ((n : ℝ) * epsilon M n) = (n : ℝ) ^ 2 := by
      field_simp [he.ne']
    rw [hmul]
    nlinarith [hcube]
  · exact hsqrt

private lemma near_giantFraction_ge_excess (hRate : RateStatement) :
    ∃ η : ℝ, 0 < η ∧ ∀ e : ℝ, 0 < e → e < η →
      e ≤ giantFraction (1 + e) := by
  obtain ⟨C, e₀, hC, he₀, he₀one, hExp⟩ := hRate.2.2.2.2.2
  let η := min e₀ (min 1 (1 / (4 * (C + 1))))
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨η, hη, ?_⟩
  intro e he heη
  have he0 : e < e₀ := lt_of_lt_of_le heη (min_le_left _ _)
  have he1 : e < 1 := lt_of_lt_of_le heη
    ((min_le_right _ _).trans (min_le_left _ _))
  have hebound : e < 1 / (4 * (C + 1)) := lt_of_lt_of_le heη
    ((min_le_right _ _).trans (min_le_right _ _))
  have hreal := (hExp e he he0).2.2.2
  have hlow := (abs_le.mp hreal).1
  have hsmall : (C + 8 / 3) * e < 1 := by
    have hmul := (lt_div_iff₀ (by positivity : 0 < 4 * (C + 1))).mp hebound
    nlinarith [mul_nonneg hC.le he.le]
  have hcube : e ^ 3 ≤ e ^ 2 := by nlinarith [mul_nonneg (sq_nonneg e) (sub_nonneg.mpr he1.le)]
  have hsq : (C + 8 / 3) * e ^ 2 ≤ e := by
    nlinarith [mul_nonneg he.le (sub_nonneg.mpr hsmall.le)]
  nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hcube)]

private lemma near_center_div_cutoff_atTop (hRate : RateStatement)
    {M : NatSeq} (hbare : bareSuper M) :
    Tendsto (fun n => giantCenter M n / (largeCutoff n : ℝ))
      atTop atTop := by
  obtain ⟨η, hη, hfrac⟩ := near_giantFraction_ge_excess hRate
  have hsmall := (tendsto_order.1 (bare_epsilon_tendsto_zero (Or.inr hbare))).2 η hη
  have hq := near_cutoff_div_ne_zero hbare
  have hqpos : ∀ᶠ n : ℕ in atTop,
      0 < (largeCutoff n : ℝ) / ((n : ℝ) * epsilon M n) := by
    filter_upwards [bare_epsilon_pos (Or.inr hbare),
      largeCutoff_eventually_pos, eventually_gt_atTop 0] with n he hh hn
    positivity
  have hqgt : Tendsto (fun n =>
      (largeCutoff n : ℝ) / ((n : ℝ) * epsilon M n))
      atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hq, hqpos⟩
  have hrec := hqgt.inv_tendsto_nhdsGT_zero
  apply tendsto_atTop_mono' atTop
    (f₁ := fun n => ((largeCutoff n : ℝ) /
      ((n : ℝ) * epsilon M n))⁻¹) ?_ hrec
  filter_upwards [bare_epsilon_pos (Or.inr hbare),
    hbare.2.1, hsmall, largeCutoff_eventually_pos,
    eventually_gt_atTop 0] with n he hd hs hh hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hhR : (0 : ℝ) < largeCutoff n := by exact_mod_cast hh
  have heq : degree M n = 1 + epsilon M n := by
    rw [epsilon, abs_of_pos (sub_pos.mpr hd)]
    ring
  have hfracn := hfrac (epsilon M n) he hs
  have hm := mul_le_mul_of_nonneg_left hfracn hnR.le
  have hden := div_le_div_of_nonneg_right hm hhR.le
  calc
    ((largeCutoff n : ℝ) / ((n : ℝ) * epsilon M n))⁻¹ =
        (n : ℝ) * epsilon M n / (largeCutoff n : ℝ) := by
      field_simp [hnR.ne', he.ne', hhR.ne']
    _ ≤ giantCenter M n / (largeCutoff n : ℝ) := by
      simpa [giantCenter, heq] using! hden

private lemma near_deriv_bound (hRate : RateStatement) :
    ∃ η : ℝ, 0 < η ∧ ∀ e : ℝ, 0 < e → e < η →
      |deriv giantFraction (1 + e)| ≤ 3 := by
  have ht := hRate.2.2.2.2.1
  have hupper := (tendsto_order.1 ht).2 3 (by norm_num)
  have hlower := (tendsto_order.1 ht).1 1 (by norm_num)
  have hbound : ∀ᶠ e : ℝ in 𝓝[>] 0,
      |deriv giantFraction (1 + e)| ≤ 3 :=
    (hupper.and hlower).mono (fun e h => abs_le.mpr ⟨by linarith [h.2], h.1.le⟩)
  obtain ⟨η, hη, hsub⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp hbound
  refine ⟨η, hη, ?_⟩
  intro e he heη
  exact hsub ⟨he, heη⟩

private lemma near_center_gap (hRate : RateStatement)
    {M : NatSeq} (hbare : bareSuper M) :
    ∀ᶠ n : ℕ in atTop,
      giantCenter M n -
        giantCenter (fun j => M j - sprinkleTime (1 / 16) j) n +
        2 * ((largeCutoff n : ℝ) / 4) <
          (largeCutoff n : ℝ) := by
  let M₀ : NatSeq := fun n => M n - sprinkleTime (1 / 16) n
  have hbare0 := near_old_bare hbare
  obtain ⟨η, hη, hderiv⟩ := near_deriv_bound hRate
  have hM : ∀ᶠ n : ℕ in atTop, degree M n < 1 + η :=
    ((tendsto_order.1 hbare.2.2.1).2 (1 + η) (by linarith))
  have hM0 : ∀ᶠ n : ℕ in atTop, degree M₀ n < 1 + η :=
    ((tendsto_order.1 hbare0.2.2.1).2 (1 + η) (by linarith))
  have hle := sprinkleTime_le_M_eventually (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) ≤ 1 / 16) hbare.2.2.1
  filter_upwards [hM, hM0, hbare.2.1, hbare0.2.1, hle,
    largeCutoff_eventually_pos, eventually_gt_atTop 0]
    with n hm hm0 hp hp0 htime hh hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hhR : (0 : ℝ) < largeCutoff n := by exact_mod_cast hh
  have hdegeq : degree M n - degree M₀ n =
      2 * (sprinkleTime (1 / 16) n : ℝ) / (n : ℝ) := by
    dsimp [M₀, degree]
    rw [Nat.cast_sub htime]
    ring
  have hdegnonneg : 0 ≤ degree M n - degree M₀ n := by
    rw [hdegeq]
    positivity
  have hmem0 : degree M₀ n ∈ Set.Icc (degree M₀ n) (degree M n) :=
    ⟨le_refl _, sub_nonneg.mp hdegnonneg⟩
  have hmem : degree M n ∈ Set.Icc (degree M₀ n) (degree M n) :=
    ⟨sub_nonneg.mp hdegnonneg, le_refl _⟩
  have hdiff : ∀ x ∈ Set.Icc (degree M₀ n) (degree M n),
      DifferentiableAt ℝ giantFraction x := by
    intro x hx
    have hx1 : x ∈ Set.Ioi (1 : ℝ) := by
      change 1 < x
      exact hp0.trans_le hx.1
    exact (hRate.2.2.1 x hx1).differentiableAt
      (IsOpen.mem_nhds isOpen_Ioi hx1)
  have hLip := Convex.norm_image_sub_le_of_norm_deriv_le hdiff
    (by
      intro x hx
      have hx1 : 1 < x := hp0.trans_le hx.1
      have hxη : x - 1 < η := by linarith [hx.2]
      simpa [Real.norm_eq_abs, add_sub_cancel_left] using!
        hderiv (x - 1) (by linarith) hxη)
    (convex_Icc (degree M₀ n) (degree M n)) hmem0 hmem
  simp only [Real.norm_eq_abs, abs_of_nonneg hdegnonneg] at hLip
  have hLip' : giantFraction (degree M n) -
      giantFraction (degree M₀ n) ≤
      3 * (degree M n - degree M₀ n) :=
    (le_abs_self _).trans hLip
  rw [hdegeq] at hLip'
  have hcenter : giantCenter M n - giantCenter M₀ n ≤
      6 * (sprinkleTime (1 / 16) n : ℝ) := by
    calc
      giantCenter M n - giantCenter M₀ n =
          (n : ℝ) * (giantFraction (degree M n) -
            giantFraction (degree M₀ n)) := by unfold giantCenter; ring
      _ ≤ (n : ℝ) * (3 * (2 * (sprinkleTime (1 / 16) n : ℝ) /
        (n : ℝ))) := mul_le_mul_of_nonneg_left hLip' hnR.le
      _ = 6 * (sprinkleTime (1 / 16) n : ℝ) := by field_simp; ring
  have ht := sprinkleTime_le (1 / 16) (by norm_num) n
  have hcenter' : giantCenter M n - giantCenter M₀ n ≤
      3 * (largeCutoff n : ℝ) / 8 := by nlinarith
  change giantCenter M n - giantCenter M₀ n +
    2 * ((largeCutoff n : ℝ) / 4) < (largeCutoff n : ℝ)
  linarith

private lemma near_endpoint_bad (hF : FiniteEnumerationStatement)
    (hCyc : CyclicStructureStatement) (hTree : TreeMassStatement)
    {M : NatSeq} (hbare : bareSuper M) :
    Tendsto (fun n => probM n (M n)
      (fun G => |largeMass G (largeCutoff n) - giantCenter M n| >
        (largeCutoff n : ℝ) / 4)) atTop (𝓝 0) := by
  have htight := near_largeMass_tight hF hCyc hTree M hbare
  have hbase := deviation_tendsto_zero_of_tight M
    (fun n G => largeMass G (largeCutoff n)) (giantCenter M)
    (fun n => Real.sqrt ((n : ℝ) / epsilon M n))
    (fun n => (largeCutoff n : ℝ))
    htight (near_noise_div_cutoff_zero hbare)
    (by filter_upwards [largeCutoff_eventually_pos] with n hn
        exact_mod_cast hn)
    (1 / 4) (by norm_num)
  simpa [div_eq_mul_inv, mul_comm] using! hbase

theorem near_unique_bad_tendsto_zero
    (hF : FiniteEnumerationStatement) (hRate : RateStatement)
    (hCyc : CyclicStructureStatement) (hTree : TreeMassStatement)
    (M : NatSeq) (hbare : bareSuper M) :
    Tendsto (fun n => probM n (M n)
      (fun G => countGE G (largeCutoff n) ≠ 1)) atTop (𝓝 0) := by
  let t : NatSeq := sprinkleTime (1 / 16)
  let M₀ : NatSeq := fun n => M n - t n
  let h : NatSeq := largeCutoff
  let a : RealSeq := fun n => (h n : ℝ) / 4
  have hbare0 : bareSuper M₀ := near_old_bare hbare
  have htime := sprinkleTime_le_M_eventually (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) ≤ 1 / 16) hbare.2.2.1
  have hsize : ∀ᶠ n : ℕ in atTop,
      M₀ n + t n = M n ∧ M n ≤ capacity n := by
    filter_upwards [htime, hbare.1] with n ht hm
    exact ⟨Nat.sub_add_cancel ht, hm⟩
  have hcut : ∀ᶠ n : ℕ in atTop, 0 < h n :=
    largeCutoff_eventually_pos
  have hgap : ∀ᶠ n : ℕ in atTop,
      giantCenter M n - giantCenter M₀ n + 2 * a n < h n := by
    simpa [M₀, t, h, a] using! near_center_gap hRate hbare
  have hOld : Tendsto (fun n => probM n (M₀ n)
      (fun G => |largeMass G (h n) - giantCenter M₀ n| > a n))
      atTop (𝓝 0) := by
    simpa [h, a] using! near_endpoint_bad hF hCyc hTree hbare0
  have hFinal : Tendsto (fun n => probM n (M n)
      (fun G => |largeMass G (h n) - giantCenter M n| > a n))
      atTop (𝓝 0) := by
    simpa [h, a] using! near_endpoint_bad hF hCyc hTree hbare
  have hcenter := near_center_div_cutoff_atTop hRate hbare0
  have htight := near_largeMass_tight hF hCyc hTree M₀ hbare0
  have hscale := near_noise_div_cutoff_zero hbare0
  have hMass : Tendsto (fun n => probM n (M₀ n)
      (fun G => oldMassRatio G (h n) < 1)) atTop (𝓝 0) := by
    exact oldMassRatio_lower_tail_of_tight M₀ h
      (giantCenter M₀)
      (fun n => Real.sqrt ((n : ℝ) / epsilon M₀ n))
      htight hcut hcenter hscale 1
  have hJoin : Tendsto (fun n => expectM n (M₀ n) (fun G =>
      growProb G (t n) (fun H => ¬ oldLargeJoined G H (h n))))
      atTop (𝓝 0) := by
    apply sprinkling_join_failure_tendsto_zero hF M₀ h t
      (c := (1 / 16 : ℝ) / 4) (by norm_num)
    · exact hsize.mono fun n hn => hn.1.le.trans hn.2
    · exact hcut
    · exact capacity_eventually_pos
    · simpa [h, t] using! sprinkle_coefficient_lower (1 / 16)
        (by norm_num : (0 : ℝ) < 1 / 16)
    · intro L
      exact oldMassRatio_lower_tail_of_tight M₀ h
        (giantCenter M₀)
        (fun n => Real.sqrt ((n : ℝ) / epsilon M₀ n))
        htight hcut hcenter hscale L
  exact unique_bad_tendsto_zero_of_center_comparison hF M₀ M h t
    (giantCenter M₀) (giantCenter M) a
    hsize hcut hgap hOld hFinal hMass hJoin

theorem near_giant_branch
    (hF : FiniteEnumerationStatement) (hRate : RateStatement)
    (hTuple : TupleEstimatesStatement)
    (hCyc : CyclicStructureStatement) (hTree : TreeMassStatement)
    (M : NatSeq) (hbare : bareSuper M) :
    tightScaled M (fun n G => largeMass G (largeCutoff n)) (giantCenter M)
      (fun n => Real.sqrt ((n : ℝ) / epsilon M n)) ∧
    tightScaled M (fun _ G => (rankSize G 1 : ℝ)) (giantCenter M)
      (fun n => Real.sqrt ((n : ℝ) / epsilon M n)) ∧
    Tendsto (fun n => probM n (M n) separatedStructure) atTop (𝓝 1) := by
  exact near_giantBranch_of_unique_tree hF hCyc hTree M hbare
    (near_unique_bad_tendsto_zero hF hRate hCyc hTree M hbare)
    (near_tree_bad_tendsto_zero hF hTuple hbare)

end
end Erdos745.WrapUp.Proofs.Internal.W10_GIANT_Near
