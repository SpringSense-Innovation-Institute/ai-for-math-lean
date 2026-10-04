module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W06_P02

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


namespace Erdos745.WrapUp.Proofs.W06_POISSON

noncomputable section

open Erdos745.WrapUp
open Filter
open scoped BigOperators Topology

def nearHeight (M : NatSeq) (r : ℝ) (n : ℕ) : ℕ :=
  ⌈nearThreshold M n r⌉₊

def nearLeadingNormalization (M : NatSeq) (r : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) / (degree M n * Real.sqrt (2 * Real.pi)) *
    (Real.rpow (rate (degree M n)) (3 / 2 : ℝ) *
      Real.rpow (nearNumerator M n r) (-5 / 2 : ℝ) *
        Real.exp (-nearNumerator M n r))

lemma bare_admissible {M : NatSeq} (hbare : bareSub M ∨ bareSuper M) :
    admissible M := by
  rcases hbare with h | h
  · exact h.1
  · exact h.1

lemma bare_degree_tendsto_one {M : NatSeq} (hbare : bareSub M ∨ bareSuper M) :
    Tendsto (degree M) atTop (nhds 1) := by
  rcases hbare with h | h
  · exact h.2.2.1
  · exact h.2.2.1

lemma bare_width_tendsto_atTop {M : NatSeq} (hbare : bareSub M ∨ bareSuper M) :
    Tendsto (widthParameter M) atTop atTop := by
  rcases hbare with h | h
  · exact h.2.2.2
  · exact h.2.2.2

lemma bare_degree_side {M : NatSeq} (hbare : bareSub M ∨ bareSuper M) :
    (∀ᶠ n in atTop, 0 < degree M n ∧ degree M n < 1) ∨
      (∀ᶠ n in atTop, 1 < degree M n) := by
  rcases hbare with h | h
  · exact Or.inl h.2.1
  · exact Or.inr h.2.1

lemma bare_epsilon_tendsto_zero {M : NatSeq} (hbare : bareSub M ∨ bareSuper M) :
    Tendsto (epsilon M) atTop (nhds 0) := by
  have hd := bare_degree_tendsto_one hbare
  have h := (hd.sub_const 1).abs
  simpa [epsilon] using! h

lemma bare_epsilon_pos {M : NatSeq} (hbare : bareSub M ∨ bareSuper M) :
    ∀ᶠ n in atTop, 0 < epsilon M n := by
  rcases bare_degree_side hbare with hsub | hsup
  · filter_upwards [hsub] with n hn
    rw [epsilon]
    exact abs_pos.mpr (sub_ne_zero.mpr hn.2.ne)
  · filter_upwards [hsup] with n hn
    rw [epsilon]
    exact abs_pos.mpr (sub_ne_zero.mpr hn.ne')

lemma rate_over_epsilon_sq_tendsto
    (hRate : RateStatement) {M : NatSeq} (hbare : bareSub M ∨ bareSuper M) :
    Tendsto (fun n ↦ rate (degree M n) / epsilon M n ^ 2)
      atTop (nhds (1 / 2 : ℝ)) := by
  obtain ⟨C, e0, hC, he0, he01, hTaylor⟩ := hRate.2.2.2.2.2
  have he := bare_epsilon_tendsto_zero hbare
  have hepos := bare_epsilon_pos hbare
  have hesmall : ∀ᶠ n in atTop, epsilon M n < e0 :=
    (tendsto_order.1 he).2 e0 he0
  have hbound : ∀ᶠ n in atTop,
      |rate (degree M n) / epsilon M n ^ 2 - (1 / 2 : ℝ)| ≤
        C * epsilon M n ^ 2 + epsilon M n / 3 := by
    rcases bare_degree_side hbare with hsub | hsup
    · filter_upwards [hsub, hepos, hesmall] with n hn hen hes
      let e := epsilon M n
      have hdeg : degree M n = 1 - e := by
        dsimp [e, epsilon]
        rw [abs_of_neg (sub_neg.mpr hn.2)]
        ring
      have ht := (hTaylor e (by simpa [e] using! hen) (by simpa [e] using hes)).2.1
      rw [← hdeg] at ht
      have he2 : 0 < e ^ 2 := sq_pos_of_pos hen
      have hdiv :
          |(rate (degree M n) - (e ^ 2 / 2 + e ^ 3 / 3)) / e ^ 2| ≤
            C * e ^ 2 := by
        rw [abs_div, abs_of_pos he2]
        apply (div_le_iff₀ he2).2
        nlinarith
      have hcenter : (e ^ 2 / 2 + e ^ 3 / 3) / e ^ 2 = 1 / 2 + e / 3 := by
        apply (div_eq_iff (pow_ne_zero _ hen.ne')).2
        ring
      have hmain :
          |rate (degree M n) / e ^ 2 - (1 / 2 : ℝ)| ≤
            |(rate (degree M n) - (e ^ 2 / 2 + e ^ 3 / 3)) / e ^ 2| + e / 3 := by
        rw [show rate (degree M n) / e ^ 2 - (1 / 2 : ℝ) =
          (rate (degree M n) - (e ^ 2 / 2 + e ^ 3 / 3)) / e ^ 2 + e / 3 by
            calc
              rate (degree M n) / e ^ 2 - (1 / 2 : ℝ) =
                  (rate (degree M n) - (e ^ 2 / 2 + e ^ 3 / 3)) / e ^ 2 +
                    ((e ^ 2 / 2 + e ^ 3 / 3) / e ^ 2 - 1 / 2) := by ring
              _ = _ := by rw [hcenter]; ring]
        calc
          |(rate (degree M n) - (e ^ 2 / 2 + e ^ 3 / 3)) / e ^ 2 + e / 3| ≤
              |(rate (degree M n) - (e ^ 2 / 2 + e ^ 3 / 3)) / e ^ 2| + |e / 3| :=
            abs_add_le _ _
          _ = |(rate (degree M n) - (e ^ 2 / 2 + e ^ 3 / 3)) / e ^ 2| + e / 3 := by
            rw [abs_of_nonneg (div_nonneg hen.le (by norm_num))]
      have hnext := add_le_add hdiv (le_refl (e / 3))
      simpa [e] using! hmain.trans hnext
    · filter_upwards [hsup, hepos, hesmall] with n hn hen hes
      let e := epsilon M n
      have hdeg : degree M n = 1 + e := by
        dsimp [e, epsilon]
        rw [abs_of_pos (sub_pos.mpr hn)]
        ring
      have ht := (hTaylor e (by simpa [e] using! hen) (by simpa [e] using hes)).1
      rw [← hdeg] at ht
      have he2 : 0 < e ^ 2 := sq_pos_of_pos hen
      have hdiv :
          |(rate (degree M n) - (e ^ 2 / 2 - e ^ 3 / 3)) / e ^ 2| ≤
            C * e ^ 2 := by
        rw [abs_div, abs_of_pos he2]
        apply (div_le_iff₀ he2).2
        nlinarith
      have hcenter : (e ^ 2 / 2 - e ^ 3 / 3) / e ^ 2 = 1 / 2 - e / 3 := by
        apply (div_eq_iff (pow_ne_zero _ hen.ne')).2
        ring
      have hmain :
          |rate (degree M n) / e ^ 2 - (1 / 2 : ℝ)| ≤
            |(rate (degree M n) - (e ^ 2 / 2 - e ^ 3 / 3)) / e ^ 2| + e / 3 := by
        rw [show rate (degree M n) / e ^ 2 - (1 / 2 : ℝ) =
          (rate (degree M n) - (e ^ 2 / 2 - e ^ 3 / 3)) / e ^ 2 - e / 3 by
            calc
              rate (degree M n) / e ^ 2 - (1 / 2 : ℝ) =
                  (rate (degree M n) - (e ^ 2 / 2 - e ^ 3 / 3)) / e ^ 2 +
                    ((e ^ 2 / 2 - e ^ 3 / 3) / e ^ 2 - 1 / 2) := by ring
              _ = _ := by rw [hcenter]; ring]
        calc
          |(rate (degree M n) - (e ^ 2 / 2 - e ^ 3 / 3)) / e ^ 2 - e / 3| ≤
              |(rate (degree M n) - (e ^ 2 / 2 - e ^ 3 / 3)) / e ^ 2| + |e / 3| :=
            abs_sub _ _
          _ = |(rate (degree M n) - (e ^ 2 / 2 - e ^ 3 / 3)) / e ^ 2| + e / 3 := by
            rw [abs_of_nonneg (div_nonneg hen.le (by norm_num))]
      have hnext := add_le_add hdiv (le_refl (e / 3))
      simpa [e] using! hmain.trans hnext
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero_norm'
  · simpa [Real.norm_eq_abs] using! hbound
  have he2 : Tendsto (fun n ↦ epsilon M n ^ 2) atTop (nhds 0) := by
    simpa using! he.pow 2
  have hsum := (he2.const_mul C).add (he.const_mul (1 / 3 : ℝ))
  convert hsum using 1
  · funext n
    ring
  · ring

lemma near_rate_tendsto_zero
    (hRate : RateStatement) {M : NatSeq} (hbare : bareSub M ∨ bareSuper M) :
    Tendsto (fun n ↦ rate (degree M n)) atTop (nhds 0) := by
  have hr := rate_over_epsilon_sq_tendsto hRate hbare
  have he := bare_epsilon_tendsto_zero hbare
  have he2 : Tendsto (fun n ↦ epsilon M n ^ 2) atTop (nhds 0) := by
    simpa using! he.pow 2
  have hmul := hr.mul he2
  have hmul' : Tendsto
      (fun n ↦ rate (degree M n) / epsilon M n ^ 2 * epsilon M n ^ 2)
      atTop (nhds 0) := by simpa using! hmul
  apply hmul'.congr'
  filter_upwards [bare_epsilon_pos hbare] with n hen
  field_simp [hen.ne']

lemma near_rate_eventually_pos
    (hRate : RateStatement) {M : NatSeq} (hbare : bareSub M ∨ bareSuper M) :
    ∀ᶠ n in atTop, 0 < rate (degree M n) := by
  rcases bare_degree_side hbare with hsub | hsup
  · filter_upwards [hsub] with n hn
    exact hRate.1 _ hn.1 hn.2.ne
  · filter_upwards [hsup] with n hn
    exact hRate.1 _ (zero_lt_one.trans hn) hn.ne'

lemma near_log_width_tendsto_atTop {M : NatSeq}
    (hbare : bareSub M ∨ bareSuper M) :
    Tendsto (fun n ↦ Real.log (widthParameter M n / 8)) atTop atTop := by
  have hw := bare_width_tendsto_atTop hbare
  have hz : Tendsto (fun n ↦ widthParameter M n / 8) atTop atTop := by
    simpa [div_eq_mul_inv, mul_comm] using!
      hw.const_mul_atTop (by norm_num : 0 < (8 : ℝ)⁻¹)
  exact Real.tendsto_log_atTop.comp hz

lemma nearNumerator_div_log_tendsto_one {M : NatSeq}
    (hbare : bareSub M ∨ bareSuper M) (r : ℝ) :
    Tendsto (fun n ↦ nearNumerator M n r /
      Real.log (widthParameter M n / 8)) atTop (nhds 1) := by
  let LL : RealSeq := fun n ↦ Real.log (widthParameter M n / 8)
  have hLL : Tendsto LL atTop atTop := by
    simpa [LL] using! near_log_width_tendsto_atTop hbare
  have hlogDiv : Tendsto (fun n ↦ Real.log (LL n) / LL n) atTop (nhds 0) := by
    have hbase := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have hc := hbase.comp hLL
    simpa [LL] using! hc
  have hrDiv : Tendsto (fun n ↦ r / LL n) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hLL
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hlim := (hone.sub
    (hlogDiv.const_mul (5 / 2 : ℝ))).add hrDiv
  have hlim' : Tendsto
      (fun n ↦ 1 - (5 / 2 : ℝ) * (Real.log (LL n) / LL n) + r / LL n)
      atTop (nhds 1) := by simpa using! hlim
  apply hlim'.congr'
  have hLLne : ∀ᶠ n in atTop, LL n ≠ 0 := by
    have hpos := (tendsto_atTop.1 hLL) 1
    exact hpos.mono fun _ hn ↦ (zero_lt_one.trans_le hn).ne'
  filter_upwards [hLLne] with n hn
  change 1 - (5 / 2 : ℝ) * (Real.log (LL n) / LL n) + r / LL n =
    (LL n - (5 / 2 : ℝ) * Real.log (LL n) + r) / LL n
  field_simp [hn]

lemma nearNumerator_tendsto_atTop {M : NatSeq}
    (hbare : bareSub M ∨ bareSuper M) (r : ℝ) :
    Tendsto (nearNumerator M · r) atTop atTop := by
  let LL : RealSeq := fun n ↦ Real.log (widthParameter M n / 8)
  have hLL : Tendsto LL atTop atTop := by
    simpa [LL] using! near_log_width_tendsto_atTop hbare
  have hratio := nearNumerator_div_log_tendsto_one hbare r
  apply tendsto_atTop.2
  intro b
  have hratioLower : ∀ᶠ n in atTop,
      (1 / 2 : ℝ) ≤ nearNumerator M n r / LL n :=
    ((tendsto_order.1 hratio).1 (1 / 2) (by norm_num)).mono fun _ h ↦ h.le
  have hLLLarge : ∀ᶠ n in atTop, max 1 (2 * b) ≤ LL n :=
    (tendsto_atTop.1 hLL) (max 1 (2 * b))
  filter_upwards [hratioLower, hLLLarge] with n hn hLn
  have hLpos : 0 < LL n := zero_lt_one.trans_le (le_trans (le_max_left _ _) hLn)
  have hprod : (1 / 2 : ℝ) * LL n ≤ nearNumerator M n r := by
    exact (le_div_iff₀ hLpos).1 hn
  have hb : b ≤ (1 / 2 : ℝ) * LL n := by
    have := le_trans (le_max_right (1 : ℝ) (2 * b)) hLn
    linarith
  exact hb.trans hprod

lemma near_rounding_asymptotics
    (hRate : RateStatement) {M : NatSeq} (hbare : bareSub M ∨ bareSuper M)
    (r : ℝ) :
    Tendsto (fun n ↦ rate (degree M n) * (nearHeight M r n : ℝ) -
      nearNumerator M n r) atTop (nhds 0) ∧
    Tendsto (nearHeight M r) atTop atTop := by
  let aa : RealSeq := fun n ↦ rate (degree M n)
  let LL : RealSeq := fun n ↦ nearNumerator M n r
  have haa := near_rate_tendsto_zero hRate hbare
  have haaPos := near_rate_eventually_pos hRate hbare
  have hLL := nearNumerator_tendsto_atTop hbare r
  have hLLPos : ∀ᶠ n in atTop, 0 < LL n :=
    ((tendsto_atTop.1 hLL) 1).mono fun _ h ↦ zero_lt_one.trans_le h
  have hround : ∀ᶠ n in atTop,
      0 ≤ aa n * (nearHeight M r n : ℝ) - LL n ∧
      aa n * (nearHeight M r n : ℝ) - LL n < aa n := by
    filter_upwards [haaPos, hLLPos] with n han hLn
    dsimp [aa, LL] at han hLn ⊢
    have hquot : 0 ≤ LL n / aa n := (div_pos hLn han).le
    have hlo := Nat.le_ceil (LL n / aa n)
    have hhi := Nat.ceil_lt_add_one hquot
    dsimp [aa, LL] at hquot hlo hhi
    constructor
    · change 0 ≤ aa n * (↑⌈LL n / aa n⌉₊ : ℝ) - LL n
      apply sub_nonneg.mpr
      calc
        LL n = aa n * (LL n / aa n) := by
          rw [mul_comm, div_mul_cancel₀ _ han.ne']
        _ ≤ aa n * (↑⌈LL n / aa n⌉₊ : ℝ) :=
          mul_le_mul_of_nonneg_left hlo han.le
    · change aa n * (↑⌈LL n / aa n⌉₊ : ℝ) - LL n < aa n
      have hre : nearNumerator M n r / rate (degree M n) + 1 =
          (nearNumerator M n r + rate (degree M n)) / rate (degree M n) := by
        field_simp [han.ne']
      rw [hre] at hhi
      have hm := (lt_div_iff₀ han).1 hhi
      nlinarith
  constructor
  · apply squeeze_zero'
    · exact hround.mono fun _ h ↦ h.1
    · exact hround.mono fun _ h ↦ h.2.le
    · simpa [aa] using! haa
  · apply tendsto_atTop.2
    intro b
    have haaOne : ∀ᶠ n in atTop, aa n ≤ 1 :=
      ((tendsto_order.1 haa).2 1 zero_lt_one).mono fun _ h ↦ h.le
    have hLLb : ∀ᶠ n in atTop, (b : ℝ) ≤ LL n := (tendsto_atTop.1 hLL) b
    filter_upwards [haaPos, haaOne, hLLb, hround] with n han ha1 hLb hr
    have hLh : LL n ≤ aa n * (nearHeight M r n : ℝ) := by linarith [hr.1]
    have hcast : (b : ℝ) ≤ (nearHeight M r n : ℝ) := by
      calc
        (b : ℝ) ≤ LL n := hLb
        _ ≤ aa n * (nearHeight M r n : ℝ) := hLh
        _ ≤ (nearHeight M r n : ℝ) := by
          exact mul_le_of_le_one_left (by positivity) ha1
    exact_mod_cast hcast

lemma near_height_scale
    (hRate : RateStatement) {M : NatSeq} (hbare : bareSub M ∨ bareSuper M)
    (r : ℝ) :
    Tendsto (fun n ↦ epsilon M n ^ 2 * (nearHeight M r n : ℝ) /
      Real.log (widthParameter M n / 8)) atTop (nhds 2) := by
  let aa : RealSeq := fun n ↦ rate (degree M n)
  let ee : RealSeq := fun n ↦ epsilon M n
  let LL : RealSeq := fun n ↦ nearNumerator M n r
  let WW : RealSeq := fun n ↦ Real.log (widthParameter M n / 8)
  let hh : NatSeq := nearHeight M r
  have hratio := rate_over_epsilon_sq_tendsto hRate hbare
  have hLratio := nearNumerator_div_log_tendsto_one hbare r
  have hround := (near_rounding_asymptotics hRate hbare r).1
  have hWW : Tendsto WW atTop atTop := by
    simpa [WW] using! near_log_width_tendsto_atTop hbare
  have hroundDiv : Tendsto
      (fun n ↦ (aa n * (hh n : ℝ) - LL n) / WW n) atTop (nhds 0) :=
    hround.div_atTop hWW
  have haHDiv : Tendsto (fun n ↦ aa n * (hh n : ℝ) / WW n)
      atTop (nhds 1) := by
    have hadd := hLratio.add hroundDiv
    have hadd' : Tendsto
        (fun n ↦ LL n / WW n + (aa n * (hh n : ℝ) - LL n) / WW n)
        atTop (nhds 1) := by simpa [LL, WW] using! hadd
    have hWWPos : ∀ᶠ n in atTop, 0 < WW n :=
      ((tendsto_atTop.1 hWW) 1).mono fun _ h ↦ zero_lt_one.trans_le h
    apply hadd'.congr'
    filter_upwards [hWWPos] with n hwn
    dsimp [aa, LL, WW, hh]
    field_simp [hwn.ne']
    ring
  have hdiv := haHDiv.div hratio (by norm_num : (1 / 2 : ℝ) ≠ 0)
  have hdiv' : Tendsto
      ((fun n ↦ aa n * (hh n : ℝ) / WW n) /
        fun n ↦ aa n / ee n ^ 2) atTop (nhds 2) := by simpa using! hdiv
  have haaPos := near_rate_eventually_pos hRate hbare
  have hWWPos : ∀ᶠ n in atTop, 0 < WW n :=
    ((tendsto_atTop.1 hWW) 1).mono fun _ h ↦ zero_lt_one.trans_le h
  apply hdiv'.congr'
  filter_upwards [bare_epsilon_pos hbare, haaPos, hWWPos] with n he ha hw
  dsimp [aa, ee, WW, hh]
  field_simp [he.ne', ha.ne', hw.ne']

lemma nearRate_pos (r : ℝ) : 0 < nearRate r := by
  rw [nearRate]
  positivity

lemma nearLeadingNormalization_tendsto
    (hRate : RateStatement) {M : NatSeq} (hbare : bareSub M ∨ bareSuper M)
    (r : ℝ) :
    Tendsto (nearLeadingNormalization M r) atTop (nhds (nearRate r)) := by
  let dd : RealSeq := degree M
  let ee : RealSeq := epsilon M
  let aa : RealSeq := fun n ↦ rate (dd n)
  let ww : RealSeq := widthParameter M
  let zz : RealSeq := fun n ↦ ww n / 8
  let TT : RealSeq := fun n ↦ Real.log (zz n)
  let LL : RealSeq := fun n ↦ nearNumerator M n r
  have hdd := bare_degree_tendsto_one hbare
  have heePos := bare_epsilon_pos hbare
  have hww := bare_width_tendsto_atTop hbare
  have hwwPos : ∀ᶠ n in atTop, 0 < ww n :=
    ((tendsto_atTop.1 hww) 1).mono fun _ h ↦ zero_lt_one.trans_le h
  have hTT : Tendsto TT atTop atTop := by
    simpa [TT, zz, ww] using! near_log_width_tendsto_atTop hbare
  have hTTPos : ∀ᶠ n in atTop, 0 < TT n :=
    ((tendsto_atTop.1 hTT) 1).mono fun _ h ↦ zero_lt_one.trans_le h
  have hLL := nearNumerator_tendsto_atTop hbare r
  have hLLPos : ∀ᶠ n in atTop, 0 < LL n :=
    ((tendsto_atTop.1 hLL) 1).mono fun _ h ↦ zero_lt_one.trans_le h
  have haaPos := near_rate_eventually_pos hRate hbare
  have hrateRatio := rate_over_epsilon_sq_tendsto hRate hbare
  have hratePow : Tendsto
      (fun n ↦ Real.rpow (aa n / ee n ^ 2) (3 / 2 : ℝ)) atTop
      (nhds (Real.rpow (1 / 2 : ℝ) (3 / 2 : ℝ))) := by
    simpa [aa, ee] using! hrateRatio.rpow_const (Or.inl (by norm_num))
  have hTL := nearNumerator_div_log_tendsto_one hbare r
  have hLT : Tendsto (fun n ↦ TT n / LL n) atTop (nhds 1) := by
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    have hinv := hone.div hTL one_ne_zero
    have hinv' : Tendsto
        ((fun _ : ℕ ↦ (1 : ℝ)) /
          fun n ↦ nearNumerator M n r / Real.log (widthParameter M n / 8))
        atTop (nhds 1) := by simpa using! hinv
    apply hinv'.congr'
    filter_upwards [hTTPos, hLLPos] with n ht hl
    dsimp [TT, LL, zz, ww]
    field_simp [ht.ne', hl.ne']
  have hLTPow : Tendsto (fun n ↦ Real.rpow (TT n / LL n) (5 / 2 : ℝ))
      atTop (nhds 1) := by
    simpa using! hLT.rpow_const (Or.inl one_ne_zero)
  have hconst :
      8 * Real.exp (-r) / Real.sqrt (2 * Real.pi) *
          Real.rpow (1 / 2 : ℝ) (3 / 2 : ℝ) = nearRate r := by
    rw [nearRate]
    have hs2 : 0 < Real.sqrt 2 := by positivity
    have hsp : 0 < Real.sqrt Real.pi := by positivity
    have hs2sq : Real.sqrt 2 * Real.sqrt 2 = 2 := by nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)]
    have hsprod : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi := by
      rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2)]
    have hrpow : Real.rpow (1 / 2 : ℝ) (3 / 2 : ℝ) = 1 / (2 * Real.sqrt 2) := by
      calc
        Real.rpow (1 / 2 : ℝ) (3 / 2 : ℝ) =
            Real.rpow (1 / 2 : ℝ) (1 + 1 / 2) := by congr 2 <;> ring
        _ = Real.rpow (1 / 2 : ℝ) 1 * Real.rpow (1 / 2 : ℝ) (1 / 2) :=
          Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2) 1 (1 / 2)
        _ = 1 / (2 * Real.sqrt 2) := by
          rw [show Real.rpow (1 / 2 : ℝ) 1 = (1 / 2 : ℝ) by
            exact Real.rpow_one _]
          have hsqrt : Real.rpow (1 / 2 : ℝ) (1 / 2 : ℝ) = 1 / Real.sqrt 2 := by
            calc
              Real.rpow (1 / 2 : ℝ) (1 / 2 : ℝ) = Real.sqrt (1 / 2 : ℝ) :=
                (Real.sqrt_eq_rpow _).symm
              _ = Real.sqrt 1 / Real.sqrt 2 := Real.sqrt_div (by norm_num) 2
              _ = 1 / Real.sqrt 2 := by norm_num
          rw [hsqrt]
          ring
    rw [hsprod, hrpow]
    field_simp [hs2.ne', hsp.ne']
    nlinarith
  have honeDiv : Tendsto (fun n ↦ (1 : ℝ) / dd n) atTop (nhds 1) := by
    change Tendsto (fun n ↦ (1 : ℝ) / degree M n) atTop (nhds 1)
    convert (show Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) from
      tendsto_const_nhds).div hdd one_ne_zero using 1 <;> norm_num <;> rfl
  have hall := ((honeDiv.mul hratePow).mul hLTPow)
    |>.const_mul (8 * Real.exp (-r) / Real.sqrt (2 * Real.pi))
  have hlimit :
      (8 * Real.exp (-r) / Real.sqrt (2 * Real.pi)) *
        (1 * Real.rpow (1 / 2 : ℝ) (3 / 2 : ℝ) * 1) = nearRate r := by
    simpa [mul_assoc] using! hconst
  have hall' : Tendsto
      (fun n ↦ (8 * Real.exp (-r) / Real.sqrt (2 * Real.pi)) *
        ((1 : ℝ) / dd n * Real.rpow (aa n / ee n ^ 2) (3 / 2 : ℝ) *
          Real.rpow (TT n / LL n) (5 / 2 : ℝ)))
      atTop (nhds (nearRate r)) := by
    rw [← hlimit]
    exact hall
  apply hall'.congr'
  have hddPos : ∀ᶠ n in atTop, 0 < dd n :=
    ((tendsto_order.1 hdd).1 0 zero_lt_one).mono fun _ h ↦ h
  filter_upwards [heePos, hwwPos, hTTPos, hLLPos, haaPos, hddPos]
    with n hen hwn htn hln han hdn
  have he2 : 0 < ee n ^ 2 := sq_pos_of_pos hen
  have hpowSplit : Real.rpow (aa n) (3 / 2 : ℝ) =
      ee n ^ 3 * Real.rpow (aa n / ee n ^ 2) (3 / 2 : ℝ) := by
    have haaEq : aa n = ee n ^ 2 * (aa n / ee n ^ 2) := by
      symm
      exact mul_div_cancel₀ (aa n) (pow_ne_zero _ hen.ne')
    calc
      Real.rpow (aa n) (3 / 2 : ℝ) =
          Real.rpow (ee n ^ 2 * (aa n / ee n ^ 2)) (3 / 2 : ℝ) := by rw [← haaEq]
      _ = Real.rpow (ee n ^ 2) (3 / 2 : ℝ) *
          Real.rpow (aa n / ee n ^ 2) (3 / 2 : ℝ) :=
        Real.mul_rpow he2.le (div_nonneg han.le he2.le)
      _ = _ := by
        have hepow : Real.rpow (ee n ^ 2) (3 / 2 : ℝ) = ee n ^ 3 := by
          calc
            Real.rpow (ee n ^ 2) (3 / 2 : ℝ) =
                Real.rpow (Real.rpow (ee n) 2) (3 / 2 : ℝ) := by
              exact congrArg (fun x ↦ Real.rpow x (3 / 2 : ℝ))
                (Real.rpow_natCast (ee n) 2).symm
            _ = Real.rpow (ee n) (2 * (3 / 2 : ℝ)) :=
              (Real.rpow_mul hen.le 2 (3 / 2 : ℝ)).symm
            _ = Real.rpow (ee n) (3 : ℝ) := by congr 1 <;> norm_num
            _ = ee n ^ 3 := by
              simpa only using! (Real.rpow_natCast (ee n) 3)
        rw [hepow]
  have hExp : ww n * Real.exp (-LL n) =
      8 * Real.exp (-r) * Real.rpow (TT n) (5 / 2 : ℝ) := by
    have hzeq : ww n = 8 * zz n := by dsimp [zz]; ring
    have hexpz : Real.exp (TT n) = zz n := by
      dsimp [TT]
      exact Real.exp_log (div_pos hwn (by norm_num))
    have hpowlog : Real.exp ((5 / 2 : ℝ) * Real.log (TT n)) =
        Real.rpow (TT n) (5 / 2 : ℝ) := by
      calc
        Real.exp ((5 / 2 : ℝ) * Real.log (TT n)) =
            Real.exp (Real.log (TT n) * (5 / 2 : ℝ)) := by congr 1 <;> ring
        _ = Real.rpow (TT n) (5 / 2 : ℝ) :=
          (Real.rpow_def_of_pos htn (5 / 2 : ℝ)).symm
    dsimp [LL, nearNumerator]
    change ww n * Real.exp (-(Real.log (ww n / 8) - (5 / 2 : ℝ) *
        Real.log (Real.log (ww n / 8)) + r)) =
      8 * Real.exp (-r) * Real.rpow (TT n) (5 / 2 : ℝ)
    rw [show -(Real.log (ww n / 8) - (5 / 2 : ℝ) *
        Real.log (Real.log (ww n / 8)) + r) =
        -TT n + (5 / 2 : ℝ) * Real.log (TT n) - r by
          dsimp [TT, zz]
          ring]
    rw [show -TT n + (5 / 2 : ℝ) * Real.log (TT n) - r =
      -TT n + ((5 / 2 : ℝ) * Real.log (TT n)) + (-r) by ring]
    rw [Real.exp_add, Real.exp_add, Real.exp_neg, hexpz, hpowlog, hzeq]
    field_simp [show zz n ≠ 0 by positivity]
  have hwidth : (n : ℝ) * ee n ^ 3 = ww n := by rfl
  have hpowRatio : Real.rpow (TT n / LL n) (5 / 2 : ℝ) =
      Real.rpow (TT n) (5 / 2 : ℝ) * Real.rpow (LL n) (-5 / 2 : ℝ) := by
    calc
      Real.rpow (TT n / LL n) (5 / 2 : ℝ) =
          Real.rpow (TT n) (5 / 2 : ℝ) / Real.rpow (LL n) (5 / 2 : ℝ) :=
        Real.div_rpow htn.le hln.le _
      _ = Real.rpow (TT n) (5 / 2 : ℝ) * Real.rpow (LL n) (-5 / 2 : ℝ) := by
        have hneg : (-5 / 2 : ℝ) = -(5 / 2 : ℝ) := by ring
        calc
          Real.rpow (TT n) (5 / 2 : ℝ) / Real.rpow (LL n) (5 / 2 : ℝ) =
          Real.rpow (TT n) (5 / 2 : ℝ) *
                (Real.rpow (LL n) (5 / 2 : ℝ))⁻¹ := by rfl
          _ = Real.rpow (TT n) (5 / 2 : ℝ) *
              Real.rpow (LL n) (-(5 / 2 : ℝ)) := by
            exact congrArg (fun x ↦ Real.rpow (TT n) (5 / 2 : ℝ) * x)
              (Real.rpow_neg hln.le (5 / 2 : ℝ)).symm
          _ = _ := by rw [hneg]
  have hcombo : (n : ℝ) * ee n ^ 3 * Real.exp (-LL n) =
      8 * Real.exp (-r) * Real.rpow (TT n) (5 / 2 : ℝ) := by
    rw [hwidth, hExp]
  change (8 * Real.exp (-r) / Real.sqrt (2 * Real.pi)) *
      ((1 : ℝ) / dd n * Real.rpow (aa n / ee n ^ 2) (3 / 2 : ℝ) *
        Real.rpow (TT n / LL n) (5 / 2 : ℝ)) =
    (n : ℝ) / (dd n * Real.sqrt (2 * Real.pi)) *
      (Real.rpow (aa n) (3 / 2 : ℝ) * Real.rpow (LL n) (-5 / 2 : ℝ) *
        Real.exp (-LL n))
  rw [hpowSplit, hpowRatio]
  rw [show (n : ℝ) / (dd n * Real.sqrt (2 * Real.pi)) *
      (ee n ^ 3 * Real.rpow (aa n / ee n ^ 2) (3 / 2 : ℝ) *
        Real.rpow (LL n) (-5 / 2 : ℝ) * Real.exp (-LL n)) =
      (1 : ℝ) / dd n / Real.sqrt (2 * Real.pi) *
        Real.rpow (aa n / ee n ^ 2) (3 / 2 : ℝ) *
        Real.rpow (LL n) (-5 / 2 : ℝ) *
        ((n : ℝ) * ee n ^ 3 * Real.exp (-LL n)) by
          field_simp [hdn.ne']
          ]
  rw [hcombo]
  ring

lemma near_treeLeadingTail_tendsto
    (hRate : RateStatement) (hSums : AnalyticSumsStatement)
    {M : NatSeq} (hbare : bareSub M ∨ bareSuper M) (r : ℝ) :
    Tendsto (fun n ↦ treeLeadingTail n (M n) (nearHeight M r n))
      atTop (nhds (nearRate r)) := by
  let aa : RealSeq := fun n ↦ rate (degree M n)
  let LL : RealSeq := fun n ↦ nearNumerator M n r
  let hh : NatSeq := nearHeight M r
  have haaPos := near_rate_eventually_pos hRate hbare
  have haa := near_rate_tendsto_zero hRate hbare
  have hLL := nearNumerator_tendsto_atTop hbare r
  have hround := (near_rounding_asymptotics hRate hbare r).1
  have hhh := (near_rounding_asymptotics hRate hbare r).2
  have htail := hSums.2.2.2 aa LL hh haaPos haa hLL hround
  have hweighted := weightedTreeTail_div_treeTail_tendsto_one aa hh haaPos hhh
  have hratio : Tendsto
      (fun n ↦ weightedTreeTail (aa n) (hh n) /
        (Real.rpow (aa n) (3 / 2 : ℝ) * Real.rpow (LL n) (-5 / 2 : ℝ) *
          Real.exp (-LL n))) atTop (nhds 1) := by
    have hmul := hweighted.mul htail
    have hmul' : Tendsto
        (fun n ↦ weightedTreeTail (aa n) (hh n) / treeTail (aa n) (hh n) *
          (treeTail (aa n) (hh n) /
            (Real.rpow (aa n) (3 / 2 : ℝ) * Real.rpow (LL n) (-5 / 2 : ℝ) *
              Real.exp (-LL n)))) atTop (nhds 1) := by simpa using! hmul
    apply hmul'.congr'
    have htreePos : ∀ᶠ n in atTop, 0 < treeTail (aa n) (hh n) := by
      filter_upwards [haaPos] with n han
      exact treeTail_pos _ _ han
    have hLLPos : ∀ᶠ n in atTop, 0 < LL n :=
      ((tendsto_atTop.1 hLL) 1).mono fun _ h ↦ zero_lt_one.trans_le h
    filter_upwards [htreePos, haaPos, hLLPos] with n hn han hln
    have hden : 0 < Real.rpow (aa n) (3 / 2 : ℝ) *
        Real.rpow (LL n) (-5 / 2 : ℝ) * Real.exp (-LL n) := by
      exact mul_pos (mul_pos (Real.rpow_pos_of_pos han _) (Real.rpow_pos_of_pos hln _))
        (Real.exp_pos _)
    exact div_mul_div_cancel₀ hn.ne'
  have hnorm := nearLeadingNormalization_tendsto hRate hbare r
  have hmul := hratio.mul hnorm
  have hdegreePos : ∀ᶠ n in atTop, 0 < degree M n := by
    rcases bare_degree_side hbare with hsub | hsup
    · exact hsub.mono fun _ h ↦ h.1
    · exact hsup.mono fun _ h ↦ zero_lt_one.trans h
  have hdenPos : ∀ᶠ n in atTop,
      0 < Real.rpow (aa n) (3 / 2 : ℝ) * Real.rpow (LL n) (-5 / 2 : ℝ) *
        Real.exp (-LL n) := by
    have hLLPos : ∀ᶠ n in atTop, 0 < LL n :=
      ((tendsto_atTop.1 hLL) 1).mono fun _ h ↦ zero_lt_one.trans_le h
    filter_upwards [haaPos, hLLPos] with n han hln
    exact mul_pos (mul_pos (Real.rpow_pos_of_pos han _) (Real.rpow_pos_of_pos hln _))
      (Real.exp_pos _)
  have hmul' : Tendsto
      (fun n ↦ weightedTreeTail (aa n) (hh n) /
          (Real.rpow (aa n) (3 / 2 : ℝ) * Real.rpow (LL n) (-5 / 2 : ℝ) *
            Real.exp (-LL n)) * nearLeadingNormalization M r n)
      atTop (nhds (nearRate r)) := by simpa using! hmul
  apply hmul'.congr'
  filter_upwards [hdegreePos, hdenPos] with n hdn hden
  rw [treeLeadingTail_eq_weightedTreeTail n (M n) (hh n) hdn]
  have hdeq : degreeAt n (M n) = degree M n := rfl
  rw [hdeq]
  change weightedTreeTail (aa n) (hh n) /
      (Real.rpow (aa n) (3 / 2 : ℝ) * Real.rpow (LL n) (-5 / 2 : ℝ) *
        Real.exp (-LL n)) *
      ((n : ℝ) / (degree M n * Real.sqrt (2 * Real.pi)) *
        (Real.rpow (aa n) (3 / 2 : ℝ) * Real.rpow (LL n) (-5 / 2 : ℝ) *
          Real.exp (-LL n))) =
    (n : ℝ) / (degree M n * Real.sqrt (2 * Real.pi)) *
      weightedTreeTail (aa n) (hh n)
  calc
    weightedTreeTail (aa n) (hh n) /
          (Real.rpow (aa n) (3 / 2 : ℝ) * Real.rpow (LL n) (-5 / 2 : ℝ) *
            Real.exp (-LL n)) *
          ((n : ℝ) / (degree M n * Real.sqrt (2 * Real.pi)) *
            (Real.rpow (aa n) (3 / 2 : ℝ) * Real.rpow (LL n) (-5 / 2 : ℝ) *
              Real.exp (-LL n))) =
        (n : ℝ) / (degree M n * Real.sqrt (2 * Real.pi)) *
          (weightedTreeTail (aa n) (hh n) /
            (Real.rpow (aa n) (3 / 2 : ℝ) * Real.rpow (LL n) (-5 / 2 : ℝ) *
              Real.exp (-LL n)) *
            (Real.rpow (aa n) (3 / 2 : ℝ) * Real.rpow (LL n) (-5 / 2 : ℝ) *
              Real.exp (-LL n))) := by ring
    _ = _ := by rw [div_mul_cancel₀ _ hden.ne']

end

end Erdos745.WrapUp.Proofs.W06_POISSON


namespace Erdos745.WrapUp.Proofs.W06_POISSON

noncomputable section

open Erdos745.WrapUp
open Filter
open scoped BigOperators Topology

def nearCutoff (B : ℝ) (M : NatSeq) (n : ℕ) : ℕ :=
  ⌈B * (epsilon M n)⁻¹ ^ 2 * Real.log (widthParameter M n)⌉₊

def finitePowerTail (n h : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico h (n + 1), Real.rpow (k : ℝ) (-5 / 2 : ℝ)

lemma sum_Ico_rpow_split (h N : ℕ) (hhN : h ≤ N) :
    (∑ k ∈ Finset.Ico h (N + 1), Real.rpow (k : ℝ) (-5 / 2 : ℝ)) =
      Real.rpow (h : ℝ) (-5 / 2 : ℝ) +
        ∑ k ∈ Finset.Ico h N, Real.rpow ((k + 1 : ℕ) : ℝ) (-5 / 2 : ℝ) := by
  induction N, hhN using Nat.le_induction with
  | base => simp
  | succ N hhN ih =>
      conv_lhs => rw [Finset.sum_Ico_succ_top (Nat.le_succ_of_le hhN)]
      rw [ih]
      rw [Finset.sum_Ico_succ_top hhN]
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_succ]
      ring

lemma finitePowerTail_nonneg (n h : ℕ) : 0 ≤ finitePowerTail n h := by
  rw [finitePowerTail]
  exact Finset.sum_nonneg fun k _ ↦ Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ k) _

lemma finitePowerTail_le (n h : ℕ) (hh : 0 < h) :
    finitePowerTail n h ≤ 2 * Real.rpow (h : ℝ) (-3 / 2 : ℝ) := by
  by_cases hhn : h ≤ n
  · rw [finitePowerTail, sum_Ico_rpow_split h n hhn]
    have hanti : AntitoneOn (fun x : ℝ ↦ Real.rpow x (-5 / 2 : ℝ))
        (Set.Icc (h : ℝ) (n : ℝ)) :=
      (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)).mono (by
        intro x hx
        exact lt_of_lt_of_le (by exact_mod_cast hh) hx.1)
    have hsum := hanti.sum_le_integral_Ico hhn
    have hzero : (0 : ℝ) ∉ Set.uIcc (h : ℝ) (n : ℝ) := by
      rw [Set.uIcc_of_le (by exact_mod_cast hhn)]
      intro hz
      have := hz.1
      exact (not_le_of_gt (by exact_mod_cast hh : (0 : ℝ) < h)) this
    have hintEq : (∫ x : ℝ in (h : ℝ)..(n : ℝ),
        Real.rpow x (-5 / 2 : ℝ)) =
        (Real.rpow (n : ℝ) (-5 / 2 + 1 : ℝ) -
          Real.rpow (h : ℝ) (-5 / 2 + 1 : ℝ)) / (-5 / 2 + 1 : ℝ) :=
      integral_rpow (r := (-5 / 2 : ℝ)) (Or.inr ⟨by norm_num, hzero⟩)
    norm_num at hintEq
    have hintEq' : (∫ x : ℝ in (h : ℝ)..(n : ℝ), Real.rpow x (-5 / 2 : ℝ)) =
        (Real.rpow (n : ℝ) (-3 / 2 : ℝ) -
          Real.rpow (h : ℝ) (-3 / 2 : ℝ)) / (-3 / 2 : ℝ) := by
      simpa only [Real.rpow_eq_pow, neg_div] using! hintEq
    have hnnonneg : 0 ≤ Real.rpow (n : ℝ) (-3 / 2 : ℝ) :=
      Real.rpow_nonneg (by positivity) _
    have hint : (∫ x : ℝ in (h : ℝ)..(n : ℝ), Real.rpow x (-5 / 2 : ℝ)) ≤
        (2 / 3 : ℝ) * Real.rpow (h : ℝ) (-3 / 2 : ℝ) := by
      calc
        (∫ x : ℝ in (h : ℝ)..(n : ℝ), Real.rpow x (-5 / 2 : ℝ)) =
            (Real.rpow (n : ℝ) (-3 / 2 : ℝ) -
              Real.rpow (h : ℝ) (-3 / 2 : ℝ)) / (-3 / 2 : ℝ) := hintEq'
        _ ≤ _ := by nlinarith
    have hhreal : (1 : ℝ) ≤ h := by exact_mod_cast hh
    have hfirst : Real.rpow (h : ℝ) (-5 / 2 : ℝ) ≤
        Real.rpow (h : ℝ) (-3 / 2 : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_le hhreal (by norm_num)
    have hsum' := hsum.trans hint
    have hhpow0 : 0 ≤ Real.rpow (h : ℝ) (-3 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
    linarith
  · have hempty : Finset.Ico h (n + 1) = ∅ := by
      rw [Finset.Ico_eq_empty]
      omega
    rw [finitePowerTail, hempty]
    simp
    positivity

lemma sum_fin_indicator_rpow_eq_finitePowerTail (n h : ℕ) :
    (∑ k : Fin (n + 1), if h ≤ k.val then
      Real.rpow (k.val : ℝ) (-5 / 2 : ℝ) else 0) = finitePowerTail n h := by
  rw [finitePowerTail]
  change (∑ k : Fin (n + 1),
    (fun j : ℕ ↦ if h ≤ j then Real.rpow (j : ℝ) (-5 / 2 : ℝ) else 0) k.val) = _
  calc
    (∑ k : Fin (n + 1),
      (fun j : ℕ ↦ if h ≤ j then Real.rpow (j : ℝ) (-5 / 2 : ℝ) else 0) k.val) =
        ∑ k ∈ Finset.range (n + 1),
          (if h ≤ k then Real.rpow (k : ℝ) (-5 / 2 : ℝ) else 0) :=
      by simpa only using! (Fin.sum_univ_eq_sum_range
        (fun j : ℕ ↦ if h ≤ j then Real.rpow (j : ℝ) (-5 / 2 : ℝ) else 0) (n + 1))
    _ = _ := by
      calc
        (∑ k ∈ Finset.range (n + 1),
            if h ≤ k then Real.rpow (k : ℝ) (-5 / 2 : ℝ) else 0) =
            ∑ k ∈ Finset.Ico h (n + 1),
              (if h ≤ k then Real.rpow (k : ℝ) (-5 / 2 : ℝ) else 0) := by
          symm
          apply Finset.sum_subset
          · intro k hk
            exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
          · intro k hk hnot
            have : ¬h ≤ k := by
              intro hle
              apply hnot
              exact Finset.mem_Ico.mpr ⟨hle, Finset.mem_range.mp hk⟩
            simp [this]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [if_pos (Finset.mem_Ico.1 hk).1]

lemma outsideRectangleTupleSum_le_global
    (n M q h H : ℕ) (C kappa : ℝ)
    (hC : 0 ≤ C) (hkappa : 0 < kappa)
    (hdegree : 1 / 2 ≤ degreeAt n M)
    (hGlobal : ∀ ks : Fin q → ℕ, (∀ i, 0 < ks i) →
      tupleGlobalBound n M q ks C kappa)
    (hh : 0 < h) :
    outsideRectangleTupleSum n M q h H ≤
      C * (n : ℝ) ^ q *
        Real.exp (-kappa * (epsilon (fun _ ↦ M) n) ^ 2 * (H : ℝ)) *
          (finitePowerTail n h) ^ q := by
  classical
  have heq : epsilon (fun _ ↦ M) n = |degreeAt n M - 1| := by rfl
  rw [outsideRectangleTupleSum]
  calc
    (∑ ks : Fin q → Fin (n + 1),
        if (∀ i, h ≤ (ks i).val) ∧ (∃ i, H < (ks i).val) then
          tupleMoment n M q (fun i ↦ (ks i).val) else 0) ≤
      ∑ ks : Fin q → Fin (n + 1),
        C * (n : ℝ) ^ q *
          Real.exp (-kappa * |degreeAt n M - 1| ^ 2 * (H : ℝ)) *
            ∏ i, (if h ≤ (ks i).val then
              Real.rpow ((ks i).val : ℝ) (-5 / 2 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro ks _
      by_cases hout : (∀ i, h ≤ (ks i).val) ∧ (∃ i, H < (ks i).val)
      · rw [if_pos hout]
        have hpos : ∀ i, 0 < (ks i).val :=
          fun i ↦ lt_of_lt_of_le hh (hout.1 i)
        have hg := hGlobal (fun i ↦ (ks i).val) hpos
        rw [tupleGlobalBound] at hg
        have hKnonneg : 0 ≤ ∑ i, ((ks i).val : ℝ) := by positivity
        have hcube : 0 ≤ (∑ i, ((ks i).val : ℝ)) ^ 3 / (n : ℝ) ^ 2 := by
          positivity
        obtain ⟨i, hi⟩ := hout.2
        have hHK : (H : ℝ) ≤ ∑ j, ((ks j).val : ℝ) := by
          calc
            (H : ℝ) ≤ ((ks i).val : ℝ) := by exact_mod_cast hi.le
            _ ≤ ∑ j, ((ks j).val : ℝ) := Finset.single_le_sum
              (f := fun j : Fin q ↦ ((ks j).val : ℝ))
              (fun j _ ↦ by positivity) (Finset.mem_univ i)
        have harg : |degreeAt n M - 1| ^ 2 * (H : ℝ) ≤
            |degreeAt n M - 1| ^ 2 * (∑ j, ((ks j).val : ℝ)) +
              (∑ j, ((ks j).val : ℝ)) ^ 3 / (n : ℝ) ^ 2 := by
          nlinarith [sq_nonneg |degreeAt n M - 1|]
        have hexp : Real.exp (-kappa *
              (|degreeAt n M - 1| ^ 2 * (∑ j, ((ks j).val : ℝ)) +
                (∑ j, ((ks j).val : ℝ)) ^ 3 / (n : ℝ) ^ 2)) ≤
            Real.exp (-kappa * |degreeAt n M - 1| ^ 2 * (H : ℝ)) := by
          apply Real.exp_le_exp.mpr
          nlinarith
        have hprod :
            (∏ i, Real.rpow ((ks i).val : ℝ) (-5 / 2 : ℝ)) =
              ∏ i, (if h ≤ (ks i).val then
                Real.rpow ((ks i).val : ℝ) (-5 / 2 : ℝ) else 0) := by
          apply Finset.prod_congr rfl
          intro j _
          rw [if_pos (hout.1 j)]
        rw [hprod] at hg
        calc
          tupleMoment n M q (fun i ↦ (ks i).val) ≤
              (C * (n : ℝ) ^ q *
                ∏ i, (if h ≤ (ks i).val then
                  Real.rpow ((ks i).val : ℝ) (-5 / 2 : ℝ) else 0)) *
                Real.exp (-kappa * ((degreeAt n M - 1) ^ 2 *
                  (∑ i, ((ks i).val : ℝ)) +
                  (∑ i, ((ks i).val : ℝ)) ^ 3 / (n : ℝ) ^ 2)) := hg
          _ ≤ (C * (n : ℝ) ^ q *
                ∏ i, (if h ≤ (ks i).val then
                  Real.rpow ((ks i).val : ℝ) (-5 / 2 : ℝ) else 0)) *
                Real.exp (-kappa * |degreeAt n M - 1| ^ 2 * (H : ℝ)) := by
            have hexp' : Real.exp (-kappa * ((degreeAt n M - 1) ^ 2 *
                  (∑ i, ((ks i).val : ℝ)) +
                  (∑ i, ((ks i).val : ℝ)) ^ 3 / (n : ℝ) ^ 2)) ≤
                Real.exp (-kappa * |degreeAt n M - 1| ^ 2 * (H : ℝ)) := by
              simpa [sq_abs] using! hexp
            exact mul_le_mul_of_nonneg_left hexp'
              (mul_nonneg (mul_nonneg hC (by positivity))
                (Finset.prod_nonneg fun j _ ↦ by
                  by_cases hj : h ≤ (ks j).val
                  · rw [if_pos hj]; exact Real.rpow_nonneg (by positivity) _
                  · rw [if_neg hj]))
          _ = _ := by ring
      · rw [if_neg hout]
        exact mul_nonneg
          (mul_nonneg (mul_nonneg hC (by positivity)) (Real.exp_pos _).le)
          (Finset.prod_nonneg fun j _ ↦ by
            by_cases hj : h ≤ (ks j).val
            · rw [if_pos hj]; exact Real.rpow_nonneg (by positivity) _
            · rw [if_neg hj])
    _ = C * (n : ℝ) ^ q *
        Real.exp (-kappa * |degreeAt n M - 1| ^ 2 * (H : ℝ)) *
          (finitePowerTail n h) ^ q := by
      rw [← Finset.mul_sum]
      have hfac := Fintype.sum_pow
        (fun k : Fin (n + 1) ↦ if h ≤ k.val then
          Real.rpow (k.val : ℝ) (-5 / 2 : ℝ) else 0) q
      rw [← hfac]
      rw [sum_fin_indicator_rpow_eq_finitePowerTail]
    _ = _ := by rw [heq]

lemma near_cutoff_basic
    (hRate : RateStatement) {M : NatSeq} (hbare : bareSub M ∨ bareSuper M)
    (r B : ℝ) (hB : 4 < B) :
    Tendsto (nearCutoff B M) atTop atTop ∧
    (∀ᶠ n in atTop, nearHeight M r n ≤ nearCutoff B M n) ∧
    (∀ᶠ n in atTop, nearCutoff B M n ≤ n) := by
  let ee : RealSeq := epsilon M
  let ww : RealSeq := widthParameter M
  let XX : RealSeq := fun n ↦ B * (ee n)⁻¹ ^ 2 * Real.log (ww n)
  have hee := bare_epsilon_tendsto_zero hbare
  have heePos := bare_epsilon_pos hbare
  have hww := bare_width_tendsto_atTop hbare
  have hlogw : Tendsto (fun n ↦ Real.log (ww n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hww
  have hlogwPos : ∀ᶠ n in atTop, 0 < Real.log (ww n) :=
    ((tendsto_atTop.1 hlogw) 1).mono fun _ h ↦ zero_lt_one.trans_le h
  have hinvTop : Tendsto (fun n ↦ (ee n)⁻¹ ^ 2) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    obtain ⟨c, hc, hcb⟩ : ∃ c : ℝ, 0 < c ∧ b ≤ c⁻¹ ^ 2 := by
      refine ⟨1 / Real.sqrt (max 1 b), by positivity, ?_⟩
      have hm : 0 < max 1 b := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      rw [inv_div, div_one]
      rw [Real.sq_sqrt hm.le]
      exact le_max_right _ _
    have hec : ∀ᶠ n in atTop, ee n ≤ c :=
      ((tendsto_order.1 hee).2 c hc).mono fun _ h ↦ h.le
    filter_upwards [heePos, hec] with n hen henc
    have hinv : c⁻¹ ≤ (ee n)⁻¹ := (inv_le_inv₀ hc hen).2 henc
    exact hcb.trans (sq_le_sq₀ (by positivity) (by positivity) |>.2 hinv)
  have hX : Tendsto XX atTop atTop := by
    have hprod := hlogw.const_mul_atTop
      (lt_trans (by norm_num : (0 : ℝ) < 4) hB)
    apply tendsto_atTop.2
    intro b
    have hi : ∀ᶠ n in atTop, 1 ≤ (ee n)⁻¹ ^ 2 := (tendsto_atTop.1 hinvTop) 1
    have hp : ∀ᶠ n in atTop, b ≤ B * Real.log (ww n) := (tendsto_atTop.1 hprod) b
    filter_upwards [hi, hp, hlogwPos] with n hi hp hl
    dsimp [XX]
    calc
      b ≤ B * Real.log (ww n) := hp
      _ ≤ B * (ee n)⁻¹ ^ 2 * Real.log (ww n) := by
        have hB0 : 0 ≤ B := by linarith
        have hBB : B ≤ B * (ee n)⁻¹ ^ 2 := le_mul_of_one_le_right hB0 hi
        exact mul_le_mul_of_nonneg_right hBB hl.le
  have hH : Tendsto (nearCutoff B M) atTop atTop := by
    exact tendsto_nat_ceil_atTop.comp (by simpa [nearCutoff, XX] using! hX)
  have hscale := near_height_scale hRate hbare r
  have hlogRatio : Tendsto
      (fun n ↦ Real.log (widthParameter M n / 8) /
        Real.log (widthParameter M n)) atTop (nhds 1) := by
    have hconst : Tendsto (fun _ : ℕ ↦ Real.log (8 : ℝ)) atTop
        (nhds (Real.log 8)) := tendsto_const_nhds
    have hdiff : ∀ᶠ n in atTop,
        Real.log (widthParameter M n / 8) =
          Real.log (widthParameter M n) - Real.log 8 := by
      have hwpos : ∀ᶠ n in atTop, 0 < widthParameter M n :=
        ((tendsto_atTop.1 hww) 1).mono fun _ h ↦ zero_lt_one.trans_le h
      filter_upwards [hwpos] with n hn
      rw [Real.log_div hn.ne' (by norm_num : (8 : ℝ) ≠ 0)]
    have hsmall := hconst.div_atTop hlogw
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hone' := hone.sub hsmall
    have hone'' : Tendsto (fun n : ℕ ↦
        1 - Real.log 8 / Real.log (ww n)) atTop (nhds 1) := by
      simpa using! hone'
    apply hone''.congr'
    filter_upwards [hdiff, hlogwPos] with n heq hl
    dsimp [ww] at hl ⊢
    rw [heq]
    field_simp [hl.ne']
  have hheightRatio : Tendsto
      (fun n ↦ epsilon M n ^ 2 * (nearHeight M r n : ℝ) /
        Real.log (widthParameter M n)) atTop (nhds 2) := by
    have hm := hscale.mul hlogRatio
    have hm' : Tendsto
        (fun n ↦ (epsilon M n ^ 2 * (nearHeight M r n : ℝ) /
          Real.log (widthParameter M n / 8)) *
          (Real.log (widthParameter M n / 8) /
            Real.log (widthParameter M n))) atTop (nhds 2) := by simpa using! hm
    apply hm'.congr'
    have hlog8Pos : ∀ᶠ n in atTop, 0 < Real.log (widthParameter M n / 8) :=
      ((tendsto_atTop.1 (near_log_width_tendsto_atTop hbare)) 1).mono
        fun _ h ↦ zero_lt_one.trans_le h
    filter_upwards [hlog8Pos, hlogwPos] with n h8 hw
    field_simp [h8.ne', hw.ne']
  have hheightLt : ∀ᶠ n in atTop,
      epsilon M n ^ 2 * (nearHeight M r n : ℝ) /
        Real.log (widthParameter M n) < B :=
    (tendsto_order.1 hheightRatio).2 B (by linarith)
  have hheightCut : ∀ᶠ n in atTop, nearHeight M r n ≤ nearCutoff B M n := by
    filter_upwards [heePos, hlogwPos, hheightLt] with n hen hlog hs
    have hbound : (nearHeight M r n : ℝ) ≤
        B * (epsilon M n)⁻¹ ^ 2 * Real.log (widthParameter M n) := by
      have he2 : 0 < epsilon M n ^ 2 := sq_pos_of_pos hen
      rw [div_lt_iff₀ hlog] at hs
      have hs' : epsilon M n ^ 2 * (nearHeight M r n : ℝ) <
          B * Real.log (widthParameter M n) := hs
      have hdiv : (nearHeight M r n : ℝ) <
          (B * Real.log (widthParameter M n)) / epsilon M n ^ 2 := by
        exact (lt_div_iff₀ he2).2 (by nlinarith)
      calc
        (nearHeight M r n : ℝ) ≤
            (B * Real.log (widthParameter M n)) / epsilon M n ^ 2 := hdiv.le
        _ = B * (epsilon M n)⁻¹ ^ 2 * Real.log (widthParameter M n) := by
          field_simp [hen.ne']
    exact_mod_cast hbound.trans (Nat.le_ceil _)
  have hHleN : ∀ᶠ n in atTop, nearCutoff B M n ≤ n := by
    have hlogDiv : Tendsto (fun n ↦ Real.log (ww n) / ww n) atTop (nhds 0) := by
      have hbase := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      simpa [ww] using! hbase.comp hww
    have hterm : Tendsto (fun n ↦ B * ee n * (Real.log (ww n) / ww n))
        atTop (nhds 0) := by
      have ht := (hee.mul hlogDiv).const_mul B
      have ht' : Tendsto (fun n ↦ B *
          (epsilon M n * (Real.log (ww n) / ww n))) atTop (nhds 0) := by
        simpa [ee] using! ht
      apply ht'.congr'
      filter_upwards with n
      dsimp [ee]
      ring
    have hninv : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 1
    have hratio : Tendsto
        (fun n ↦ (XX n + 1) / (n : ℝ)) atTop (nhds 0) := by
      have hadd := hterm.add hninv
      have hadd' : Tendsto
          (fun n ↦ B * ee n * (Real.log (ww n) / ww n) + 1 / (n : ℝ))
          atTop (nhds 0) := by simpa using! hadd
      apply hadd'.congr'
      filter_upwards [heePos, eventually_gt_atTop 0] with n hen hnpos
      dsimp [XX, ee, ww, widthParameter]
      have hn : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
      field_simp [hen.ne', hn]
    have hlt : ∀ᶠ n in atTop, (XX n + 1) / (n : ℝ) < 1 :=
      (tendsto_order.1 hratio).2 1 zero_lt_one
    filter_upwards [hlt, heePos, hlogwPos, eventually_gt_atTop 0]
      with n hn hen hlog hnpos
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hceil : (nearCutoff B M n : ℝ) < XX n + 1 := by
      exact Nat.ceil_lt_add_one (by
        exact mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) hlog.le)
    have hupper : XX n + 1 < (n : ℝ) := (div_lt_one hnreal).1 hn
    exact Nat.le_of_lt (by exact_mod_cast hceil.trans hupper)
  exact ⟨hH, hheightCut, hHleN⟩

lemma near_cutoff_error_tendsto_zero
    {M : NatSeq} (hbare : bareSub M ∨ bareSuper M)
    (q : ℕ) (B C : ℝ) (hB : 0 < B) :
    Tendsto (fun n ↦
      C * ((q : ℝ) * (nearCutoff B M n : ℝ) / n +
        epsilon M n * ((q : ℝ) * (nearCutoff B M n : ℝ)) ^ 2 / n +
        ((q : ℝ) * (nearCutoff B M n : ℝ)) ^ 3 / (n : ℝ) ^ 2))
      atTop (nhds 0) := by
  let ee : RealSeq := epsilon M
  let ww : RealSeq := widthParameter M
  let XX : RealSeq := fun n ↦ B * (ee n)⁻¹ ^ 2 * Real.log (ww n)
  let HH : NatSeq := nearCutoff B M
  have hee := bare_epsilon_tendsto_zero hbare
  have heePos := bare_epsilon_pos hbare
  have hww := bare_width_tendsto_atTop hbare
  have hlog1 : Tendsto (fun n ↦ Real.log (ww n) / ww n) atTop (nhds 0) := by
    simpa [ww] using! (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hww
  have hlog2 : Tendsto (fun n ↦ Real.log (ww n) ^ 2 / ww n) atTop (nhds 0) := by
    simpa [ww] using! (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp hww
  have hlog3 : Tendsto (fun n ↦ Real.log (ww n) ^ 3 / ww n) atTop (nhds 0) := by
    simpa [ww] using! (Real.tendsto_pow_log_div_mul_add_atTop 1 0 3 one_ne_zero).comp hww
  have hlog3w2 : Tendsto (fun n ↦ Real.log (ww n) ^ 3 / ww n ^ 2)
      atTop (nhds 0) := by
    have hinv : Tendsto (fun n ↦ (ww n)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hww
    convert hlog3.mul hinv using 1 <;> ring
  have hninv : Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun n ↦
      (q : ℝ) * (XX n + 1) / n +
        ee n * ((q : ℝ) * (XX n + 1)) ^ 2 / n +
        ((q : ℝ) * (XX n + 1)) ^ 3 / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
    have h1 : Tendsto (fun n ↦ (XX n + 1) / (n : ℝ)) atTop (nhds 0) := by
      have ht := (hee.mul hlog1).const_mul B
      have hu := ht.add hninv
      have hu' : Tendsto
          (fun n ↦ B * (epsilon M n * (Real.log (ww n) / ww n)) +
            ((n : ℝ))⁻¹) atTop (nhds 0) := by simpa using! hu
      apply hu'.congr'
      filter_upwards [heePos] with n hen
      dsimp [XX, ee, ww, widthParameter]
      field_simp [hen.ne']
    have h2 : Tendsto (fun n ↦ ee n * (XX n + 1) ^ 2 / (n : ℝ))
        atTop (nhds 0) := by
      have hmain := hlog2.const_mul (B ^ 2)
      have hcross := (hee.pow 2 |>.mul hlog1).const_mul (2 * B)
      have hlast := hee.mul hninv
      have hall := (hmain.add hcross).add hlast
      have hall' : Tendsto
          (fun n ↦ B ^ 2 * (Real.log (ww n) ^ 2 / ww n) +
            2 * B * (epsilon M n ^ 2 * (Real.log (ww n) / ww n)) +
            epsilon M n * ((n : ℝ))⁻¹) atTop (nhds 0) := by simpa using! hall
      apply hall'.congr'
      filter_upwards [heePos] with n hen
      dsimp [XX, ee, ww, widthParameter]
      field_simp [hen.ne']
      ring
    have h3 : Tendsto (fun n ↦ (XX n + 1) ^ 3 / (n : ℝ) ^ 2)
        atTop (nhds 0) := by
      have hmain := hlog3w2.const_mul (B ^ 3)
      have hcross2 := ((hee.pow 2).mul hlog2 |>.mul
        (tendsto_inv_atTop_zero.comp hww)).const_mul (3 * B ^ 2)
      have hcross1 := ((hee.pow 4).mul hlog1 |>.mul
        (tendsto_inv_atTop_zero.comp hww)).const_mul (3 * B)
      have hlast := hninv.pow 2
      have hall := ((hmain.add hcross2).add hcross1).add hlast
      have hall' : Tendsto
          (fun n ↦ B ^ 3 * (Real.log (ww n) ^ 3 / ww n ^ 2) +
            3 * B ^ 2 * (epsilon M n ^ 2 * (Real.log (ww n) ^ 2 / ww n) *
              (ww n)⁻¹) +
            3 * B * (epsilon M n ^ 4 * (Real.log (ww n) / ww n) *
              (ww n)⁻¹) + ((n : ℝ))⁻¹ ^ 2) atTop (nhds 0) := by
        simpa [ww] using! hall
      apply hall'.congr'
      filter_upwards [heePos] with n hen
      dsimp [XX, ee, ww, widthParameter]
      field_simp [hen.ne']
      ring
    have hall := ((h1.const_mul (q : ℝ)).add (h2.const_mul ((q : ℝ) ^ 2))).add
      (h3.const_mul ((q : ℝ) ^ 3))
    convert hall using 1 <;> ring
  have hceil : ∀ᶠ n in atTop, (HH n : ℝ) ≤ XX n + 1 := by
    have hlog : Tendsto (fun n ↦ Real.log (ww n)) atTop atTop :=
      Real.tendsto_log_atTop.comp hww
    have hlogPos := (tendsto_atTop.1 hlog) 1
    filter_upwards [heePos, hlogPos] with n hen hlogn
    exact (Nat.ceil_lt_add_one (by
      exact mul_nonneg (mul_nonneg hB.le (sq_nonneg _))
        (zero_le_one.trans hlogn))).le
  have hinner : Tendsto (fun n ↦
      (q : ℝ) * (HH n : ℝ) / n +
        ee n * ((q : ℝ) * (HH n : ℝ)) ^ 2 / n +
        ((q : ℝ) * (HH n : ℝ)) ^ 3 / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards [heePos] with n hen
      positivity
    · filter_upwards [hceil, heePos] with n hH hen
      have hn : 0 ≤ (n : ℝ) := by positivity
      have hq : 0 ≤ (q : ℝ) := by positivity
      have hXX : 0 ≤ XX n + 1 := le_trans (by positivity : 0 ≤ (HH n : ℝ)) hH
      have hlin := mul_le_mul_of_nonneg_left hH hq
      have hsq := (sq_le_sq₀ (by positivity) (by positivity)).2 hlin
      have hcub := pow_le_pow_left₀ (by positivity) hlin 3
      exact add_le_add (add_le_add
        (div_le_div_of_nonneg_right hlin hn)
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hen.le) hn))
        (div_le_div_of_nonneg_right hcub (by positivity))
    · simpa using! hsmall
  simpa [HH, ee] using! hinner.const_mul C

lemma near_cutoff_treeLeadingTail_tendsto_zero
    (hRate : RateStatement) (hSums : AnalyticSumsStatement)
    {M : NatSeq} (hbare : bareSub M ∨ bareSuper M)
    (B : ℝ) (hB : 8 < B) :
    Tendsto (fun n ↦ treeLeadingTail n (M n) (nearCutoff B M n + 1))
      atTop (nhds 0) := by
  let aa : RealSeq := fun n ↦ rate (degree M n)
  let HH : NatSeq := fun n ↦ nearCutoff B M n + 1
  let QQ : RealSeq := fun n ↦ aa n * (HH n : ℝ)
  have haaPos := near_rate_eventually_pos hRate hbare
  have haa := near_rate_tendsto_zero hRate hbare
  have hH := (near_cutoff_basic hRate hbare 0 B (lt_trans (by norm_num) hB)).1
  have hHH : Tendsto HH atTop atTop := by
    apply tendsto_atTop_mono' atTop (Eventually.of_forall fun n ↦ Nat.le_succ (nearCutoff B M n)) hH
  have hratio := rate_over_epsilon_sq_tendsto hRate hbare
  have hww := bare_width_tendsto_atTop hbare
  have hlogw : Tendsto (fun n ↦ Real.log (widthParameter M n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hww
  have hQlower : ∀ᶠ n in atTop,
      (B / 4) * Real.log (widthParameter M n) ≤ QQ n := by
    have hratioLower : ∀ᶠ n in atTop, (1 / 4 : ℝ) ≤
        rate (degree M n) / epsilon M n ^ 2 :=
      ((tendsto_order.1 hratio).1 (1 / 4) (by norm_num)).mono fun _ h ↦ h.le
    have hepos := bare_epsilon_pos hbare
    have hlogpos := ((tendsto_atTop.1 hlogw) 1).mono
      fun _ h ↦ zero_lt_one.trans_le h
    filter_upwards [hratioLower, hepos, hlogpos, haaPos] with n hr hen hl ha
    have hceil := Nat.le_ceil
      (B * (epsilon M n)⁻¹ ^ 2 * Real.log (widthParameter M n))
    have haH : rate (degree M n) *
        (B * (epsilon M n)⁻¹ ^ 2 * Real.log (widthParameter M n)) ≤ QQ n := by
      dsimp [QQ, HH]
      exact (mul_le_mul_of_nonneg_left
        (hceil.trans (by exact_mod_cast Nat.le_add_right (nearCutoff B M n) 1)) ha.le)
    have hprod : (B / 4) * Real.log (widthParameter M n) ≤
        rate (degree M n) *
          (B * (epsilon M n)⁻¹ ^ 2 * Real.log (widthParameter M n)) := by
      have hBL : 0 ≤ B * Real.log (widthParameter M n) := by positivity
      have hm := mul_le_mul_of_nonneg_left hr hBL
      field_simp [hen.ne'] at hm ⊢
      nlinarith
    exact hprod.trans haH
  have hQTop : Tendsto QQ atTop atTop := by
    exact tendsto_atTop_mono' atTop hQlower
      (hlogw.const_mul_atTop (by linarith : 0 < B / 4))
  have hmove := hSums.2.2.2 aa QQ HH haaPos haa hQTop (by
    simpa [QQ] using! tendsto_const_nhds)
  have hweighted := weightedTreeTail_div_treeTail_tendsto_one aa HH haaPos hHH
  have hnormZero : Tendsto (fun n : ℕ ↦
      (n : ℝ) / (degree M n * Real.sqrt (2 * Real.pi)) *
        (Real.rpow (aa n) (3 / 2 : ℝ) * Real.rpow (QQ n) (-5 / 2 : ℝ) *
          Real.exp (-QQ n))) atTop (nhds 0) := by
    have hdeg := bare_degree_tendsto_one hbare
    have hpref : Tendsto (fun n ↦ 1 / (degree M n * Real.sqrt (2 * Real.pi)))
        atTop (nhds (1 / (1 * Real.sqrt (2 * Real.pi)))) := by
      exact tendsto_const_nhds.div (hdeg.mul tendsto_const_nhds) (by positivity)
    have hratePow : Tendsto
        (fun n ↦ Real.rpow (rate (degree M n) / epsilon M n ^ 2) (3 / 2 : ℝ))
        atTop (nhds (Real.rpow (1 / 2 : ℝ) (3 / 2 : ℝ))) := by
      simpa using! (rate_over_epsilon_sq_tendsto hRate hbare).rpow_const
        (Or.inl (by norm_num : (1 / 2 : ℝ) ≠ 0))
    have hqpow : Tendsto (fun n ↦ Real.rpow (QQ n) (-5 / 2 : ℝ)) atTop (nhds 0) :=
      by
        have ht := (tendsto_rpow_neg_atTop
          (by norm_num : (0 : ℝ) < 5 / 2)).comp hQTop
        apply ht.congr'
        filter_upwards with n
        rw [Real.rpow_eq_pow]
        exact congrArg (fun z : ℝ ↦ (QQ n) ^ z) (by ring)
    have hdecay : Tendsto (fun n ↦ widthParameter M n * Real.exp (-QQ n))
        atTop (nhds 0) := by
      have hupper : Tendsto (fun n ↦ Real.rpow (widthParameter M n)
          (1 - B / 4)) atTop (nhds 0) :=
        by
          have ht := (tendsto_rpow_neg_atTop
            (by linarith : 0 < B / 4 - 1)).comp hww
          apply ht.congr'
          filter_upwards with n
          rw [Real.rpow_eq_pow]
          exact congrArg (fun z : ℝ ↦ (widthParameter M n) ^ z) (by ring)
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      · filter_upwards [bare_epsilon_pos hbare] with n hen
        exact mul_nonneg (by dsimp [widthParameter]; positivity) (Real.exp_pos _).le
      · have hwpos : ∀ᶠ n in atTop, 0 < widthParameter M n :=
          ((tendsto_atTop.1 hww) 1).mono fun _ h ↦ zero_lt_one.trans_le h
        filter_upwards [hQlower, hwpos] with n hlow hwn
        calc
          widthParameter M n * Real.exp (-QQ n) ≤
              widthParameter M n * Real.exp (-(B / 4 * Real.log (widthParameter M n))) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hwn.le
          _ = Real.rpow (widthParameter M n) (1 - B / 4) := by
            calc
              widthParameter M n * Real.exp (-(B / 4 * Real.log (widthParameter M n))) =
                  Real.exp (Real.log (widthParameter M n)) *
                    Real.exp ((-B / 4) * Real.log (widthParameter M n)) := by
                rw [Real.exp_log hwn]
                congr 2 <;> ring
              _ = Real.exp ((1 - B / 4) * Real.log (widthParameter M n)) := by
                rw [← Real.exp_add]
                congr 1 <;> ring
              _ = Real.rpow (widthParameter M n) (1 - B / 4) := by
                rw [Real.rpow_eq_pow]
                rw [show (1 - B / 4) * Real.log (widthParameter M n) =
                  Real.log (widthParameter M n) * (1 - B / 4) by ring]
                exact (Real.rpow_def_of_pos hwn _).symm
    have hall := (((hpref.mul hratePow).mul hqpow).mul hdecay)
    simp only [mul_zero] at hall
    apply hall.congr'
    filter_upwards [bare_epsilon_pos hbare, haaPos] with n hen han
    dsimp [aa, QQ]
    have he2 : 0 < epsilon M n ^ 2 := sq_pos_of_pos hen
    have hsplit : Real.rpow (rate (degree M n)) (3 / 2 : ℝ) =
        epsilon M n ^ 3 *
          Real.rpow (rate (degree M n) / epsilon M n ^ 2) (3 / 2 : ℝ) := by
      have haaEq : rate (degree M n) = epsilon M n ^ 2 *
          (rate (degree M n) / epsilon M n ^ 2) := by
        symm
        exact mul_div_cancel₀ _ (pow_ne_zero _ hen.ne')
      calc
        Real.rpow (rate (degree M n)) (3 / 2 : ℝ) =
            Real.rpow (epsilon M n ^ 2 *
              (rate (degree M n) / epsilon M n ^ 2)) (3 / 2 : ℝ) := by rw [← haaEq]
        _ = Real.rpow (epsilon M n ^ 2) (3 / 2 : ℝ) *
            Real.rpow (rate (degree M n) / epsilon M n ^ 2) (3 / 2 : ℝ) :=
          Real.mul_rpow he2.le (div_nonneg han.le he2.le)
        _ = _ := by
          have hepow : Real.rpow (epsilon M n ^ 2) (3 / 2 : ℝ) =
              epsilon M n ^ 3 := by
            calc
              Real.rpow (epsilon M n ^ 2) (3 / 2 : ℝ) =
                  Real.rpow (Real.rpow (epsilon M n) 2) (3 / 2 : ℝ) := by
                exact congrArg (fun x ↦ Real.rpow x (3 / 2 : ℝ))
                  (Real.rpow_natCast (epsilon M n) 2).symm
              _ = Real.rpow (epsilon M n) (2 * (3 / 2 : ℝ)) :=
                (Real.rpow_mul hen.le 2 (3 / 2 : ℝ)).symm
              _ = Real.rpow (epsilon M n) (3 : ℝ) := by congr 1 <;> norm_num
              _ = epsilon M n ^ 3 := by
                simpa only using! (Real.rpow_natCast (epsilon M n) 3)
          rw [hepow]
    change 1 / (degree M n * Real.sqrt (2 * Real.pi)) *
        Real.rpow (rate (degree M n) / epsilon M n ^ 2) (3 / 2 : ℝ) *
        Real.rpow (rate (degree M n) * (HH n : ℝ)) (-5 / 2 : ℝ) *
        (widthParameter M n * Real.exp (-(rate (degree M n) * (HH n : ℝ)))) =
      (n : ℝ) / (degree M n * Real.sqrt (2 * Real.pi)) *
        (Real.rpow (rate (degree M n)) (3 / 2 : ℝ) *
          Real.rpow (rate (degree M n) * (HH n : ℝ)) (-5 / 2 : ℝ) *
          Real.exp (-(rate (degree M n) * (HH n : ℝ))) )
    rw [hsplit]
    rw [← show (n : ℝ) * epsilon M n ^ 3 = widthParameter M n by rfl]
    ring
  have hratioTail : Tendsto (fun n ↦
      weightedTreeTail (aa n) (HH n) /
        (Real.rpow (aa n) (3 / 2 : ℝ) * Real.rpow (QQ n) (-5 / 2 : ℝ) *
          Real.exp (-QQ n))) atTop (nhds 1) := by
    have hm := hweighted.mul hmove
    have hm' : Tendsto (fun n ↦
        weightedTreeTail (aa n) (HH n) / treeTail (aa n) (HH n) *
          (treeTail (aa n) (HH n) /
            (Real.rpow (aa n) (3 / 2 : ℝ) * Real.rpow (QQ n) (-5 / 2 : ℝ) *
              Real.exp (-QQ n)))) atTop (nhds 1) := by simpa using! hm
    apply hm'.congr'
    filter_upwards [haaPos] with n han
    have ht := treeTail_pos (aa n) (HH n) han
    exact div_mul_div_cancel₀ ht.ne'
  have hall := hratioTail.mul hnormZero
  simp only [mul_zero] at hall
  apply hall.congr'
  have hdegPos : ∀ᶠ n in atTop, 0 < degree M n :=
    ((tendsto_order.1 (bare_degree_tendsto_one hbare)).1 0 zero_lt_one).mono
      fun _ h ↦ h
  have hdenPos : ∀ᶠ n in atTop,
      0 < Real.rpow (aa n) (3 / 2 : ℝ) * Real.rpow (QQ n) (-5 / 2 : ℝ) *
        Real.exp (-QQ n) := by
    filter_upwards [haaPos, (tendsto_atTop.1 hQTop) 1] with n han hqn
    exact mul_pos (mul_pos (Real.rpow_pos_of_pos han _)
      (Real.rpow_pos_of_pos (zero_lt_one.trans_le hqn) _)) (Real.exp_pos _)
  filter_upwards [hdegPos, hdenPos] with n hdn hden
  rw [treeLeadingTail_eq_weightedTreeTail n (M n) (HH n) hdn]
  have hdeq : degreeAt n (M n) = degree M n := rfl
  rw [hdeq]
  change weightedTreeTail (aa n) (HH n) /
      (Real.rpow (aa n) (3 / 2 : ℝ) * Real.rpow (QQ n) (-5 / 2 : ℝ) *
        Real.exp (-QQ n)) *
      ((n : ℝ) / (degree M n * Real.sqrt (2 * Real.pi)) *
        (Real.rpow (aa n) (3 / 2 : ℝ) * Real.rpow (QQ n) (-5 / 2 : ℝ) *
          Real.exp (-QQ n))) =
    (n : ℝ) / (degree M n * Real.sqrt (2 * Real.pi)) *
      weightedTreeTail (aa n) (HH n)
  calc
    _ = (n : ℝ) / (degree M n * Real.sqrt (2 * Real.pi)) *
        (weightedTreeTail (aa n) (HH n) /
          (Real.rpow (aa n) (3 / 2 : ℝ) * Real.rpow (QQ n) (-5 / 2 : ℝ) *
            Real.exp (-QQ n)) *
          (Real.rpow (aa n) (3 / 2 : ℝ) * Real.rpow (QQ n) (-5 / 2 : ℝ) *
            Real.exp (-QQ n))) := by ring
    _ = _ := by rw [div_mul_cancel₀ _ hden.ne']

set_option maxHeartbeats 1600000 in
lemma barelyCritical_factorialMoments
    (hEnum : FiniteEnumerationStatement) (hRate : RateStatement)
    (hTuple : TupleEstimatesStatement) (hSums : AnalyticSumsStatement)
    (M : NatSeq) (hbare : bareSub M ∨ bareSuper M) (r : ℝ) :
    ∀ q : ℕ, 0 < q → Tendsto
      (fun n ↦ expectM n (M n)
        (fun G ↦ (falling (treeCountGE G (nearHeight M r n)) q : ℝ)))
      atTop (nhds ((nearRate r) ^ q)) := by
  intro q hq
  obtain ⟨C, kappa, hC, hkappa, n0, hGlobalLocal⟩ := hTuple.1 q hq
  let B : ℝ := max 16 ((q + 2 : ℝ) / kappa)
  have hB16 : (16 : ℝ) ≤ B := le_max_left _ _
  have hB8 : (8 : ℝ) < B := lt_of_lt_of_le (by norm_num) hB16
  have hB4 : (4 : ℝ) < B := lt_trans (by norm_num) hB8
  have hBpos : 0 < B := lt_trans (by norm_num) hB4
  have hkB : (q : ℝ) + 1 < kappa * B := by
    have hfrac : (q + 2 : ℝ) / kappa ≤ B := le_max_right _ _
    have := (div_le_iff₀ hkappa).1 hfrac
    nlinarith
  let HH : NatSeq := nearCutoff B M
  let hh : NatSeq := nearHeight M r
  let eta : RealSeq := fun n ↦ C *
    ((q : ℝ) * (HH n : ℝ) / n +
      epsilon M n * ((q : ℝ) * (HH n : ℝ)) ^ 2 / n +
      ((q : ℝ) * (HH n : ℝ)) ^ 3 / (n : ℝ) ^ 2)
  have heta : Tendsto eta atTop (nhds 0) := by
    simpa [eta, HH] using! near_cutoff_error_tendsto_zero hbare q B C hBpos
  have hcut := near_cutoff_basic hRate hbare r B hB4
  have hHtop : Tendsto HH atTop atTop := by simpa [HH] using! hcut.1
  have hhH : ∀ᶠ n in atTop, hh n ≤ HH n := by simpa [hh, HH] using! hcut.2.1
  have hHn : ∀ᶠ n in atTop, HH n ≤ n := by simpa [HH] using! hcut.2.2
  have hhTop := (near_rounding_asymptotics hRate hbare r).2
  have hhpos : ∀ᶠ n in atTop, 0 < hh n := by
    have hOne := (tendsto_atTop.1 hhTop) 1
    exact hOne.mono fun _ h ↦ Nat.zero_lt_one.trans_le h
  have hcap := bare_admissible hbare
  have hdeg := bare_degree_tendsto_one hbare
  have hdegLo : ∀ᶠ n in atTop, 1 / 2 ≤ degree M n :=
    ((tendsto_order.1 hdeg).1 (1 / 2) (by norm_num)).mono fun _ h ↦ h.le
  have hdegHi : ∀ᶠ n in atTop, degree M n ≤ 3 / 2 :=
    ((tendsto_order.1 hdeg).2 (3 / 2) (by norm_num)).mono fun _ h ↦ h.le
  have hdegPos : ∀ᶠ n in atTop, 0 < degree M n :=
    hdegLo.mono fun _ h ↦ lt_of_lt_of_le (by norm_num) h
  have hn0 : ∀ᶠ n in atTop, n0 ≤ n := eventually_ge_atTop n0
  have htrunc : Tendsto
      (fun n ↦ truncatedTreeLeadingSum n (M n) (hh n) (HH n))
      atTop (nhds (nearRate r)) := by
    have hfull := near_treeLeadingTail_tendsto hRate hSums hbare r
    have htail := near_cutoff_treeLeadingTail_tendsto_zero hRate hSums hbare B hB8
    have hsub := hfull.sub htail
    simp only [sub_zero] at hsub
    apply hsub.congr'
    have hratePos := near_rate_eventually_pos hRate hbare
    filter_upwards [hhH, hHn, hdegPos, hratePos] with n hlow hhigh hd ha
    exact (truncatedTreeLeadingSum_eq_tail_sub n (M n) (hh n) (HH n)
      hlow hhigh hd ha).symm
  have hlead : Tendsto
      (fun n ↦ rectangleLeadingSum n (M n) q (hh n) (HH n))
      atTop (nhds ((nearRate r) ^ q)) := by
    have hp := htrunc.pow q
    apply hp.congr'
    filter_upwards with n
    exact (rectangleLeadingSum_eq_pow n (M n) q (hh n) (HH n)).symm
  have hrect : Tendsto
      (fun n ↦ rectangleTupleSum n (M n) q (hh n) (HH n))
      atTop (nhds ((nearRate r) ^ q)) := by
    have hlower := (Real.continuous_exp.continuousAt.tendsto.comp heta.neg).mul hlead
    have hupper := (Real.continuous_exp.continuousAt.tendsto.comp heta).mul hlead
    have hqHsmall : ∀ᶠ n in atTop,
        (q : ℝ) * (HH n : ℝ) ≤ (n : ℝ) / 16 := by
      have hterm : Tendsto (fun n ↦ (q : ℝ) * (HH n : ℝ) / n)
          atTop (nhds 0) := by
        have hsum := near_cutoff_error_tendsto_zero hbare q B 1 hBpos
        have hsum' : Tendsto (fun n ↦
            (q : ℝ) * (HH n : ℝ) / n +
              epsilon M n * ((q : ℝ) * (HH n : ℝ)) ^ 2 / n +
              ((q : ℝ) * (HH n : ℝ)) ^ 3 / (n : ℝ) ^ 2)
            atTop (nhds 0) := by simpa [HH] using! hsum
        apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
          (show Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0) from tendsto_const_nhds)
          hsum'
        · filter_upwards with n
          positivity
        · filter_upwards [bare_epsilon_pos hbare] with n hen
          have h2 : 0 ≤ epsilon M n *
              ((q : ℝ) * (HH n : ℝ)) ^ 2 / n := by positivity
          have h3 : 0 ≤ ((q : ℝ) * (HH n : ℝ)) ^ 3 /
              (n : ℝ) ^ 2 := by positivity
          linarith
      have he := (tendsto_order.1 hterm).2 (1 / 16) (by norm_num)
      filter_upwards [he, eventually_gt_atTop 0] with n hn hnpos
      have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
      have hmul := (div_le_iff₀ hnreal).1 hn.le
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using! hmul
    have hsandwich : ∀ᶠ n in atTop,
        Real.exp (-eta n) * rectangleLeadingSum n (M n) q (hh n) (HH n) ≤
          rectangleTupleSum n (M n) q (hh n) (HH n) ∧
        rectangleTupleSum n (M n) q (hh n) (HH n) ≤
          Real.exp (eta n) * rectangleLeadingSum n (M n) q (hh n) (HH n) := by
      filter_upwards [hn0, hcap, hdegLo, hdegHi, hhpos, hhH, hHn, hdegPos,
        hqHsmall] with n hn hc hlo hhi hhp hlow hHN hdp hqHs
      apply rectangleTupleSum_sandwich n (M n) q (hh n) (HH n) (eta n)
        (lt_of_lt_of_le hhp (hlow.trans hHN)) hdp hhp
      intro ks hks
      have hpos : ∀ i, 0 < (ks i).val :=
        fun i ↦ lt_of_lt_of_le hhp (hks i).1
      have hK : (∑ i, ((ks i).val : ℝ)) ≤ (q : ℝ) * (HH n : ℝ) := by
        calc
          (∑ i, ((ks i).val : ℝ)) ≤ ∑ _i : Fin q, (HH n : ℝ) :=
            Finset.sum_le_sum fun i _ ↦ by exact_mod_cast (hks i).2
          _ = (q : ℝ) * (HH n : ℝ) := by simp
      have hKsmall : (∑ i, ((ks i).val : ℝ)) ≤ (n : ℝ) / 16 := by
        exact hK.trans hqHs
      have hloc := (hGlobalLocal n (M n) (fun i ↦ (ks i).val) hn hc hlo hhi hpos).2 hKsmall
      refine ⟨hloc.1, hloc.2.trans ?_⟩
      rw [tupleLocalBound] at hloc
      have hK0 : 0 ≤ ∑ i, ((ks i).val : ℝ) := by positivity
      have hqH0 : 0 ≤ (q : ℝ) * (HH n : ℝ) := by positivity
      have h1 := div_le_div_of_nonneg_right hK (by positivity : 0 ≤ (n : ℝ))
      have h2 : |degreeAt n (M n) - 1| * (∑ i, ((ks i).val : ℝ)) ^ 2 /
          (n : ℝ) ≤ |degreeAt n (M n) - 1| *
            ((q : ℝ) * (HH n : ℝ)) ^ 2 / (n : ℝ) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hK0 hqH0).2 hK)
            (abs_nonneg (degreeAt n (M n) - 1))) (by positivity)
      have h3 := div_le_div_of_nonneg_right
        (pow_le_pow_left₀ hK0 hK 3) (by positivity : 0 ≤ (n : ℝ) ^ 2)
      have heq : |degreeAt n (M n) - 1| = epsilon M n := rfl
      dsimp [eta]
      rw [heq]
      exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add h1 h2) h3) hC.le
    have hlower' : Tendsto (fun n ↦
        Real.exp (-eta n) * rectangleLeadingSum n (M n) q (hh n) (HH n))
        atTop (nhds ((nearRate r) ^ q)) := by simpa using! hlower
    have hupper' : Tendsto (fun n ↦
        Real.exp (eta n) * rectangleLeadingSum n (M n) q (hh n) (HH n))
        atTop (nhds ((nearRate r) ^ q)) := by simpa using! hupper
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower' hupper'
      (hsandwich.mono fun _ h ↦ h.1) (hsandwich.mono fun _ h ↦ h.2)
  have hout : Tendsto
      (fun n ↦ outsideRectangleTupleSum n (M n) q (hh n) (HH n))
      atTop (nhds 0) := by
    let upper : RealSeq := fun n ↦
      C * (n : ℝ) ^ q *
        Real.exp (-kappa * epsilon M n ^ 2 * (HH n : ℝ)) *
          (2 * Real.rpow (hh n : ℝ) (-3 / 2 : ℝ)) ^ q
    have hupper : Tendsto upper atTop (nhds 0) := by
      have hscale := near_height_scale hRate hbare r
      have hww := bare_width_tendsto_atTop hbare
      have hlogw : Tendsto (fun n ↦ Real.log (widthParameter M n)) atTop atTop :=
        Real.tendsto_log_atTop.comp hww
      have hbase : Tendsto (fun n ↦ Real.rpow (widthParameter M n)
          ((q : ℝ) - kappa * B)) atTop (nhds 0) :=
        by simpa only [neg_sub] using!
          (tendsto_rpow_neg_atTop (by linarith : 0 < kappa * B - (q : ℝ))).comp hww
      apply squeeze_zero'
      · filter_upwards with n
        dsimp [upper]
        positivity
      · have hepos := bare_epsilon_pos hbare
        have hwpos : ∀ᶠ n in atTop, 1 ≤ widthParameter M n :=
          (tendsto_atTop.1 hww) 1
        have hlogone : ∀ᶠ n in atTop, 1 ≤ Real.log (widthParameter M n) :=
          (tendsto_atTop.1 hlogw) 1
        have hlogpos : ∀ᶠ n in atTop, 0 < Real.log (widthParameter M n) :=
          hlogone.mono fun _ h ↦ zero_lt_one.trans_le h
        have hheight : ∀ᶠ n in atTop,
            (epsilon M n)⁻¹ ^ 2 * Real.log (widthParameter M n) ≤
              (hh n : ℝ) := by
          have hscaleLower : ∀ᶠ n in atTop, (3 / 2 : ℝ) ≤
              epsilon M n ^ 2 * (hh n : ℝ) /
                Real.log (widthParameter M n / 8) :=
            ((tendsto_order.1 hscale).1 (3 / 2) (by norm_num)).mono fun _ h ↦ h.le
          have hlogcompare : ∀ᶠ n in atTop,
              (2 / 3 : ℝ) * Real.log (widthParameter M n) ≤
                Real.log (widthParameter M n / 8) := by
            have hratio : Tendsto (fun n ↦
                Real.log (widthParameter M n / 8) /
                  Real.log (widthParameter M n)) atTop (nhds 1) := by
              have hc : Tendsto (fun n : ℕ ↦ Real.log (8 : ℝ) /
                  Real.log (widthParameter M n)) atTop (nhds 0) :=
                tendsto_const_nhds.div_atTop hlogw
              have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
                tendsto_const_nhds
              have hlim : Tendsto (fun n : ℕ ↦
                  1 - Real.log 8 / Real.log (widthParameter M n))
                  atTop (nhds 1) := by simpa using! hone.sub hc
              apply hlim.congr'
              filter_upwards [hlogpos, hepos] with n hl hen
              have hnpos : 0 < n := by
                by_contra hn
                have : n = 0 := Nat.eq_zero_of_not_pos hn
                subst n
                simp [widthParameter] at hl
              have hw : 0 < widthParameter M n := by
                dsimp [widthParameter]
                positivity
              rw [Real.log_div hw.ne' (by norm_num : (8 : ℝ) ≠ 0)]
              field_simp [hl.ne']
            have he := (tendsto_order.1 hratio).1 (2 / 3) (by norm_num)
            filter_upwards [he, hlogpos] with n he hl
            exact (le_div_iff₀ hl).1 he.le
          filter_upwards [hscaleLower, hlogcompare, hepos, hlogpos] with n hs hl hen hlog
          have hlog8 : 0 < Real.log (widthParameter M n / 8) :=
            lt_of_lt_of_le (mul_pos (by norm_num) hlog) hl
          have he2 : 0 < epsilon M n ^ 2 := sq_pos_of_pos hen
          have hs' : (3 / 2 : ℝ) * Real.log (widthParameter M n / 8) ≤
              epsilon M n ^ 2 * (hh n : ℝ) :=
            (le_div_iff₀ hlog8).1 hs
          rw [inv_pow]
          rw [show (epsilon M n ^ 2)⁻¹ * Real.log (widthParameter M n) =
            Real.log (widthParameter M n) / epsilon M n ^ 2 by
              rw [div_eq_mul_inv]; ring]
          apply (div_le_iff₀ he2).2
          nlinarith
        have hcutexp : ∀ᶠ n in atTop,
            Real.exp (-kappa * epsilon M n ^ 2 * (HH n : ℝ)) ≤
              Real.rpow (widthParameter M n) (-kappa * B) := by
          filter_upwards [hepos, hlogpos, hwpos] with n hen hlog hwn
          have hceil := Nat.le_ceil
            (B * (epsilon M n)⁻¹ ^ 2 * Real.log (widthParameter M n))
          have he2 : 0 < epsilon M n ^ 2 := sq_pos_of_pos hen
          have harg : B * Real.log (widthParameter M n) ≤
              epsilon M n ^ 2 * (HH n : ℝ) := by
            have hm := mul_le_mul_of_nonneg_left hceil he2.le
            have hx : B * (epsilon M n)⁻¹ ^ 2 * Real.log (widthParameter M n) =
                B * Real.log (widthParameter M n) / epsilon M n ^ 2 := by
              field_simp [hen.ne']
            dsimp [HH, nearCutoff]
            rw [hx]
            field_simp [hen.ne'] at hm
            exact hm
          calc
            Real.exp (-kappa * epsilon M n ^ 2 * (HH n : ℝ)) ≤
                Real.exp ((-kappa * B) * Real.log (widthParameter M n)) :=
              Real.exp_le_exp.mpr (by nlinarith)
            _ = Real.rpow (widthParameter M n) (-kappa * B) := by
              rw [show (-kappa * B) * Real.log (widthParameter M n) =
                Real.log (widthParameter M n) * (-kappa * B) by ring]
              rw [Real.rpow_eq_pow]
              exact (Real.rpow_def_of_pos
                (lt_of_lt_of_le zero_lt_one hwn) _).symm
        filter_upwards [hepos, hwpos, hlogone, hheight, hcutexp, hhpos]
          with n hen hwn hlogone hheight hcutexp hhp
        have hlog : 0 < Real.log (widthParameter M n) :=
          zero_lt_one.trans_le hlogone
        have hhreal : 0 < (hh n : ℝ) := by exact_mod_cast hhp
        have hpowHeight : Real.rpow (hh n : ℝ) (-3 / 2 : ℝ) ≤
            epsilon M n ^ 3 * Real.rpow (Real.log (widthParameter M n))
              (-3 / 2 : ℝ) := by
          have hanti := Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
            (by norm_num : (-3 / 2 : ℝ) ≤ 0)
          have hxpos : 0 < (epsilon M n)⁻¹ ^ 2 *
              Real.log (widthParameter M n) := by positivity
          have hp := hanti hxpos hhreal hheight
          have hsimp : Real.rpow ((epsilon M n)⁻¹ ^ 2 *
                Real.log (widthParameter M n)) (-3 / 2 : ℝ) =
              epsilon M n ^ 3 * Real.rpow (Real.log (widthParameter M n))
                (-3 / 2 : ℝ) := by
            have hinvpow : Real.rpow ((epsilon M n)⁻¹ ^ 2) (-3 / 2 : ℝ) =
                epsilon M n ^ 3 := by
              have heq : (epsilon M n)⁻¹ ^ 2 =
                  Real.rpow (epsilon M n) (-2 : ℝ) := by
                calc
                  (epsilon M n)⁻¹ ^ 2 = (epsilon M n ^ 2)⁻¹ := by
                    field_simp [hen.ne']
                  _ = (Real.rpow (epsilon M n) (2 : ℝ))⁻¹ := by
                    exact congrArg Inv.inv (Real.rpow_natCast (epsilon M n) 2).symm
                  _ = Real.rpow (epsilon M n) (-2 : ℝ) :=
                    (Real.rpow_neg hen.le 2).symm
              calc
                Real.rpow ((epsilon M n)⁻¹ ^ 2) (-3 / 2 : ℝ) =
                    Real.rpow (Real.rpow (epsilon M n) (-2 : ℝ))
                      (-3 / 2 : ℝ) := by rw [heq]
                _ = Real.rpow (epsilon M n) ((-2 : ℝ) * (-3 / 2 : ℝ)) :=
                  (Real.rpow_mul hen.le (-2 : ℝ) (-3 / 2 : ℝ)).symm
                _ = Real.rpow (epsilon M n) (3 : ℝ) := by congr 1 <;> norm_num
                _ = epsilon M n ^ 3 := by
                  simpa only using! (Real.rpow_natCast (epsilon M n) 3)
            calc
              Real.rpow ((epsilon M n)⁻¹ ^ 2 *
                  Real.log (widthParameter M n)) (-3 / 2 : ℝ) =
                  Real.rpow ((epsilon M n)⁻¹ ^ 2) (-3 / 2 : ℝ) *
                    Real.rpow (Real.log (widthParameter M n)) (-3 / 2 : ℝ) :=
                Real.mul_rpow (by positivity) hlog.le
              _ = _ := by rw [hinvpow]
          exact hp.trans_eq hsimp
        have hlogpow : Real.rpow (Real.log (widthParameter M n))
            (-3 / 2 : ℝ) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hlogone (by norm_num)
        have hntail : (n : ℝ) * Real.rpow (hh n : ℝ) (-3 / 2 : ℝ) ≤
            widthParameter M n := by
          calc
            (n : ℝ) * Real.rpow (hh n : ℝ) (-3 / 2 : ℝ) ≤
                (n : ℝ) * (epsilon M n ^ 3 *
                  Real.rpow (Real.log (widthParameter M n)) (-3 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hpowHeight (by positivity)
            _ ≤ (n : ℝ) * epsilon M n ^ 3 := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_of_le_one_right (pow_nonneg hen.le 3) hlogpow) (by positivity)
            _ = widthParameter M n := rfl
        have hpowntail := pow_le_pow_left₀
          (mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)) hntail q
        dsimp [upper]
        calc
          C * (n : ℝ) ^ q *
                Real.exp (-kappa * epsilon M n ^ 2 * (HH n : ℝ)) *
                (2 * Real.rpow (hh n : ℝ) (-3 / 2 : ℝ)) ^ q ≤
              C * 2 ^ q * ((n : ℝ) * Real.rpow (hh n : ℝ) (-3 / 2 : ℝ)) ^ q *
                Real.rpow (widthParameter M n) (-kappa * B) := by
            have heq : C * (n : ℝ) ^ q *
                  Real.exp (-kappa * epsilon M n ^ 2 * (HH n : ℝ)) *
                  (2 * Real.rpow (hh n : ℝ) (-3 / 2 : ℝ)) ^ q =
                (C * 2 ^ q * ((n : ℝ) *
                  Real.rpow (hh n : ℝ) (-3 / 2 : ℝ)) ^ q) *
                  Real.exp (-kappa * epsilon M n ^ 2 * (HH n : ℝ)) := by ring
            rw [heq]
            exact mul_le_mul
              (le_refl _)
              hcutexp
              (Real.exp_pos _).le
              (mul_nonneg (mul_nonneg hC.le (by positivity))
                (pow_nonneg (mul_nonneg (by positivity)
                  (Real.rpow_nonneg (by positivity) _)) q))
          _ ≤ C * 2 ^ q * (widthParameter M n) ^ q *
                Real.rpow (widthParameter M n) (-kappa * B) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpowntail
                (mul_nonneg hC.le (by positivity)))
              (Real.rpow_nonneg (by positivity) _)
          _ = C * 2 ^ q * Real.rpow (widthParameter M n)
                ((q : ℝ) - kappa * B) := by
            rw [show (widthParameter M n) ^ q =
              Real.rpow (widthParameter M n) (q : ℝ) by
                simpa only using! (Real.rpow_natCast (widthParameter M n) q).symm]
            have hr : Real.rpow (widthParameter M n) (q : ℝ) *
                Real.rpow (widthParameter M n) (-kappa * B) =
                Real.rpow (widthParameter M n) ((q : ℝ) - kappa * B) := by
              calc
                _ = Real.rpow (widthParameter M n)
                    ((q : ℝ) + (-kappa * B)) :=
                  (Real.rpow_add (lt_of_lt_of_le zero_lt_one hwn) _ _).symm
                _ = _ := by congr 1 <;> ring
            calc
              C * 2 ^ q * Real.rpow (widthParameter M n) (q : ℝ) *
                  Real.rpow (widthParameter M n) (-kappa * B) =
                  C * 2 ^ q * (Real.rpow (widthParameter M n) (q : ℝ) *
                    Real.rpow (widthParameter M n) (-kappa * B)) := by ring
              _ = _ := by rw [hr]
      · simpa using! hbase.const_mul (C * 2 ^ q)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    · exact Filter.Eventually.of_forall fun n ↦ outsideRectangleTupleSum_nonneg n (M n) q (hh n) (HH n)
    · filter_upwards [hn0, hcap, hdegLo, hdegHi, hhpos] with n hn hc hlo hhi hhp
      have hg := (hGlobalLocal n (M n) (fun _ : Fin q ↦ 1) hn hc hlo hhi
        (fun _ ↦ Nat.zero_lt_one)).1
      have hb := outsideRectangleTupleSum_le_global n (M n) q (hh n) (HH n)
        C kappa hC.le hkappa hlo (fun ks hpos ↦
          (hGlobalLocal n (M n) ks hn hc hlo hhi hpos).1) hhp
      exact hb.trans (by
        dsimp [upper]
        have htailpow := pow_le_pow_left₀ (finitePowerTail_nonneg n (hh n))
          (finitePowerTail_le n (hh n) hhp) q
        exact mul_le_mul_of_nonneg_left htailpow
          (mul_nonneg (mul_nonneg hC.le (by positivity)) (Real.exp_pos _).le))
  have htotal : Tendsto (fun n ↦ factorialTupleSum n (M n) q (hh n))
      atTop (nhds ((nearRate r) ^ q)) := by
    have hadd := hrect.add hout
    simp only [add_zero] at hadd
    apply hadd.congr'
    filter_upwards [hhH] with n hlow
    exact (factorialTupleSum_eq_rectangle_add_outside n (M n) q (hh n) (HH n) hlow).symm
  apply htotal.congr'
  filter_upwards [hcap, hhpos] with n hc hp
  exact (factorialMoment_treeCountGE_internal hEnum n (M n) q (hh n) hc hp).symm

end

end Erdos745.WrapUp.Proofs.W06_POISSON
