module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-02».MomentLocal

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT02.Mean

open Filter Finset Set
open scoped BigOperators Topology
open Erdos448.Stage4
open Erdos448.Stage4.Contracts

noncomputable section

instance (p : Prop) : Decidable p := Classical.propDecidable p

lemma lambda_lt_two {Y : Set ℝ} (hY : CompactMomentDomain Y) :
    lambdaOfFamily Y < 2 := by
  have hsup_mem : sSup Y ∈ Y := hY.2.1.sSup_mem hY.1
  exact max_lt one_lt_two (hY.2.2 hsup_mem).2

lemma one_le_lambda (Y : Set ℝ) : 1 ≤ lambdaOfFamily Y :=
  le_max_left _ _

lemma y_le_lambda {Y : Set ℝ} (hY : CompactMomentDomain Y)
    {y : ℝ} (hy : y ∈ Y) : y ≤ lambdaOfFamily Y := by
  exact (le_csSup hY.2.1.isBounded.bddAbove hy).trans (le_max_right _ _)

lemma local_constant_pos {Y : Set ℝ} (hY : CompactMomentDomain Y) :
    0 < localFamilyConstant Y := by
  unfold localFamilyConstant
  have hden : 0 < 2 - lambdaOfFamily Y := sub_pos.mpr (lambda_lt_two hY)
  positivity

lemma momentWeight_one (q : MomentParameters) : momentWeight q 1 = 1 := by
  simp only [momentWeight, dif_pos zero_lt_one, moment,
    divisorSet, Nat.divisors_one, Finset.sum_singleton, omegaBelowRaw,
    roughTau, Nat.cast_one]
  have hr : IsRough 1 q.theta := by
    intro p hp hpd
    exact (hp.ne_one (Nat.dvd_one.mp hpd)).elim
  have hrs : IsRough 1 q.sigma := by
    intro p hp hpd
    exact (hp.ne_one (Nat.dvd_one.mp hpd)).elim
  simp [roughIndicator, hr, hrs, omegaBelow]

lemma momentWeight_prime
    (q : MomentParameters) (p : ℕ) (hp : p.Prime)
    (hsigma : q.sigma ≤ p) (hpu : (p : ℝ) < q.u) :
    momentWeight q p = (1 + q.y) / 2 := by
  have h := (Erdos448.Stage7.ROOT02.MomentLocal.p010 q).2 p 1 hp (by omega)
  have hp_theta : ¬(p : ℝ) < q.theta :=
    not_lt_of_ge (q.sigma_ge_theta.trans hsigma)
  have hp_sigma : ¬(p : ℝ) < q.sigma := not_lt_of_ge hsigma
  rw [show momentWeight q p = moment q ⟨p, hp.pos⟩ by simp [momentWeight, hp.pos]]
  have hv : moment q ⟨p, hp.pos⟩ = 2⁻¹ * (q.y + 1) := by
    simpa [pow_one, hp_theta, hp_sigma, hpu] using h.1
  rw [hv]
  ring

lemma momentWeight_prime_pow_bound
    {Y : Set ℝ} (hY : CompactMomentDomain Y)
    (q : MomentParameters) (hy : q.y ∈ Y)
    (p j : ℕ) (hp : p.Prime) :
    0 ≤ momentWeight q (p ^ j) ∧
      momentWeight q (p ^ j) ≤ lambdaOfFamily Y ^ j := by
  by_cases hj : j = 0
  · subst j
    simp [momentWeight_one, one_le_lambda]
  · have hjp : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
    have h := (Erdos448.Stage7.ROOT02.MomentLocal.p010 q).2 p j hp hjp
    have hpj : 0 < p ^ j := pow_pos hp.pos j
    have heq : momentWeight q (p ^ j) = moment q ⟨p ^ j, hpj⟩ := by
      simp [momentWeight, hpj]
    rw [heq]
    exact ⟨h.2.1, h.2.2.trans
      (pow_le_pow_left₀ (by positivity) (max_le (one_le_lambda Y) (y_le_lambda hY hy)) j)⟩

lemma local_series_summable
    (hEXT : EXT001Statement) {Y : Set ℝ} (hY : CompactMomentDomain Y)
    (q : MomentParameters) (hy : q.y ∈ Y) (p : ℕ) (hp : p.Prime) :
    Summable (fun j : ℕ => momentWeight q (p ^ j) / (p : ℝ) ^ j) := by
  let range : MeanParameterRange 1 (lambdaOfFamily Y) :=
    ⟨zero_le_one, zero_le_one.trans (one_le_lambda Y),
      lambda_lt_two hY⟩
  rcases hEXT 1 (lambdaOfFamily Y) range with ⟨out⟩
  apply out.local_series_summable (momentWeight q) _ p hp
  intro r hr j
  have h := momentWeight_prime_pow_bound hY q hy r j hr
  exact ⟨h.1, by simpa using h.2⟩

lemma local_factor_error
    (hEXT : EXT001Statement) {Y : Set ℝ} (hY : CompactMomentDomain Y)
    (q : MomentParameters) (hy : q.y ∈ Y)
    (p : ℕ) (hp : p.Prime) (hsigma : q.sigma ≤ p)
    (hpu : (p : ℝ) < q.u) :
    let L := (1 - 1 / (p : ℝ)) * meanEulerSeries (momentWeight q) p
    let c := (q.y - 1) / 2
    |L - (1 + c / p)| ≤
      localFamilyConstant Y * (p : ℝ).rpow (-2) := by
  dsimp
  let lam := lambdaOfFamily Y
  let a := (1 + q.y) / 2
  let term : ℕ → ℝ := fun j => momentWeight q (p ^ j) / (p : ℝ) ^ j
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlam1 : 1 ≤ lam := one_le_lambda Y
  have hlam2 : lam < 2 := lambda_lt_two hY
  have hlam0 : 0 ≤ lam := zero_le_one.trans hlam1
  have hratio0 : 0 ≤ lam / (p : ℝ) := div_nonneg hlam0 hp0.le
  have hratio1 : lam / (p : ℝ) < 1 := by
    rw [div_lt_one hp0]
    exact hlam2.trans_le hp2
  have hsum : Summable term := local_series_summable hEXT hY q hy p hp
  have hsplit := hsum.sum_add_tsum_nat_add 2
  have hterm0 : term 0 = 1 := by simp [term, momentWeight_one]
  have hterm1 : term 1 = a / p := by
    simp [term, a, momentWeight_prime q p hp hsigma hpu]
  have htail_nonneg : ∀ j : ℕ, 0 ≤ term (j + 2) := by
    intro j
    exact div_nonneg (momentWeight_prime_pow_bound hY q hy p (j + 2) hp).1
      (pow_nonneg hp0.le _)
  have htail_bound : ∀ j : ℕ,
      term (j + 2) ≤ (lam / (p : ℝ)) ^ (j + 2) := by
    intro j
    have hnum := (momentWeight_prime_pow_bound hY q hy p (j + 2) hp).2
    calc
      term (j + 2) ≤ lam ^ (j + 2) / (p : ℝ) ^ (j + 2) :=
        div_le_div_of_nonneg_right hnum (pow_nonneg hp0.le _)
      _ = (lam / (p : ℝ)) ^ (j + 2) := by rw [div_pow]
  have hgeom : Summable (fun j : ℕ => (lam / (p : ℝ)) ^ (j + 2)) :=
    (summable_geometric_of_lt_one hratio0 hratio1).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  have htail_sum := Summable.tsum_le_tsum htail_bound
    (hsum.comp_injective (fun _ _ h => Nat.add_right_cancel h)) hgeom
  have hgeom_eq :
      (∑' j : ℕ, (lam / (p : ℝ)) ^ (j + 2)) =
        (lam / (p : ℝ)) ^ 2 / (1 - lam / (p : ℝ)) := by
    let r := lam / (p : ℝ)
    have hs : Summable (fun j : ℕ => r ^ j) :=
      summable_geometric_of_lt_one hratio0 hratio1
    calc
      (∑' j : ℕ, r ^ (j + 2)) = ∑' j : ℕ, r ^ 2 * r ^ j := by
        apply tsum_congr
        intro j
        rw [pow_add]
        ring
      _ = r ^ 2 * ∑' j : ℕ, r ^ j := hs.tsum_mul_left _
      _ = r ^ 2 * (1 - r)⁻¹ := by rw [tsum_geometric_of_lt_one hratio0 hratio1]
      _ = r ^ 2 / (1 - r) := by rw [div_eq_mul_inv]
  rw [hgeom_eq] at htail_sum
  let tail := ∑' j : ℕ, term (j + 2)
  have hseries : meanEulerSeries (momentWeight q) p = 1 + a / p + tail := by
    unfold meanEulerSeries
    rw [← hsplit]
    simp [Finset.sum_range_succ, hterm0, hterm1, tail, add_assoc]
  have htail0 : 0 ≤ tail := tsum_nonneg htail_nonneg
  have hden : 0 < 1 - lam / (p : ℝ) := sub_pos.mpr hratio1
  have htail_coarse :
      tail ≤ (2 * lam ^ 2 / (2 - lam)) / (p : ℝ) ^ 2 := by
    have hp_lam : lam ≤ (p : ℝ) := hlam2.le.trans hp2
    have hden_cmp : (2 - lam) / 2 ≤ 1 - lam / (p : ℝ) := by
      have hdiv : lam / (p : ℝ) ≤ lam / 2 :=
        div_le_div_of_nonneg_left hlam0 (by norm_num) hp2
      nlinarith
    have hsmall_den : 0 < (2 - lam) / 2 := div_pos (sub_pos.mpr hlam2) (by norm_num)
    calc
      tail ≤ (lam / (p : ℝ)) ^ 2 / (1 - lam / (p : ℝ)) := htail_sum
      _ ≤ (lam / (p : ℝ)) ^ 2 / ((2 - lam) / 2) := by
        exact div_le_div_of_nonneg_left (sq_nonneg _) hsmall_den hden_cmp
      _ = (2 * lam ^ 2 / (2 - lam)) / (p : ℝ) ^ 2 := by
        field_simp [hp0.ne', (sub_pos.mpr hlam2).ne']
  have ha0 : 0 ≤ a := by
    dsimp [a]
    nlinarith [(hY.2.2 hy).1]
  have ha2 : a ≤ 2 := by
    dsimp [a]
    have := (hY.2.2 hy).2
    linarith
  have hp_inv : 0 ≤ 1 - 1 / (p : ℝ) := by
    have hp1 : (1 : ℝ) ≤ p := one_le_two.trans hp2
    exact sub_nonneg.mpr ((div_le_one hp0).2 hp1)
  rw [hseries]
  have hid :
      (1 - 1 / (p : ℝ)) * (1 + a / p + tail) -
          (1 + (q.y - 1) / 2 / p) =
        (1 - 1 / (p : ℝ)) * tail - a / (p : ℝ) ^ 2 := by
    dsimp [a]
    field_simp [hp0.ne']
    ring
  rw [hid]
  let K := 2 * lam ^ 2 / (2 - lam)
  let C := 4 + K
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sub_pos.mpr hlam2).le
  have haC : a ≤ C := by dsimp [C, K]; nlinarith
  have htailC : tail ≤ C / (p : ℝ) ^ 2 := by
    exact htail_coarse.trans (div_le_div_of_nonneg_right (by dsimp [C, K]; linarith) (sq_nonneg _))
  have habs : |(1 - 1 / (p : ℝ)) * tail - a / (p : ℝ) ^ 2| ≤
      C / (p : ℝ) ^ 2 := by
    rw [abs_le]
    constructor
    · have haDiv : a / (p : ℝ) ^ 2 ≤ C / (p : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right haC (sq_nonneg _)
      nlinarith [mul_nonneg hp_inv htail0]
    · have hfac_le : (1 - 1 / (p : ℝ)) * tail ≤ tail := by
        have hinv_nonneg : 0 ≤ 1 / (p : ℝ) := by positivity
        nlinarith [mul_nonneg hinv_nonneg htail0]
      have haDiv0 : 0 ≤ a / (p : ℝ) ^ 2 :=
        div_nonneg ha0 (sq_nonneg (p : ℝ))
      nlinarith
  have hrpow : (p : ℝ).rpow (-2) = 1 / (p : ℝ) ^ 2 := by
    norm_num [Real.rpow_neg hp0.le, Real.rpow_two]
  change |(1 - 1 / (p : ℝ)) * tail - a / (p : ℝ) ^ 2| ≤
    localFamilyConstant Y * (p : ℝ).rpow (-2)
  rw [hrpow]
  unfold localFamilyConstant
  simpa [C, K, lam, div_eq_mul_inv] using habs

structure MomentIndex (Y : Set ℝ) (hY : CompactMomentDomain Y) where
  y : ℝ
  hy : y ∈ Y
  theta : ℝ
  htheta : 2 ≤ theta
  sigma : ℝ
  hsigma : theta ≤ sigma
  u : ℝ
  hu : sigma < u

@[expose] def MomentIndex.q {Y : Set ℝ} {hY : CompactMomentDomain Y}
    (i : MomentIndex Y hY) : MomentParameters :=
  { y := i.y, y_pos := (hY.2.2 i.hy).1, y_lt_two := (hY.2.2 i.hy).2,
    theta := i.theta, theta_ge_two := i.htheta,
    sigma := i.sigma, sigma_ge_theta := i.hsigma,
    u := i.u, u_gt_sigma := i.hu }

@[expose] def coeff {Y : Set ℝ} {hY : CompactMomentDomain Y}
    (i : MomentIndex Y hY) : ℝ := (i.y - 1) / 2

@[expose] def localFactor {Y : Set ℝ} {hY : CompactMomentDomain Y}
    (i : MomentIndex Y hY) (p : ℕ) : ℝ :=
  if i.sigma ≤ p ∧ (p : ℝ) < i.u then
    (1 - 1 / (p : ℝ)) * meanEulerSeries (momentWeight i.q) p
  else 1 + coeff i / p

@[expose] def ambientFactor (p : ℕ) : ℝ := (1 - 1 / (p : ℝ))⁻¹

lemma ambient_pos (p : ℕ) (hp : p.Prime) : 0 < ambientFactor p := by
  unfold ambientFactor
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact inv_pos.mpr (sub_pos.mpr (by simpa using (div_lt_one (by positivity : (0 : ℝ) < p)).2 hp1))

lemma localFactor_pos
    (hEXT : EXT001Statement) {Y : Set ℝ} (hY : CompactMomentDomain Y)
    (i : MomentIndex Y hY) (p : ℕ) (hp : p.Prime) : 0 < localFactor i p := by
  unfold localFactor
  split_ifs with h
  · have hs : Summable (fun j => momentWeight i.q (p ^ j) / (p : ℝ) ^ j) :=
      local_series_summable hEXT hY i.q i.hy p hp
    have hseries : 0 < meanEulerSeries (momentWeight i.q) p := by
      unfold meanEulerSeries
      have h0 : 0 < momentWeight i.q (p ^ 0) / (p : ℝ) ^ 0 := by
        simp [momentWeight_one]
      exact (hs.tsum_pos (fun j => by
        exact div_nonneg (momentWeight_prime_pow_bound hY i.q i.hy p j hp).1
          (pow_nonneg (by positivity) _)) 0 h0)
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    exact mul_pos (sub_pos.mpr (by simpa using
      (div_lt_one (by positivity : (0 : ℝ) < p)).2 hp1)) hseries
  · have hc : -(1 / 2 : ℝ) ≤ coeff i := by
      unfold coeff
      have := (hY.2.2 i.hy).1
      linarith
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have : -(1 : ℝ) < coeff i / p := by
      have hp0 : (0 : ℝ) < p := by positivity
      rw [lt_div_iff₀ hp0]
      linarith
    linarith

/-- Uniform in all moment parameters, including endpoints. -/
lemma localFactor_lower_half
    (hEXT : EXT001Statement) {Y : Set ℝ} (hY : CompactMomentDomain Y)
    (i : MomentIndex Y hY) (p : ℕ) (hp : p.Prime) :
    (1 / 2 : ℝ) ≤ localFactor i p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold localFactor
  split_ifs with h
  · have hs : Summable (fun j => momentWeight i.q (p ^ j) / (p : ℝ) ^ j) :=
      local_series_summable hEXT hY i.q i.hy p hp
    have hnonneg : ∀ j : ℕ, 0 ≤ momentWeight i.q (p ^ j) / (p : ℝ) ^ j := by
      intro j
      exact div_nonneg (momentWeight_prime_pow_bound hY i.q i.hy p j hp).1
        (pow_nonneg hp0.le j)
    have hseries : 1 ≤ meanEulerSeries (momentWeight i.q) p := by
      have hsum := hs.sum_le_tsum {0} (fun j _ => hnonneg j)
      simpa [meanEulerSeries, momentWeight_one] using hsum
    have hinv : (1 : ℝ) / p ≤ 1 / 2 :=
      (div_le_iff₀ hp0).2 (by linarith)
    have hfactor : (1 / 2 : ℝ) ≤ 1 - 1 / p := by linarith
    calc
      (1 / 2 : ℝ) = (1 / 2 : ℝ) * 1 := by ring
      _ ≤ (1 - 1 / (p : ℝ)) * meanEulerSeries (momentWeight i.q) p :=
        mul_le_mul hfactor hseries (by norm_num) (by linarith)
  · have hc : -(1 / 2 : ℝ) ≤ coeff i := by
      unfold coeff
      have hy := (hY.2.2 i.hy).1
      linarith
    have hquot : -(1 / 2 : ℝ) ≤ coeff i / p :=
      (le_div_iff₀ hp0).2 (by nlinarith)
    linarith

lemma family_output
    (hEXT : EXT001Statement) (h008 : P008Statement.{0})
    (Y : Set ℝ) (hY : CompactMomentDomain Y) :
    Nonempty (P008Output (coeff (hY := hY)) (localFactor (hY := hY))) := by
  let Q := MomentIndex Y hY
  have hQ : Nonempty Q := by
    rcases hY.1 with ⟨y, hy⟩
    exact ⟨⟨y, hy, 2, le_rfl, 2, le_rfl, 3, by norm_num⟩⟩
  apply h008 Q hQ (-1 / 2) (1 / 2) (by norm_num) (by norm_num)
    1 (localFamilyConstant Y) (by norm_num) (local_constant_pos hY)
    2 (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (coeff (hY := hY))
  · intro i
    unfold coeff
    have hi := hY.2.2 i.hy
    norm_num at hi ⊢
    constructor <;> linarith
  · exact localFactor_lower_half hEXT hY
  · intro i p hp hp2
    unfold localFactor
    split_ifs with h
    · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      convert local_factor_error hEXT hY i.q i.hy p hp h.1 h.2 using 1 <;>
        norm_num [coeff, MomentIndex.q, Real.rpow_neg hp0.le, Real.rpow_two]
    · simp only [sub_self, abs_zero]
      exact mul_nonneg (local_constant_pos hY).le (Real.rpow_nonneg (by positivity) _)
  · intro i p hp hp2 hp_lt
    exact (not_lt_of_ge (by exact_mod_cast hp2) hp_lt).elim

lemma meanEulerSeries_eq
    (hEXT : EXT001Statement) {Y : Set ℝ} (hY : CompactMomentDomain Y)
    (q : MomentParameters) (hy : q.y ∈ Y) (p : ℕ) (hp : p.Prime) :
    meanEulerSeries (momentWeight q) p =
      if (p : ℝ) < q.theta then 1
      else if (p : ℝ) < q.sigma then ambientFactor p
      else if (p : ℝ) < q.u then
        ambientFactor p *
          ((1 - 1 / (p : ℝ)) * meanEulerSeries (momentWeight q) p)
      else ambientFactor p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hinv0 : 0 ≤ 1 / (p : ℝ) := by positivity
  have hinv1 : 1 / (p : ℝ) < 1 := by simpa using (div_lt_one hp0).2 hp1
  have hsum := local_series_summable hEXT hY q hy p hp
  by_cases htheta : (p : ℝ) < q.theta
  · rw [if_pos htheta]
    unfold meanEulerSeries
    calc
      (∑' j : ℕ, momentWeight q (p ^ j) / (p : ℝ) ^ j) =
          momentWeight q (p ^ 0) / (p : ℝ) ^ 0 := by
        apply tsum_eq_single 0
        intro j hj
        have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
        have hlocal := (Erdos448.Stage7.ROOT02.MomentLocal.p010 q).2 p j hp hj1
        have hpj : 0 < p ^ j := pow_pos hp.pos j
        rw [show momentWeight q (p ^ j) = moment q ⟨p ^ j, hpj⟩ by
          simp [momentWeight, hpj], hlocal.1]
        simp [htheta]
      _ = 1 := by simp [momentWeight_one]
  · have htheta' : q.theta ≤ p := le_of_not_gt htheta
    by_cases hsigma : (p : ℝ) < q.sigma
    · rw [if_neg htheta, if_pos hsigma]
      have hfun : (fun j : ℕ => momentWeight q (p ^ j) / (p : ℝ) ^ j) =
          fun j => (1 / (p : ℝ)) ^ j := by
        funext j
        by_cases hj : j = 0
        · subst j; simp [momentWeight_one]
        · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
          have hlocal := (Erdos448.Stage7.ROOT02.MomentLocal.p010 q).2 p j hp hj1
          have hpj : 0 < p ^ j := pow_pos hp.pos j
          have hp_sigma : (p : ℝ) < q.sigma := hsigma
          rw [show momentWeight q (p ^ j) = moment q ⟨p ^ j, hpj⟩ by
            simp [momentWeight, hpj], hlocal.1]
          simp [htheta, hp_sigma, one_div, inv_pow]
      unfold meanEulerSeries ambientFactor
      rw [hfun, tsum_geometric_of_lt_one hinv0 hinv1]
    · have hsigma' : q.sigma ≤ p := le_of_not_gt hsigma
      by_cases hu : (p : ℝ) < q.u
      · rw [if_neg htheta, if_neg hsigma, if_pos hu]
        unfold ambientFactor
        have hfactor : 0 < 1 - 1 / (p : ℝ) := sub_pos.mpr hinv1
        rw [← mul_assoc, inv_mul_cancel₀ hfactor.ne', one_mul]
      · rw [if_neg htheta, if_neg hsigma, if_neg hu]
        have hfun : (fun j : ℕ => momentWeight q (p ^ j) / (p : ℝ) ^ j) =
            fun j => (1 / (p : ℝ)) ^ j := by
          funext j
          by_cases hj : j = 0
          · subst j; simp [momentWeight_one]
          · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
            have hlocal := (Erdos448.Stage7.ROOT02.MomentLocal.p010 q).2 p j hp hj1
            have hpj : 0 < p ^ j := pow_pos hp.pos j
            rw [show momentWeight q (p ^ j) = moment q ⟨p ^ j, hpj⟩ by
              simp [momentWeight, hpj], hlocal.1]
            simp [htheta, hsigma, hu, one_div, inv_pow]
        unfold meanEulerSeries ambientFactor
        rw [hfun, tsum_geometric_of_lt_one hinv0 hinv1]

lemma interval_product_extend
    (L : ℕ → ℝ) {A B X : ℝ} (hA : 2 ≤ A) (hBX : B ≤ X) :
    primeIntervalProduct L A B =
      ∏ p ∈ strictPrimeRange X,
        if A ≤ (p : ℝ) ∧ (p : ℝ) < B then L p else 1 := by
  unfold primeIntervalProduct
  have hsub : strictPrimeRange B ⊆ strictPrimeRange X := by
    intro p hp
    simp only [strictPrimeRange, positiveNatsBelow, Finset.mem_filter,
      Finset.mem_range] at hp ⊢
    exact ⟨⟨Nat.lt_ceil.mpr (hp.1.2.2.trans_le hBX), hp.1.2.1,
      hp.1.2.2.trans_le hBX⟩, hp.2⟩
  let f : ℕ → ℝ := fun p =>
    if p ∈ strictPrimeRange B then (if A ≤ (p : ℝ) then L p else 1) else 1
  calc
    (∏ p ∈ strictPrimeRange B, if A ≤ (p : ℝ) then L p else 1) =
        ∏ p ∈ strictPrimeRange B, f p := by
      apply Finset.prod_congr rfl
      intro p hp
      simp [f, hp]
    _ = ∏ p ∈ strictPrimeRange X, f p := by
      apply Finset.prod_subset hsub
      intro p hpX hpB
      simp [f, hpB]
    _ = ∏ p ∈ strictPrimeRange X,
        if A ≤ (p : ℝ) ∧ (p : ℝ) < B then L p else 1 := by
      apply Finset.prod_congr rfl
      intro p hpX
      have hpB : p ∈ strictPrimeRange B ↔ (p : ℝ) < B := by
        simp only [strictPrimeRange, positiveNatsBelow, Finset.mem_filter,
          Finset.mem_range]
        have hpPrime := (Finset.mem_filter.mp hpX).2
        have hpPos := hpPrime.pos
        simp [hpPrime, hpPos, Nat.lt_ceil]
      by_cases hAB : A ≤ (p : ℝ) ∧ (p : ℝ) < B
      · simp [f, hpB.mpr hAB.2, hAB.1, hAB]
      · by_cases hpA : A ≤ (p : ℝ)
        · have hpBneg : ¬(p : ℝ) < B := fun h => hAB ⟨hpA, h⟩
          simp [f, hpB, hpBneg, hAB]
        · simp [f, hpA, hAB]

lemma euler_product_split
    (hEXT : EXT001Statement) {Y : Set ℝ} (hY : CompactMomentDomain Y)
    (i : MomentIndex Y hY) {x : ℝ} (hux : i.u ≤ x) :
    strictEulerProduct (momentWeight i.q) x =
      primeIntervalProduct ambientFactor 2 x * roughDensity i.theta *
        primeIntervalProduct (localFactor i) i.sigma i.u := by
  have hsx : i.sigma ≤ x := i.hu.le.trans hux
  have htx : i.theta ≤ x := i.hsigma.trans hsx
  have hrough := interval_product_extend mertensFactor
    (A := 2) (B := i.theta) (X := x) (by norm_num) htx
  rw [interval_product_extend ambientFactor (A := 2) (B := x) (X := x)
      (by norm_num) le_rfl,
    interval_product_extend (localFactor i) (A := i.sigma) (B := i.u) (X := x)
      (i.htheta.trans i.hsigma) hux]
  unfold strictEulerProduct roughDensity
  unfold primeIntervalProduct at hrough
  have hrough_raw :
      (∏ p ∈ strictPrimeRange i.theta, (1 - 1 / (p : ℝ))) =
        ∏ p ∈ strictPrimeRange x,
          if 2 ≤ (p : ℝ) ∧ (p : ℝ) < i.theta then mertensFactor p else 1 := by
    calc
      (∏ p ∈ strictPrimeRange i.theta, (1 - 1 / (p : ℝ))) =
          ∏ p ∈ strictPrimeRange i.theta,
            if 2 ≤ (p : ℝ) then mertensFactor p else 1 := by
        apply Finset.prod_congr rfl
        intro p hp
        have hpPrime := (Finset.mem_filter.mp hp).2
        simp [mertensFactor, show (2 : ℝ) ≤ p by exact_mod_cast hpPrime.two_le]
      _ = _ := hrough
  rw [hrough_raw]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpPrime := (Finset.mem_filter.mp hp).2
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpPrime.two_le
  have hpX : (p : ℝ) < x :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.2
  rw [meanEulerSeries_eq hEXT hY i.q i.hy p hpPrime]
  unfold localFactor ambientFactor
  by_cases ht : (p : ℝ) < i.theta
  · have hns : ¬ i.sigma ≤ p := not_le.mpr (ht.trans_le i.hsigma)
    simp [MomentIndex.q, ht, hp2, hpX, hns, mertensFactor]
    have hp0 : (0 : ℝ) < p := by positivity
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
    field_simp [hp0.ne', (sub_pos.mpr hp1).ne']
  · have ht' : i.theta ≤ p := le_of_not_gt ht
    by_cases hs : (p : ℝ) < i.sigma
    · have hns : ¬ i.sigma ≤ p := not_le.mpr hs
      simp [MomentIndex.q, ht, hs, hp2, hpX, hns, mertensFactor]
    · have hs' : i.sigma ≤ p := le_of_not_gt hs
      by_cases hu : (p : ℝ) < i.u
      · simp [MomentIndex.q, ht, hs, hu, hp2, hpX, hs', mertensFactor]
      · simp [MomentIndex.q, ht, hs, hu, hp2, hpX, hs', mertensFactor]

lemma ambient_output (h007 : P007Statement) :
    Nonempty (P007Output ambientFactor 1) := by
  apply h007 1 1 4 (by norm_num) (by norm_num) ambientFactor ambient_pos
  intro p hp hp2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have heq : ambientFactor p - (1 + 1 / p) =
      1 / ((p : ℝ) * (p - 1)) := by
    unfold ambientFactor
    field_simp [hp0.ne', (sub_pos.mpr hp1).ne']
    ring
  have hdenpos : 0 < (p : ℝ) * (p - 1) := mul_pos hp0 (sub_pos.mpr hp1)
  rw [heq, abs_of_pos (one_div_pos.mpr hdenpos)]
  have hrpow : (p : ℝ).rpow (-1 - 1) = 1 / (p : ℝ) ^ 2 := by
    norm_num [Real.rpow_neg hp0.le, Real.rpow_two]
  rw [hrpow]
  rw [div_le_iff₀ (mul_pos hp0 (sub_pos.mpr hp1)), div_eq_mul_inv]
  field_simp [hp0.ne']
  have hp2R : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  nlinarith

theorem p011
    (hEXT : EXT001Statement) (h007 : P007Statement) (h008 : P008Statement.{0}) :
    P011Statement := by
  intro Y hY
  rcases ambient_output h007 with ⟨ambient⟩
  rcases family_output hEXT h008 Y hY with ⟨family⟩
  let ambientUpper : ℝ := max 1 ambient.comparison.upper
  let C : ℝ := ambientUpper * family.comparison.upper /
    Real.log 2 * (hEXT 1 (lambdaOfFamily Y)
      ⟨zero_le_one, zero_le_one.trans (one_le_lambda Y), lambda_lt_two hY⟩).some.constant
  have hC : 0 < C := by
    have hupper : 0 < ambientUpper :=
      lt_of_lt_of_le zero_lt_one (le_max_left 1 ambient.comparison.upper)
    have hext := (hEXT 1 (lambdaOfFamily Y)
      ⟨zero_le_one, zero_le_one.trans (one_le_lambda Y), lambda_lt_two hY⟩).some.constant_pos
    dsimp [C]
    exact mul_pos (div_pos (mul_pos hupper family.comparison.upper_pos)
      (Real.log_pos one_lt_two)) hext
  refine ⟨{
    C_Y := C
    C_Y_pos := hC
    lambda_lt_two := lambda_lt_two hY
    local_constant_pos := local_constant_pos hY
    bound := ?_
  }⟩
  intro y hy theta sigma u x htheta hsigma hu hux hx
  dsimp
  let i : MomentIndex Y hY := ⟨y, hy, theta, htheta, sigma, hsigma, u, hu⟩
  let range : MeanParameterRange 1 (lambdaOfFamily Y) :=
    ⟨zero_le_one, zero_le_one.trans (one_le_lambda Y), lambda_lt_two hY⟩
  let ext := (hEXT 1 (lambdaOfFamily Y) range).some
  have hgeom : PrimePowerGeometricBound (momentWeight i.q) 1 (lambdaOfFamily Y) := by
    intro p hp j
    have h := momentWeight_prime_pow_bound hY i.q hy p j hp
    exact ⟨h.1, by simpa using h.2⟩
  have hmean := ext.bound (momentWeight i.q)
    (Erdos448.Stage7.ROOT02.MomentLocal.p010 i.q).1 hgeom x hx
  rw [euler_product_split hEXT hY i hux] at hmean
  have hamb : primeIntervalProduct ambientFactor 2 x ≤
      ambientUpper * (Real.log x / Real.log 2) := by
    by_cases hx' : 2 < x
    · have hb := (ambient.interval_bounds 2 x (by norm_num) hx').2
      have hratio0 : 0 ≤ Real.log x / Real.log 2 :=
        div_nonneg (Real.log_pos (one_lt_two.trans hx')).le
          (Real.log_pos one_lt_two).le
      calc
        primeIntervalProduct ambientFactor 2 x ≤
            ambient.comparison.upper * (Real.log x / Real.log 2) := by
          simpa using hb
        _ ≤ ambientUpper * (Real.log x / Real.log 2) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hratio0
    · have hxeq : x = 2 := le_antisymm (le_of_not_gt hx') hx
      rw [ambient.empty_branch 2 x (by norm_num) hx hxeq.le, hxeq]
      simp [ambientUpper, (Real.log_pos one_lt_two).ne', le_max_left]
  have hfam := (family.family_bounds i sigma u
    (htheta.trans hsigma) hu).2
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogx : 0 < Real.log x := Real.log_pos (one_lt_two.trans_le hx)
  have hrough0 : 0 ≤ roughDensity theta := by
    unfold roughDensity
    apply Finset.prod_nonneg
    intro p hp
    have hpPrime := (Finset.mem_filter.mp hp).2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpPrime.one_lt.le
    exact sub_nonneg.mpr ((div_le_one hp0).2 hp1)
  have hambRhs0 : 0 ≤ ambientUpper * (Real.log x / Real.log 2) := by
    exact mul_nonneg (le_max_of_le_left zero_le_one)
      (div_nonneg hlogx.le hlog2.le)
  have hlocal0 : 0 ≤ primeIntervalProduct (localFactor i) sigma u := by
    unfold primeIntervalProduct
    apply Finset.prod_nonneg
    intro p hp
    split_ifs
    · exact (localFactor_pos hEXT hY i p (Finset.mem_filter.mp hp).2).le
    · norm_num
  have hprod :
      primeIntervalProduct ambientFactor 2 x * roughDensity theta *
          primeIntervalProduct (localFactor i) sigma u ≤
        ambientUpper * (Real.log x / Real.log 2) *
          roughDensity theta *
          (family.comparison.upper *
            (Real.log u / Real.log sigma).rpow ((y - 1) / 2)) := by
    have hfirst := mul_le_mul hamb le_rfl hrough0 hambRhs0
    exact mul_le_mul hfirst hfam hlocal0 (mul_nonneg hambRhs0 hrough0)
  calc
    strictMean (momentWeight i.q) x ≤
        ext.constant * (x / Real.log x) *
          (primeIntervalProduct ambientFactor 2 x * roughDensity theta *
            primeIntervalProduct (localFactor i) sigma u) := hmean
    _ ≤ ext.constant * (x / Real.log x) *
        (ambientUpper * (Real.log x / Real.log 2) *
          roughDensity theta *
          (family.comparison.upper *
            (Real.log u / Real.log sigma).rpow ((y - 1) / 2))) := by
      exact mul_le_mul_of_nonneg_left hprod
        (mul_nonneg ext.constant_pos.le (div_nonneg (by positivity) hlogx.le))
    _ = C * x * roughDensity theta *
          (Real.log u / Real.log sigma).rpow ((y - 1) / 2) := by
      dsimp [C, ext]
      field_simp [hlogx.ne', hlog2.ne']

end

end Erdos448.Stage7.ROOT02.Mean
