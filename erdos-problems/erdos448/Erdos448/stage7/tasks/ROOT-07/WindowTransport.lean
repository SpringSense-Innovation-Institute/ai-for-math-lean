module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-07».Transport

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT07.WindowTransport

open Finset
open scoped BigOperators

open Erdos448.Stage4
open Erdos448.Stage4.Contracts

noncomputable section

lemma mem_positiveNatsBelow {z : ℝ} {n : ℕ} :
    n ∈ positiveNatsBelow z ↔ 0 < n ∧ (n : ℝ) < z := by
  constructor
  · intro hn
    exact (Finset.mem_filter.mp hn).2
  · rintro ⟨hn, hnz⟩
    rw [positiveNatsBelow, Finset.mem_filter]
    exact ⟨by simpa using Nat.lt_ceil.mpr hnz, hn, hnz⟩

lemma safeLog_pos (z : ℝ) : 0 < safeLog z := by
  unfold safeLog
  exact lt_of_lt_of_le (by norm_num) (le_max_left 1 (Real.log z))

lemma safeLog_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    safeLog a ≤ safeLog b := by
  unfold safeLog
  exact max_le_max_left 1
    (Real.strictMonoOn_log.monotoneOn ha (lt_of_lt_of_le ha hab) hab)

lemma safeLog_scale (a c : ℝ) (ha : 0 < a) (hc : 1 ≤ c) :
    safeLog a ≤ (1 + Real.log c) * safeLog (a / c) := by
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc
  have hsOne : 1 ≤ safeLog (a / c) := by simp [safeLog]
  have hsLog : Real.log (a / c) ≤ safeLog (a / c) := by simp [safeLog]
  unfold safeLog
  apply max_le
  · calc
      1 ≤ max 1 (Real.log (a / c)) := le_max_left _ _
      _ ≤ (1 + Real.log c) * max 1 (Real.log (a / c)) := by
        exact le_mul_of_one_le_left (by positivity) (by linarith)
  · have hlogeq : Real.log a = Real.log (a / c) + Real.log c := by
      rw [Real.log_div (ne_of_gt ha) (ne_of_gt hcpos)]
      ring
    rw [hlogeq]
    calc
      Real.log (a / c) + Real.log c ≤
          max 1 (Real.log (a / c)) + Real.log c := by
        simpa [add_comm] using add_le_add_right hsLog (Real.log c)
      _ ≤ max 1 (Real.log (a / c)) +
          Real.log c * max 1 (Real.log (a / c)) := by
        have := mul_le_mul_of_nonneg_left hsOne hlogc
        simpa [safeLog] using this
      _ = (1 + Real.log c) * max 1 (Real.log (a / c)) := by ring

lemma neg_half_transport {a b R : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hR : 0 < R) (hab : a ≤ R * b) :
    b.rpow (-1 / 2) ≤ R.rpow (1 / 2) * a.rpow (-1 / 2) := by
  have hdiv : a / R ≤ b := (div_le_iff₀ hR).2 (by simpa [mul_comm] using hab)
  have hr := Real.rpow_le_rpow_of_nonpos (div_pos ha hR) hdiv (by norm_num : (-1 / 2 : ℝ) ≤ 0)
  calc
    b.rpow (-1 / 2) ≤ (a / R).rpow (-1 / 2) := hr
    _ = R.rpow (1 / 2) * a.rpow (-1 / 2) := by
      have hdivpow := Real.div_rpow (le_of_lt ha) (le_of_lt hR) (-1 / 2 : ℝ)
      change (a / R) ^ (-1 / 2 : ℝ) = R ^ (1 / 2 : ℝ) * a ^ (-1 / 2 : ℝ)
      rw [hdivpow]
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring,
        Real.rpow_neg (le_of_lt hR)]
      rw [div_inv_eq_mul]
      ring

lemma neg_rpow_transport {a b R e : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hR : 0 < R) (hR_one : 1 ≤ R)
    (he : e ≤ 0) (hne : -e ≤ 1) (hab : a ≤ R * b) :
    b.rpow e ≤ R * a.rpow e := by
  have hdiv : a / R ≤ b := (div_le_iff₀ hR).2 (by simpa [mul_comm] using hab)
  have hr := Real.rpow_le_rpow_of_nonpos (div_pos ha hR) hdiv he
  calc
    b.rpow e ≤ (a / R).rpow e := hr
    _ = R.rpow (-e) * a.rpow e := by
      have hdivpow : (a / R).rpow e = a.rpow e / R.rpow e :=
        Real.div_rpow (le_of_lt ha) (le_of_lt hR) e
      rw [hdivpow]
      change a ^ e / R ^ e = R ^ (-e) * a ^ e
      rw [Real.rpow_neg (le_of_lt hR) e]
      ring
    _ ≤ R.rpow 1 * a.rpow e := by
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hR_one hne)
        (Real.rpow_nonneg ha.le _)
    _ = R * a.rpow e := by
      change R ^ (1 : ℝ) * a ^ e = R * a ^ e
      rw [Real.rpow_one R]

lemma theta_zpow (theta : ℝ) (htheta : 0 < theta) (k : ℕ) :
    theta ^ (1 - (2 : ℤ) * k) = theta / theta ^ (2 * k) := by
  have hne : theta ≠ 0 := ne_of_gt htheta
  rw [zpow_sub₀ hne]
  rw [zpow_one]
  congr 1

lemma theta_zpow_three (theta : ℝ) (htheta : 0 < theta) (k : ℕ) :
    theta ^ (1 - (3 : ℤ) * k) = theta / theta ^ (3 * k) := by
  have hne : theta ≠ 0 := ne_of_gt htheta
  rw [zpow_sub₀ hne, zpow_one]
  congr 1

lemma theta_zpow_enlarged (theta : ℝ) (htheta : 0 < theta) (k : ℕ) :
    theta ^ (-((3 : ℤ) * k) - 3) = 1 / theta ^ (3 * k + 3) := by
  rw [show -((3 : ℤ) * k) - 3 = -((3 * k + 3 : ℕ) : ℤ) by omega]
  rw [zpow_neg, zpow_natCast]
  simp only [one_div]

lemma window_ratio (q : WeightParameters) (x : ℝ) {d d' : ℕ}
    (hd : 0 < d) (hd' : 0 < d')
    (hp : P054Payload q.theta q.k ⟨d, hd⟩ ⟨d', hd'⟩) :
    let X := x * q.theta ^ (1 - (2 : ℤ) * q.k)
    let M := x / (d * d' : ℕ)
    0 < x → M ≤ X ∧ X / q.theta ^ 4 ≤ M := by
  intro X M hx
  have ht : 0 < q.theta := lt_of_lt_of_le (by norm_num) q.theta_ge_two
  have hpow : 0 < q.theta ^ (2 * q.k) := pow_pos ht _
  have hD : (0 : ℝ) < (d * d' : ℕ) := by positivity
  dsimp [X, M]
  rw [theta_zpow q.theta ht q.k]
  constructor
  · apply (div_le_iff₀ hD).2
    have hl := hp.product_lower
    have hsplit : q.theta ^ (2 * q.k) =
        q.theta ^ (2 * q.k - 1) * q.theta := by
      have hk := q.k_pos
      calc
        q.theta ^ (2 * q.k) = q.theta ^ ((2 * q.k - 1) + 1) := by
          congr 1
          omega
        _ = q.theta ^ (2 * q.k - 1) * q.theta := by rw [pow_add, pow_one]
    have hlR : q.theta ^ (2 * q.k - 1) < ((d * d' : ℕ) : ℝ) := by
      simpa using hp.product_lower
    have hl' : q.theta ^ (2 * q.k) < ((d * d' : ℕ) : ℝ) * q.theta := by
      rw [hsplit]
      nlinarith [mul_pos (sub_pos.mpr hlR) ht]
    field_simp [ne_of_gt hpow]
    nlinarith [q.theta_ge_two]
  · apply (le_div_iff₀ hD).2
    have hu := hp.product_upper
    have hu' : (d * d' : ℕ) < q.theta ^ (2 * q.k) * q.theta ^ 3 := by
      simpa [pow_add] using hu
    field_simp [ne_of_gt hpow, ne_of_gt ht]
    nlinarith [q.theta_ge_two]

lemma endpoint_neg_half (q : WeightParameters) (x M : ℝ)
    (hx : 0 < x)
    (hM : x * q.theta ^ (1 - (2 : ℤ) * q.k) / q.theta ^ 4 ≤ M) :
    (safeLog (2 * M)).rpow (-1 / 2) ≤
      (1 + Real.log (q.theta ^ 4)).rpow (1 / 2) *
        (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow (-1 / 2) := by
  let X := x * q.theta ^ (1 - (2 : ℤ) * q.k)
  let R := 1 + Real.log (q.theta ^ 4)
  have ht : 0 < q.theta := lt_of_lt_of_le (by norm_num) q.theta_ge_two
  have hX : 0 < X := mul_pos hx (zpow_pos ht _)
  have hc : 1 ≤ q.theta ^ 4 := one_le_pow₀ (by linarith [q.theta_ge_two])
  have hR : 0 < R := by dsimp [R]; nlinarith [Real.log_nonneg hc]
  have hscale := safeLog_scale (2 * X) (q.theta ^ 4) (mul_pos (by norm_num) hX) hc
  have hmono : safeLog (2 * X / q.theta ^ 4) ≤ safeLog (2 * M) := by
    apply safeLog_mono
    · positivity
    · dsimp [X] at hM ⊢
      ring_nf at hM ⊢
      nlinarith
  have hres : (safeLog (2 * M)).rpow (-1 / 2) ≤
      R.rpow (1 / 2) * (safeLog (2 * X)).rpow (-1 / 2) := by
    apply neg_half_transport (safeLog_pos _) (safeLog_pos _) hR
    calc
      safeLog (2 * X) ≤ R * safeLog (2 * X / q.theta ^ 4) := hscale
      _ ≤ R * safeLog (2 * M) := mul_le_mul_of_nonneg_left hmono hR.le
  simpa [X, R, mul_assoc] using hres

lemma endpoint_neg_half_raw (q : WeightParameters) (x M : ℝ)
    (hx : 0 < x)
    (hM : x * q.theta ^ (1 - (2 : ℤ) * q.k) / q.theta ^ 4 ≤ M) :
    (safeLog M).rpow (-1 / 2) ≤
      (1 + Real.log (q.theta ^ 4)).rpow (1 / 2) *
        (safeLog (x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow (-1 / 2) := by
  let X := x * q.theta ^ (1 - (2 : ℤ) * q.k)
  let R := 1 + Real.log (q.theta ^ 4)
  have ht : 0 < q.theta := lt_of_lt_of_le (by norm_num) q.theta_ge_two
  have hX : 0 < X := mul_pos hx (zpow_pos ht _)
  have hc : 1 ≤ q.theta ^ 4 := one_le_pow₀ (by linarith [q.theta_ge_two])
  have hR : 0 < R := by dsimp [R]; nlinarith [Real.log_nonneg hc]
  have hscale := safeLog_scale X (q.theta ^ 4) hX hc
  have hmono : safeLog (X / q.theta ^ 4) ≤ safeLog M := by
    exact safeLog_mono (div_pos hX (pow_pos ht _)) hM
  have hres : (safeLog M).rpow (-1 / 2) ≤
      R.rpow (1 / 2) * (safeLog X).rpow (-1 / 2) := by
    apply neg_half_transport (safeLog_pos _) (safeLog_pos _) hR
    exact hscale.trans (mul_le_mul_of_nonneg_left hmono hR.le)
  simpa [X, R] using hres

lemma upper_cutoff_mem (q : WeightParameters) (x : ℝ) {d d' m : ℕ}
    (hd : 0 < d) (hd' : 0 < d') (hm : 0 < m)
    (hp : P054Payload q.theta q.k ⟨d, hd⟩ ⟨d', hd'⟩)
    (hz : q.theta ^ q.k ≤ zValue x m d d') :
    m ∈ positiveNatsBelow (x * q.theta ^ (1 - (3 : ℤ) * q.k)) := by
  apply mem_positiveNatsBelow.mpr
  refine ⟨hm, ?_⟩
  have ht : 0 < q.theta := lt_of_lt_of_le (by norm_num) q.theta_ge_two
  have hD : (0 : ℝ) < (d * d' : ℕ) := by positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hz' : q.theta ^ q.k * ((m : ℝ) * (d * d' : ℕ)) ≤ x := by
    unfold zValue at hz
    have hz0 : q.theta ^ q.k ≤ x / ((m : ℝ) * (d * d' : ℕ)) := by
      simpa only [Nat.cast_mul, Nat.mul_assoc] using hz
    exact (le_div_iff₀ (mul_pos hmR hD)).mp hz0
  have hlR : q.theta ^ (2 * q.k - 1) < ((d * d' : ℕ) : ℝ) := by
    simpa using hp.product_lower
  have hprod : (m : ℝ) * q.theta ^ (3 * q.k - 1) < x := by
    have hk := q.k_pos
    have hpow : q.theta ^ (3 * q.k - 1) =
        q.theta ^ q.k * q.theta ^ (2 * q.k - 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow]
    have hdelta : 0 < q.theta ^ q.k *
        (((d * d' : ℕ) : ℝ) - q.theta ^ (2 * q.k - 1)) :=
      mul_pos (pow_pos ht q.k) (sub_pos.mpr hlR)
    nlinarith [mul_pos hmR hdelta]
  rw [theta_zpow_three q.theta ht q.k]
  have hp3 : 0 < q.theta ^ (3 * q.k) := pow_pos ht _
  rw [show x * (q.theta / q.theta ^ (3 * q.k)) =
    (x * q.theta) / q.theta ^ (3 * q.k) by ring]
  apply (lt_div_iff₀ hp3).2
  have hk := q.k_pos
  have hsplit : q.theta ^ (3 * q.k) = q.theta ^ (3 * q.k - 1) * q.theta := by
    calc
      _ = q.theta ^ ((3 * q.k - 1) + 1) := by congr 1; omega
      _ = _ := by rw [pow_add, pow_one]
  rw [hsplit]
  nlinarith [mul_pos (sub_pos.mpr hprod) ht]

lemma middle_lower_cutoff (q : WeightParameters) (x : ℝ) {d d' m : ℕ}
    (hd : 0 < d) (hd' : 0 < d') (hm : 0 < m)
    (hp : P054Payload q.theta q.k ⟨d, hd⟩ ⟨d', hd'⟩)
    (hz : zValue x m d d' < q.theta ^ q.k) :
    x * q.theta ^ (-((3 : ℤ) * q.k) - 3) < (m : ℝ) := by
  have ht : 0 < q.theta := lt_of_lt_of_le (by norm_num) q.theta_ge_two
  have hD : (0 : ℝ) < (d * d' : ℕ) := by positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hz' : x < q.theta ^ q.k * ((m : ℝ) * (d * d' : ℕ)) := by
    unfold zValue at hz
    have hz0 : x / ((m : ℝ) * (d * d' : ℕ)) < q.theta ^ q.k := by
      simpa only [Nat.cast_mul, Nat.mul_assoc] using hz
    exact (div_lt_iff₀ (mul_pos hmR hD)).mp hz0
  have hu : ((d * d' : ℕ) : ℝ) < q.theta ^ (2 * q.k + 3) := by
    simpa using hp.product_upper
  have hprod : x < (m : ℝ) * q.theta ^ (3 * q.k + 3) := by
    calc
      x < q.theta ^ q.k * ((m : ℝ) * (d * d' : ℕ)) := hz'
      _ < q.theta ^ q.k * ((m : ℝ) * q.theta ^ (2 * q.k + 3)) := by
        have hdelta : 0 < q.theta ^ q.k * (m : ℝ) *
            (q.theta ^ (2 * q.k + 3) - ((d * d' : ℕ) : ℝ)) :=
          mul_pos (mul_pos (pow_pos ht _) hmR) (sub_pos.mpr hu)
        nlinarith
      _ = (m : ℝ) * q.theta ^ (3 * q.k + 3) := by
        rw [show 3 * q.k + 3 = q.k + (2 * q.k + 3) by omega, pow_add]
        ring
  rw [theta_zpow_enlarged q.theta ht q.k]
  rw [show x * (1 / q.theta ^ (3 * q.k + 3)) =
      x / q.theta ^ (3 * q.k + 3) by ring]
  exact (div_lt_iff₀ (pow_pos ht _)).2 (by simpa [mul_comm] using hprod)

lemma restricted_half_sum_le (q : WeightParameters) (x : ℝ) {d d' : ℕ}
    (hd : 0 < d) (hd' : 0 < d') :
    (∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
      if zValue x m d d' < q.sigma then (safeLog m).rpow (-1 / 2) else 0) ≤
      safeLogHalfSum (x / (d * d' : ℕ)) := by
  unfold safeLogHalfSum
  apply Finset.sum_le_sum
  intro m hm
  split
  · exact le_rfl
  · exact Real.rpow_nonneg (safeLog_pos _).le _

theorem p067 (h053 : P053Statement) (h054 : P054Statement)
    (W : CommonWeightWitnesses) : P067Statement := by
  obtain ⟨Cps, hCps, hps⟩ := h053
  intro theta htheta
  let R : ℝ := 1 + Real.log (theta ^ 4)
  let CC : ℝ := Cps * theta * R.rpow (1 / 2)
  have ht : 0 < theta := lt_of_lt_of_le (by norm_num) htheta
  have hR : 0 < R := by
    dsimp [R]
    nlinarith [Real.log_nonneg (one_le_pow₀ (by linarith : 1 ≤ theta) : 1 ≤ theta ^ 4)]
  have hCC : 0 < CC := mul_pos (mul_pos hCps ht) (Real.rpow_pos_of_pos hR _)
  refine ⟨CC, hCC, ?_⟩
  intro q hq hSigma x hx
  subst theta
  have hxpos : 0 < x := by
    have := pow_pos (lt_of_lt_of_le (by norm_num) q.theta_ge_two) (2 * q.k - 1)
    linarith
  have hlog : 0 < Real.log q.sigma := Real.log_pos (by linarith [q.theta_ge_two, q.sigma_ge_theta])
  classical
  unfold substitutedRegular regularC regularOuter outerPairSum convolutionC
  simp only
  rw [show CC * ((Real.log q.sigma).rpow (-q.y / 2) *
        (∑ d ∈ positiveNatsBelow (q.theta ^ (q.k + 1)),
          ∑ d' ∈ positiveNatsBelow (q.theta ^ (q.k + 2)),
            if hd : 0 < d then
              if hd' : 0 < d' then
                if q.theta ^ q.k ≤ (d : ℝ) ∧
                    Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩ then
                  (roughIndicator d q.sigma : ℝ) *
                    q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
                    w3Weight q (d * d')
                else 0 else 0 else 0) *
        (x / q.theta ^ (2 * q.k) * (Real.log q.sigma).rpow (q.y / 2) *
          (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow (-1 / 2))) =
      (CC * (Real.log q.sigma).rpow (-q.y / 2) *
        (x / q.theta ^ (2 * q.k) * (Real.log q.sigma).rpow (q.y / 2) *
          (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow (-1 / 2))) *
        (∑ d ∈ positiveNatsBelow (q.theta ^ (q.k + 1)),
          ∑ d' ∈ positiveNatsBelow (q.theta ^ (q.k + 2)),
            if hd : 0 < d then
              if hd' : 0 < d' then
                if q.theta ^ q.k ≤ (d : ℝ) ∧
                    Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩ then
                  (roughIndicator d q.sigma : ℝ) *
                    q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
                    w3Weight q (d * d')
                else 0 else 0 else 0) by ring,
      Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hdSet
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d' hd'Set
  by_cases hd : 0 < d
  · by_cases hd' : 0 < d'
    · by_cases houter : q.theta ^ q.k ≤ (d : ℝ) ∧
          Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩
      · simp only [hd, hd', houter, and_true, dite_true, if_true]
        have hdUpper : (d : ℝ) < q.theta ^ (q.k + 1) :=
          (mem_positiveNatsBelow.mp hdSet).2
        have hp := h054 q.k q.k_pos q.theta (by linarith [q.theta_ge_two])
          ⟨d, hd⟩ ⟨d', hd'⟩ houter.1 hdUpper houter.2
        let D := d * d'
        let M := x / (D : ℕ)
        let X := x * q.theta ^ (1 - (2 : ℤ) * q.k)
        have hD : 0 < D := Nat.mul_pos hd hd'
        have hM : 0 < M := div_pos hxpos (by positivity)
        have hratio := window_ratio q x hd hd' hp hxpos
        have hsum := restricted_half_sum_le q x hd hd'
        have hpsM := hps M hM
        have hend := endpoint_neg_half q x M hxpos hratio.2
        have hw := W.w3_dom_w1 q D hD
        have hrough : 0 ≤ (roughIndicator d q.sigma : ℝ) := by positivity
        have hy : 0 ≤ q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) :=
          Real.rpow_nonneg q.y_pos.le _
        have hinner :
            w1Weight D *
                (∑ m ∈ positiveNatsBelow M,
                  if zValue x m d d' < q.sigma then
                    (safeLog m).rpow (-1 / 2) else 0) ≤
              Cps * R.rpow (1 / 2) * w3Weight q D * X *
                (safeLog (2 * X)).rpow (-1 / 2) := by
          calc
            _ ≤ w1Weight D * safeLogHalfSum M :=
              mul_le_mul_of_nonneg_left hsum
                ((W.weight_type q .w1).nonnegative_multiplicative.nonnegative D hD)
            _ ≤ w1Weight D *
                (Cps * M * (safeLog (2 * M)).rpow (-1 / 2)) :=
              mul_le_mul_of_nonneg_left hpsM
                ((W.weight_type q .w1).nonnegative_multiplicative.nonnegative D hD)
            _ ≤ w3Weight q D *
                (Cps * M * (safeLog (2 * M)).rpow (-1 / 2)) := by
              exact mul_le_mul_of_nonneg_right hw
                (mul_nonneg (mul_nonneg hCps.le hM.le)
                  (Real.rpow_nonneg (safeLog_pos _).le _))
            _ ≤ w3Weight q D *
                (Cps * X *
                  (R.rpow (1 / 2) * (safeLog (2 * X)).rpow (-1 / 2))) := by
              apply mul_le_mul_of_nonneg_left _
                ((W.weight_type q .w3).nonnegative_multiplicative.nonnegative D hD)
              have hXnonneg : 0 ≤ X := by positivity
              calc
                Cps * M * (safeLog (2 * M)).rpow (-1 / 2) ≤
                    Cps * X * (safeLog (2 * M)).rpow (-1 / 2) := by
                  exact mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hratio.1 hCps.le)
                    (Real.rpow_nonneg (safeLog_pos _).le _)
                _ ≤ Cps * X *
                    (R.rpow (1 / 2) * (safeLog (2 * X)).rpow (-1 / 2)) := by
                  have hend' : (safeLog (2 * M)).rpow (-1 / 2) ≤
                      R.rpow (1 / 2) * (safeLog (2 * X)).rpow (-1 / 2) := by
                    dsimp [R, X]
                    simpa only [mul_assoc, Real.rpow_eq_pow] using hend
                  exact mul_le_mul_of_nonneg_left hend'
                    (mul_nonneg hCps.le hXnonneg)
            _ = Cps * R.rpow (1 / 2) * w3Weight q D * X *
                (safeLog (2 * X)).rpow (-1 / 2) := by ring
        have hcoeff : 0 ≤ (roughIndicator d q.sigma : ℝ) *
            q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) := mul_nonneg hrough hy
        have hcancel :
            (Real.log q.sigma).rpow (-q.y / 2) *
                (Real.log q.sigma).rpow (q.y / 2) = 1 := by
          have hadd := Real.rpow_add hlog (-q.y / 2) (q.y / 2)
          calc
            _ = (Real.log q.sigma).rpow (-q.y / 2 + q.y / 2) := hadd.symm
            _ = (Real.log q.sigma).rpow 0 := by congr 1 <;> ring
            _ = 1 := by simp
        dsimp [M, X, D] at hinner ⊢
        calc
          (roughIndicator d q.sigma : ℝ) *
                q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
                (w1Weight (d * d') *
                  ∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                    if zValue x m d d' < q.sigma then
                      (safeLog m).rpow (-1 / 2) else 0) ≤
              (roughIndicator d q.sigma : ℝ) *
                q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
                (Cps * R.rpow (1 / 2) * w3Weight q (d * d') *
                  (x * q.theta ^ (1 - (2 : ℤ) * q.k)) *
                  (safeLog (2 * (x * q.theta ^ (1 - (2 : ℤ) * q.k)))).rpow (-1 / 2)) :=
            mul_le_mul_of_nonneg_left hinner hcoeff
          _ = (CC * (Real.log q.sigma).rpow (-q.y / 2) *
              (x / q.theta ^ (2 * q.k) *
                (Real.log q.sigma).rpow (q.y / 2) *
                (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow (-1 / 2))) *
              ((roughIndicator d q.sigma : ℝ) *
                q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
                w3Weight q (d * d')) := by
            have hXeq : x * q.theta ^ (1 - (2 : ℤ) * q.k) =
                q.theta * (x / q.theta ^ (2 * q.k)) := by
              rw [theta_zpow q.theta
                (lt_of_lt_of_le (by norm_num) q.theta_ge_two) q.k]
              ring
            have hsarg : 2 * (x * q.theta ^ (1 - (2 : ℤ) * q.k)) =
                2 * x * q.theta ^ (1 - (2 : ℤ) * q.k) := by ring
            let coeff : ℝ := (roughIndicator d q.sigma : ℝ) *
              q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ)
            let rr : ℝ := R.rpow (1 / 2)
            let ss : ℝ :=
              (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow (-1 / 2)
            let lm : ℝ := (Real.log q.sigma).rpow (-q.y / 2)
            let lp : ℝ := (Real.log q.sigma).rpow (q.y / 2)
            have hlogs : lm * lp = 1 := by simpa [lm, lp] using hcancel
            rw [hsarg]
            change coeff *
                (Cps * rr * w3Weight q (d * d') *
                  (x * q.theta ^ (1 - (2 : ℤ) * q.k)) * ss) =
              (CC * lm * (x / q.theta ^ (2 * q.k) * lp * ss)) *
                (coeff * w3Weight q (d * d'))
            rw [hXeq]
            calc
              _ = Cps * q.theta * rr * coeff * w3Weight q (d * d') *
                  (x / q.theta ^ (2 * q.k)) * ss := by ring
              _ = (Cps * q.theta * rr * lm *
                    (x / q.theta ^ (2 * q.k) * lp * ss)) *
                  (coeff * w3Weight q (d * d')) := by
                symm
                calc
                  _ = (lm * lp) *
                      (Cps * q.theta * rr * coeff * w3Weight q (d * d') *
                        (x / q.theta ^ (2 * q.k)) * ss) := by ring
                  _ = _ := by rw [hlogs]; ring
              _ = _ := by rfl
      · simp [hd, hd', houter]
    · simp [hd']
  · simp [hd]

theorem p063 (h054 : P054Statement) (W : CommonWeightWitnesses) :
    P063Statement := by
  intro theta htheta
  let R : ℝ := 1 + Real.log (theta ^ 4)
  let CA : ℝ := theta * R.rpow (1 / 2)
  have ht : 0 < theta := lt_of_lt_of_le (by norm_num) htheta
  have hR : 0 < R := by
    dsimp [R]
    nlinarith [Real.log_nonneg (one_le_pow₀ (by linarith : 1 ≤ theta) : 1 ≤ theta ^ 4)]
  have hCA : 0 < CA := mul_pos ht (Real.rpow_pos_of_pos hR _)
  refine ⟨CA, hCA, ?_⟩
  intro q hq hSigma x hx
  subst theta
  have hxpos : 0 < x := by
    have := pow_pos (lt_of_lt_of_le (by norm_num) q.theta_ge_two) (2 * q.k - 1)
    linarith
  classical
  unfold substitutedRegular regularA regularOuter outerPairSum convolutionA
  simp only
  rw [show CA * ((Real.log q.sigma).rpow (-q.y / 2) *
        (∑ d ∈ positiveNatsBelow (q.theta ^ (q.k + 1)),
          ∑ d' ∈ positiveNatsBelow (q.theta ^ (q.k + 2)),
            if hd : 0 < d then if hd' : 0 < d' then
              if q.theta ^ q.k ≤ (d : ℝ) ∧ Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩ then
                (roughIndicator d q.sigma : ℝ) *
                  q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
                  w3Weight q (d * d') else 0 else 0 else 0) *
        (x / q.theta ^ (2 * q.k) * (q.k : ℝ).rpow ((q.y - 1) / 2) *
          ∑ m ∈ positiveNatsBelow (x * q.theta ^ (1 - (3 : ℤ) * q.k)),
            (safeLog m).rpow (-1 / 2) / m *
              (safeLog (x * q.theta ^ (1 - (2 : ℤ) * q.k) / m)).rpow (-1 / 2))) =
      (CA * (Real.log q.sigma).rpow (-q.y / 2) *
        (x / q.theta ^ (2 * q.k) * (q.k : ℝ).rpow ((q.y - 1) / 2) *
          ∑ m ∈ positiveNatsBelow (x * q.theta ^ (1 - (3 : ℤ) * q.k)),
            (safeLog m).rpow (-1 / 2) / m *
              (safeLog (x * q.theta ^ (1 - (2 : ℤ) * q.k) / m)).rpow (-1 / 2))) *
        (∑ d ∈ positiveNatsBelow (q.theta ^ (q.k + 1)),
          ∑ d' ∈ positiveNatsBelow (q.theta ^ (q.k + 2)),
            if hd : 0 < d then if hd' : 0 < d' then
              if q.theta ^ q.k ≤ (d : ℝ) ∧ Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩ then
                (roughIndicator d q.sigma : ℝ) *
                  q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
                  w3Weight q (d * d') else 0 else 0 else 0) by ring,
      Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hdSet
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d' hd'Set
  by_cases hd : 0 < d
  · by_cases hd' : 0 < d'
    · by_cases houter : q.theta ^ q.k ≤ (d : ℝ) ∧
          Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩
      · simp only [hd, hd', houter, and_true, dite_true, if_true]
        have hdUpper : (d : ℝ) < q.theta ^ (q.k + 1) :=
          (mem_positiveNatsBelow.mp hdSet).2
        have hp := h054 q.k q.k_pos q.theta (by linarith [q.theta_ge_two])
          ⟨d, hd⟩ ⟨d', hd'⟩ houter.1 hdUpper houter.2
        let D := d * d'
        let X := x * q.theta ^ (1 - (2 : ℤ) * q.k)
        let U := x * q.theta ^ (1 - (3 : ℤ) * q.k)
        let S := (positiveNatsBelow (x / (D : ℕ))).filter
          (fun m => q.theta ^ q.k ≤ zValue x m d d')
        let g : ℕ → ℝ := fun m =>
          (safeLog m).rpow (-1 / 2) / m *
            (safeLog (X / m)).rpow (-1 / 2)
        have hD : 0 < D := Nat.mul_pos hd hd'
        have hsubset : S ⊆ positiveNatsBelow U := by
          intro m hmS
          have hmOuter := (Finset.mem_filter.mp hmS).1
          have hm : 0 < m := (mem_positiveNatsBelow.mp hmOuter).1
          exact upper_cutoff_mem q x hd hd' hm hp (Finset.mem_filter.mp hmS).2
        have hpoint : ∀ m ∈ S,
            (safeLog m).rpow (-1 / 2) * zValue x m d d' *
                (safeLog (zValue x m d d')).rpow (-1 / 2) ≤
              R.rpow (1 / 2) * X * g m := by
          intro m hmS
          have hmOuter := (Finset.mem_filter.mp hmS).1
          have hm : 0 < m := (mem_positiveNatsBelow.mp hmOuter).1
          have hmR : (0 : ℝ) < m := by exact_mod_cast hm
          have hxdiv : 0 < x / (m : ℝ) := div_pos hxpos hmR
          have hratio := window_ratio q (x / (m : ℝ)) hd hd' hp hxdiv
          have hzEq : zValue x m d d' = (x / (m : ℝ)) / (D : ℕ) := by
            unfold zValue D
            norm_num [Nat.cast_mul]
            field_simp
          have hupper : zValue x m d d' ≤ X / m := by
            rw [hzEq]
            dsimp [X, D]
            simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hratio.1
          have hlower : (x / (m : ℝ)) * q.theta ^ (1 - (2 : ℤ) * q.k) /
                q.theta ^ 4 ≤ zValue x m d d' := by
            rw [hzEq]
            exact hratio.2
          have hlog := endpoint_neg_half_raw q (x / (m : ℝ))
            (zValue x m d d') hxdiv hlower
          have hsafe : 0 ≤ (safeLog (m : ℝ)).rpow (-1 / 2) :=
            Real.rpow_nonneg (safeLog_pos _).le _
          have hznonneg : 0 ≤ zValue x m d d' := by
            unfold zValue
            positivity
          have hlog' : (safeLog (zValue x m d d')).rpow (-1 / 2) ≤
              R.rpow (1 / 2) * (safeLog (X / m)).rpow (-1 / 2) := by
            simpa [R, X, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hlog
          have htargetlog : 0 ≤ (safeLog (X / m)).rpow (-1 / 2) :=
            Real.rpow_nonneg (safeLog_pos _).le _
          calc
            _ ≤ (safeLog m).rpow (-1 / 2) * (X / m) *
                (safeLog (zValue x m d d')).rpow (-1 / 2) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hupper hsafe)
                (Real.rpow_nonneg (safeLog_pos _).le _)
            _ ≤ (safeLog m).rpow (-1 / 2) * (X / m) *
                (R.rpow (1 / 2) * (safeLog (X / m)).rpow (-1 / 2)) := by
              exact mul_le_mul_of_nonneg_left hlog'
                (mul_nonneg hsafe (div_nonneg (by positivity) hmR.le))
            _ = R.rpow (1 / 2) * X * g m := by
              dsimp [g]
              field_simp
        have hsum :
            (∑ m ∈ positiveNatsBelow (x / (D : ℕ)),
              if q.theta ^ q.k ≤ zValue x m d d' then
                (safeLog m).rpow (-1 / 2) * zValue x m d d' *
                  (safeLog (zValue x m d d')).rpow (-1 / 2) else 0) ≤
              R.rpow (1 / 2) * X *
                ∑ m ∈ positiveNatsBelow U, g m := by
          rw [← Finset.sum_filter]
          change (∑ m ∈ S, _) ≤ _
          calc
            _ ≤ ∑ m ∈ S, R.rpow (1 / 2) * X * g m :=
              Finset.sum_le_sum hpoint
            _ ≤ ∑ m ∈ positiveNatsBelow U, R.rpow (1 / 2) * X * g m := by
              apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
              intro m hmU hmS
              exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hR.le _) (by positivity))
                (mul_nonneg
                  (div_nonneg (Real.rpow_nonneg (safeLog_pos _).le _) (by positivity))
                  (Real.rpow_nonneg (safeLog_pos _).le _))
            _ = _ := by rw [Finset.mul_sum]
        have hw := W.w3_dom_w2 q D hD
        have hw2 : 0 ≤ w2Weight q D :=
          (W.weight_type q .w2).nonnegative_multiplicative.nonnegative D hD
        have hgSum : 0 ≤ ∑ m ∈ positiveNatsBelow U, g m := by
          apply Finset.sum_nonneg
          intro m hm
          exact mul_nonneg
            (div_nonneg (Real.rpow_nonneg (safeLog_pos _).le _) (by positivity))
            (Real.rpow_nonneg (safeLog_pos _).le _)
        have hinner : w2Weight q D *
              (∑ m ∈ positiveNatsBelow (x / (D : ℕ)),
                if q.theta ^ q.k ≤ zValue x m d d' then
                  (safeLog m).rpow (-1 / 2) * zValue x m d d' *
                    (safeLog (zValue x m d d')).rpow (-1 / 2) else 0) ≤
            w3Weight q D * (R.rpow (1 / 2) * X *
              ∑ m ∈ positiveNatsBelow U, g m) := by
          calc
            _ ≤ w2Weight q D * (R.rpow (1 / 2) * X *
                ∑ m ∈ positiveNatsBelow U, g m) :=
              mul_le_mul_of_nonneg_left hsum hw2
            _ ≤ _ := mul_le_mul_of_nonneg_right hw
              (mul_nonneg (mul_nonneg (Real.rpow_nonneg hR.le _) (by positivity)) hgSum)
        have hcoeff : 0 ≤ (roughIndicator d q.sigma : ℝ) *
            q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
            ((Real.log q.sigma).rpow (-q.y / 2) *
              (q.k : ℝ).rpow ((q.y - 1) / 2)) := by
          exact mul_nonneg
            (mul_nonneg (by positivity) (Real.rpow_nonneg q.y_pos.le _))
            (mul_nonneg
              (Real.rpow_nonneg (Real.log_nonneg (by linarith [q.theta_ge_two, q.sigma_ge_theta])) _)
              (Real.rpow_nonneg (by positivity) _))
        dsimp [D, X, U, g] at hinner ⊢
        let A : ℝ := (roughIndicator d q.sigma : ℝ) *
          q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ)
        let B : ℝ := (Real.log q.sigma).rpow (-q.y / 2) *
          (q.k : ℝ).rpow ((q.y - 1) / 2)
        change A * (B * w2Weight q (d * d') *
            (∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
              if q.theta ^ q.k ≤ zValue x m d d' then
                (safeLog m).rpow (-1 / 2) * zValue x m d d' *
                  (safeLog (zValue x m d d')).rpow (-1 / 2) else 0)) ≤ _
        calc
          _ = (A * B) *
              (w2Weight q (d * d') *
                ∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                  if q.theta ^ q.k ≤ zValue x m d d' then
                    (safeLog m).rpow (-1 / 2) * zValue x m d d' *
                      (safeLog (zValue x m d d')).rpow (-1 / 2) else 0) := by
            simp only [mul_assoc]
          _ ≤ (A * B) *
              (w3Weight q (d * d') *
                (R.rpow (1 / 2) *
                  (x * q.theta ^ (1 - (2 : ℤ) * q.k)) *
                  ∑ m ∈ positiveNatsBelow (x * q.theta ^ (1 - (3 : ℤ) * q.k)),
                    (safeLog m).rpow (-1 / 2) / m *
                      (safeLog (x * q.theta ^ (1 - (2 : ℤ) * q.k) / m)).rpow (-1 / 2))) :=
            mul_le_mul_of_nonneg_left hinner hcoeff
          _ = (CA * (Real.log q.sigma).rpow (-q.y / 2) *
              (x / q.theta ^ (2 * q.k) *
                (q.k : ℝ).rpow ((q.y - 1) / 2) *
                ∑ m ∈ positiveNatsBelow (x * q.theta ^ (1 - (3 : ℤ) * q.k)),
                  (safeLog m).rpow (-1 / 2) / m *
                    (safeLog (x * q.theta ^ (1 - (2 : ℤ) * q.k) / m)).rpow (-1 / 2))) *
              ((roughIndicator d q.sigma : ℝ) *
                q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
                w3Weight q (d * d')) := by
            let L : ℝ := (Real.log q.sigma).rpow (-q.y / 2)
            let K : ℝ := (q.k : ℝ).rpow ((q.y - 1) / 2)
            let T : ℝ :=
              ∑ m ∈ positiveNatsBelow (x * q.theta ^ (1 - (3 : ℤ) * q.k)),
                (safeLog m).rpow (-1 / 2) / m *
                  (safeLog (x * q.theta ^ (1 - (2 : ℤ) * q.k) / m)).rpow (-1 / 2)
            have hB : B = L * K := by rfl
            have hXeq : x * q.theta ^ (1 - (2 : ℤ) * q.k) =
                q.theta * (x / q.theta ^ (2 * q.k)) := by
              rw [theta_zpow q.theta
                (lt_of_lt_of_le (by norm_num) q.theta_ge_two) q.k]
              ring
            change (A * B) * (w3Weight q (d * d') *
                (R.rpow (1 / 2) *
                  (x * q.theta ^ (1 - (2 : ℤ) * q.k)) * T)) =
              (CA * L * (x / q.theta ^ (2 * q.k) * K * T)) *
                (A * w3Weight q (d * d'))
            rw [hXeq]
            rw [hB]
            dsimp [CA]
            ring
      · simp [hd, hd', houter]
    · simp [hd']
  · simp [hd]

theorem p065 (h054 : P054Statement) (W : CommonWeightWitnesses) :
    P065Statement := by
  intro theta htheta
  let R : ℝ := 1 + Real.log (theta ^ 4)
  let CB : ℝ := theta * R
  have ht : 0 < theta := lt_of_lt_of_le (by norm_num) htheta
  have hR : 0 < R := by
    dsimp [R]
    nlinarith [Real.log_nonneg (one_le_pow₀ (by linarith : 1 ≤ theta) : 1 ≤ theta ^ 4)]
  have hRone : 1 ≤ R := by
    dsimp [R]
    nlinarith [Real.log_nonneg (one_le_pow₀ (by linarith : 1 ≤ theta) : 1 ≤ theta ^ 4)]
  have hCB : 0 < CB := mul_pos ht hR
  refine ⟨CB, hCB, ?_⟩
  intro q hq hSigma x hx
  subst theta
  have hxpos : 0 < x := by
    have := pow_pos (lt_of_lt_of_le (by norm_num) q.theta_ge_two) (2 * q.k - 1)
    linarith
  classical
  unfold substitutedRegular regularB regularOuter outerPairSum convolutionBEnlarged
  simp only
  rw [show CB * ((Real.log q.sigma).rpow (-q.y / 2) *
        (∑ d ∈ positiveNatsBelow (q.theta ^ (q.k + 1)),
          ∑ d' ∈ positiveNatsBelow (q.theta ^ (q.k + 2)),
            if hd : 0 < d then if hd' : 0 < d' then
              if q.theta ^ q.k ≤ (d : ℝ) ∧ Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩ then
                (roughIndicator d q.sigma : ℝ) *
                  q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
                  w3Weight q (d * d') else 0 else 0 else 0) *
        (x / q.theta ^ (2 * q.k) *
          ∑ m ∈ positiveNatsBelow (x * q.theta ^ (1 - (2 : ℤ) * q.k)),
            if x * q.theta ^ (-((3 : ℤ) * q.k) - 3) < m then
              (safeLog m).rpow (-1 / 2) / m *
                (safeLog (x * q.theta ^ (1 - (2 : ℤ) * q.k) / m)).rpow
                  (q.y / 2 - 1) else 0)) =
      (CB * (Real.log q.sigma).rpow (-q.y / 2) *
        (x / q.theta ^ (2 * q.k) *
          ∑ m ∈ positiveNatsBelow (x * q.theta ^ (1 - (2 : ℤ) * q.k)),
            if x * q.theta ^ (-((3 : ℤ) * q.k) - 3) < m then
              (safeLog m).rpow (-1 / 2) / m *
                (safeLog (x * q.theta ^ (1 - (2 : ℤ) * q.k) / m)).rpow
                  (q.y / 2 - 1) else 0)) *
        (∑ d ∈ positiveNatsBelow (q.theta ^ (q.k + 1)),
          ∑ d' ∈ positiveNatsBelow (q.theta ^ (q.k + 2)),
            if hd : 0 < d then if hd' : 0 < d' then
              if q.theta ^ q.k ≤ (d : ℝ) ∧ Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩ then
                (roughIndicator d q.sigma : ℝ) *
                  q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
                  w3Weight q (d * d') else 0 else 0 else 0) by ring,
      Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hdSet
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d' hd'Set
  by_cases hd : 0 < d
  · by_cases hd' : 0 < d'
    · by_cases houter : q.theta ^ q.k ≤ (d : ℝ) ∧
          Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩
      · simp only [hd, hd', houter, and_true, dite_true, if_true]
        have hdUpper : (d : ℝ) < q.theta ^ (q.k + 1) :=
          (mem_positiveNatsBelow.mp hdSet).2
        have hp := h054 q.k q.k_pos q.theta (by linarith [q.theta_ge_two])
          ⟨d, hd⟩ ⟨d', hd'⟩ houter.1 hdUpper houter.2
        let D := d * d'
        let X := x * q.theta ^ (1 - (2 : ℤ) * q.k)
        let S := (positiveNatsBelow (x / (D : ℕ))).filter
          (fun m => q.sigma ≤ zValue x m d d' ∧
            zValue x m d d' < q.theta ^ q.k)
        let T : Finset ℕ := (positiveNatsBelow X).filter
          (fun m : ℕ => x * q.theta ^ (-((3 : ℤ) * q.k) - 3) < (m : ℝ))
        let g : ℕ → ℝ := fun m =>
          (safeLog m).rpow (-1 / 2) / m *
            (safeLog (X / m)).rpow (q.y / 2 - 1)
        have hD : 0 < D := Nat.mul_pos hd hd'
        have hratioX := window_ratio q x hd hd' hp hxpos
        have hsubset : S ⊆ T := by
          intro m hmS
          have hmOuter := (Finset.mem_filter.mp hmS).1
          have hz := (Finset.mem_filter.mp hmS).2
          have hm : 0 < m := (mem_positiveNatsBelow.mp hmOuter).1
          have hmUpper : (m : ℝ) < X := by
            calc
              (m : ℝ) < x / (D : ℕ) := (mem_positiveNatsBelow.mp hmOuter).2
              _ ≤ X := hratioX.1
          exact Finset.mem_filter.mpr ⟨mem_positiveNatsBelow.mpr ⟨hm, hmUpper⟩,
            middle_lower_cutoff q x hd hd' hm hp hz.2⟩
        have hpoint : ∀ m ∈ S,
            (safeLog m).rpow (-1 / 2) * zValue x m d d' *
                (safeLog (zValue x m d d')).rpow (q.y / 2 - 1) ≤
              R * X * g m := by
          intro m hmS
          have hmOuter := (Finset.mem_filter.mp hmS).1
          have hz := (Finset.mem_filter.mp hmS).2
          have hm : 0 < m := (mem_positiveNatsBelow.mp hmOuter).1
          have hmR : (0 : ℝ) < m := by exact_mod_cast hm
          have hxdiv : 0 < x / (m : ℝ) := div_pos hxpos hmR
          have hratio := window_ratio q (x / (m : ℝ)) hd hd' hp hxdiv
          have hzEq : zValue x m d d' = (x / (m : ℝ)) / (D : ℕ) := by
            unfold zValue D
            norm_num [Nat.cast_mul]
            field_simp
          have hupper : zValue x m d d' ≤ X / m := by
            rw [hzEq]
            dsimp [X, D]
            simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hratio.1
          have hXm : 0 < X / (m : ℝ) := by
            dsimp [X]
            positivity
          have hzpos : 0 < zValue x m d d' :=
            lt_of_lt_of_le (lt_of_lt_of_le (by norm_num) q.theta_ge_two)
              (q.sigma_ge_theta.trans hz.1)
          have hc : 1 ≤ q.theta ^ 4 :=
            one_le_pow₀ (by linarith [q.theta_ge_two] : 1 ≤ q.theta)
          have hscale := safeLog_scale (X / (m : ℝ)) (q.theta ^ 4) hXm hc
          have hlower : X / (m : ℝ) / q.theta ^ 4 ≤ zValue x m d d' := by
            rw [hzEq]
            dsimp [X, D]
            simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hratio.2
          have hmono : safeLog (X / (m : ℝ) / q.theta ^ 4) ≤
              safeLog (zValue x m d d') :=
            safeLog_mono (div_pos hXm (pow_pos
              (lt_of_lt_of_le (by norm_num) q.theta_ge_two) _)) hlower
          have hlogbase : safeLog (X / (m : ℝ)) ≤
              R * safeLog (zValue x m d d') :=
            hscale.trans (mul_le_mul_of_nonneg_left hmono hR.le)
          have he : q.y / 2 - 1 ≤ 0 := by linarith [q.y_lt_one]
          have hne : -(q.y / 2 - 1) ≤ 1 := by linarith [q.y_pos]
          have hlog := neg_rpow_transport (safeLog_pos _) (safeLog_pos _)
            hR hRone he hne hlogbase
          have hsafe : 0 ≤ (safeLog (m : ℝ)).rpow (-1 / 2) :=
            Real.rpow_nonneg (safeLog_pos _).le _
          calc
            _ ≤ (safeLog m).rpow (-1 / 2) * (X / m) *
                (safeLog (zValue x m d d')).rpow (q.y / 2 - 1) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hupper hsafe)
                (Real.rpow_nonneg (safeLog_pos _).le _)
            _ ≤ (safeLog m).rpow (-1 / 2) * (X / m) *
                (R * (safeLog (X / m)).rpow (q.y / 2 - 1)) := by
              exact mul_le_mul_of_nonneg_left hlog
                (mul_nonneg hsafe (div_nonneg (by positivity) hmR.le))
            _ = R * X * g m := by
              dsimp [g]
              field_simp
        have hsum :
            (∑ m ∈ positiveNatsBelow (x / (D : ℕ)),
              if q.sigma ≤ zValue x m d d' ∧
                  zValue x m d d' < q.theta ^ q.k then
                (safeLog m).rpow (-1 / 2) * zValue x m d d' *
                  (safeLog (zValue x m d d')).rpow (q.y / 2 - 1) else 0) ≤
              R * X *
                ∑ m ∈ positiveNatsBelow X,
                  if x * q.theta ^ (-((3 : ℤ) * q.k) - 3) < m then
                    g m else 0 := by
          rw [← Finset.sum_filter]
          change (∑ m ∈ S, _) ≤ _
          calc
            _ ≤ ∑ m ∈ S, R * X * g m := Finset.sum_le_sum hpoint
            _ ≤ ∑ m ∈ T, R * X * g m := by
              apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
              intro m hmT hmS
              exact mul_nonneg (mul_nonneg hR.le (by positivity))
                (mul_nonneg
                  (div_nonneg (Real.rpow_nonneg (safeLog_pos _).le _) (by positivity))
                  (Real.rpow_nonneg (safeLog_pos _).le _))
            _ = R * X * ∑ m ∈ T, g m := by rw [Finset.mul_sum]
            _ = _ := by rw [← Finset.sum_filter]
        have hw := W.w3_dom_w2 q D hD
        have hw2 : 0 ≤ w2Weight q D :=
          (W.weight_type q .w2).nonnegative_multiplicative.nonnegative D hD
        have hgSum : 0 ≤ ∑ m ∈ positiveNatsBelow X,
            if x * q.theta ^ (-((3 : ℤ) * q.k) - 3) < m then g m else 0 := by
          apply Finset.sum_nonneg
          intro m hm
          split
          · exact mul_nonneg
              (div_nonneg (Real.rpow_nonneg (safeLog_pos _).le _) (by positivity))
              (Real.rpow_nonneg (safeLog_pos _).le _)
          · exact le_rfl
        have hinner : w2Weight q D *
              (∑ m ∈ positiveNatsBelow (x / (D : ℕ)),
                if q.sigma ≤ zValue x m d d' ∧
                    zValue x m d d' < q.theta ^ q.k then
                  (safeLog m).rpow (-1 / 2) * zValue x m d d' *
                    (safeLog (zValue x m d d')).rpow (q.y / 2 - 1) else 0) ≤
            w3Weight q D * (R * X *
              ∑ m ∈ positiveNatsBelow X,
                if x * q.theta ^ (-((3 : ℤ) * q.k) - 3) < m then g m else 0) := by
          calc
            _ ≤ w2Weight q D * (R * X *
                ∑ m ∈ positiveNatsBelow X,
                  if x * q.theta ^ (-((3 : ℤ) * q.k) - 3) < m then g m else 0) :=
              mul_le_mul_of_nonneg_left hsum hw2
            _ ≤ _ := mul_le_mul_of_nonneg_right hw
              (mul_nonneg (mul_nonneg hR.le (by positivity)) hgSum)
        have hcoeff : 0 ≤ (roughIndicator d q.sigma : ℝ) *
            q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
              (Real.log q.sigma).rpow (-q.y / 2) :=
          mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg q.y_pos.le _))
            (Real.rpow_nonneg
              (Real.log_nonneg (by linarith [q.theta_ge_two, q.sigma_ge_theta])) _)
        dsimp [D, X, g] at hinner ⊢
        let A : ℝ := (roughIndicator d q.sigma : ℝ) *
          q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ)
        let L : ℝ := (Real.log q.sigma).rpow (-q.y / 2)
        let U : ℝ := x * q.theta ^ (1 - (2 : ℤ) * q.k)
        let G : ℝ := ∑ m ∈ positiveNatsBelow U,
          if x * q.theta ^ (-((3 : ℤ) * q.k) - 3) < m then
            (safeLog m).rpow (-1 / 2) / m *
              (safeLog (U / m)).rpow (q.y / 2 - 1) else 0
        change A * (L * w2Weight q (d * d') *
            (∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
              if q.sigma ≤ zValue x m d d' ∧
                  zValue x m d d' < q.theta ^ q.k then
                (safeLog m).rpow (-1 / 2) * zValue x m d d' *
                  (safeLog (zValue x m d d')).rpow (q.y / 2 - 1) else 0)) ≤ _
        calc
          _ = (A * L) * (w2Weight q (d * d') *
              ∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                if q.sigma ≤ zValue x m d d' ∧
                    zValue x m d d' < q.theta ^ q.k then
                  (safeLog m).rpow (-1 / 2) * zValue x m d d' *
                    (safeLog (zValue x m d d')).rpow (q.y / 2 - 1) else 0) := by
            simp only [mul_assoc]
          _ ≤ (A * L) * (w3Weight q (d * d') * (R * U * G)) :=
            mul_le_mul_of_nonneg_left hinner hcoeff
          _ = (CB * L * (x / q.theta ^ (2 * q.k) * G)) *
              (A * w3Weight q (d * d')) := by
            have hUeq : U = q.theta * (x / q.theta ^ (2 * q.k)) := by
              dsimp [U]
              rw [theta_zpow q.theta
                (lt_of_lt_of_le (by norm_num) q.theta_ge_two) q.k]
              ring
            rw [hUeq]
            dsimp [CB]
            ring
      · simp [hd, hd', houter]
    · simp [hd']
  · simp [hd]

end

end Erdos448.Stage7.ROOT07.WindowTransport
