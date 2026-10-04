module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-04».Helpers

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT04.Reindex

open Erdos448.Stage4
open Erdos448.Stage7.ROOT04.Helpers

noncomputable section

instance (p : Prop) : Decidable p := Classical.propDecidable p

lemma divisor_le {a n : ℕ} (hn : 0 < n) (ha : a ∣ n) : a ≤ n :=
  Nat.le_of_dvd hn ha

lemma prime_le_of_dvd {p a : ℕ} (_hp : p.Prime) (hpa : p ∣ a) (ha : 0 < a) : p ≤ a :=
  Nat.le_of_dvd ha hpa

lemma rough_factor_ge {a n : ℕ} {theta : ℝ}
    (hnrough : IsRough n theta) (ha1 : 1 < a) (han : a ∣ n) : theta ≤ a := by
  obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd (ne_of_gt ha1)
  have hpn : p ∣ n := hpa.trans han
  exact (hnrough p hp hpn).trans (by exact_mod_cast prime_le_of_dvd hp hpa (by omega))

lemma close_divisor_lt
    (n D D' : PosNat) {theta : ℝ} (htheta : 1 < theta)
    (hnrough : IsRough n.1 theta) (hD : D.1 ∣ n.1) (hD' : D'.1 ∣ n.1)
    (hclose : Close theta D D') : D.1 < n.1 := by
  have hDle := divisor_le n.2 hD
  apply lt_of_le_of_ne hDle
  intro hEq
  have hDn : D.1 = n.1 := le_antisymm hDle (by omega)
  have hD'le := divisor_le n.2 hD'
  have hD'pos := D'.2
  have hD'ne : D'.1 ≠ n.1 := by
    intro heq
    apply hclose.1
    apply Subtype.ext
    omega
  have hD'lt : D'.1 < n.1 := lt_of_le_of_ne hD'le hD'ne
  have hquotpos : 0 < n.1 / D'.1 := Nat.div_pos (Nat.le_of_lt hD'lt) hD'pos
  have hquot1 : 1 < n.1 / D'.1 := by
    have hne : n.1 / D'.1 ≠ 1 := by
      intro hq
      have := Nat.div_mul_cancel hD'
      rw [hq, one_mul] at this
      exact hD'ne this
    omega
  have hqge : theta ≤ ((n.1 / D'.1 : ℕ) : ℝ) :=
    rough_factor_ge hnrough hquot1 (Nat.div_dvd_of_dvd hD')
  have hmul : theta * D'.1 ≤ n.1 := by
    have hcast : ((n.1 / D'.1 : ℕ) : ℝ) * D'.1 = n.1 := by
      exact_mod_cast Nat.div_mul_cancel hD'
    calc
      theta * D'.1 ≤ ((n.1 / D'.1 : ℕ) : ℝ) * D'.1 :=
        mul_le_mul_of_nonneg_right hqge (by positivity)
      _ = n.1 := hcast
  have hratio : (D'.1 : ℝ) / D.1 ≤ 1 / theta := by
    rw [hDn]
    have htpos : 0 < theta := lt_trans zero_lt_one htheta
    have hnpos : (0 : ℝ) < n.1 := by exact_mod_cast n.2
    rw [div_le_div_iff₀ hnpos htpos]
    nlinarith
  exact (not_lt_of_ge hratio) hclose.2.1

lemma gcd_reindex
    (n D D' : PosNat) {theta : ℝ}
    (hD : D.1 ∣ n.1) (hD' : D'.1 ∣ n.1) (_hclose : Close theta D D') :
    0 < Nat.gcd D.1 D'.1 ∧
      0 < D.1 / Nat.gcd D.1 D'.1 ∧
      0 < D'.1 / Nat.gcd D.1 D'.1 ∧
      D.1 = (D.1 / Nat.gcd D.1 D'.1) * Nat.gcd D.1 D'.1 ∧
      D'.1 = (D'.1 / Nat.gcd D.1 D'.1) * Nat.gcd D.1 D'.1 ∧
      Nat.Coprime (D.1 / Nat.gcd D.1 D'.1) (D'.1 / Nat.gcd D.1 D'.1) ∧
      (D.1 / Nat.gcd D.1 D'.1) * (D'.1 / Nat.gcd D.1 D'.1) *
          Nat.gcd D.1 D'.1 ∣ n.1 ∧
      (D'.1 : ℝ) / D.1 =
        ((D'.1 / Nat.gcd D.1 D'.1 : ℕ) : ℝ) /
          ((D.1 / Nat.gcd D.1 D'.1 : ℕ) : ℝ) := by
  let t := Nat.gcd D.1 D'.1
  let d := D.1 / t
  let d' := D'.1 / t
  have ht : 0 < t := Nat.gcd_pos_of_pos_left _ D.2
  have htd : t ∣ D.1 := Nat.gcd_dvd_left _ _
  have htd' : t ∣ D'.1 := Nat.gcd_dvd_right _ _
  have hdt : d * t = D.1 := Nat.div_mul_cancel htd
  have hd't : d' * t = D'.1 := Nat.div_mul_cancel htd'
  have hd : 0 < d := Nat.div_pos (Nat.gcd_le_left _ D.2) ht
  have hd' : 0 < d' := Nat.div_pos (Nat.gcd_le_right _ D'.2) ht
  have hcop : Nat.Coprime d d' := Nat.coprime_div_gcd_div_gcd ht
  have hlcm : Nat.lcm D.1 D'.1 = d * d' * t := by
    apply Nat.eq_of_mul_eq_mul_left ht
    rw [Nat.gcd_mul_lcm]
    simp only [← hdt, ← hd't]
    ring
  have hdiv : d * d' * t ∣ n.1 := by
    rw [← hlcm]
    exact Nat.lcm_dvd hD hD'
  have hratio : (D'.1 : ℝ) / D.1 = (d' : ℝ) / d := by
    rw [← hdt, ← hd't]
    push_cast
    field_simp
  exact ⟨ht, hd, hd', hdt.symm, hd't.symm, hcop, hdiv, hratio⟩

lemma reduced_rough_and_gt_one
    (q : Lemma4Parameters) (n D D' : PosNat)
    (hnrough : roughIndicator n.1 q.theta = 1)
    (hDrough : roughIndicator D.1 q.sigma = 1)
    (hD : D.1 ∣ n.1) (hD' : D'.1 ∣ n.1) (hclose : Close q.theta D D') :
    let t := Nat.gcd D.1 D'.1
    let d := D.1 / t
    let d' := D'.1 / t
    roughIndicator d q.sigma = 1 ∧ roughIndicator t q.sigma = 1 ∧
      1 < d ∧ q.sigma ≤ d := by
  dsimp
  let t := Nat.gcd D.1 D'.1
  let d := D.1 / t
  let d' := D'.1 / t
  obtain ⟨ht, hd, hd', hDt, hD't, hcop, hdiv, hratio⟩ :=
    gcd_reindex n D D' hD hD' hclose
  change 0 < t at ht
  change 0 < d at hd
  change 0 < d' at hd'
  change D.1 = d * t at hDt
  change D'.1 = d' * t at hD't
  change d * d' * t ∣ n.1 at hdiv
  change (D'.1 : ℝ) / D.1 = (d' : ℝ) / d at hratio
  have hmul : roughIndicator d q.sigma * roughIndicator t q.sigma = 1 := by
    rw [← roughIndicator_mul, ← hDt]
    exact hDrough
  have hdr : roughIndicator d q.sigma = 1 :=
    Nat.dvd_one.mp ⟨roughIndicator t q.sigma, hmul.symm⟩
  have htr : roughIndicator t q.sigma = 1 :=
    Nat.dvd_one.mp ⟨roughIndicator d q.sigma, by simpa [mul_comm] using hmul.symm⟩
  have hnR : IsRough n.1 q.theta := (roughIndicator_eq_one_iff _ _).mp hnrough
  have hdgt : 1 < d := by
    by_contra hnot
    have hd1 : d = 1 := by omega
    have hd'ne : d' ≠ 1 := by
      intro heq
      apply hclose.1
      apply Subtype.ext
      rw [hDt, hD't, hd1, heq]
    have hd'gt : 1 < d' := by omega
    have hd'dvd : d' ∣ n.1 := by
      have hlocal : d' ∣ d * d' * t := ⟨d * t, by ring⟩
      exact hlocal.trans hdiv
    have hd'ge : q.theta ≤ d' := rough_factor_ge hnR hd'gt hd'dvd
    have hratio' : ((d' : ℝ) / d) = d' := by simp [hd1]
    have := hclose.2.2
    rw [hratio, hratio'] at this
    exact (not_lt_of_ge hd'ge) this
  have hdR : IsRough d q.sigma := (roughIndicator_eq_one_iff _ _).mp hdr
  have hdge : q.sigma ≤ d := by
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hdgt)
    exact (hdR p hp hpd).trans (by exact_mod_cast prime_le_of_dvd hp hpd hd)
  simpa [t, d, d'] using And.intro hdr (And.intro htr (And.intro hdgt hdge))

lemma bin_lower
    (q : Lemma4Parameters) {d k : ℕ} (hdge : q.sigma ≤ d)
    (hbin : q.theta ^ k ≤ (d : ℝ) ∧ (d : ℝ) < q.theta ^ (k + 1)) :
    lowerBinIndex q.sigma q.theta ≤ k := by
  have hlt : 0 < Real.log q.theta := Real.log_pos
    (lt_of_lt_of_le (by norm_num) q.theta_ge_two)
  have hls : 0 < Real.log q.sigma := Real.log_pos
    (lt_of_lt_of_le (by norm_num) (q.theta_ge_two.trans q.sigma_ge_theta))
  have htheta : 0 < q.theta := lt_trans zero_lt_one
    (lt_of_lt_of_le (by norm_num) q.theta_ge_two)
  have hspos : 0 < q.sigma := lt_of_lt_of_le (by norm_num)
    (q.theta_ge_two.trans q.sigma_ge_theta)
  have hdpos : (0 : ℝ) < d := lt_of_lt_of_le hspos hdge
  have hlogd : Real.log q.sigma ≤ Real.log d :=
    Real.log_le_log hspos (by exact_mod_cast hdge)
  have hlogpow : Real.log d < (k + 1 : ℕ) * Real.log q.theta := by
    rw [← Real.log_pow]
    exact Real.log_lt_log hdpos hbin.2
  have hratio : Real.log q.sigma / Real.log q.theta < (k : ℝ) + 1 := by
    apply (div_lt_iff₀ hlt).2
    push_cast at hlogpow
    nlinarith
  have hk1 : 1 ≤ k := by
    by_contra hk
    have hk0 : k = 0 := by omega
    rw [hk0] at hratio
    have hsigtheta : Real.log q.theta ≤ Real.log q.sigma :=
      Real.log_le_log (lt_of_lt_of_le (by norm_num) q.theta_ge_two) q.sigma_ge_theta
    have : 1 ≤ Real.log q.sigma / Real.log q.theta := by
      apply (le_div_iff₀ hlt).2
      simpa using hsigtheta
    norm_num at hratio
    linarith
  have hhalf : (1 / 2 : ℝ) * Real.log q.sigma / Real.log q.theta ≤ k := by
    have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hratio1 : 1 ≤ Real.log q.sigma / Real.log q.theta := by
      apply (le_div_iff₀ hlt).2
      simpa using Real.log_le_log
        (lt_of_lt_of_le (by norm_num) q.theta_ge_two) q.sigma_ge_theta
    have hratio_le : Real.log q.sigma / Real.log q.theta ≤ 2 * (k : ℝ) := by
      nlinarith
    calc
      (1 / 2 : ℝ) * Real.log q.sigma / Real.log q.theta =
          (1 / 2) * (Real.log q.sigma / Real.log q.theta) := by ring
      _ ≤ (1 / 2) * (2 * (k : ℝ)) :=
        mul_le_mul_of_nonneg_left hratio_le (by norm_num)
      _ = k := by ring
  unfold lowerBinIndex
  apply max_le hk1
  exact Nat.ceil_le.mpr (by simpa [mul_div_assoc] using hhalf)

end

end Erdos448.Stage7.ROOT04.Reindex
