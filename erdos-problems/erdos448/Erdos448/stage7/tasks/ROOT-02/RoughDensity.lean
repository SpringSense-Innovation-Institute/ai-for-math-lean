module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage4.contracts.GroupA

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT02.RoughDensity

open Filter Finset Set Function
open scoped BigOperators Topology
open Erdos448.Stage4
open Erdos448.Stage4.Contracts

lemma periodic_count_mul
    (p : ℕ → Prop) [DecidablePred p] {q : ℕ}
    (hp : Periodic p q) (k : ℕ) :
    Nat.count p (k * q) = k * Nat.count p q := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_mul, Nat.count_add, ih]
      have hshift : (fun n : ℕ => p (k * q + n)) = p := by
        funext n
        simpa [Nat.nsmul_eq_mul, add_comm] using hp.nsmul k n
      have hcount_shift :
          Nat.count (fun n : ℕ => p (k * q + n)) q = Nat.count p q := by
        rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
        congr 1
        ext n
        simp only [Finset.mem_filter, Finset.mem_range]
        exact and_congr_right fun _ => iff_of_eq (congrFun hshift n)
      rw [hcount_shift]
      simp [Nat.succ_mul]

lemma periodic_count_decompose
    (p : ℕ → Prop) [DecidablePred p] {q : ℕ}
    (hp : Periodic p q) (n : ℕ) :
    Nat.count p n =
      (n / q) * Nat.count p q + Nat.count p (n % q) := by
  by_cases hq : q = 0
  · subst q
    simp
  · have hn : n = (n / q) * q + n % q := by
      calc
        n = q * (n / q) + n % q := (Nat.div_add_mod n q).symm
        _ = (n / q) * q + n % q := by ac_rfl
    have hshift : (fun m : ℕ => p ((n / q) * q + m)) = p := by
      funext m
      simpa [Nat.nsmul_eq_mul, add_comm] using hp.nsmul (n / q) m
    have hcount_shift :
        Nat.count (fun m : ℕ => p ((n / q) * q + m)) (n % q) =
          Nat.count p (n % q) := by
      rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
      congr 1
      ext m
      simp only [Finset.mem_filter, Finset.mem_range]
      exact and_congr_right fun _ => iff_of_eq (congrFun hshift m)
    calc
      Nat.count p n = Nat.count p ((n / q) * q + n % q) :=
        congrArg (Nat.count p) hn
      _ = Nat.count p ((n / q) * q) +
          Nat.count (fun m : ℕ => p ((n / q) * q + m)) (n % q) :=
        Nat.count_add (p := p) _ _
      _ = (n / q) * Nat.count p q + Nat.count p (n % q) := by
        rw [periodic_count_mul p hp, hcount_shift]

theorem periodic_density
    (p : ℕ → Prop) [DecidablePred p] {q : ℕ}
    (hq : 0 < q) (hp : Periodic p q) :
    Tendsto
      (fun n : ℕ => (Nat.count p n : ℝ) / n)
      atTop (nhds ((Nat.count p q : ℝ) / q)) := by
  let delta : ℝ := (Nat.count p q : ℝ) / q
  have herror : ∀ n : ℕ, 0 < n →
      dist delta ((Nat.count p n : ℝ) / n) ≤ (q : ℝ) / n := by
    intro n hn
    let k := n / q
    let r := n % q
    let c := Nat.count p q
    let b := Nat.count p r
    have hrlt : r < q := Nat.mod_lt n hq
    have hb : b ≤ r := Nat.count_le _
    have hc : c ≤ q := Nat.count_le _
    have hcount : Nat.count p n = k * c + b := by
      simpa [k, r, c, b] using periodic_count_decompose p hp n
    have hn_decomp : n = k * q + r := by
      dsimp [k, r]
      calc
        n = q * (n / q) + n % q := (Nat.div_add_mod n q).symm
        _ = (n / q) * q + n % q := by ac_rfl
    have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hnum_nonneg :
        -(q : ℝ) ^ 2 ≤ (q : ℝ) * b - (c : ℝ) * r := by
      have hb0 : (0 : ℝ) ≤ b := by positivity
      have hcR : (c : ℝ) ≤ q := by exact_mod_cast hc
      have hrR : (r : ℝ) ≤ q := by exact_mod_cast hrlt.le
      have hcr : (c : ℝ) * r ≤ q * q :=
        mul_le_mul hcR hrR (by positivity) (by positivity)
      nlinarith
    have hnum_le :
        (q : ℝ) * b - (c : ℝ) * r ≤ (q : ℝ) ^ 2 := by
      have hbR : (b : ℝ) ≤ r := by exact_mod_cast hb
      have hrR : (r : ℝ) ≤ q := by exact_mod_cast hrlt.le
      have hqb : (q : ℝ) * b ≤ q * q :=
        mul_le_mul_of_nonneg_left (hbR.trans hrR) (by positivity)
      nlinarith
    have hnum_abs :
        |(q : ℝ) * b - (c : ℝ) * r| ≤ (q : ℝ) ^ 2 :=
      (abs_le).2 ⟨hnum_nonneg, hnum_le⟩
    have hdiff :
        delta - (Nat.count p n : ℝ) / n =
          ((c : ℝ) * r - (q : ℝ) * b) /
            ((n : ℝ) * q) := by
      dsimp [delta]
      change (c : ℝ) / q - (Nat.count p n : ℝ) / n = _
      have hcountR : (Nat.count p n : ℝ) = (k : ℝ) * c + b := by
        exact_mod_cast hcount
      have hn_decompR : (n : ℝ) = (k : ℝ) * q + r := by
        exact_mod_cast hn_decomp
      rw [hcountR]
      field_simp [hnR.ne', hqR.ne']
      rw [hn_decompR]
      ring
    rw [Real.dist_eq, hdiff, abs_div, abs_mul, abs_of_pos hnR, abs_of_pos hqR,
      abs_sub_comm]
    rw [div_le_div_iff₀ (mul_pos hnR hqR) hnR]
    nlinarith
  have hbound :
      Tendsto (fun n : ℕ => (q : ℝ) / n) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hdist :
      Tendsto
        (fun n : ℕ =>
          dist delta ((Nat.count p n : ℝ) / n))
        atTop (nhds 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hbound
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact herror n hn
  exact tendsto_const_nhds.congr_dist hdist

@[expose] noncomputable def roughModulus (theta : ℝ) : ℕ :=
  ∏ p ∈ strictPrimeRange theta, p

lemma roughModulus_pos (theta : ℝ) : 0 < roughModulus theta := by
  unfold roughModulus
  exact Finset.prod_pos fun p hp =>
    (Finset.mem_filter.mp hp).2.pos

lemma rough_iff_coprime (theta : ℝ) (n : ℕ) :
    IsRough n theta ↔ Nat.Coprime (roughModulus theta) n := by
  rw [roughModulus, Nat.coprime_prod_left_iff]
  constructor
  · intro hn p hp
    have hp' : p.Prime := (Finset.mem_filter.mp hp).2
    rw [hp'.coprime_iff_not_dvd]
    intro hpn
    have htheta := hn p hp' hpn
    have hplt : (p : ℝ) < theta := by
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.2
    exact (not_lt_of_ge htheta) hplt
  · intro hn p hp hpn
    by_contra htheta
    have hplt : (p : ℝ) < theta := lt_of_not_ge htheta
    have hprange : p ∈ strictPrimeRange theta := by
      simp only [strictPrimeRange, positiveNatsBelow, Finset.mem_filter,
        Finset.mem_range]
      refine ⟨⟨Nat.lt_ceil.mpr hplt, hp.pos, hplt⟩, hp⟩
    have hcop : Nat.Coprime p n := by
      exact hn p hprange
    exact (hp.coprime_iff_not_dvd.mp hcop) hpn

lemma rough_prefix_count (theta : ℝ) (x : ℕ) :
    prefixCount (roughNumberSet theta) x =
      Nat.count (fun n => 0 < n ∧ Nat.Coprime (roughModulus theta) n) x := by
  classical
  rw [prefixCount, Nat.count_eq_card_filter_range]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, roughNumberSet, Set.mem_setOf_eq]
  rw [rough_iff_coprime]
  tauto

lemma positive_coprime_periodic (theta : ℝ)
    (hq_one : roughModulus theta ≠ 1) :
    Periodic
      (fun n : ℕ => 0 < n ∧ Nat.Coprime (roughModulus theta) n)
      (roughModulus theta) := by
  intro n
  have hq := roughModulus_pos theta
  apply propext
  constructor
  · intro h
    have hn : 0 < n := by
      by_contra hn0
      have : n = 0 := Nat.eq_zero_of_not_pos hn0
      subst n
      simp only [zero_add] at h
      have hnot : ¬Nat.Coprime (roughModulus theta) (roughModulus theta) := by
        rw [Nat.coprime_self]
        exact hq_one
      exact hnot h.2
    exact ⟨hn, (Nat.periodic_coprime (roughModulus theta) n).mp h.2⟩
  · intro h
    exact ⟨Nat.add_pos_right n hq,
      (Nat.periodic_coprime (roughModulus theta) n).mpr h.2⟩

lemma modulus_primeFactors (theta : ℝ) :
    (roughModulus theta).primeFactors = strictPrimeRange theta := by
  unfold roughModulus
  apply Nat.primeFactors_prod
  intro p hp
  exact (Finset.mem_filter.mp hp).2

lemma roughDensity_eq_totient_ratio (theta : ℝ) :
    roughDensity theta =
      (Nat.totient (roughModulus theta) : ℝ) / roughModulus theta := by
  have hq : roughModulus theta ≠ 0 := (roughModulus_pos theta).ne'
  have hrat := Nat.totient_eq_mul_prod_factors (roughModulus theta)
  rw [modulus_primeFactors] at hrat
  have hcastQ := congrArg (fun z : ℚ => (z : ℝ)) hrat
  have hcast :
      (Nat.totient (roughModulus theta) : ℝ) =
        (roughModulus theta : ℝ) *
          ∏ p ∈ strictPrimeRange theta, (1 - (p : ℝ)⁻¹) := by
    norm_num at hcastQ ⊢
    simpa using hcastQ
  unfold roughDensity
  rw [hcast]
  field_simp [Nat.cast_ne_zero.mpr hq]

theorem p019 : P019Statement := by
  intro theta htheta
  unfold HasNaturalDensity prefixDensity
  by_cases hq_one : roughModulus theta = 1
  · have hprefix : ∀ x : ℕ,
        prefixCount (roughNumberSet theta) x = x - 1 := by
      intro x
      rw [rough_prefix_count]
      simp only [hq_one, Nat.coprime_one_left, and_true]
      induction x with
      | zero => simp
      | succ x ih =>
          rw [Nat.count_succ, ih]
          by_cases hx : x = 0
          · subst x
            simp
          · have hxpos := Nat.pos_of_ne_zero hx
            simp [hxpos, Nat.sub_add_cancel hxpos]
    have hmodel :
        Tendsto (fun x : ℕ => 1 - 1 / (x : ℝ)) atTop (nhds 1) := by
      have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
        tendsto_const_nhds
      have hfrac : Tendsto (fun x : ℕ => (1 : ℝ) / (x : ℝ)) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      simpa only [sub_zero] using hone.sub hfrac
    have heventually : ∀ᶠ x : ℕ in atTop,
        (prefixCount (roughNumberSet theta) x : ℝ) / x =
          1 - 1 / (x : ℝ) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [hprefix, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hx.ne')]
      have hxR : (x : ℝ) ≠ 0 := by exact_mod_cast hx.ne'
      norm_num only [Nat.cast_one]
      field_simp [hxR]
    have hrough : roughDensity theta = 1 := by
      rw [roughDensity_eq_totient_ratio, hq_one]
      norm_num
    rw [hrough]
    exact hmodel.congr' (Filter.EventuallyEq.symm heventually)
  · have hperiod := periodic_density
      (fun n : ℕ => 0 < n ∧ Nat.Coprime (roughModulus theta) n)
      (roughModulus_pos theta) (positive_coprime_periodic theta hq_one)
    have hcount :
        Nat.count
            (fun n : ℕ => 0 < n ∧ Nat.Coprime (roughModulus theta) n)
            (roughModulus theta) =
          Nat.totient (roughModulus theta) := by
      rw [Nat.count_eq_card_filter_range, Nat.totient_eq_card_coprime]
      congr 1
      ext n
      by_cases hn : n = 0
      · subst n
        simp [Nat.coprime_zero_right, hq_one]
      · simp [hn, Nat.pos_of_ne_zero hn]
    rw [hcount] at hperiod
    simpa [rough_prefix_count, roughDensity_eq_totient_ratio] using hperiod

end Erdos448.Stage7.ROOT02.RoughDensity
