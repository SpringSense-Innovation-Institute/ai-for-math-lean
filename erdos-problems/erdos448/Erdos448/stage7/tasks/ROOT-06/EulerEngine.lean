module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage4.WrapupFamilies
public import Erdos448.stage6.TaskContracts
public import Erdos448.stage7.shared.LocalFactorFloor

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT06.EulerEngine

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Erdos448.Stage4.WrapupFamilies
open Finset
open scoped BigOperators

noncomputable section

instance (p : Prop) : Decidable p := Classical.propDecidable p

@[expose] def regularBase : RegularIndex where
  parameters := {
    theta := 2
    theta_ge_two := le_rfl
    y := 1 / 2
    y_pos := by norm_num
    y_lt_one := by norm_num
    k := 1
    k_pos := by omega
    sigma := 2
    sigma_ge_theta := le_rfl }
  member := .w1
  regular := by norm_num
  z := 2
  z_ge_two := le_rfl

theorem regular_nonempty : Nonempty RegularIndex := ⟨regularBase⟩

theorem actual_floor (W : CommonWeightWitnesses)
    (h051H : P051HStatement) (q : RegularIndex) {p : ℕ} (hp : p.Prime) :
    1 ≤ regularEuler q p := by
  exact Erdos448.Stage7.Shared.localEulerFactor_ge_one hp
    (W.weight_type q.parameters q.member).nonnegative_multiplicative
    (W.weight_type q.parameters q.member).normalized
    (W.modifier q.parameters)
    (h051H W q.parameters q.member (modifierWeight q.parameters)
      (W.modifier q.parameters) p hp).domain.summable

theorem model_mid_floor (q : RegularIndex) {p : ℕ} (hp : p.Prime) :
    1 ≤ 1 + q.parameters.y / (2 * (p : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hy := q.parameters.y_pos
  have : 0 ≤ q.parameters.y / (2 * (p : ℝ)) := by positivity
  linarith

theorem model_high_floor {p : ℕ} (hp : p.Prime) :
    1 ≤ 1 + (1 : ℝ) / (2 * (p : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have : 0 ≤ (1 : ℝ) / (2 * (p : ℝ)) := by positivity
  linarith

lemma isRough_prime_pow_iff {p j : ℕ} (hp : p.Prime) (hj : 0 < j)
    (s : ℝ) : IsRough (p ^ j) s ↔ s ≤ p := by
  constructor
  · intro h
    exact h p hp (dvd_pow_self p hj.ne')
  · intro h r hr hrd
    have hrp : r ∣ p := hr.dvd_of_dvd_pow hrd
    have : r = p := (Nat.dvd_prime hp).mp hrp |>.resolve_left hr.ne_one
    simpa [this] using h

lemma roughIndicator_prime_pow {p j : ℕ} (hp : p.Prime) (s : ℝ) :
    roughIndicator (p ^ j) s = if j = 0 then 1 else if s ≤ p then 1 else 0 := by
  by_cases hj : j = 0
  · subst j
    have hone : IsRough 1 s := by
      intro r hr hrd
      have hr1 : r = 1 := Nat.dvd_one.mp hrd
      subst r
      exact (Nat.not_prime_one hr).elim
    simp [roughIndicator, hone]
  · have hjp : 0 < j := Nat.pos_of_ne_zero hj
    by_cases hs : s ≤ p
    · simp [roughIndicator, hj, hs, (isRough_prime_pow_iff hp hjp s).2 hs]
    · simp [roughIndicator, hj, hs, (isRough_prime_pow_iff hp hjp s).not.mpr hs]

lemma omegaBelowRaw_prime_pow {p j : ℕ} (hp : p.Prime) (u : ℝ) :
    omegaBelowRaw (p ^ j) u = if (p : ℝ) < u then j else 0 := by
  by_cases hj : j = 0
  · subst j
    simp [omegaBelowRaw, omegaBelow]
  · have hpj : 0 < p ^ j := pow_pos hp.pos j
    simp only [omegaBelowRaw, dif_pos hpj, omegaBelow,
      Nat.primeFactors_prime_pow hj hp, Finset.sum_singleton]
    rw [Nat.factorization_pow_self hp]

theorem midOutput (hP008 : P008Statement.{0}) (W : CommonWeightWitnesses)
    (h051H : P051HStatement) :
    Nonempty (P008Output regularMidCoefficient regularMidFactor) := by
  have heta : 0 < commonEta W := lt_min W.cStar_pos zero_lt_one
  have hC : 0 < commonError W := by
    dsimp [commonError]
    linarith [W.CStar_pos, W.LambdaStar_pos]
  apply hP008 RegularIndex regular_nonempty 0 (1 / 2) (by norm_num)
    (by positivity : 0 < (1 : ℝ) + 0 / 2)
    (commonEta W) (commonError W) heta hC
    2 1 1 le_rfl zero_lt_one le_rfl
  · intro q
    constructor
    · exact div_nonneg q.parameters.y_pos.le (by norm_num)
    · have := q.parameters.y_lt_one
      dsimp [regularMidCoefficient]
      linarith
  · intro q p hp
    unfold regularMidFactor
    split_ifs
    · exact actual_floor W h051H q hp
    · exact model_mid_floor q hp
  · intro q p hp _
    unfold regularMidFactor
    split_ifs with hactive
    · have hbprime : modifierWeight q.parameters p = q.parameters.y := by
        unfold modifierWeight
        rw [if_pos hp.pos]
        have hr := roughIndicator_prime_pow (j := 1) hp q.parameters.sigma
        have ho := omegaBelowRaw_prime_pow (j := 1) hp
          (q.parameters.theta ^ q.parameters.k)
        have hpH : (p : ℝ) < q.parameters.theta ^ q.parameters.k :=
          (lt_min_iff.mp hactive.2).2
        rw [show roughIndicator p q.parameters.sigma = 1 by
          simpa [hactive.1] using hr,
          show omegaBelowRaw p (q.parameters.theta ^ q.parameters.k) = 1 by
            simpa [hpH] using ho]
        simp
      simpa [regularEuler, regularMidCoefficient, commonEta, commonError,
        hbprime, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (h051H W q.parameters q.member (modifierWeight q.parameters)
          (W.modifier q.parameters) p hp).replaced_main_term
    · dsimp [regularMidCoefficient, commonError, commonEta]
      have heq : 1 + q.parameters.y / (2 * (p : ℝ)) -
          (1 + q.parameters.y / 2 / (p : ℝ)) = 0 := by ring
      rw [heq, abs_zero]
      exact mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _)
  · intro q p hp hp2 hplt
    exfalso
    exact (not_lt_of_ge (by exact_mod_cast hp2 : (2 : ℝ) ≤ p)) hplt

theorem highOutput (hP008 : P008Statement.{0}) (W : CommonWeightWitnesses)
    (h051H : P051HStatement) :
    Nonempty (P008Output regularHighCoefficient regularHighFactor) := by
  have heta : 0 < commonEta W := lt_min W.cStar_pos zero_lt_one
  have hC : 0 < commonError W := by
    dsimp [commonError]
    linarith [W.CStar_pos, W.LambdaStar_pos]
  apply hP008 RegularIndex regular_nonempty (1 / 2) (1 / 2) le_rfl
    (by norm_num : 0 < (1 : ℝ) + (1 / 2) / 2)
    (commonEta W) (commonError W) heta hC
    2 1 1 le_rfl zero_lt_one le_rfl
  · intro q
    exact ⟨le_rfl, le_rfl⟩
  · intro q p hp
    unfold regularHighFactor
    split_ifs
    · exact actual_floor W h051H q hp
    · exact model_high_floor hp
  · intro q p hp _
    unfold regularHighFactor
    split_ifs with hactive
    · have hbprime : modifierWeight q.parameters p = 1 := by
        unfold modifierWeight
        rw [if_pos hp.pos]
        have hr := roughIndicator_prime_pow (j := 1) hp q.parameters.sigma
        have ho := omegaBelowRaw_prime_pow (j := 1) hp
          (q.parameters.theta ^ q.parameters.k)
        have hsigp : q.parameters.sigma ≤ (p : ℝ) :=
          q.regular.trans hactive.1
        rw [show roughIndicator p q.parameters.sigma = 1 by
          simpa [hsigp] using hr,
          show omegaBelowRaw p (q.parameters.theta ^ q.parameters.k) = 0 by
            simpa [not_lt.mpr hactive.1] using ho]
        simp
      simpa [regularEuler, regularHighCoefficient, commonEta, commonError,
        hbprime, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (h051H W q.parameters q.member (modifierWeight q.parameters)
          (W.modifier q.parameters) p hp).replaced_main_term
    · dsimp [regularHighCoefficient, commonError, commonEta]
      have heq : 1 + (1 : ℝ) / (2 * (p : ℝ)) -
          (1 + (1 / 2 : ℝ) / (p : ℝ)) = 0 := by ring
      rw [heq, abs_zero]
      exact mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _)
  · intro q p hp hp2 hplt
    exfalso
    exact (not_lt_of_ge (by exact_mod_cast hp2 : (2 : ℝ) ≤ p)) hplt

lemma modifier_prime_pow_zero
    (q : WeightParameters) {p j : ℕ} (hp : p.Prime) (hj : 1 ≤ j)
    (hps : (p : ℝ) < q.sigma) : modifierWeight q (p ^ j) = 0 := by
  have hpj : 0 < p ^ j := Nat.pow_pos hp.pos
  have hpdiv : p ∣ p ^ j := by
    exact dvd_pow_self p (Nat.ne_of_gt hj)
  have hnrough : ¬ IsRough (p ^ j) q.sigma := by
    intro h
    exact (not_le_of_gt hps) (h p hp hpdiv)
  unfold modifierWeight
  rw [if_pos hpj]
  simp [roughIndicator, hnrough]

theorem euler_eq_one_below_sigma
    (W : CommonWeightWitnesses) (h051H : P051HStatement)
    (q : WeightParameters) (member : WeightMember) {p : ℕ} (hp : p.Prime)
    (hps : (p : ℝ) < q.sigma) :
    localEulerFactor (selectedWeight q member) (modifierWeight q) p = 1 := by
  have hsum := (h051H W q member (modifierWeight q) (W.modifier q) p hp).domain.summable
  rw [localEulerFactor]
  calc
    (∑' j : ℕ, selectedWeight q member (p ^ j) * modifierWeight q (p ^ j) /
        (p : ℝ) ^ j) =
        ∑' j : ℕ, if j = 0 then 1 else 0 := by
          apply tsum_congr
          intro j
          by_cases hj : j = 0
          · subst j
            simp [(W.weight_type q member).normalized, (W.modifier q).normalized]
          · have hjpos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
            rw [modifier_prime_pow_zero q hp hjpos hps]
            simp [hj]
    _ = 1 := by simp

theorem mem_strictPrimeRange {x : ℝ} {p : ℕ} :
    p ∈ strictPrimeRange x ↔ p.Prime ∧ (p : ℝ) < x := by
  constructor
  · intro h
    have hfilter := Finset.mem_filter.mp h
    exact ⟨hfilter.2, (Finset.mem_filter.mp hfilter.1).2.2⟩
  · rintro ⟨hp, hpx⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨?_, hp.pos, hpx⟩, hp⟩
    exact Finset.mem_range.mpr (Nat.lt_ceil.mpr hpx)

lemma strictPrimeRange_mono {A B : ℝ} (hAB : A ≤ B) :
    strictPrimeRange A ⊆ strictPrimeRange B := by
  intro p hp
  exact mem_strictPrimeRange.mpr
    ⟨(mem_strictPrimeRange.mp hp).1, (mem_strictPrimeRange.mp hp).2.trans_le hAB⟩

lemma intervalProduct_extend_right
    (L : ℕ → ℝ) {A C B : ℝ} (hCB : C ≤ B) :
    primeIntervalProduct L A C =
      ∏ p ∈ strictPrimeRange B,
        if A ≤ (p : ℝ) ∧ (p : ℝ) < C then L p else 1 := by
  unfold primeIntervalProduct
  apply Finset.prod_subset_one_on_sdiff (strictPrimeRange_mono hCB)
  · intro p hpDiff
    have hpB := (Finset.mem_sdiff.mp hpDiff).1
    have hpNotC := (Finset.mem_sdiff.mp hpDiff).2
    have hpNotLtC : ¬(p : ℝ) < C := by
      intro hpLtC
      exact hpNotC (mem_strictPrimeRange.mpr
        ⟨(mem_strictPrimeRange.mp hpB).1, hpLtC⟩)
    simp [hpNotLtC]
  · intro p hpC
    have hpLtC := (mem_strictPrimeRange.mp hpC).2
    by_cases hpA : A ≤ (p : ℝ) <;> simp [hpA, hpLtC]

theorem strictEuler_eq_mid
    (W : CommonWeightWitnesses) (h051H : P051HStatement)
    (q : RegularIndex) (hz : q.z ≤ q.parameters.theta ^ q.parameters.k)
    (hsz : q.parameters.sigma ≤ q.z) :
    (∏ p ∈ strictPrimeRange q.z, regularEuler q p) =
      primeIntervalProduct (regularMidFactor q) q.parameters.sigma q.z := by
  unfold primeIntervalProduct
  apply Finset.prod_congr rfl
  intro p hpz
  have hp := (mem_strictPrimeRange.mp hpz).1
  have hpz' := (mem_strictPrimeRange.mp hpz).2
  by_cases hsp : q.parameters.sigma ≤ (p : ℝ)
  · have hactive : q.parameters.sigma ≤ (p : ℝ) ∧
        (p : ℝ) < min q.z (q.parameters.theta ^ q.parameters.k) := by
      refine ⟨hsp, lt_min hpz' ?_⟩
      exact hpz'.trans_le hz
    simp [hsp, regularMidFactor, hactive]
  · have hps : (p : ℝ) < q.parameters.sigma := lt_of_not_ge hsp
    unfold regularEuler
    rw [euler_eq_one_below_sigma W h051H q.parameters q.member hp hps]
    simp [hsp]

theorem strictEuler_eq_mid_mul_high
    (W : CommonWeightWitnesses) (h051H : P051HStatement)
    (q : RegularIndex) (hHz : q.parameters.theta ^ q.parameters.k ≤ q.z) :
    (∏ p ∈ strictPrimeRange q.z, regularEuler q p) =
      primeIntervalProduct (regularMidFactor q) q.parameters.sigma
          (q.parameters.theta ^ q.parameters.k) *
        primeIntervalProduct (regularHighFactor q)
          (q.parameters.theta ^ q.parameters.k) q.z := by
  rw [intervalProduct_extend_right (regularMidFactor q) hHz]
  unfold primeIntervalProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hpz
  have hp := (mem_strictPrimeRange.mp hpz).1
  have hpz' := (mem_strictPrimeRange.mp hpz).2
  by_cases hsp : q.parameters.sigma ≤ (p : ℝ)
  · by_cases hpH : (p : ℝ) < q.parameters.theta ^ q.parameters.k
    · have hmid : q.parameters.sigma ≤ (p : ℝ) ∧
          (p : ℝ) < min q.z (q.parameters.theta ^ q.parameters.k) :=
        ⟨hsp, lt_min hpz' hpH⟩
      have hnotHigh : ¬q.parameters.theta ^ q.parameters.k ≤ (p : ℝ) :=
        not_le_of_gt hpH
      simp [regularMidFactor, regularHighFactor, hmid, hnotHigh, hsp]
    · have hHp : q.parameters.theta ^ q.parameters.k ≤ (p : ℝ) := le_of_not_gt hpH
      have hhigh : q.parameters.theta ^ q.parameters.k ≤ (p : ℝ) ∧
          (p : ℝ) < q.z := ⟨hHp, hpz'⟩
      have hnotMid : ¬((p : ℝ) < min q.z
          (q.parameters.theta ^ q.parameters.k)) := by
        exact fun h => hpH (lt_min_iff.mp h).2
      simp [regularMidFactor, regularHighFactor, hnotMid, hhigh, hsp]
  · have hps : (p : ℝ) < q.parameters.sigma := lt_of_not_ge hsp
    have hnotH : ¬q.parameters.theta ^ q.parameters.k ≤ (p : ℝ) := by
      intro h
      exact hsp (q.regular.trans h)
    unfold regularEuler
    rw [euler_eq_one_below_sigma W h051H q.parameters q.member hp hps]
    simp [hsp, hnotH]

end

end Erdos448.Stage7.ROOT06.EulerEngine
