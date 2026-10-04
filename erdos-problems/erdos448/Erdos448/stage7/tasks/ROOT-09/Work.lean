module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.shared.LocalFactorFloor
public import Erdos448.stage7.foundation.«P068-P069».Work
public import Erdos448.stage6.TaskContracts

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT09.Work

open Finset
open scoped BigOperators

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Erdos448.Stage6.TaskContracts

noncomputable section

lemma mem_positiveNatsBelow {z : ℝ} {n : ℕ} :
    n ∈ positiveNatsBelow z ↔ 0 < n ∧ (n : ℝ) < z := by
  constructor
  · intro hn
    exact (Finset.mem_filter.mp hn).2
  · rintro ⟨hn, hnz⟩
    rw [positiveNatsBelow, Finset.mem_filter]
    exact ⟨by simpa using Nat.lt_ceil.mpr hnz, hn, hnz⟩

lemma isRough_mul_iff (a b : ℕ) (s : ℝ) :
    IsRough (a * b) s ↔ IsRough a s ∧ IsRough b s := by
  constructor
  · intro h
    exact ⟨fun p hp hpa => h p hp (dvd_mul_of_dvd_left hpa b),
      fun p hp hpb => h p hp (dvd_mul_of_dvd_right hpb a)⟩
  · rintro ⟨ha, hb⟩ p hp hpab
    rcases hp.dvd_mul.mp hpab with hpa | hpb
    · exact ha p hp hpa
    · exact hb p hp hpb

lemma roughIndicator_mul (a b : ℕ) (s : ℝ) :
    roughIndicator (a * b) s = roughIndicator a s * roughIndicator b s := by
  by_cases ha : IsRough a s <;> by_cases hb : IsRough b s
  · have hab := (isRough_mul_iff a b s).2 ⟨ha, hb⟩
    simp [roughIndicator, ha, hb, hab]
  · have hab : ¬ IsRough (a * b) s := fun h => hb ((isRough_mul_iff a b s).1 h).2
    simp [roughIndicator, ha, hb, hab]
  · have hab : ¬ IsRough (a * b) s := fun h => ha ((isRough_mul_iff a b s).1 h).1
    simp [roughIndicator, ha, hb, hab]
  · have hab : ¬ IsRough (a * b) s := fun h => ha ((isRough_mul_iff a b s).1 h).1
    simp [roughIndicator, ha, hb, hab]

lemma omegaBelowRaw_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (u : ℝ) :
    omegaBelowRaw (a * b) u = omegaBelowRaw a u + omegaBelowRaw b u := by
  simp only [omegaBelowRaw, dif_pos ha, dif_pos hb, dif_pos (Nat.mul_pos ha hb),
    omegaBelow]
  change (a * b).factorization.sum (fun p e => if (p : ℝ) < u then e else 0) =
    a.factorization.sum (fun p e => if (p : ℝ) < u then e else 0) +
      b.factorization.sum (fun p e => if (p : ℝ) < u then e else 0)
  rw [Nat.factorization_mul (Nat.ne_of_gt ha) (Nat.ne_of_gt hb)]
  apply Finsupp.sum_add_index'
  · intro p
    simp
  · intro p e₁ e₂
    by_cases hp : (p : ℝ) < u <;> simp [hp]

lemma modifier_split (q : WeightParameters) {d t : ℕ}
    (hd : 0 < d) (ht : 0 < t) :
    (roughIndicator (d * t) q.sigma : ℝ) *
        q.y.rpow (omegaBelowRaw (d * t) (q.theta ^ q.k) : ℝ) =
      ((roughIndicator d q.sigma : ℝ) *
        q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ)) *
        modifierWeight q t := by
  simp only [modifierWeight, if_pos ht]
  rw [roughIndicator_mul, omegaBelowRaw_mul hd ht, Nat.cast_add]
  have hyadd :
      q.y.rpow ((omegaBelowRaw d (q.theta ^ q.k) : ℝ) +
          (omegaBelowRaw t (q.theta ^ q.k) : ℝ)) =
        q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
          q.y.rpow (omegaBelowRaw t (q.theta ^ q.k) : ℝ) :=
    Real.rpow_add q.y_pos _ _
  rw [hyadd]
  push_cast
  ring

lemma triangular_inner_eq (x : ℝ) {D t : ℕ}
    (hD : 0 < D) (ht : 0 < t) :
    positiveNatsBelow (x / (t * D : ℕ)) =
      (positiveNatsBelow (x / D)).filter
        (fun m => t ∈ positiveNatsBelow (x / (m * D : ℕ))) := by
  ext m
  simp only [Finset.mem_filter, mem_positiveNatsBelow]
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  constructor
  · rintro ⟨hm, hmBound⟩
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hprod : (m : ℝ) * (t : ℝ) * (D : ℝ) < x := by
      have := (lt_div_iff₀ (show (0 : ℝ) < (t * D : ℕ) by positivity)).mp hmBound
      norm_num [Nat.cast_mul] at this ⊢
      nlinarith
    have hmOuter : (m : ℝ) < x / (D : ℝ) := by
      apply (lt_div_iff₀ hDR).2
      have htOne : (1 : ℝ) ≤ t := by exact_mod_cast ht
      calc
        (m : ℝ) * D = (m : ℝ) * 1 * D := by ring
        _ ≤ (m : ℝ) * t * D := by gcongr
        _ < x := hprod
    have htInner : (t : ℝ) < x / (m * D : ℕ) := by
      apply (lt_div_iff₀ (show (0 : ℝ) < (m * D : ℕ) by positivity)).2
      norm_num [Nat.cast_mul]
      nlinarith
    exact ⟨⟨hm, hmOuter⟩, ht, htInner⟩
  · rintro ⟨⟨hm, hmOuter⟩, htMem, htBound⟩
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hprod : (t : ℝ) * ((m : ℝ) * (D : ℝ)) < x := by
      have := (lt_div_iff₀ (show (0 : ℝ) < (m * D : ℕ) by positivity)).mp htBound
      norm_num [Nat.cast_mul] at this ⊢
      exact this
    refine ⟨hm, (lt_div_iff₀ (show (0 : ℝ) < (t * D : ℕ) by positivity)).2 ?_⟩
    norm_num [Nat.cast_mul]
    nlinarith

lemma triangular_swap (x : ℝ) {D : ℕ} (hD : 0 < D)
    (f : ℕ → ℕ → ℝ) :
    (∑ t ∈ positiveNatsBelow (x / D),
        ∑ m ∈ positiveNatsBelow (x / (t * D : ℕ)), f t m) =
      ∑ m ∈ positiveNatsBelow (x / D),
        ∑ t ∈ positiveNatsBelow (x / (m * D : ℕ)), f t m := by
  classical
  let S := positiveNatsBelow (x / D)
  calc
    (∑ t ∈ S, ∑ m ∈ positiveNatsBelow (x / (t * D : ℕ)), f t m) =
        ∑ t ∈ S, ∑ m ∈ S,
          if t ∈ positiveNatsBelow (x / (m * D : ℕ)) then f t m else 0 := by
      apply Finset.sum_congr rfl
      intro t htS
      have ht : 0 < t := (mem_positiveNatsBelow.mp htS).1
      rw [triangular_inner_eq x hD ht]
      simp only [Finset.sum_filter]
      rfl
    _ = ∑ m ∈ S, ∑ t ∈ S,
          if t ∈ positiveNatsBelow (x / (m * D : ℕ)) then f t m else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ m ∈ S, ∑ t ∈ positiveNatsBelow (x / (m * D : ℕ)), f t m := by
      apply Finset.sum_congr rfl
      intro m hmS
      have hm : 0 < m := (mem_positiveNatsBelow.mp hmS).1
      rw [← Finset.sum_filter]
      congr 1
      ext t
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.2
      · intro htInner
        have heq := triangular_inner_eq x hD hm
        have hmem : t ∈ (positiveNatsBelow (x / D)).filter
            (fun t => m ∈ positiveNatsBelow (x / (t * D : ℕ))) := by
          rw [← heq]
          exact htInner
        exact ⟨(Finset.mem_filter.mp hmem).1, htInner⟩

@[expose] def transitionLowEuler (q : TransitionParameters) (p : ℕ) : ℝ :=
  if (p : ℝ) < q.sigma then
    localEulerFactor w1Weight (modifierWeight q.toWeightParameters) p
  else 1

@[expose] def transitionHighEuler (q : TransitionParameters) (p : ℕ) : ℝ :=
  if q.sigma ≤ (p : ℝ) then
    localEulerFactor w1Weight (modifierWeight q.toWeightParameters) p
  else 1 + 1 / (2 * (p : ℝ))

@[expose] def transitionLowCoefficient (_ : TransitionParameters) : ℝ := 0

@[expose] def transitionHighCoefficient (_ : TransitionParameters) : ℝ := 1 / 2

structure TransitionEulerComparisons where
  low : P008Output transitionLowCoefficient transitionLowEuler
  high : P008Output transitionHighCoefficient transitionHighEuler

@[expose] def exampleTransitionParameters : TransitionParameters where
  theta := 2
  theta_ge_two := le_rfl
  y := 1 / 2
  y_pos := by norm_num
  y_lt_one := by norm_num
  k := 1
  k_pos := le_rfl
  sigma := 3
  sigma_ge_theta := by norm_num
  sigma_gt_bin := by norm_num
  sigma_lt_next_bin := by norm_num

lemma modifier_prime_below_sigma
    (q : TransitionParameters) {p : ℕ} (hp : p.Prime)
    (hbelow : (p : ℝ) < q.sigma) :
    modifierWeight q.toWeightParameters p = 0 := by
  have hnot : ¬ IsRough p q.sigma := by
    intro hrough
    exact (not_le_of_gt hbelow) (hrough p hp (dvd_refl p))
  simp [modifierWeight, hp.pos, roughIndicator, hnot]

lemma modifier_prime_above_sigma
    (q : TransitionParameters) {p : ℕ} (hp : p.Prime)
    (habove : q.sigma ≤ (p : ℝ)) :
    modifierWeight q.toWeightParameters p = 1 := by
  have hrough : IsRough p q.sigma := by
    intro r hr hdiv
    rcases (Nat.dvd_prime hp).mp hdiv with hrone | hrp
    · subst r
      exact False.elim (Nat.not_prime_one hr)
    · simpa [hrp] using habove
  have homega : omegaBelowRaw p (q.theta ^ q.k) = 0 := by
    simp only [omegaBelowRaw, dif_pos hp.pos, omegaBelow]
    rw [hp.primeFactors]
    simp only [Finset.sum_singleton]
    have hcut : ¬ (p : ℝ) < q.theta ^ q.k := by
      exact not_lt_of_ge (le_trans (le_of_lt q.sigma_gt_bin) habove)
    simp [hcut]
  simp [modifierWeight, hp.pos, roughIndicator, hrough, homega]

lemma shiftedGeometricBounds_w1_modifier
    (W : CommonWeightWitnesses) (q : WeightParameters) :
    ShiftedGeometricBounds w1Weight (modifierWeight q)
      (fun _ => W.LambdaStar) 1 := by
  intro p hp i j
  have hmod := (W.modifier q).prime_power_bounds p hp j
  have hone : 1 ≤ W.LambdaStar := by
    have hrpow : 0 < (2 : ℝ).rpow (-W.cStar) := Real.rpow_pos_of_pos (by norm_num) _
    nlinarith [W.LambdaStar_lower, W.CStar_pos]
  by_cases hij : i + j = 0
  · have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst i
    subst j
    have hnorm : w1Weight 1 = 1 := (W.weight_type q .w1).normalized
    simpa [hnorm, (W.modifier q).normalized] using
      (show 0 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ W.LambdaStar from ⟨by norm_num, hone⟩)
  · have hijpos : 1 ≤ i + j := Nat.one_le_iff_ne_zero.mpr hij
    have hw := (W.weight_type q .w1).prime_power_bounds p hp (i + j) hijpos
    constructor
    · exact mul_nonneg hw.1 hmod.1
    · simpa [selectedWeight] using mul_le_mul hw.2 hmod.2 hmod.1 (by linarith)

lemma shiftedPrimeProduct_le_w2
    (chain : WeightChainSpec) (W : CommonWeightWitnesses)
    (q : WeightParameters) (K : PosNat) (X : ℝ) :
    shiftedPrimeProduct w1Weight (modifierWeight q) K X ≤
      w2Weight q K.1 := by
  classical
  unfold shiftedPrimeProduct w2Weight maxShift multiplicativeExtension
  simp only [if_neg (Nat.ne_of_gt K.2)]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro p hpMem
    have hp := Nat.prime_of_mem_primeFactors hpMem
    have he : 1 ≤ K.1.factorization p :=
      hp.factorization_pos_of_dvd (Nat.ne_of_gt K.2)
        (Nat.dvd_of_mem_primeFactors hpMem)
    by_cases hpx : (p : ℝ) < X
    · simp only [if_pos hpx, if_neg (not_le_of_gt hpx), mul_one]
      unfold exactShiftFactor
      have hshift :
          localShift w1Weight (modifierWeight q) p (K.1.factorization p) =
            shift w1Weight (modifierWeight q) (p ^ K.1.factorization p) := by
        symm
        exact chain.w2_shift q |>.shift_prime_power p hp _ he
      rw [hshift]
      exact chain.w2_shift q |>.shift_nonnegative_multiplicative.nonnegative _
        (pow_pos hp.pos _)
    · simp only [if_neg hpx, if_pos (le_of_not_gt hpx), one_mul]
      exact (W.weight_type q .w1).nonnegative_multiplicative.nonnegative _
        (pow_pos hp.pos _)
  · intro p hpMem
    have hp := Nat.prime_of_mem_primeFactors hpMem
    have he : 1 ≤ K.1.factorization p :=
      hp.factorization_pos_of_dvd (Nat.ne_of_gt K.2)
        (Nat.dvd_of_mem_primeFactors hpMem)
    by_cases hpx : (p : ℝ) < X
    · simp only [if_pos hpx, if_neg (not_le_of_gt hpx), mul_one]
      exact le_max_left _ _
    · simp only [if_neg hpx, if_pos (le_of_not_gt hpx), one_mul]
      exact le_max_right _ _

theorem transitionEulerComparisons
    (h008 : P008Statement.{0}) (W : CommonWeightWitnesses)
    (h051 : P051HStatement) : Nonempty TransitionEulerComparisons := by
  let eta : ℝ := min W.cStar 1
  let Cerr : ℝ := W.CStar + 2 * W.LambdaStar
  have heta : 0 < eta := by simp [eta, W.cStar_pos]
  have hCerr : 0 < Cerr := by dsimp [Cerr]; nlinarith [W.CStar_pos, W.LambdaStar_pos]
  have hlowFloor : ∀ q : TransitionParameters, ∀ p : ℕ, p.Prime →
      1 ≤ transitionLowEuler q p := by
    intro q p hp
    unfold transitionLowEuler
    split_ifs with hbelow
    · exact Erdos448.Stage7.Shared.localEulerFactor_ge_one hp
        (W.weight_type q.toWeightParameters .w1).nonnegative_multiplicative
        (W.weight_type q.toWeightParameters .w1).normalized
        (W.modifier q.toWeightParameters)
        (h051 W q.toWeightParameters .w1
          (modifierWeight q.toWeightParameters) (W.modifier q.toWeightParameters)
          p hp).domain.summable
    · norm_num
  have hlowErr : ∀ q : TransitionParameters, ∀ p : ℕ, p.Prime → (2 : ℝ) ≤ p →
      |transitionLowEuler q p - (1 + transitionLowCoefficient q / p)| ≤
        Cerr * (p : ℝ).rpow (-1 - eta) := by
    intro q p hp hp2
    unfold transitionLowEuler transitionLowCoefficient
    split_ifs with hbelow
    · have hb := modifier_prime_below_sigma q hp hbelow
      have hs := (h051 W q.toWeightParameters .w1
        (modifierWeight q.toWeightParameters) (W.modifier q.toWeightParameters)
        p hp).replaced_main_term
      simpa [hb, eta, Cerr, selectedWeight] using hs
    · simp only [zero_div, add_zero, sub_self, abs_zero]
      exact mul_nonneg hCerr.le (Real.rpow_nonneg (by positivity) _)
  obtain ⟨low⟩ := h008 TransitionParameters ⟨exampleTransitionParameters⟩
    (0 : ℝ) (0 : ℝ) (by norm_num) (by rw [zero_div, add_zero]; norm_num)
    eta Cerr heta hCerr
    2 1 1 (by norm_num) (by norm_num) (by norm_num)
    transitionLowCoefficient (by intro q; simp [transitionLowCoefficient])
    transitionLowEuler hlowFloor hlowErr (by
      intro q p hp hp2 hplt
      exfalso
      have hp2R : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      linarith)
  have hhighFloor : ∀ q : TransitionParameters, ∀ p : ℕ, p.Prime →
      1 ≤ transitionHighEuler q p := by
    intro q p hp
    unfold transitionHighEuler
    split_ifs with habove
    · exact Erdos448.Stage7.Shared.localEulerFactor_ge_one hp
        (W.weight_type q.toWeightParameters .w1).nonnegative_multiplicative
        (W.weight_type q.toWeightParameters .w1).normalized
        (W.modifier q.toWeightParameters)
        (h051 W q.toWeightParameters .w1
          (modifierWeight q.toWeightParameters) (W.modifier q.toWeightParameters)
          p hp).domain.summable
    · have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hfrac : 0 ≤ 1 / (2 * (p : ℝ)) := by positivity
      linarith
  have hhighErr : ∀ q : TransitionParameters, ∀ p : ℕ, p.Prime → (2 : ℝ) ≤ p →
      |transitionHighEuler q p - (1 + transitionHighCoefficient q / p)| ≤
        Cerr * (p : ℝ).rpow (-1 - eta) := by
    intro q p hp hp2
    unfold transitionHighEuler transitionHighCoefficient
    split_ifs with habove
    · have hb := modifier_prime_above_sigma q hp habove
      have hs := (h051 W q.toWeightParameters .w1
        (modifierWeight q.toWeightParameters) (W.modifier q.toWeightParameters)
        p hp).replaced_main_term
      simpa [hb, eta, Cerr, selectedWeight, div_eq_mul_inv, mul_comm] using hs
    · have heq : 1 / (2 * (p : ℝ)) = (1 / 2 : ℝ) / p := by ring
      rw [heq, sub_self, abs_zero]
      exact mul_nonneg hCerr.le (Real.rpow_nonneg (by positivity) _)
  obtain ⟨high⟩ := h008 TransitionParameters ⟨exampleTransitionParameters⟩
    (1 / 2) (1 / 2) (by norm_num) (by norm_num) eta Cerr heta hCerr
    2 1 1 (by norm_num) (by norm_num) (by norm_num)
    transitionHighCoefficient (by intro q; simp [transitionHighCoefficient])
    transitionHighEuler hhighFloor hhighErr (by
      intro q p hp hp2 hplt
      exfalso
      have hp2R : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      linarith)
  exact ⟨⟨low, high⟩⟩

lemma transition_sum_partition
    {s : Finset ℕ} (sigma : ℝ) (z : ℕ → ℝ) (f : ℕ → ℝ) :
    (∑ m ∈ s, f m) =
      (∑ m ∈ s, if sigma ≤ z m then f m else 0) +
        ∑ m ∈ s, if z m < sigma then f m else 0 := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases h : sigma ≤ z m
  · simp [h, not_lt_of_ge h]
  · have hz : z m < sigma := lt_of_not_ge h
    simp [h, hz]

lemma nonnegative_outer_coefficient
    (q : WeightParameters) (d : ℕ) :
    0 ≤ (roughIndicator d q.sigma : ℝ) *
      q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) := by
  exact mul_nonneg (by positivity) (Real.rpow_nonneg q.y_pos.le _)

lemma high_transition_kernel_nonnegative
    (q : TransitionParameters) (x : ℝ) (hx : 0 ≤ x) (d d' : ℕ) :
    0 ≤ (Real.log q.sigma).rpow (-1 / 2) *
      ∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
        if q.sigma ≤ zValue x m d d' then
          (safeLog m).rpow (-1 / 2) * zValue x m d d' *
            (safeLog (zValue x m d d')).rpow (-1 / 2)
        else 0 := by
  apply mul_nonneg (Real.rpow_nonneg (Real.log_nonneg (by
    linarith [q.theta_ge_two, q.sigma_ge_theta])) _)
  apply Finset.sum_nonneg
  intro m hm
  split_ifs
  · have hmpos : 0 < m := (Finset.mem_filter.mp hm).2.1
    have hdd : 0 ≤ (m * d * d' : ℕ) := Nat.zero_le _
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by simp [safeLog]) _) (div_nonneg hx (by positivity)))
      (Real.rpow_nonneg (by simp [safeLog]) _)
  · positivity

lemma low_transition_kernel_nonnegative
    (q : TransitionParameters) (x : ℝ) (d d' : ℕ) :
    0 ≤ ∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
      if zValue x m d d' < q.sigma then (safeLog m).rpow (-1 / 2) else 0 := by
  apply Finset.sum_nonneg
  intro m hm
  split_ifs
  · exact Real.rpow_nonneg
      (le_trans (by norm_num) (le_max_left 1 (Real.log (m : ℝ)))) _
  · positivity

theorem p075 (h050 : P050Statement) (h052 : P052Statement) :
    P075Statement := by
  intro theta htheta
  obtain ⟨C, hC, hsm⟩ := h052 theta htheta
  refine ⟨C, hC, ?_⟩
  intro q hq x hx
  classical
  rw [h050 q.toWeightParameters x hx]
  unfold fourVariableInversion transitionSmoothed smoothedRegular
  simp only [partitionAccepts, if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hdSet
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d' hd'Set
  by_cases hd : 0 < d
  · by_cases hd' : 0 < d'
    · by_cases houter : q.theta ^ q.k ≤ (d : ℝ) ∧
          Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩
      · simp only [hd, hd', houter, true_and, and_true, dite_true, if_true]
        let D := d * d'
        let A : ℝ := (roughIndicator d q.sigma : ℝ) *
          q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ)
        have hD : 0 < D := Nat.mul_pos hd hd'
        have hA : 0 ≤ A :=
          mul_nonneg (by positivity) (Real.rpow_nonneg q.y_pos.le _)
        have hxPos : 0 < x := by
          have hp : 0 < q.theta ^ (2 * q.k - 1) :=
            pow_pos (lt_of_lt_of_le (by norm_num) q.theta_ge_two) _
          linarith
        have hterms :
            (∑ t ∈ positiveNatsBelow (x / D),
              (roughIndicator (d * t) q.sigma : ℝ) *
                q.y.rpow (omegaBelowRaw (d * t) (q.theta ^ q.k) : ℝ) *
                (∑ m ∈ positiveNatsBelow (x / (t * d * d' : ℕ)),
                  a0Weight (m * t * d * d'))) ≤
              C * (A * ∑ m ∈ positiveNatsBelow (x / D),
                (safeLog m).rpow (-1 / 2) *
                  shiftedMean q.toWeightParameters (zValue x m d d') ⟨D, hD⟩) := by
          calc
            _ ≤ ∑ t ∈ positiveNatsBelow (x / D),
                (roughIndicator (d * t) q.sigma : ℝ) *
                  q.y.rpow (omegaBelowRaw (d * t) (q.theta ^ q.k) : ℝ) *
                  (C * w1Weight (t * D) * safeLogHalfSum (x / (t * D : ℕ))) := by
              apply Finset.sum_le_sum
              intro t htSet
              have ht : 0 < t := (mem_positiveNatsBelow.mp htSet).1
              have hz : 0 < x / (t * D : ℕ) := div_pos hxPos (by positivity)
              have hbound := hsm q.toWeightParameters hq
                ⟨t * D, Nat.mul_pos ht hD⟩ (x / (t * D : ℕ)) hz
              have hcoeff : 0 ≤ (roughIndicator (d * t) q.sigma : ℝ) *
                  q.y.rpow (omegaBelowRaw (d * t) (q.theta ^ q.k) : ℝ) :=
                mul_nonneg (by positivity) (Real.rpow_nonneg q.y_pos.le _)
              have hin :
                  (∑ m ∈ positiveNatsBelow (x / (t * d * d' : ℕ)),
                    a0Weight (m * t * d * d')) =
                    reciprocalDivisorSum (x / (t * D : ℕ))
                      ⟨t * D, Nat.mul_pos ht hD⟩ := by
                unfold reciprocalDivisorSum D
                simp only [Nat.mul_assoc]
              rw [hin]
              exact mul_le_mul_of_nonneg_left hbound hcoeff
            _ = C * (A * ∑ m ∈ positiveNatsBelow (x / D),
                (safeLog m).rpow (-1 / 2) *
                  shiftedMean q.toWeightParameters (zValue x m d d') ⟨D, hD⟩) := by
              have hsplit :
                  (∑ t ∈ positiveNatsBelow (x / D),
                    (roughIndicator (d * t) q.sigma : ℝ) *
                      q.y.rpow (omegaBelowRaw (d * t) (q.theta ^ q.k) : ℝ) *
                      (C * w1Weight (t * D) * safeLogHalfSum (x / (t * D : ℕ)))) =
                    ∑ t ∈ positiveNatsBelow (x / D),
                      (A * modifierWeight q.toWeightParameters t) *
                        (C * w1Weight (t * D) * safeLogHalfSum (x / (t * D : ℕ))) := by
                apply Finset.sum_congr rfl
                intro t htSet
                rw [modifier_split q.toWeightParameters hd
                  (mem_positiveNatsBelow.mp htSet).1]
              rw [hsplit]
              simp_rw [safeLogHalfSum, Finset.mul_sum]
              rw [triangular_swap x hD (fun t m =>
                (A * modifierWeight q.toWeightParameters t) *
                  (C * w1Weight (t * D) * (safeLog m).rpow (-1 / 2)))]
              unfold Erdos448.Stage4.shiftedMean zValue A D
              simp_rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro m hm
              simp only [Nat.mul_assoc]
              apply Finset.sum_congr rfl
              intro t ht
              ring
        simpa [D, A] using hterms
      · simp [hd, hd', houter]
    · simp [hd']
  · simp [hd]

theorem p076 : P076Statement := by
  intro q x hx
  classical
  unfold transitionSmoothed smoothedRegular transitionRestricted
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d' hd'
  by_cases hdp : 0 < d
  · simp only [dif_pos hdp]
    by_cases hd'p : 0 < d'
    · simp only [dif_pos hd'p]
      by_cases hbase :
          q.theta ^ q.k ≤ (d : ℝ) ∧ Close q.theta ⟨d, hdp⟩ ⟨d', hd'p⟩
      · simp only [if_pos hbase, partitionAccepts]
        simp only [if_true]
        rw [transition_sum_partition q.sigma
          (fun m => zValue x m d d')
          (fun m => (safeLog m).rpow (-1 / 2) *
            shiftedMean q.toWeightParameters (zValue x m d d')
              ⟨d * d', Nat.mul_pos hdp hd'p⟩)]
        ring
      · simp [hbase]
    · simp [hd'p]
  · simp [hdp]

theorem p078 (W : CommonWeightWitnesses) : P078Statement := by
  intro q x hx
  classical
  have hx0 : 0 ≤ x := by
    have htheta : 0 < q.theta := lt_of_lt_of_le (by norm_num) q.theta_ge_two
    exact le_of_lt (lt_trans (pow_pos htheta _) hx)
  unfold transitionSubstituted transitionTransported
  apply Finset.sum_le_sum
  intro d hd
  apply Finset.sum_le_sum
  intro d' hd'
  by_cases hdp : 0 < d
  · simp only [dif_pos hdp]
    by_cases hd'p : 0 < d'
    · simp only [dif_pos hd'p]
      by_cases hbase :
          q.theta ^ q.k ≤ (d : ℝ) ∧ Close q.theta ⟨d, hdp⟩ ⟨d', hd'p⟩
      · simp only [if_pos hbase]
        have hcoeff := nonnegative_outer_coefficient q.toWeightParameters d
        have hkernel := high_transition_kernel_nonnegative q x hx0 d d'
        have hweight := W.w3_dom_w2 q.toWeightParameters (d * d')
          (Nat.mul_pos hdp hd'p)
        calc
          (roughIndicator d q.sigma : ℝ) *
                q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
              ((Real.log q.sigma).rpow (-1 / 2) *
                w2Weight q.toWeightParameters (d * d') *
                  ∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                    if q.sigma ≤ zValue x m d d' then
                      (safeLog m).rpow (-1 / 2) * zValue x m d d' *
                        (safeLog (zValue x m d d')).rpow (-1 / 2)
                    else 0) =
              ((roughIndicator d q.sigma : ℝ) *
                q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ)) *
                (w2Weight q.toWeightParameters (d * d') *
                  ((Real.log q.sigma).rpow (-1 / 2) *
                    ∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                      if q.sigma ≤ zValue x m d d' then
                        (safeLog m).rpow (-1 / 2) * zValue x m d d' *
                          (safeLog (zValue x m d d')).rpow (-1 / 2)
                      else 0)) := by ring
          _ ≤ ((roughIndicator d q.sigma : ℝ) *
                q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ)) *
                (w3Weight q.toWeightParameters (d * d') *
                  ((Real.log q.sigma).rpow (-1 / 2) *
                    ∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                      if q.sigma ≤ zValue x m d d' then
                        (safeLog m).rpow (-1 / 2) * zValue x m d d' *
                          (safeLog (zValue x m d d')).rpow (-1 / 2)
                      else 0)) := by
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hweight hkernel) hcoeff
          _ = (roughIndicator d q.sigma : ℝ) *
                q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
                w3Weight q.toWeightParameters (d * d') *
                  ((Real.log q.sigma).rpow (-1 / 2) *
                    ∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                      if q.sigma ≤ zValue x m d d' then
                        (safeLog m).rpow (-1 / 2) * zValue x m d d' *
                          (safeLog (zValue x m d d')).rpow (-1 / 2)
                      else 0) := by ring
      · simp [hbase]
    · simp [hd'p]
  · simp [hdp]

theorem p079 (h057 : P057Statement) : P079Statement := by
  intro q x hx
  classical
  have hx0 : 0 < x := by
    have htheta : 0 < q.theta := lt_of_lt_of_le (by norm_num) q.theta_ge_two
    exact lt_trans (pow_pos htheta _) hx
  unfold transitionRestricted transitionSubstituted
  apply Finset.sum_le_sum
  intro d hd
  apply Finset.sum_le_sum
  intro d' hd'
  by_cases hdp : 0 < d
  · simp only [dif_pos hdp]
    by_cases hd'p : 0 < d'
    · simp only [dif_pos hd'p]
      by_cases hbase :
          q.theta ^ q.k ≤ (d : ℝ) ∧ Close q.theta ⟨d, hdp⟩ ⟨d', hd'p⟩
      · simp only [if_pos hbase]
        apply mul_le_mul_of_nonneg_left _
          (nonnegative_outer_coefficient q.toWeightParameters d)
        rw [mul_sum]
        apply Finset.sum_le_sum
        intro m hm
        by_cases hlow : zValue x m d d' < q.sigma
        · simp only [if_pos hlow]
          have hmpos : 0 < m := (Finset.mem_filter.mp hm).2.1
          have hzpos : 0 < zValue x m d d' := by
            unfold zValue
            exact div_pos hx0 (by positivity)
          have hterminal := h057 q.toWeightParameters
            ⟨d * d', Nat.mul_pos hdp hd'p⟩ (zValue x m d d') hzpos hlow
          calc
            (safeLog m).rpow (-1 / 2) *
                shiftedMean q.toWeightParameters (zValue x m d d')
                  ⟨d * d', Nat.mul_pos hdp hd'p⟩ ≤
              (safeLog m).rpow (-1 / 2) * w1Weight (d * d') :=
                mul_le_mul_of_nonneg_left hterminal
                  (Real.rpow_nonneg
                    (le_trans (by norm_num)
                      (le_max_left 1 (Real.log (m : ℝ)))) _)
            _ = w1Weight (d * d') * (safeLog m).rpow (-1 / 2) := by ring
        · simp [hlow]
      · simp [hbase]
    · simp [hd'p]
  · simp [hdp]

theorem p080 (W : CommonWeightWitnesses) : P080Statement := by
  intro q x hx
  classical
  unfold transitionSubstituted transitionTransported
  apply Finset.sum_le_sum
  intro d hd
  apply Finset.sum_le_sum
  intro d' hd'
  by_cases hdp : 0 < d
  · simp only [dif_pos hdp]
    by_cases hd'p : 0 < d'
    · simp only [dif_pos hd'p]
      by_cases hbase :
          q.theta ^ q.k ≤ (d : ℝ) ∧ Close q.theta ⟨d, hdp⟩ ⟨d', hd'p⟩
      · simp only [if_pos hbase]
        have hcoeff := nonnegative_outer_coefficient q.toWeightParameters d
        have hkernel := low_transition_kernel_nonnegative q x d d'
        have hweight := W.w3_dom_w1 q.toWeightParameters (d * d')
          (Nat.mul_pos hdp hd'p)
        calc
          (roughIndicator d q.sigma : ℝ) *
                q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
              (w1Weight (d * d') *
                ∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                  if zValue x m d d' < q.sigma then
                    (safeLog m).rpow (-1 / 2)
                  else 0) =
              ((roughIndicator d q.sigma : ℝ) *
                q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ)) *
                (w1Weight (d * d') *
                  ∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                    if zValue x m d d' < q.sigma then
                      (safeLog m).rpow (-1 / 2)
                    else 0) := by ring
          _ ≤ ((roughIndicator d q.sigma : ℝ) *
                q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ)) *
                (w3Weight q.toWeightParameters (d * d') *
                  ∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                    if zValue x m d d' < q.sigma then
                      (safeLog m).rpow (-1 / 2)
                    else 0) := by
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hweight hkernel) hcoeff
          _ = (roughIndicator d q.sigma : ℝ) *
                q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
                w3Weight q.toWeightParameters (d * d') *
                  (∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                    if zValue x m d d' < q.sigma then
                      (safeLog m).rpow (-1 / 2)
                    else 0) := by ring
      · simp [hbase]
    · simp [hd'p]
  · simp [hdp]

theorem p081 : P081Statement := by
  intro theta htheta
  have hlog : 0 < Real.log theta := Real.log_pos (by linarith)
  let comparison : PositiveComparison :=
    { lower := Real.log theta
      upper := 2 * Real.log theta
      lower_pos := hlog
      upper_pos := by positivity }
  refine ⟨{
    comparison := comparison
    strict_log_bounds := ?_
    asymptotic_bounds := ?_ }⟩
  · intro q hq
    have hthetaq : 0 < q.theta := by linarith [q.theta_ge_two]
    have hsigma : 0 < q.sigma :=
      lt_trans (pow_pos hthetaq q.k) q.sigma_gt_bin
    have hlo := Real.strictMonoOn_log (pow_pos hthetaq q.k) hsigma q.sigma_gt_bin
    have hhi := Real.strictMonoOn_log hsigma (pow_pos hthetaq (q.k + 1))
      q.sigma_lt_next_bin
    simpa [Real.log_pow] using And.intro hlo hhi
  · intro q hq
    have hthetaq : 0 < q.theta := by linarith [q.theta_ge_two]
    have hsigma : 0 < q.sigma :=
      lt_trans (pow_pos hthetaq q.k) q.sigma_gt_bin
    have hlo := Real.strictMonoOn_log (pow_pos hthetaq q.k) hsigma q.sigma_gt_bin
    have hhi := Real.strictMonoOn_log hsigma (pow_pos hthetaq (q.k + 1))
      q.sigma_lt_next_bin
    rw [Real.log_pow] at hlo hhi
    change Real.log theta * q.k ≤ Real.log q.sigma ∧
      Real.log q.sigma ≤ (2 * Real.log theta) * q.k
    constructor
    · rw [← hq]
      simpa [mul_comm] using hlo.le
    · rw [← hq]
      have hk : (1 : ℝ) ≤ q.k := by exact_mod_cast q.k_pos
      have hlogq : 0 ≤ Real.log q.theta := (Real.log_pos (by linarith)).le
      norm_num at hhi ⊢
      nlinarith

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
  have hr := Real.rpow_le_rpow_of_nonpos (div_pos ha hR) hdiv
    (by norm_num : (-1 / 2 : ℝ) ≤ 0)
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

lemma theta_zpow (theta : ℝ) (htheta : 0 < theta) (k : ℕ) :
    theta ^ (1 - (2 : ℤ) * k) = theta / theta ^ (2 * k) := by
  have hne : theta ≠ 0 := ne_of_gt htheta
  rw [zpow_sub₀ hne, zpow_one]
  congr 1

lemma transition_window_ratio (q : TransitionParameters) (x : ℝ)
    {d d' : ℕ} (hd : 0 < d) (hd' : 0 < d')
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
    have hlR : q.theta ^ (2 * q.k - 1) < ((d * d' : ℕ) : ℝ) := by
      simpa using hp.product_lower
    have hsplit : q.theta ^ (2 * q.k) =
        q.theta ^ (2 * q.k - 1) * q.theta := by
      have hk := q.k_pos
      calc
        q.theta ^ (2 * q.k) = q.theta ^ ((2 * q.k - 1) + 1) := by
          congr 1
          omega
        _ = q.theta ^ (2 * q.k - 1) * q.theta := by rw [pow_add, pow_one]
    have hl' : q.theta ^ (2 * q.k) < ((d * d' : ℕ) : ℝ) * q.theta := by
      rw [hsplit]
      nlinarith [mul_pos (sub_pos.mpr hlR) ht]
    field_simp [ne_of_gt hpow]
    nlinarith [q.theta_ge_two]
  · apply (le_div_iff₀ hD).2
    have hu' : (d * d' : ℕ) < q.theta ^ (2 * q.k) * q.theta ^ 3 := by
      simpa [pow_add] using hp.product_upper
    field_simp [ne_of_gt hpow, ne_of_gt ht]
    nlinarith [q.theta_ge_two]

lemma transition_endpoint_neg_half (q : TransitionParameters)
    (x M : ℝ) (hx : 0 < x)
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
  have hscale := safeLog_scale (2 * X) (q.theta ^ 4)
    (mul_pos (by norm_num) hX) hc
  have hmono : safeLog (2 * X / q.theta ^ 4) ≤ safeLog (2 * M) := by
    apply safeLog_mono
    · positivity
    · dsimp [X] at hM ⊢
      ring_nf at hM ⊢
      nlinarith
  have hres : (safeLog (2 * M)).rpow (-1 / 2) ≤
      R.rpow (1 / 2) * (safeLog (2 * X)).rpow (-1 / 2) := by
    apply neg_half_transport (safeLog_pos _) (safeLog_pos _) hR
    exact hscale.trans (mul_le_mul_of_nonneg_left hmono hR.le)
  simpa [X, R, mul_assoc] using hres

lemma restricted_transition_half_sum_le
    (q : TransitionParameters) (x : ℝ) {d d' : ℕ} :
    (∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
      if zValue x m d d' < q.sigma then (safeLog m).rpow (-1 / 2) else 0) ≤
      safeLogHalfSum (x / (d * d' : ℕ)) := by
  unfold safeLogHalfSum
  apply Finset.sum_le_sum
  intro m hm
  split
  · exact le_rfl
  · exact Real.rpow_nonneg (safeLog_pos _).le _

theorem p083 (h053 : P053Statement) (h054 : P054Statement)
    (W : CommonWeightWitnesses) : P083Statement := by
  obtain ⟨Cps, hCps, hps⟩ := h053
  intro theta htheta
  let R : ℝ := 1 + Real.log (theta ^ 4)
  let CtrL : ℝ := Cps * theta * R.rpow (1 / 2)
  have ht : 0 < theta := lt_of_lt_of_le (by norm_num) htheta
  have hR : 0 < R := by
    dsimp [R]
    nlinarith [Real.log_nonneg
      (one_le_pow₀ (by linarith : 1 ≤ theta) : 1 ≤ theta ^ 4)]
  have hCtrL : 0 < CtrL :=
    mul_pos (mul_pos hCps ht) (Real.rpow_pos_of_pos hR _)
  refine ⟨CtrL, hCtrL, ?_⟩
  intro q hq x hx
  subst theta
  have hxpos : 0 < x := by
    have := pow_pos (lt_of_lt_of_le (by norm_num) q.theta_ge_two)
      (2 * q.k - 1)
    linarith
  classical
  unfold transitionTransported transitionOuter outerPairSum
  simp only
  rw [show CtrL * (x / q.theta ^ (2 * q.k)) *
        (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow (-1 / 2) *
        (∑ d ∈ positiveNatsBelow (q.theta ^ (q.k + 1)),
          ∑ d' ∈ positiveNatsBelow (q.theta ^ (q.k + 2)),
            if hd : 0 < d then if hd' : 0 < d' then
              if q.theta ^ q.k ≤ (d : ℝ) ∧ Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩ then
                (roughIndicator d q.sigma : ℝ) *
                  q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
                  w3Weight q.toWeightParameters (d * d')
              else 0 else 0 else 0) =
      (CtrL * (x / q.theta ^ (2 * q.k)) *
        (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow (-1 / 2)) *
        (∑ d ∈ positiveNatsBelow (q.theta ^ (q.k + 1)),
          ∑ d' ∈ positiveNatsBelow (q.theta ^ (q.k + 2)),
            if hd : 0 < d then if hd' : 0 < d' then
              if q.theta ^ q.k ≤ (d : ℝ) ∧ Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩ then
                (roughIndicator d q.sigma : ℝ) *
                  q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
                  w3Weight q.toWeightParameters (d * d')
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
        have hratio := transition_window_ratio q x hd hd' hp hxpos
        have hsum := restricted_transition_half_sum_le q x (d := d) (d' := d')
        have hpsM := hps M hM
        have hend := transition_endpoint_neg_half q x M hxpos hratio.2
        have hinner :
            (∑ m ∈ positiveNatsBelow M,
              if zValue x m d d' < q.sigma then
                (safeLog m).rpow (-1 / 2) else 0) ≤
              Cps * R.rpow (1 / 2) * X *
                (safeLog (2 * X)).rpow (-1 / 2) := by
          calc
            _ ≤ safeLogHalfSum M := hsum
            _ ≤ Cps * M * (safeLog (2 * M)).rpow (-1 / 2) := hpsM
            _ ≤ Cps * X * (safeLog (2 * M)).rpow (-1 / 2) := by
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
                (mul_nonneg hCps.le (by positivity))
            _ = Cps * R.rpow (1 / 2) * X *
                (safeLog (2 * X)).rpow (-1 / 2) := by ring
        have hcoeff : 0 ≤ (roughIndicator d q.sigma : ℝ) *
            q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
              w3Weight q.toWeightParameters D :=
          mul_nonneg
            (nonnegative_outer_coefficient q.toWeightParameters d)
            ((W.weight_type q.toWeightParameters .w3).nonnegative_multiplicative.nonnegative
              D hD)
        dsimp [D, M, X] at hinner ⊢
        calc
          (roughIndicator d q.sigma : ℝ) *
                q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
                w3Weight q.toWeightParameters (d * d') *
                (∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                  if zValue x m d d' < q.sigma then
                    (safeLog m).rpow (-1 / 2) else 0) ≤
              ((roughIndicator d q.sigma : ℝ) *
                q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
                w3Weight q.toWeightParameters (d * d')) *
                (Cps * R.rpow (1 / 2) *
                  (x * q.theta ^ (1 - (2 : ℤ) * q.k)) *
                  (safeLog (2 * (x * q.theta ^
                    (1 - (2 : ℤ) * q.k)))).rpow (-1 / 2)) := by
            exact mul_le_mul_of_nonneg_left hinner hcoeff
          _ = (CtrL * (x / q.theta ^ (2 * q.k)) *
                (safeLog (2 * x * q.theta ^
                  (1 - (2 : ℤ) * q.k))).rpow (-1 / 2)) *
              ((roughIndicator d q.sigma : ℝ) *
                q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
                w3Weight q.toWeightParameters (d * d')) := by
            have hXeq : x * q.theta ^ (1 - (2 : ℤ) * q.k) =
                q.theta * (x / q.theta ^ (2 * q.k)) := by
              rw [theta_zpow q.theta
                (lt_of_lt_of_le (by norm_num) q.theta_ge_two) q.k]
              ring
            have hsarg : 2 * (x * q.theta ^ (1 - (2 : ℤ) * q.k)) =
                2 * x * q.theta ^ (1 - (2 : ℤ) * q.k) := by ring
            rw [hsarg, hXeq]
            dsimp [CtrL]
            ring
      · simp [hd, hd', houter]
    · simp [hd']
  · simp [hd]

lemma modifier_prime_power_below_sigma
    (q : TransitionParameters) {p j : ℕ} (hp : p.Prime)
    (hbelow : (p : ℝ) < q.sigma) (hj : 0 < j) :
    modifierWeight q.toWeightParameters (p ^ j) = 0 := by
  have hnot : ¬ IsRough (p ^ j) q.sigma := by
    intro hrough
    exact (not_le_of_gt hbelow)
      (hrough p hp (dvd_pow_self p (Nat.ne_of_gt hj)))
  simp [modifierWeight, pow_pos hp.pos j, roughIndicator, hnot]

lemma localEulerSeries_w1_eq_one_below
    (W : CommonWeightWitnesses) (q : TransitionParameters) {p : ℕ}
    (hp : p.Prime) (hbelow : (p : ℝ) < q.sigma) :
    localEulerSeries w1Weight (modifierWeight q.toWeightParameters) p = 1 := by
  unfold localEulerSeries
  rw [tsum_eq_single 0]
  · have hw := (W.weight_type q.toWeightParameters .w1).normalized
    have hb := (W.modifier q.toWeightParameters).normalized
    change w1Weight 1 * modifierWeight q.toWeightParameters 1 / 1 = 1
    rw [show w1Weight 1 = 1 by simpa [selectedWeight] using hw, hb]
    norm_num
  · intro j hj
    rw [modifier_prime_power_below_sigma q hp hbelow (Nat.pos_of_ne_zero hj)]
    simp

lemma localEulerSeries_w3_eq_one_below
    (W : CommonWeightWitnesses) (q : TransitionParameters) {p : ℕ}
    (hp : p.Prime) (hbelow : (p : ℝ) < q.sigma) :
    localEulerSeries (w3Weight q.toWeightParameters)
        (modifierWeight q.toWeightParameters) p = 1 := by
  unfold localEulerSeries
  rw [tsum_eq_single 0]
  · have hw := (W.weight_type q.toWeightParameters .w3).normalized
    have hb := (W.modifier q.toWeightParameters).normalized
    change w3Weight q.toWeightParameters 1 *
      modifierWeight q.toWeightParameters 1 / 1 = 1
    rw [show w3Weight q.toWeightParameters 1 = 1 by
      simpa [selectedWeight] using hw, hb]
    norm_num
  · intro j hj
    rw [modifier_prime_power_below_sigma q hp hbelow (Nat.pos_of_ne_zero hj)]
    simp

@[expose] def transitionHighEulerW3 (q : TransitionParameters) (p : ℕ) : ℝ :=
  if q.sigma ≤ (p : ℝ) then
    localEulerFactor (w3Weight q.toWeightParameters)
      (modifierWeight q.toWeightParameters) p
  else 1 + 1 / (2 * (p : ℝ))

theorem transitionEulerComparisonW3
    (h008 : P008Statement.{0}) (W : CommonWeightWitnesses)
    (h051 : P051HStatement) :
    Nonempty (P008Output transitionHighCoefficient transitionHighEulerW3) := by
  let eta : ℝ := min W.cStar 1
  let Cerr : ℝ := W.CStar + 2 * W.LambdaStar
  have heta : 0 < eta := by simp [eta, W.cStar_pos]
  have hCerr : 0 < Cerr := by
    dsimp [Cerr]
    nlinarith [W.CStar_pos, W.LambdaStar_pos]
  have hfloor : ∀ q : TransitionParameters, ∀ p : ℕ, p.Prime →
      1 ≤ transitionHighEulerW3 q p := by
    intro q p hp
    unfold transitionHighEulerW3
    split_ifs with habove
    · exact Erdos448.Stage7.Shared.localEulerFactor_ge_one hp
        (W.weight_type q.toWeightParameters .w3).nonnegative_multiplicative
        (W.weight_type q.toWeightParameters .w3).normalized
        (W.modifier q.toWeightParameters)
        (h051 W q.toWeightParameters .w3
          (modifierWeight q.toWeightParameters) (W.modifier q.toWeightParameters)
          p hp).domain.summable
    · have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have : 0 ≤ 1 / (2 * (p : ℝ)) := by positivity
      linarith
  have herr : ∀ q : TransitionParameters, ∀ p : ℕ, p.Prime → (2 : ℝ) ≤ p →
      |transitionHighEulerW3 q p - (1 + transitionHighCoefficient q / p)| ≤
        Cerr * (p : ℝ).rpow (-1 - eta) := by
    intro q p hp hp2
    unfold transitionHighEulerW3 transitionHighCoefficient
    split_ifs with habove
    · have hb := modifier_prime_above_sigma q hp habove
      have hs := (h051 W q.toWeightParameters .w3
        (modifierWeight q.toWeightParameters) (W.modifier q.toWeightParameters)
        p hp).replaced_main_term
      simpa [hb, eta, Cerr, selectedWeight, div_eq_mul_inv, mul_comm] using hs
    · have heq : 1 / (2 * (p : ℝ)) = (1 / 2 : ℝ) / p := by ring
      rw [heq, sub_self, abs_zero]
      exact mul_nonneg hCerr.le (Real.rpow_nonneg (by positivity) _)
  exact h008 TransitionParameters ⟨exampleTransitionParameters⟩
    (1 / 2) (1 / 2) (by norm_num) (by norm_num) eta Cerr heta hCerr
    2 1 1 (by norm_num) (by norm_num) (by norm_num)
    transitionHighCoefficient (by intro q; simp [transitionHighCoefficient])
    transitionHighEulerW3 hfloor herr (by
      intro q p hp hp2 hplt
      exfalso
      have hp2R : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      linarith)

lemma eulerProduct_w1_eq_high
    (W : CommonWeightWitnesses) (q : TransitionParameters) (z : ℝ) :
    (∏ p ∈ strictPrimeRange z,
      localEulerSeries w1Weight (modifierWeight q.toWeightParameters) p) =
      primeIntervalProduct (transitionHighEuler q) q.sigma z := by
  unfold primeIntervalProduct
  apply Finset.prod_congr rfl
  intro p hpMem
  have hp : p.Prime := (Finset.mem_filter.mp hpMem).2
  by_cases hs : q.sigma ≤ (p : ℝ)
  · simp [transitionHighEuler, hs, localEulerSeries, localEulerFactor]
  · rw [localEulerSeries_w1_eq_one_below W q hp (lt_of_not_ge hs)]
    simp [hs]

lemma eulerProduct_w3_eq_high
    (W : CommonWeightWitnesses) (q : TransitionParameters) (z : ℝ) :
    (∏ p ∈ strictPrimeRange z,
      localEulerSeries (w3Weight q.toWeightParameters)
        (modifierWeight q.toWeightParameters) p) =
      primeIntervalProduct (transitionHighEulerW3 q) q.sigma z := by
  unfold primeIntervalProduct
  apply Finset.prod_congr rfl
  intro p hpMem
  have hp : p.Prime := (Finset.mem_filter.mp hpMem).2
  by_cases hs : q.sigma ≤ (p : ℝ)
  · simp [transitionHighEulerW3, hs, localEulerSeries, localEulerFactor]
  · rw [localEulerSeries_w3_eq_one_below W q hp (lt_of_not_ge hs)]
    simp [hs]

lemma shiftedGeometricBounds_w3_modifier
    (W : CommonWeightWitnesses) (q : WeightParameters) :
    ShiftedGeometricBounds (w3Weight q) (modifierWeight q)
      (fun _ => W.LambdaStar) 1 := by
  intro p hp i j
  have hmod := (W.modifier q).prime_power_bounds p hp j
  have hone : 1 ≤ W.LambdaStar := by
    have hrpow : 0 < (2 : ℝ).rpow (-W.cStar) := Real.rpow_pos_of_pos (by norm_num) _
    nlinarith [W.LambdaStar_lower, W.CStar_pos]
  by_cases hij : i + j = 0
  · have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst i
    subst j
    simp only [Nat.zero_add, pow_zero, one_pow, mul_one]
    rw [show w3Weight q 1 = 1 by
      simpa [selectedWeight] using (W.weight_type q .w3).normalized,
      (W.modifier q).normalized]
    exact ⟨by norm_num, by simpa using hone⟩
  · have hw := (W.weight_type q .w3).prime_power_bounds p hp (i + j)
      (Nat.one_le_iff_ne_zero.mpr hij)
    constructor
    · exact mul_nonneg hw.1 hmod.1
    · simpa [selectedWeight] using mul_le_mul hw.2 hmod.2 hmod.1 (by linarith)

lemma shiftedPrimeProduct_le_w4
    (chain : WeightChainSpec) (W : CommonWeightWitnesses)
    (q : WeightParameters) (K : PosNat) (X : ℝ) :
    shiftedPrimeProduct (w3Weight q) (modifierWeight q) K X ≤ w4Weight q K.1 := by
  classical
  unfold shiftedPrimeProduct w4Weight maxShift multiplicativeExtension
  simp only [if_neg (Nat.ne_of_gt K.2)]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro p hpMem
    have hp := Nat.prime_of_mem_primeFactors hpMem
    have he : 1 ≤ K.1.factorization p :=
      hp.factorization_pos_of_dvd (Nat.ne_of_gt K.2)
        (Nat.dvd_of_mem_primeFactors hpMem)
    by_cases hpx : (p : ℝ) < X
    · simp only [if_pos hpx, if_neg (not_le_of_gt hpx), mul_one]
      unfold exactShiftFactor
      have hshift : localShift (w3Weight q) (modifierWeight q) p
          (K.1.factorization p) =
          shift (w3Weight q) (modifierWeight q) (p ^ K.1.factorization p) := by
        symm
        exact chain.w4_shift q |>.shift_prime_power p hp _ he
      rw [hshift]
      exact chain.w4_shift q |>.shift_nonnegative_multiplicative.nonnegative _
        (pow_pos hp.pos _)
    · simp only [if_neg hpx, if_pos (le_of_not_gt hpx), one_mul]
      exact (W.weight_type q .w3).nonnegative_multiplicative.nonnegative _
        (pow_pos hp.pos _)
  · intro p hpMem
    by_cases hpx : (p : ℝ) < X
    · simp only [if_pos hpx, if_neg (not_le_of_gt hpx), mul_one]
      exact le_max_left _ _
    · simp only [if_neg hpx, if_pos (le_of_not_gt hpx), one_mul]
      exact le_max_right _ _

lemma log_ratio_half_identity {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (b / a).rpow (1 / 2) / b =
      a.rpow (-1 / 2) * b.rpow (-1 / 2) := by
  change (b / a) ^ (1 / 2 : ℝ) / b =
    a ^ (-1 / 2 : ℝ) * b ^ (-1 / 2 : ℝ)
  rw [Real.div_rpow hb.le ha.le]
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring,
    Real.rpow_neg ha.le, Real.rpow_neg hb.le]
  have hbpow : b.rpow (1 / 2) * b.rpow (1 / 2) = b := by
    change b ^ (1 / 2 : ℝ) * b ^ (1 / 2 : ℝ) = b
    rw [← Real.rpow_add hb]
    rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by ring]
    exact Real.rpow_one b
  field_simp [ne_of_gt (Real.rpow_pos_of_pos ha _),
    ne_of_gt (Real.rpow_pos_of_pos hb _)]
  rw [pow_two]
  exact hbpow

lemma rpow_neg_half_sq {a : ℝ} (ha : 0 < a) :
    a.rpow (-1 / 2) * a.rpow (-1 / 2) = a.rpow (-1) := by
  change a ^ (-1 / 2 : ℝ) * a ^ (-1 / 2 : ℝ) = a ^ (-1 : ℝ)
  rw [← Real.rpow_add ha]
  norm_num

lemma safeLog_le_log_loss {theta z : ℝ}
    (htheta : 2 ≤ theta) (htz : theta ≤ z) :
    safeLog z ≤ (1 + 1 / Real.log theta) * Real.log z := by
  have hlt : 0 < Real.log theta := Real.log_pos (by linarith)
  have hzpos : 0 < z := lt_of_lt_of_le (by linarith : 0 < theta) htz
  have hlz : Real.log theta ≤ Real.log z :=
    Real.strictMonoOn_log.monotoneOn (show 0 < theta by linarith) hzpos htz
  have hlogz : 0 < Real.log z := lt_of_lt_of_le hlt hlz
  have hratio : 1 ≤ Real.log z / Real.log theta :=
    (le_div_iff₀ hlt).2 (by simpa using hlz)
  unfold safeLog
  apply max_le
  · rw [show (1 + 1 / Real.log theta) * Real.log z =
        Real.log z + Real.log z / Real.log theta by ring]
    nlinarith
  · have hextra : 0 ≤ (Real.log theta)⁻¹ * Real.log z := by positivity
    rw [one_div]
    nlinarith

theorem p077 (h005 : P005Statement) (h008 : P008Statement.{0})
    (chain : WeightChainSpec) (W : CommonWeightWitnesses)
    (h051 : P051HStatement) : P077Statement := by
  obtain ⟨mean⟩ := h005 (fun _ => W.LambdaStar) (by intro i; exact W.LambdaStar_pos.le)
    1 (by norm_num) (by norm_num)
  obtain ⟨cmp⟩ := transitionEulerComparisons h008 W h051
  intro theta htheta
  let R := 1 + 1 / Real.log theta
  let B := max 1 cmp.high.comparison.upper
  let CtrHigh := mean.constant * B * R.rpow (1 / 2)
  have hR : 0 < R := by
    dsimp [R]
    have := Real.log_pos (by linarith : 1 < theta)
    positivity
  have hCtr : 0 < CtrHigh :=
    mul_pos (mul_pos mean.constant_pos (lt_of_lt_of_le (by norm_num) (le_max_left 1 _)))
      (Real.rpow_pos_of_pos hR _)
  refine ⟨CtrHigh, hCtr, ?_⟩
  intro q hq x hx
  subst theta
  classical
  unfold transitionRestricted transitionSubstituted
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hdSet
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d' hd'Set
  by_cases hd : 0 < d
  · simp only [dif_pos hd]
    by_cases hd' : 0 < d'
    · simp only [dif_pos hd']
      by_cases houter : q.theta ^ q.k ≤ (d : ℝ) ∧
          Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩
      · simp only [if_pos houter]
        rw [show CtrHigh *
              ((roughIndicator d q.sigma : ℝ) *
                q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
                ((Real.log q.sigma).rpow (-1 / 2) *
                  w2Weight q.toWeightParameters (d * d') *
                  ∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                    if q.sigma ≤ zValue x m d d' then
                      (safeLog m).rpow (-1 / 2) * zValue x m d d' *
                        (safeLog (zValue x m d d')).rpow (-1 / 2) else 0)) =
            ((roughIndicator d q.sigma : ℝ) *
              q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ)) *
              (CtrHigh * ((Real.log q.sigma).rpow (-1 / 2) *
                w2Weight q.toWeightParameters (d * d') *
                ∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                  if q.sigma ≤ zValue x m d d' then
                    (safeLog m).rpow (-1 / 2) * zValue x m d d' *
                      (safeLog (zValue x m d d')).rpow (-1 / 2) else 0)) by ring]
        apply mul_le_mul_of_nonneg_left _
          (nonnegative_outer_coefficient q.toWeightParameters d)
        rw [Finset.mul_sum]
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro m hm
        by_cases hz : q.sigma ≤ zValue x m d d'
        · simp only [if_pos hz]
          let K : PosNat := ⟨d * d', Nat.mul_pos hd hd'⟩
          let z := zValue x m d d'
          have hz2 : 2 ≤ z := le_trans q.theta_ge_two (le_trans q.sigma_ge_theta hz)
          have hlogS : 0 < Real.log q.sigma := Real.log_pos (by linarith [q.sigma_ge_theta])
          have hlogZ : 0 < Real.log z := Real.log_pos (by linarith)
          have hmean0 := mean.bound w1Weight (modifierWeight q.toWeightParameters)
            (W.weight_type q.toWeightParameters .w1).nonnegative_multiplicative
            (W.modifier q.toWeightParameters).nonnegative_multiplicative
            (shiftedGeometricBounds_w1_modifier W q.toWeightParameters) K z hz2
          have heuler : primeIntervalProduct (transitionHighEuler q) q.sigma z ≤
              B * (Real.log z / Real.log q.sigma).rpow (1 / 2) := by
            by_cases hsigz : q.sigma < z
            · exact (cmp.high.family_bounds q q.sigma z
                (le_trans q.theta_ge_two q.sigma_ge_theta) hsigz).2.trans
                  (mul_le_mul_of_nonneg_right (le_max_right 1 _)
                    (Real.rpow_nonneg (div_nonneg hlogZ.le hlogS.le) _))
            · have heq : z = q.sigma := le_antisymm (le_of_not_gt hsigz) hz
              rw [heq, cmp.high.empty_branch q q.sigma q.sigma
                (le_trans q.theta_ge_two q.sigma_ge_theta)
                (le_trans q.theta_ge_two q.sigma_ge_theta) le_rfl]
              rw [div_self (ne_of_gt hlogS)]
              norm_num
              exact le_max_left 1 _
          rw [eulerProduct_w1_eq_high W q z] at hmean0
          have hprod := shiftedPrimeProduct_le_w2 chain W q.toWeightParameters K z
          have hprime : 0 ≤ primeIntervalProduct (transitionHighEuler q) q.sigma z := by
            unfold primeIntervalProduct
            apply Finset.prod_nonneg
            intro p hpMem
            split_ifs with hpAbove
            · unfold transitionHighEuler
              simp only [hpAbove, ↓reduceIte]
              exact le_trans (by norm_num) (Erdos448.Stage7.Shared.localEulerFactor_ge_one
                (Finset.mem_filter.mp hpMem).2
                (W.weight_type q.toWeightParameters .w1).nonnegative_multiplicative
                (W.weight_type q.toWeightParameters .w1).normalized
                (W.modifier q.toWeightParameters)
                (h051 W q.toWeightParameters .w1 (modifierWeight q.toWeightParameters)
                  (W.modifier q.toWeightParameters) p (Finset.mem_filter.mp hpMem).2).domain.summable)
            · norm_num
          have hw2nonneg : 0 ≤ w2Weight q.toWeightParameters K.1 :=
            (W.weight_type q.toWeightParameters .w2).nonnegative_multiplicative.nonnegative
              K.1 K.2
          have hmeanNonneg : 0 ≤ mean.constant := mean.constant_pos.le
          have heuler' : primeIntervalProduct (transitionHighEuler q) q.sigma z ≤
              B *
                (Real.log z / Real.log q.sigma).rpow (1 / 2) := by
            exact heuler
          have hmean : Erdos448.Stage4.shiftedMean q.toWeightParameters z K ≤
              mean.constant * B *
                w2Weight q.toWeightParameters K.1 * z *
                (Real.log q.sigma).rpow (-1 / 2) *
                (Real.log z).rpow (-1 / 2) := by
            rw [show shiftedMean q.toWeightParameters z K =
                Erdos448.Stage4.Contracts.shiftedMean w1Weight
                  (modifierWeight q.toWeightParameters) K z by
              unfold Erdos448.Stage4.shiftedMean Erdos448.Stage4.Contracts.shiftedMean
              apply Finset.sum_congr rfl
              intro n hn
              rw [Nat.mul_comm n K.1]
              ring]
            calc
              _ ≤ mean.constant * shiftedPrimeProduct w1Weight
                    (modifierWeight q.toWeightParameters) K z * (z / Real.log z) *
                    primeIntervalProduct (transitionHighEuler q) q.sigma z := hmean0
              _ ≤ mean.constant * w2Weight q.toWeightParameters K.1 *
                    (z / Real.log z) *
                    (B *
                      (Real.log z / Real.log q.sigma).rpow (1 / 2)) := by
                    calc
                      _ ≤ mean.constant * w2Weight q.toWeightParameters K.1 *
                          (z / Real.log z) *
                          primeIntervalProduct (transitionHighEuler q) q.sigma z := by
                            gcongr
                      _ ≤ _ := mul_le_mul_of_nonneg_left heuler'
                        (mul_nonneg
                          (mul_nonneg mean.constant_pos.le hw2nonneg)
                          (div_nonneg (by positivity) hlogZ.le))
              _ = (mean.constant * B * w2Weight q.toWeightParameters K.1 * z) *
                    ((Real.log z / Real.log q.sigma).rpow (1 / 2) /
                      Real.log z) := by ring
              _ = _ := by
                rw [log_ratio_half_identity hlogS hlogZ]
                ring
          have hloss := neg_half_transport (safeLog_pos z) hlogZ hR
            (safeLog_le_log_loss q.theta_ge_two (le_trans q.sigma_ge_theta hz))
          have hmean' : Erdos448.Stage4.shiftedMean q.toWeightParameters z K ≤
              CtrHigh * w2Weight q.toWeightParameters K.1 * z *
                (Real.log q.sigma).rpow (-1 / 2) *
                (safeLog z).rpow (-1 / 2) := by
            calc
              _ ≤ _ := hmean
              _ ≤ (mean.constant * B * w2Weight q.toWeightParameters K.1 * z *
                    (Real.log q.sigma).rpow (-1 / 2)) *
                    (R.rpow (1 / 2) * (safeLog z).rpow (-1 / 2)) := by
                      exact mul_le_mul_of_nonneg_left hloss
                        (mul_nonneg
                          (mul_nonneg
                            (mul_nonneg
                              (mul_nonneg mean.constant_pos.le
                                (le_trans (by norm_num : (0 : ℝ) ≤ 1)
                                  (le_max_left 1 cmp.high.comparison.upper)))
                              hw2nonneg) (by positivity))
                          (Real.rpow_nonneg hlogS.le _))
              _ = _ := by dsimp [CtrHigh]; ring
          dsimp [K, z] at hmean'
          calc
            (safeLog m).rpow (-1 / 2) *
                shiftedMean q.toWeightParameters (zValue x m d d')
                  ⟨d * d', Nat.mul_pos hd hd'⟩ ≤
              (safeLog m).rpow (-1 / 2) *
                (CtrHigh * w2Weight q.toWeightParameters (d * d') *
                  zValue x m d d' * (Real.log q.sigma).rpow (-1 / 2) *
                  (safeLog (zValue x m d d')).rpow (-1 / 2)) :=
                mul_le_mul_of_nonneg_left hmean'
                  (Real.rpow_nonneg (safeLog_pos m).le _)
            _ = CtrHigh * ((Real.log q.sigma).rpow (-1 / 2) *
                w2Weight q.toWeightParameters (d * d') *
                ((safeLog m).rpow (-1 / 2) * zValue x m d d' *
                  (safeLog (zValue x m d d')).rpow (-1 / 2))) := by ring
        · simp [hz]
      · simp [houter]
    · simp [hd']
  · simp [hd]

theorem p082 (h054 : P054Statement) (W : CommonWeightWitnesses) : P082Statement := by
  intro theta htheta
  let CtrH : ℝ := 256 * theta
  have hCtrH : 0 < CtrH := by dsimp [CtrH]; positivity
  refine ⟨CtrH, hCtrH, ?_⟩
  intro q hq x hx
  subst theta
  classical
  rw [show CtrH * (Real.log q.sigma).rpow (-1 / 2) *
        (x / q.theta ^ (2 * q.k)) * transitionOuter q =
      (CtrH * (Real.log q.sigma).rpow (-1 / 2) *
        (x / q.theta ^ (2 * q.k))) * transitionOuter q by ring]
  unfold transitionTransported transitionOuter outerPairSum
  simp only
  rw [Finset.mul_sum]
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
        have hdUpper := (mem_positiveNatsBelow.mp hdSet).2
        have hp := h054 q.k q.k_pos q.theta (by linarith [q.theta_ge_two])
          ⟨d, hd⟩ ⟨d', hd'⟩ houter.1 hdUpper houter.2
        let M := x / (d * d' : ℕ)
        have hxpos : 0 < x := lt_trans (pow_pos (by linarith [q.theta_ge_two]) _) hx
        have hM : 0 < M := div_pos hxpos (by positivity)
        have hratio := transition_window_ratio q x hd hd' hp hxpos
        have hinner : (∑ m ∈ positiveNatsBelow M,
              if q.sigma ≤ M / m then
                (safeLog m).rpow (-1 / 2) * (M / m) *
                  (safeLog (M / m)).rpow (-1 / 2) else 0) ≤ 256 * M := by
          by_cases hM1 : 1 < M
          · have hb := Erdos448.Stage7.FoundationP068P069.Work.logBetaConvolutionBound
                hM1 (show (0 : ℝ) < 1 / 2 by norm_num) (le_rfl)
            rw [show (1 / 2 : ℝ) - 1 = -1 / 2 by ring,
              show (1 / 2 : ℝ) - 1 / 2 = 0 by ring] at hb
            have hzpow : (safeLog (2 * M)).rpow 0 = 1 := Real.rpow_zero _
            rw [hzpow] at hb
            norm_num at hb
            have hb' : (∑ m ∈ positiveNatsBelow M,
                  (safeLog m).rpow (-1 / 2) / (m : ℝ) *
                    (safeLog (M / m)).rpow (-1 / 2)) ≤ 256 := by
              simpa only [Real.rpow_eq_pow, show (-(1 / 2) : ℝ) = -1 / 2 by ring] using hb
            calc
              _ ≤ M * (∑ m ∈ positiveNatsBelow M,
                  (safeLog m).rpow (-1 / 2) / (m : ℝ) *
                    (safeLog (M / m)).rpow (-1 / 2)) := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_le_sum
                    intro m hm
                    have hmpos : (0 : ℝ) < m := by
                      exact_mod_cast (mem_positiveNatsBelow.mp hm).1
                    split_ifs
                    · ring_nf
                      rfl
                    · exact mul_nonneg hM.le
                        (mul_nonneg (div_nonneg (Real.rpow_nonneg (safeLog_pos m).le _) hmpos.le)
                          (Real.rpow_nonneg (safeLog_pos (M / m)).le _))
              _ ≤ M * 256 := mul_le_mul_of_nonneg_left hb' hM.le
              _ = 256 * M := by ring
          · have hempty : positiveNatsBelow M = ∅ := by
              apply Finset.eq_empty_iff_forall_notMem.mpr
              intro m hmMem
              have hmData := mem_positiveNatsBelow.mp hmMem
              rcases hmData with ⟨hm, hmM⟩
              have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
              linarith
            rw [hempty]
            simp only [Finset.sum_empty]
            exact mul_nonneg (by norm_num) hM.le
        have hinner' : (∑ m ∈ positiveNatsBelow M,
              if q.sigma ≤ M / m then
                (safeLog m).rpow (-1 / 2) * (M / m) *
                  (safeLog (M / m)).rpow (-1 / 2) else 0) ≤
              256 * q.theta * (x / q.theta ^ (2 * q.k)) := by
          calc
            _ ≤ 256 * M := hinner
            _ ≤ 256 * (x * q.theta ^ (1 - (2 : ℤ) * q.k)) :=
              mul_le_mul_of_nonneg_left hratio.1 (by norm_num)
            _ = 256 * q.theta * (x / q.theta ^ (2 * q.k)) := by
              rw [theta_zpow q.theta (by linarith [q.theta_ge_two]) q.k]
              ring
        have hcoeff : 0 ≤ (roughIndicator d q.sigma : ℝ) *
            q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
              w3Weight q.toWeightParameters (d * d') := by
          exact mul_nonneg (nonnegative_outer_coefficient q.toWeightParameters d)
            ((W.weight_type q.toWeightParameters .w3).nonnegative_multiplicative.nonnegative
              (d * d') (Nat.mul_pos hd hd'))
        dsimp [M] at hinner' ⊢
        have hinnerZ : (∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
              if q.sigma ≤ zValue x m d d' then
                (safeLog m).rpow (-1 / 2) * zValue x m d d' *
                  (safeLog (zValue x m d d')).rpow (-1 / 2) else 0) ≤
              256 * q.theta * (x / q.theta ^ (2 * q.k)) := by
          have hzEq : ∀ m : ℕ,
              x / (d * d' : ℕ) / (m : ℝ) = zValue x m d d' := by
            intro m
            unfold zValue
            norm_num [Nat.cast_mul]
            ring
          simpa only [hzEq, Real.rpow_eq_pow] using hinner'
        have hlognonneg : 0 ≤ (Real.log q.sigma).rpow (-1 / 2) :=
          Real.rpow_nonneg (Real.log_nonneg (by linarith [q.sigma_ge_theta])) _
        calc
          _ ≤ ((roughIndicator d q.sigma : ℝ) *
                q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
                w3Weight q.toWeightParameters (d * d')) *
              ((Real.log q.sigma).rpow (-1 / 2) *
                (256 * q.theta * (x / q.theta ^ (2 * q.k)))) := by
                  exact mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_left hinnerZ hlognonneg) hcoeff
          _ = (CtrH * (Real.log q.sigma).rpow (-1 / 2) *
                (x / q.theta ^ (2 * q.k))) *
              ((roughIndicator d q.sigma : ℝ) *
                q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
                w3Weight q.toWeightParameters (d * d')) := by
                  dsimp [CtrH]
                  ring
      · simp [hd, hd', houter]
    · simp [hd']
  · simp [hd]

lemma close_second_lower (q : TransitionParameters) {d d' : ℕ}
    (hd : 0 < d) (hd' : 0 < d') (hbin : q.theta ^ q.k ≤ (d : ℝ))
    (hclose : Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩) :
    q.theta ^ (q.k - 1) < (d' : ℝ) := by
  have ht : 0 < q.theta := by linarith [q.theta_ge_two]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hratio := hclose.2.1
  have hmul : (1 / q.theta) * (d : ℝ) < (d' : ℝ) :=
    (lt_div_iff₀ hdR).mp hratio
  have hkpos := q.k_pos
  have hk : q.k - 1 + 1 = q.k := by omega
  have hpow : q.theta ^ (q.k - 1) = q.theta ^ q.k / q.theta := by
    conv_rhs => rw [← hk, pow_succ]
    field_simp
  rw [hpow]
  have := (div_le_div_iff_of_pos_right ht).2 hbin
  exact this.trans_lt (by simpa [div_eq_mul_inv, mul_comm] using hmul)

theorem p084 (h005 : P005Statement) (h008 : P008Statement.{0})
    (h054A : P054AStatement) (chain : WeightChainSpec)
    (W : CommonWeightWitnesses) (h051 : P051HStatement) : P084Statement := by
  obtain ⟨mean⟩ := h005 (fun _ => W.LambdaStar) (by intro i; exact W.LambdaStar_pos.le)
    1 (by norm_num) (by norm_num)
  obtain ⟨cmp⟩ := transitionEulerComparisonW3 h008 W h051
  intro theta htheta
  let CtrOut := theta * mean.constant * cmp.comparison.upper
  have hCtr : 0 < CtrOut := by
    dsimp [CtrOut]
    exact mul_pos (mul_pos (by linarith) mean.constant_pos) cmp.comparison.upper_pos
  refine ⟨CtrOut, hCtr, ?_⟩
  intro q hq
  subst theta
  classical
  rw [show CtrOut * q.theta ^ q.k * (Real.log q.sigma).rpow (-1) *
        w4WindowSum q.toWeightParameters =
      (CtrOut * q.theta ^ q.k * (Real.log q.sigma).rpow (-1)) *
        w4WindowSum q.toWeightParameters by ring]
  unfold transitionOuter outerPairSum w4WindowSum
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d' hd'Set
  have hd' : 0 < d' := (mem_positiveNatsBelow.mp hd'Set).1
  by_cases hlower : q.theta ^ (q.k - 1) < (d' : ℝ)
  · simp only [hlower, if_true]
    let z := q.theta ^ (q.k + 1)
    let K : PosNat := ⟨d', hd'⟩
    let g : ArithmeticWeight := fun n => modifierWeight q.toWeightParameters n *
      w3Weight q.toWeightParameters (d' * n)
    have hg : NonnegativeWeight g := by
      intro n hn
      exact mul_nonneg
        ((W.modifier q.toWeightParameters).nonnegative_multiplicative.nonnegative n hn)
        ((W.weight_type q.toWeightParameters .w3).nonnegative_multiplicative.nonnegative
          (d' * n) (Nat.mul_pos hd' hn))
    have hsum := h054A g hg q.k q.k_pos q.theta q.theta_ge_two q.sigma
      (by linarith [q.sigma_ge_theta])
    have houterSum :
        (∑ d ∈ positiveNatsBelow z,
          if hd : 0 < d then
            if hd'' : 0 < d' then
              if q.theta ^ q.k ≤ (d : ℝ) ∧ Close q.theta ⟨d, hd⟩ ⟨d', hd''⟩ then
                (roughIndicator d q.sigma : ℝ) *
                  q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ) *
                  w3Weight q.toWeightParameters (d * d') else 0 else 0 else 0) ≤
          intervalSum g (q.theta ^ q.k) z := by
      unfold intervalSum
      apply Finset.sum_le_sum
      intro d hdSet
      have hd : 0 < d := (mem_positiveNatsBelow.mp hdSet).1
      simp only [hd, hd', dite_true]
      by_cases hbase : q.theta ^ q.k ≤ (d : ℝ) ∧
          Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩
      · simp only [hbase, if_true]
        dsimp [g]
        simp [modifierWeight, hd, Nat.mul_comm]
        apply le_of_eq
        ring
      · simp only [hbase, if_false]
        split_ifs
        · exact hg d hd
        · norm_num
    have hsigz : q.sigma < z := q.sigma_lt_next_bin
    have hz2 : 2 ≤ z := by
      dsimp [z]
      have ht : 1 ≤ q.theta := by linarith [q.theta_ge_two]
      have := one_le_pow₀ ht (n := q.k + 1)
      rw [show q.k + 1 = 1 + q.k by omega, pow_add, pow_one]
      nlinarith [one_le_pow₀ ht (n := q.k)]
    have hlogS : 0 < Real.log q.sigma := Real.log_pos (by linarith [q.sigma_ge_theta])
    have hlogZ : 0 < Real.log z := Real.log_pos (by linarith)
    have hspos : 0 < q.sigma := by linarith [q.sigma_ge_theta]
    have hzpos : 0 < z := lt_trans hspos hsigz
    have hmean0 := mean.bound (w3Weight q.toWeightParameters)
      (modifierWeight q.toWeightParameters)
      (W.weight_type q.toWeightParameters .w3).nonnegative_multiplicative
      (W.modifier q.toWeightParameters).nonnegative_multiplicative
      (shiftedGeometricBounds_w3_modifier W q.toWeightParameters) K z hz2
    rw [eulerProduct_w3_eq_high W q z] at hmean0
    have heuler := (cmp.family_bounds q q.sigma z
      (le_trans q.theta_ge_two q.sigma_ge_theta) hsigz).2
    have hprod := shiftedPrimeProduct_le_w4 chain W q.toWeightParameters K z
    have hlogpow : (Real.log z).rpow (-1 / 2) ≤
        (Real.log q.sigma).rpow (-1 / 2) :=
      Real.rpow_le_rpow_of_nonpos hlogS
        (Real.strictMonoOn_log hspos hzpos hsigz).le
        (by norm_num)
    have hprime : 0 ≤ primeIntervalProduct (transitionHighEulerW3 q) q.sigma z := by
      unfold primeIntervalProduct
      apply Finset.prod_nonneg
      intro p hpMem
      split_ifs with hpAbove
      · unfold transitionHighEulerW3
        simp only [hpAbove, ↓reduceIte]
        exact (show 0 ≤ localEulerFactor (w3Weight q.toWeightParameters)
          (modifierWeight q.toWeightParameters) p from by
            exact le_trans (by norm_num) (Erdos448.Stage7.Shared.localEulerFactor_ge_one
              (Finset.mem_filter.mp hpMem).2
              (W.weight_type q.toWeightParameters .w3).nonnegative_multiplicative
              (W.weight_type q.toWeightParameters .w3).normalized
              (W.modifier q.toWeightParameters)
              (h051 W q.toWeightParameters .w3 (modifierWeight q.toWeightParameters)
                (W.modifier q.toWeightParameters) p (Finset.mem_filter.mp hpMem).2).domain.summable))
      · norm_num
    have hw4nonneg : 0 ≤ w4Weight q.toWeightParameters d' :=
      (W.weight_type q.toWeightParameters .w4).nonnegative_multiplicative.nonnegative d' hd'
    have hmeanNonneg : 0 ≤ mean.constant := mean.constant_pos.le
    have hzdiv : 0 ≤ z / Real.log z := div_nonneg hzpos.le hlogZ.le
    have heuler' : primeIntervalProduct (transitionHighEulerW3 q) q.sigma z ≤
        cmp.comparison.upper * (Real.log z / Real.log q.sigma).rpow (1 / 2) := by
      simpa [transitionHighCoefficient] using heuler
    have hraw : Erdos448.Stage4.Contracts.shiftedMean
        (w3Weight q.toWeightParameters) (modifierWeight q.toWeightParameters) K z ≤
        mean.constant * cmp.comparison.upper * w4Weight q.toWeightParameters d' *
          z * (Real.log q.sigma).rpow (-1) := by
      calc
        _ ≤ mean.constant * shiftedPrimeProduct (w3Weight q.toWeightParameters)
              (modifierWeight q.toWeightParameters) K z * (z / Real.log z) *
              primeIntervalProduct (transitionHighEulerW3 q) q.sigma z := hmean0
        _ ≤ mean.constant * w4Weight q.toWeightParameters d' *
              (z / Real.log z) *
              (cmp.comparison.upper *
                (Real.log z / Real.log q.sigma).rpow (1 / 2)) := by
              calc
                _ ≤ mean.constant * w4Weight q.toWeightParameters d' *
                    (z / Real.log z) *
                    primeIntervalProduct (transitionHighEulerW3 q) q.sigma z := by
                      gcongr
                _ ≤ _ := mul_le_mul_of_nonneg_left heuler'
                  (mul_nonneg
                    (mul_nonneg mean.constant_pos.le hw4nonneg) hzdiv)
        _ = (mean.constant * cmp.comparison.upper * w4Weight q.toWeightParameters d' * z) *
              ((Real.log z / Real.log q.sigma).rpow (1 / 2) / Real.log z) := by ring
        _ = mean.constant * cmp.comparison.upper * w4Weight q.toWeightParameters d' *
              z * (Real.log q.sigma).rpow (-1 / 2) *
              (Real.log z).rpow (-1 / 2) := by
              rw [log_ratio_half_identity hlogS hlogZ]
              ring
        _ ≤ mean.constant * cmp.comparison.upper * w4Weight q.toWeightParameters d' *
              z * (Real.log q.sigma).rpow (-1 / 2) *
              (Real.log q.sigma).rpow (-1 / 2) := by
                exact mul_le_mul_of_nonneg_left hlogpow
                  (mul_nonneg
                    (mul_nonneg
                      (mul_nonneg
                        (mul_nonneg mean.constant_pos.le cmp.comparison.upper_pos.le)
                        hw4nonneg) hzpos.le)
                    (Real.rpow_nonneg hlogS.le _))
        _ = (mean.constant * cmp.comparison.upper * w4Weight q.toWeightParameters d' * z) *
              ((Real.log q.sigma).rpow (-1 / 2) *
                (Real.log q.sigma).rpow (-1 / 2)) := by ring
        _ = _ := by rw [rpow_neg_half_sq hlogS]
    calc
      _ ≤ intervalSum g (q.theta ^ q.k) z := houterSum
      _ ≤ ∑ n ∈ positiveNatsBelow z, g n := hsum.regular_to_initial
      _ = Erdos448.Stage4.Contracts.shiftedMean (w3Weight q.toWeightParameters)
          (modifierWeight q.toWeightParameters) K z := by
            unfold Erdos448.Stage4.Contracts.shiftedMean
            apply Finset.sum_congr rfl
            intro n hn
            dsimp [g, K]
            ring
      _ ≤ mean.constant * cmp.comparison.upper * w4Weight q.toWeightParameters d' *
          z * (Real.log q.sigma).rpow (-1) := hraw
      _ = CtrOut * q.theta ^ q.k * (Real.log q.sigma).rpow (-1) *
          w4Weight q.toWeightParameters d' := by
            dsimp [CtrOut, z]
            rw [pow_succ]
            ring
  · simp only [hlower, if_false]
    rw [mul_zero]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro d hdSet
    have hd : 0 < d := (mem_positiveNatsBelow.mp hdSet).1
    simp only [hd, hd', dite_true]
    by_cases hbase : q.theta ^ q.k ≤ (d : ℝ) ∧
        Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩
    · exact (hlower (close_second_lower q hd hd' hbase.1 hbase.2)).elim
    · simp [hbase]

theorem result : Erdos448.Stage6.TaskContracts.ROOT09Target := by
  intro h005 h007 h008 h050 h052 h053 h054 h054A chain W h051 h057
  exact
    { p075 := p075 h050 h052
      p076 := p076
      p077 := p077 h005 h008 chain W h051
      p078 := p078 W
      p079 := p079 h057
      p080 := p080 W
      p081 := p081
      p082 := p082 h054 W
      p083 := p083 h053 h054 W
      p084 := p084 h005 h008 h054A chain W h051 }

end

end Erdos448.Stage7.ROOT09.Work
