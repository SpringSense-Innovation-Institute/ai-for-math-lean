module

import all Mathlib.Basic.Real.Basic
public import «Erdos448».dependencies.«DP-MERTENS».stage6.FrozenTaskContracts
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Stirling

public section

set_option backward.isDefEq.respectTransparency false

open Filter Finset
open scoped BigOperators Topology ArithmeticFunction

namespace Erdos448.DPMertens.Tasks.MSCFirstLemma

noncomputable section

open Erdos448.DPMertens Erdos448.DPMertens.Lowering

theorem theta_eq_chebyshev (x : ℝ) :
    theta x = Chebyshev.theta x := by
  classical
  unfold theta primesLE Chebyshev.theta
  apply Finset.sum_congr
  · ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    constructor
    · rintro ⟨hlt, hp⟩
      exact ⟨⟨hp.pos, Nat.lt_succ_iff.mp hlt⟩, hp⟩
    · rintro ⟨⟨_, hle⟩, hp⟩
      exact ⟨Nat.lt_succ_iff.mpr hle, hp⟩
  · intro p hp
    rfl

@[expose] def mangoldtWeightedSum (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt m / m

theorem mangoldtWeightedSum_nonneg (n : ℕ) :
    0 ≤ mangoldtWeightedSum n := by
  unfold mangoldtWeightedSum
  exact Finset.sum_nonneg fun m _ ↦
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg m)

theorem psi_le_provider (cheb : ChebyshevOutput) {n : ℕ} (hn : 2 ≤ n) :
    Chebyshev.psi n ≤ (20 * cheb.C_vartheta) * n := by
  have hthetaTwo := cheb.weak_bound 2 (by norm_num)
  have hthetaTwoLower : Real.log 2 ≤ theta 2 := by
    unfold theta
    refine Finset.single_le_sum
      (f := fun p : ℕ ↦ Real.log (p : ℝ)) (s := primesLE 2) (a := 2) ?_ ?_
    · intro p hp
      exact Real.log_nonneg (by
        norm_cast
        exact (Finset.mem_filter.mp hp).2.one_le)
    · norm_num [primesLE, Nat.prime_two]
  have hlogFour : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hcoef : Real.log 4 + 4 ≤ 20 * cheb.C_vartheta := by
    rw [hlogFour]
    nlinarith [Real.log_two_gt_d9]
  calc
    Chebyshev.psi n ≤ (Real.log 4 + 4) * n :=
      Chebyshev.psi_le_const_mul_self (by positivity)
    _ ≤ (20 * cheb.C_vartheta) * n := by gcongr

theorem log_factorial_eq_legendre (n : ℕ) :
    Real.log n.factorial =
      ∑ m ∈ Finset.Ioc 0 n,
        ArithmeticFunction.vonMangoldt m * (n / m : ℕ) := by
  have hprod : ∏ j ∈ Finset.Ioc 0 n, j = n.factorial := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.prod_Ioc_succ_top (Nat.zero_le n), Nat.factorial_succ, ih]
        exact Nat.mul_comm _ _
  calc
    Real.log n.factorial = Real.log (∏ j ∈ Finset.Ioc 0 n, (j : ℝ)) := by
      congr 1
      rw [← Nat.cast_prod, hprod]
    _ = ∑ j ∈ Finset.Ioc 0 n, Real.log j := by
      rw [Real.log_prod]
      intro j hj
      exact_mod_cast (Finset.mem_Ioc.mp hj).1.ne'
    _ = ∑ m ∈ Finset.Ioc 0 n,
        ArithmeticFunction.vonMangoldt m * (n / m : ℕ) := by
      rw [← ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum
        (R := ℝ) ArithmeticFunction.vonMangoldt n]
      rw [ArithmeticFunction.vonMangoldt_mul_zeta]
      rfl

theorem natDiv_fraction_bounds {n m : ℕ} (hm : 0 < m) :
    0 ≤ (n : ℝ) / m - (n / m : ℕ) ∧
      (n : ℝ) / m - (n / m : ℕ) ≤ 1 := by
  have hx0 : 0 ≤ (n : ℝ) / m := by positivity
  have hfloor : ⌊(n : ℝ) / m⌋₊ = n / m :=
    Nat.floor_div_eq_div n m
  constructor
  · exact sub_nonneg.mpr (by rw [← hfloor]; exact Nat.floor_le hx0)
  · rw [sub_le_iff_le_add, ← hfloor]
    linarith [Nat.lt_floor_add_one ((n : ℝ) / m)]

theorem legendre_error_bounds (cheb : ChebyshevOutput) {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ mangoldtWeightedSum n - Real.log n.factorial / n ∧
      mangoldtWeightedSum n - Real.log n.factorial / n ≤
        20 * cheb.C_vartheta := by
  have hnR : (0 : ℝ) < n := by positivity
  rw [mangoldtWeightedSum, log_factorial_eq_legendre]
  rw [Finset.sum_div]
  rw [← Finset.sum_sub_distrib]
  constructor
  · apply Finset.sum_nonneg
    intro m hm
    have hm0 : 0 < m := (Finset.mem_Ioc.mp hm).1
    have hf := (natDiv_fraction_bounds (n := n) hm0).1
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := m)
    calc
      ArithmeticFunction.vonMangoldt m / m -
          ArithmeticFunction.vonMangoldt m * (n / m : ℕ) / n =
          ArithmeticFunction.vonMangoldt m / n *
            ((n : ℝ) / m - (n / m : ℕ)) := by
              field_simp
      _ ≥ 0 := mul_nonneg (div_nonneg hΛ hnR.le) hf
  · calc
      ∑ m ∈ Finset.Ioc 0 n,
          (ArithmeticFunction.vonMangoldt m / m -
            ArithmeticFunction.vonMangoldt m * (n / m : ℕ) / n) ≤
          ∑ m ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt m / n := by
            apply Finset.sum_le_sum
            intro m hm
            have hm0 : 0 < m := (Finset.mem_Ioc.mp hm).1
            have hf := (natDiv_fraction_bounds (n := n) hm0).2
            have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := m)
            calc
              ArithmeticFunction.vonMangoldt m / m -
                  ArithmeticFunction.vonMangoldt m * (n / m : ℕ) / n =
                  ArithmeticFunction.vonMangoldt m / n *
                    ((n : ℝ) / m - (n / m : ℕ)) := by
                      field_simp
              _ ≤ ArithmeticFunction.vonMangoldt m / n := by
                nlinarith [div_nonneg hΛ hnR.le]
      _ = Chebyshev.psi n / n := by
        rw [← Finset.sum_div]
        unfold Chebyshev.psi
        rw [Nat.floor_natCast]
      _ ≤ 20 * cheb.C_vartheta := by
        rw [div_le_iff₀ hnR]
        simpa only [mul_comm] using psi_le_provider cheb hn

theorem normalized_log_factorial_bounds {n : ℕ} (hn : 2 ≤ n) :
    Real.log n - 1 ≤ Real.log n.factorial / n ∧
      Real.log n.factorial / n ≤ Real.log n := by
  have hn0 : n ≠ 0 := by omega
  have hnR : (0 : ℝ) < n := by positivity
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by norm_cast; omega)
  constructor
  · have hs := Stirling.le_log_factorial_stirling hn0
    have hpi : 0 ≤ Real.log (2 * Real.pi) := by
      apply Real.log_nonneg
      nlinarith [Real.pi_gt_three]
    rw [le_div_iff₀ hnR]
    calc
      (Real.log n - 1) * n = n * Real.log n - n := by ring
      _ ≤ n * Real.log n - n + Real.log n / 2 + Real.log (2 * Real.pi) / 2 := by
        linarith
      _ ≤ Real.log n.factorial := hs
  · have hfacNat : n.factorial ≤ n ^ n := Nat.factorial_le_pow n
    have hfac : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast hfacNat
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < n.factorial) hfac
    rw [Real.log_pow] at hlog
    rw [div_le_iff₀ hnR]
    simpa only [mul_comm] using hlog

@[expose] def activePrimePowers (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun q ↦ q.1.Prime ∧ 1 ≤ q.2 ∧ q.1 ^ q.2 ≤ n)

theorem primePowerSum_eq_active (n : ℕ) :
    primePowerSum n =
      ∑ q ∈ activePrimePowers n,
        Real.log q.1 / (q.1 : ℝ) ^ q.2 := by
  classical
  unfold primePowerSum activePrimePowers
  rw [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Finset.mem_range] at hp
  by_cases hprime : p.Prime
  · simp only [hprime, ↓reduceIte]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hactive : 1 ≤ k ∧ p ^ k ≤ n
    · simp [hprime, hactive]
    · simp [hprime, hactive]
  · simp [hprime]

theorem self_le_two_pow (k : ℕ) : k ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      have hpowPos : 0 < 2 ^ k := Nat.two_pow_pos k
      omega

theorem active_sum_eq_mangoldtWeightedSum (n : ℕ) :
    (∑ q ∈ activePrimePowers n,
        Real.log q.1 / (q.1 : ℝ) ^ q.2) = mangoldtWeightedSum n := by
  classical
  let S := (Finset.Ioc 0 n).filter IsPrimePow
  calc
    (∑ q ∈ activePrimePowers n,
        Real.log q.1 / (q.1 : ℝ) ^ q.2) =
        ∑ m ∈ S, ArithmeticFunction.vonMangoldt m / m := by
      apply Finset.sum_bij (fun q _ ↦ q.1 ^ q.2)
      · intro q hq
        rcases Finset.mem_filter.mp hq with ⟨hqRange, hprime, hk, hpow⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
          ⟨pow_pos hprime.pos _, hpow⟩,
          (isPrimePow_nat_iff _).mpr ⟨q.1, q.2, hprime, hk, rfl⟩⟩
      · intro q₁ hq₁ q₂ hq₂ heq
        rcases Finset.mem_filter.mp hq₁ with ⟨_, hp₁, hk₁, _⟩
        rcases Finset.mem_filter.mp hq₂ with ⟨_, hp₂, hk₂, _⟩
        rcases q₁ with ⟨p₁, k₁⟩
        rcases q₂ with ⟨p₂, k₂⟩
        simp only [Prod.fst, Prod.snd] at hp₁ hk₁ hp₂ hk₂ heq ⊢
        rcases Nat.Prime.pow_inj' hp₁ hp₂
          (Nat.ne_zero_of_lt hk₁) (Nat.ne_zero_of_lt hk₂) heq with ⟨rfl, rfl⟩
        rfl
      · intro m hm
        rcases Finset.mem_filter.mp hm with ⟨hmRange, hmPow⟩
        have hmLe : m ≤ n := (Finset.mem_Ioc.mp hmRange).2
        rcases (isPrimePow_nat_iff _).mp hmPow with ⟨p, k, hp, hk, rfl⟩
        have hp_le_pow : p ≤ p ^ k := le_self_pow₀ hp.one_le hk.ne'
        have hk_le_pow : k ≤ p ^ k := by
          exact (self_le_two_pow k).trans
            (Nat.pow_le_pow_left hp.two_le k)
        refine ⟨(p, k), ?_, rfl⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_,
          Finset.mem_range.mpr ?_⟩, hp, hk, hmLe⟩
        · exact Nat.lt_succ_of_le (hp_le_pow.trans hmLe)
        · exact Nat.lt_succ_of_le (hk_le_pow.trans hmLe)
      · intro q hq
        rcases Finset.mem_filter.mp hq with ⟨_, hp, hk, _⟩
        rcases q with ⟨p, k⟩
        simp only [Prod.fst, Prod.snd] at hp hk ⊢
        rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.ne_zero_of_lt hk),
          ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow]
    _ = mangoldtWeightedSum n := by
      unfold S mangoldtWeightedSum
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro m _
      by_cases hm : IsPrimePow m
      · simp only [hm, if_true]
      · simp only [hm, if_false]
        rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hm, zero_div]

theorem primePowerSum_eq_mangoldtWeightedSum (n : ℕ) :
    primePowerSum n = mangoldtWeightedSum n :=
  (primePowerSum_eq_active n).trans (active_sum_eq_mangoldtWeightedSum n)

theorem primePower_bound (cheb : ChebyshevOutput) {n : ℕ} (hn : 2 ≤ n) :
    |primePowerSum n - Real.log n| ≤
      20 * cheb.C_vartheta + 1 := by
  rw [primePowerSum_eq_mangoldtWeightedSum]
  have he := legendre_error_bounds cheb hn
  have hf := normalized_log_factorial_bounds hn
  apply abs_le.mpr
  constructor <;> nlinarith

@[expose] def higherPrimePowerPart (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (n + 1),
    if p.Prime then
      ∑ k ∈ Finset.range (n + 1),
        if 2 ≤ k ∧ p ^ k ≤ n then Real.log p / (p : ℝ) ^ k else 0
    else 0

theorem sum_ge_one_eq_one_add_ge_two
    {N : ℕ} (hN : 1 < N) (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℝ) :
    (∑ k ∈ Finset.range N, if 1 ≤ k ∧ P k then f k else 0) =
      (if P 1 then f 1 else 0) +
        ∑ k ∈ Finset.range N, if 2 ≤ k ∧ P k then f k else 0 := by
  calc
    (∑ k ∈ Finset.range N, if 1 ≤ k ∧ P k then f k else 0) =
        ∑ k ∈ Finset.range N,
          ((if k = 1 ∧ P k then f k else 0) +
            (if 2 ≤ k ∧ P k then f k else 0)) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k = 1
      · subst k
        simp
      · by_cases hk2 : 2 ≤ k
        · have hk1 : 1 ≤ k := by omega
          simp [hk, hk1, hk2]
        · have hk0 : k = 0 := by omega
          subst k
          simp
    _ = (∑ k ∈ Finset.range N, if k = 1 ∧ P k then f k else 0) +
        ∑ k ∈ Finset.range N, if 2 ≤ k ∧ P k then f k else 0 := by
      rw [Finset.sum_add_distrib]
    _ = (if P 1 then f 1 else 0) +
        ∑ k ∈ Finset.range N, if 2 ≤ k ∧ P k then f k else 0 := by
      congr 1
      by_cases hP : P 1
      · rw [if_pos hP]
        calc
          (∑ k ∈ Finset.range N, if k = 1 ∧ P k then f k else 0) =
              ∑ k ∈ Finset.range N, if k = 1 then f 1 else 0 := by
            apply Finset.sum_congr rfl
            intro k _
            by_cases hk : k = 1
            · subst k
              simp [hP]
            · simp [hk]
          _ = f 1 := by simp [hN]
      · rw [if_neg hP]
        apply Finset.sum_eq_zero
        intro k _
        by_cases hk : k = 1
        · subst k
          simp [hP]
        · simp [hk]

theorem primePowerSum_eq_weighted_add_higher {n : ℕ} (hn : 2 ≤ n) :
    primePowerSum n = weightedPrimeSum n + higherPrimePowerPart n := by
  classical
  unfold primePowerSum weightedPrimeSum primesLE higherPrimePowerPart
  rw [Nat.floor_natCast]
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hpRange
  by_cases hp : p.Prime
  · simp only [hp, ↓reduceIte]
    rw [sum_ge_one_eq_one_add_ge_two (by omega)
      (fun k ↦ p ^ k ≤ n) (fun k ↦ Real.log p / (p : ℝ) ^ k)]
    have hpLe : p ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hpRange)
    simp [hpLe]
  · simp [hp]

@[expose] def higherMangoldtTerm (m : ℕ) : ℝ :=
  (if m.Prime then 0 else ArithmeticFunction.vonMangoldt m) / m

theorem summable_higherMangoldtTerm : Summable higherMangoldtTerm := by
  have hs :=
    ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div
      (a := (0 : ZMod 1))
  apply hs.congr
  intro m
  have hz : (m : ZMod 1) = (0 : ZMod 1) := Subsingleton.elim _ _
  unfold higherMangoldtTerm ArithmeticFunction.vonMangoldt.residueClass
  simp [hz]

theorem higherMangoldtTerm_nonneg (m : ℕ) : 0 ≤ higherMangoldtTerm m := by
  unfold higherMangoldtTerm
  apply div_nonneg
  · split_ifs
    · exact le_rfl
    · exact ArithmeticFunction.vonMangoldt_nonneg
  · exact Nat.cast_nonneg m

theorem weightedPrimeSum_eq_primeMangoldt (n : ℕ) :
    weightedPrimeSum n =
      ∑ m ∈ Finset.Ioc 0 n,
        (if m.Prime then ArithmeticFunction.vonMangoldt m / m else 0) := by
  classical
  unfold weightedPrimeSum primesLE
  rw [Nat.floor_natCast]
  rw [← Finset.sum_filter]
  have hsets :
      (Finset.range (n + 1)).filter Nat.Prime =
        (Finset.Ioc 0 n).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    constructor
    · rintro ⟨hpLe, hp⟩
      exact ⟨⟨hp.pos, Nat.le_of_lt_succ hpLe⟩, hp⟩
    · rintro ⟨⟨_, hpLe⟩, hp⟩
      exact ⟨Nat.lt_succ_of_le hpLe, hp⟩
  rw [hsets]
  apply Finset.sum_congr rfl
  intro p hp
  rw [ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2]

theorem mangoldtWeightedSum_eq_prime_add_higher (n : ℕ) :
    mangoldtWeightedSum n = weightedPrimeSum n +
      ∑ m ∈ Finset.Ioc 0 n, higherMangoldtTerm m := by
  rw [weightedPrimeSum_eq_primeMangoldt]
  unfold mangoldtWeightedSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  unfold higherMangoldtTerm
  by_cases hm : m.Prime
  · simp [hm]
  · simp [hm]

theorem higherPrimePowerPart_eq_sum_higher {n : ℕ} (hn : 2 ≤ n) :
    higherPrimePowerPart n = ∑ m ∈ Finset.Ioc 0 n, higherMangoldtTerm m := by
  have hV := primePowerSum_eq_weighted_add_higher hn
  rw [primePowerSum_eq_mangoldtWeightedSum,
    mangoldtWeightedSum_eq_prime_add_higher] at hV
  linarith

theorem higherPrimePowerPart_nonneg (n : ℕ) : 0 ≤ higherPrimePowerPart n := by
  unfold higherPrimePowerPart
  apply Finset.sum_nonneg
  intro p _
  split_ifs with hp
  · apply Finset.sum_nonneg
    intro k _
    split_ifs
    · positivity [hp.pos]
    · positivity
  · positivity

@[expose] def higherTailConstant : ℝ := ∑' m : ℕ, higherMangoldtTerm m

theorem higherPrimePowerPart_le_tail {n : ℕ} (hn : 2 ≤ n) :
    higherPrimePowerPart n ≤ higherTailConstant := by
  rw [higherPrimePowerPart_eq_sum_higher hn]
  exact summable_higherMangoldtTerm.sum_le_tsum (Finset.Ioc 0 n)
    (fun m _ ↦ higherMangoldtTerm_nonneg m)

theorem higherTailConstant_nonneg : 0 ≤ higherTailConstant := by
  unfold higherTailConstant
  exact tsum_nonneg higherMangoldtTerm_nonneg

theorem integer_weightedPrimeSum_bound (cheb : ChebyshevOutput)
    {n : ℕ} (hn : 2 ≤ n) :
    |weightedPrimeSum n - Real.log n| ≤
      (20 * cheb.C_vartheta + 1) + higherTailConstant := by
  have hV := primePower_bound cheb hn
  have hsplit := primePowerSum_eq_weighted_add_higher hn
  have hH0 := higherPrimePowerPart_nonneg n
  have hHT := higherPrimePowerPart_le_tail hn
  have hcv0 : 0 ≤ 20 * cheb.C_vartheta + 1 := by
    nlinarith [cheb.C_vartheta_pos]
  rw [hsplit] at hV
  rcases abs_le.mp hV with ⟨hVlower, hVupper⟩
  apply abs_le.mpr
  constructor <;> nlinarith

theorem weightedPrimeSum_eq_floor (t : ℝ) :
    weightedPrimeSum t = weightedPrimeSum (Nat.floor t) := by
  unfold weightedPrimeSum primesLE
  rw [Nat.floor_natCast]

theorem log_floor_adapter {t : ℝ} (ht : 2 ≤ t) :
    |Real.log (Nat.floor t) - Real.log t| ≤ Real.log 2 := by
  have ht0 : 0 ≤ t := by linarith
  have hn : 2 ≤ Nat.floor t := Nat.le_floor ht
  have hnpos : (0 : ℝ) < Nat.floor t := by positivity
  have hfloor_le : (Nat.floor t : ℝ) ≤ t := Nat.floor_le ht0
  have ht_lt : t < (Nat.floor t : ℝ) + 1 := Nat.lt_floor_add_one t
  have hone_le_floor : (1 : ℝ) ≤ Nat.floor t := by norm_cast; omega
  have ht_le_twice : t ≤ 2 * (Nat.floor t : ℝ) := by linarith
  have hlog_lower : Real.log (Nat.floor t) ≤ Real.log t :=
    Real.log_le_log hnpos hfloor_le
  have hlog_upper : Real.log t ≤ Real.log 2 + Real.log (Nat.floor t) := by
    calc
      Real.log t ≤ Real.log (2 * (Nat.floor t : ℝ)) :=
        Real.log_le_log (by positivity) ht_le_twice
      _ = Real.log 2 + Real.log (Nat.floor t) := by
        rw [Real.log_mul (by norm_num) hnpos.ne']
  rw [abs_of_nonpos (sub_nonpos.mpr hlog_lower)]
  linarith

theorem real_weightedPrimeSum_bound (cheb : ChebyshevOutput)
    {t : ℝ} (ht : 2 ≤ t) :
    |weightedPrimeSum t - Real.log t| ≤
      (20 * cheb.C_vartheta + 1) + higherTailConstant + Real.log 2 := by
  have ht0 : 0 ≤ t := by linarith
  have hn : 2 ≤ Nat.floor t := Nat.le_floor ht
  have hInt := integer_weightedPrimeSum_bound cheb hn
  have hFloor := log_floor_adapter ht
  rw [weightedPrimeSum_eq_floor]
  calc
    |weightedPrimeSum ↑⌊t⌋₊ - Real.log t| =
        |(weightedPrimeSum ↑⌊t⌋₊ - Real.log ↑⌊t⌋₊) +
          (Real.log ↑⌊t⌋₊ - Real.log t)| := by ring_nf
    _ ≤ |weightedPrimeSum ↑⌊t⌋₊ - Real.log ↑⌊t⌋₊| +
        |Real.log ↑⌊t⌋₊ - Real.log t| := abs_add_le _ _
    _ ≤ ((20 * cheb.C_vartheta + 1) + higherTailConstant) +
        Real.log 2 := add_le_add hInt hFloor
    _ = (20 * cheb.C_vartheta + 1) + higherTailConstant + Real.log 2 := by ring

/-- The frozen first-lemma output, constructed parametrically from its local
Chebyshev provider. -/
@[expose] noncomputable def result :
    Erdos448.DPMertens.Lowering.TASK_MSC_FIRST_LEMMA_Target := fun cheb ↦
  { C_V := 20 * cheb.C_vartheta + 1
    C_V_nonneg := by
      nlinarith [cheb.C_vartheta_pos]
    prime_power_bound := fun n hn ↦ primePower_bound cheb hn
    C_A := (20 * cheb.C_vartheta + 1) + higherTailConstant + Real.log 2 + 1
    C_A_pos := by
      have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      nlinarith [cheb.C_vartheta_pos, higherTailConstant_nonneg]
    first_lemma := by
      intro t ht
      exact (real_weightedPrimeSum_bound cheb ht).trans (by linarith) }

end

end Erdos448.DPMertens.Tasks.MSCFirstLemma

#check Erdos448.DPMertens.Tasks.MSCFirstLemma.result
#print axioms Erdos448.DPMertens.Tasks.MSCFirstLemma.result
