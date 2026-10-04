module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage6.TaskContracts

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT05.Recovered.P051AE

open Finset Set
open scoped BigOperators NNReal

noncomputable section

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Erdos448.Stage6.TaskContracts

lemma multiplicativeExtension_one (F : ℕ → ℕ → ℝ) :
    multiplicativeExtension F 1 = 1 := by
  simp [multiplicativeExtension]

lemma multiplicativeExtension_prime_pow
    (F : ℕ → ℕ → ℝ) {p i : ℕ} (hp : p.Prime) (hi : 1 ≤ i) :
    multiplicativeExtension F (p ^ i) = F p i := by
  rw [multiplicativeExtension, if_neg (pow_ne_zero i hp.ne_zero),
    Nat.primeFactors_prime_pow (Nat.ne_of_gt hi) hp]
  simp [hp.factorization_pow]

lemma multiplicativeExtension_mul
    (F : ℕ → ℕ → ℝ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) :
    multiplicativeExtension F (a * b) =
      multiplicativeExtension F a * multiplicativeExtension F b := by
  have ha0 : a ≠ 0 := Nat.ne_of_gt ha
  have hb0 : b ≠ 0 := Nat.ne_of_gt hb
  have hab0 : a * b ≠ 0 := mul_ne_zero ha0 hb0
  simp only [multiplicativeExtension, if_neg ha0, if_neg hb0, if_neg hab0]
  rw [hab.primeFactors_mul,
    Finset.prod_union ((Nat.disjoint_primeFactors ha0 hb0).2 hab)]
  congr 1
  · apply Finset.prod_congr rfl
    intro p hp
    congr 1
    exact Nat.factorization_eq_of_coprime_left hab (List.mem_toFinset.mp hp)
  · apply Finset.prod_congr rfl
    intro p hp
    congr 1
    exact Nat.factorization_eq_of_coprime_right hab (List.mem_toFinset.mp hp)

lemma multiplicativeExtension_nonnegative
    (F : ℕ → ℕ → ℝ)
    (hF : ∀ p : ℕ, p.Prime → ∀ i : ℕ, 1 ≤ i → 0 ≤ F p i) :
    NonnegativeWeight (multiplicativeExtension F) := by
  intro n hn
  rw [multiplicativeExtension, if_neg (Nat.ne_of_gt hn)]
  exact Finset.prod_nonneg fun p hp =>
    hF p (Nat.prime_of_mem_primeFactors hp) _
      ((Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd
        (Nat.ne_of_gt hn) (Nat.dvd_of_mem_primeFactors hp))

lemma multiplicativeExtension_weight
    (F : ℕ → ℕ → ℝ)
    (hF : ∀ p : ℕ, p.Prime → ∀ i : ℕ, 1 ≤ i → 0 ≤ F p i) :
    NonnegativeMultiplicativeWeight (multiplicativeExtension F) := by
  refine ⟨multiplicativeExtension_nonnegative F hF, ?_⟩
  exact ⟨multiplicativeExtension_one F,
    fun a b ha hb hab => multiplicativeExtension_mul F ha hb hab⟩

lemma multiplicative_weight_eq_extension
    (w : ArithmeticWeight) (hw : MultiplicativeWeight w) {n : ℕ} (hn : 0 < n) :
    w n = multiplicativeExtension (fun p i => w (p ^ i)) n := by
  rw [multiplicativeExtension, if_neg (Nat.ne_of_gt hn)]
  rw [Nat.multiplicative_factorization w (fun x y hxy => by
    rcases eq_or_ne x 0 with rfl | hx
    · have : y = 1 := by simpa using hxy
      simp [this, hw.1]
    rcases eq_or_ne y 0 with rfl | hy
    · have : x = 1 := by simpa using hxy
      simp [this, hw.1]
    exact hw.2 x y (Nat.pos_of_ne_zero hx) (Nat.pos_of_ne_zero hy) hxy) hw.1
      (Nat.ne_of_gt hn)]
  exact Nat.prod_factorization_eq_prod_primeFactors _

lemma multiplicativeExtension_mono
    (F G : ℕ → ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    (hF : ∀ p : ℕ, p.Prime → ∀ i : ℕ, 1 ≤ i → 0 ≤ F p i)
    (hFG : ∀ p : ℕ, p.Prime → ∀ i : ℕ, 1 ≤ i → F p i ≤ G p i) :
    multiplicativeExtension F n ≤ multiplicativeExtension G n := by
  simp only [multiplicativeExtension, if_neg (Nat.ne_of_gt hn)]
  apply Finset.prod_le_prod₀
  · intro p hp
    exact hF p (Nat.prime_of_mem_primeFactors hp) _
      ((Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd
        (Nat.ne_of_gt hn) (Nat.dvd_of_mem_primeFactors hp))
  · intro p hp
    exact hFG p (Nat.prime_of_mem_primeFactors hp) _
      ((Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd
        (Nat.ne_of_gt hn) (Nat.dvd_of_mem_primeFactors hp))

lemma weight_le_extension
    (w : ArithmeticWeight) (hw : NonnegativeMultiplicativeWeight w)
    (F : ℕ → ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    (hlocal : ∀ p : ℕ, p.Prime → ∀ i : ℕ, 1 ≤ i → w (p ^ i) ≤ F p i) :
    w n ≤ multiplicativeExtension F n := by
  rw [multiplicative_weight_eq_extension w hw.multiplicative hn]
  apply multiplicativeExtension_mono _ _ hn
  · intro p hp i hi
    exact hw.nonnegative _ (pow_pos hp.pos i)
  · exact hlocal

theorem p051A : P051AStatement := by
  have hprime : ∀ p : ℕ, p.Prime → ∀ i : ℕ, 1 ≤ i →
      a0Weight (p ^ i) = 1 / (i + 1 : ℕ) := by
    intro p hp i hi
    rw [a0Weight, dif_pos (pow_pos hp.pos i), tau, divisorSet,
      Nat.card_divisors (pow_ne_zero i hp.ne_zero),
      Nat.primeFactors_prime_pow (Nat.ne_of_gt hi) hp]
    simp [hp.factorization_pow]
  refine ⟨?_, hprime⟩
  refine
    { c_pos := by norm_num
      C_pos := by norm_num
      Lambda_pos := by norm_num
      nonnegative_multiplicative := ?_
      normalized := ?_
      prime_power := ?_
      prime_power_bounds := ?_ }
  · refine ⟨?_, ?_⟩
    · intro n hn
      simp only [a0Weight, dif_pos hn]
      positivity
    · refine ⟨?_, ?_⟩
      · simp [a0Weight, tau, divisorSet]
      · intro a b ha hb hab
        simp only [a0Weight, dif_pos ha, dif_pos hb, dif_pos (Nat.mul_pos ha hb),
          tau, divisorSet]
        rw [hab.card_divisors_mul]
        push_cast
        field_simp
  · simp [a0Weight, tau, divisorSet]
  · intro p hp i hi
    rw [hprime p hp i hi]
    simpa using (Real.rpow_nonneg (Nat.cast_nonneg p) (-1 : ℝ))
  · intro p hp i hi
    rw [hprime p hp i hi]
    constructor
    · positivity
    · rw [div_le_one (by positivity)]
      norm_num

lemma denominator_term_nonnegative
    {a b : ArithmeticWeight} {ca Ca Lambdaa : ℝ}
    (ha : WeightTypeSpec a ca Ca Lambdaa) (hb : ModifierSpec b)
    {p : ℕ} (hp : p.Prime) (j : ℕ) :
    0 ≤ a (p ^ j) * b (p ^ j) / (p : ℝ) ^ j := by
  cases j with
  | zero => simp [ha.normalized, hb.normalized]
  | succ j =>
      exact div_nonneg
        (mul_nonneg (ha.prime_power_bounds p hp (j + 1) (by omega)).1
          (hb.prime_power_bounds p hp (j + 1)).1)
        (pow_nonneg (Nat.cast_nonneg p) _)

lemma denominator_summable
    {a b : ArithmeticWeight} {ca Ca Lambdaa : ℝ}
    (ha : WeightTypeSpec a ca Ca Lambdaa) (hb : ModifierSpec b)
    {p : ℕ} (hp : p.Prime) :
    Summable fun j : ℕ => a (p ^ j) * b (p ^ j) / (p : ℝ) ^ j := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hr0 : 0 ≤ 1 / (p : ℝ) := by positivity
  have hr1 : 1 / (p : ℝ) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  refine .of_norm_bounded
    ((summable_geometric_of_lt_one hr0 hr1).mul_left (max 1 Lambdaa)) ?_
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg (denominator_term_nonnegative ha hb hp j)]
  cases j with
  | zero => simp [ha.normalized, hb.normalized, le_max_left]
  | succ j =>
      have haB := (ha.prime_power_bounds p hp (j + 1) (by omega)).2
      have hbB := (hb.prime_power_bounds p hp (j + 1)).2
      have hb0 := (hb.prime_power_bounds p hp (j + 1)).1
      calc
        a (p ^ (j + 1)) * b (p ^ (j + 1)) / (p : ℝ) ^ (j + 1)
            ≤ Lambdaa * 1 / (p : ℝ) ^ (j + 1) := by
              gcongr
              exact ha.Lambda_pos.le
        _ = Lambdaa * (1 / (p : ℝ)) ^ (j + 1) := by
          simp [div_eq_mul_inv, inv_pow]
        _ ≤ max 1 Lambdaa * (1 / (p : ℝ)) ^ (j + 1) := by
          gcongr
          exact le_max_right _ _

theorem p051B : P051BStatement := by
  intro a ca Ca Lambdaa ha b hb p hp
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hpR
  have hr0 : 0 ≤ 1 / (p : ℝ) := by positivity
  have hr1 : 1 / (p : ℝ) < 1 := by
    rw [div_lt_one hp0]
    linarith
  let f : ℕ → ℝ := fun j => a (p ^ j) * b (p ^ j) / (p : ℝ) ^ j
  have hf : Summable f := denominator_summable ha hb hp
  have hf0 : f 0 = 1 := by simp [f, ha.normalized, hb.normalized]
  have htail_nonneg : ∀ j : ℕ, 0 ≤ f (j + 1) := by
    intro j
    exact denominator_term_nonnegative ha hb hp (j + 1)
  have htail : ∀ j : ℕ,
      f (j + 1) ≤ Lambdaa * (1 / (p : ℝ)) ^ (j + 1) := by
    intro j
    have haB := (ha.prime_power_bounds p hp (j + 1) (by omega)).2
    have hbB := (hb.prime_power_bounds p hp (j + 1)).2
    have hb0 := (hb.prime_power_bounds p hp (j + 1)).1
    calc
      f (j + 1) ≤ Lambdaa * 1 / (p : ℝ) ^ (j + 1) := by
        dsimp [f]
        gcongr
        exact ha.Lambda_pos.le
      _ = Lambdaa * (1 / (p : ℝ)) ^ (j + 1) := by
        simp [div_eq_mul_inv, inv_pow]
  have hgeom : Summable fun j : ℕ => Lambdaa * (1 / (p : ℝ)) ^ (j + 1) :=
    ((summable_geometric_of_lt_one hr0 hr1).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)).mul_left Lambdaa
  have htail_tsum :
      (∑' j : ℕ, f (j + 1)) ≤
        ∑' j : ℕ, Lambdaa * (1 / (p : ℝ)) ^ (j + 1) :=
    (hf.comp_injective (fun _ _ h => Nat.add_right_cancel h)).tsum_le_tsum htail hgeom
  have hgeom_value :
      (∑' j : ℕ, Lambdaa * (1 / (p : ℝ)) ^ (j + 1)) =
        Lambdaa / ((p : ℝ) - 1) := by
    have hshift : (∑' j : ℕ, (1 / (p : ℝ)) ^ (j + 1)) =
        (1 - 1 / (p : ℝ))⁻¹ - 1 := by
      have h := (summable_geometric_of_lt_one hr0 hr1).tsum_eq_zero_add
      rw [tsum_geometric_of_lt_one hr0 hr1] at h
      apply eq_sub_iff_add_eq.mpr
      simpa [one_div, inv_pow, add_comm] using h.symm
    calc
      (∑' j : ℕ, Lambdaa * (1 / (p : ℝ)) ^ (j + 1)) =
          (∑' j : ℕ, (1 / (p : ℝ)) ^ (j + 1) * Lambdaa) := by
            apply tsum_congr
            intro j
            ring
      _ = (∑' j : ℕ, (1 / (p : ℝ)) ^ (j + 1)) * Lambdaa :=
        _root_.tsum_mul_right
      _ = ((1 - 1 / (p : ℝ))⁻¹ - 1) * Lambdaa := by rw [hshift]
      _ = Lambdaa / ((p : ℝ) - 1) := by
        have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0
        have hpmne : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp [hpne, hpmne]
        ring
  have hden_split : shiftDenominator a b p = 1 + ∑' j : ℕ, f (j + 1) := by
    rw [shiftDenominator, show (fun j => a (p ^ j) * b (p ^ j) / (p : ℝ) ^ j) = f from rfl,
      hf.tsum_eq_zero_add, hf0]
  refine
    { summable := hf
      lower := ?_
      upper_geometric := ?_
      upper_prime := ?_ }
  · rw [hden_split]
    exact le_add_of_nonneg_right (tsum_nonneg htail_nonneg)
  · rw [hden_split]
    linarith [htail_tsum, hgeom_value]
  · have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hfrac : 1 / ((p : ℝ) - 1) ≤ 2 / (p : ℝ) := by
      rw [div_le_div_iff₀ hpm1 hp0]
      nlinarith
    calc
      1 + Lambdaa / ((p : ℝ) - 1)
          = 1 + Lambdaa * (1 / ((p : ℝ) - 1)) := by ring
      _ ≤ 1 + Lambdaa * (2 / (p : ℝ)) := by
        gcongr
        exact ha.Lambda_pos.le
      _ = 1 + 2 * Lambdaa / (p : ℝ) := by ring

lemma numerator_term_nonnegative
    {a b : ArithmeticWeight} {ca Ca Lambdaa : ℝ}
    (ha : WeightTypeSpec a ca Ca Lambdaa) (hb : ModifierSpec b)
    {p i : ℕ} (hp : p.Prime) (hi : 1 ≤ i) (j : ℕ) :
    0 ≤ a (p ^ (i + j)) * b (p ^ j) * (1 + j * Real.log p) /
      (p : ℝ) ^ j := by
  have hai : 1 ≤ i + j := le_add_right hi
  have ha0 := (ha.prime_power_bounds p hp (i + j) hai).1
  have hb0 := (hb.prime_power_bounds p hp j).1
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  positivity

lemma numerator_summable
    {a b : ArithmeticWeight} {ca Ca Lambdaa : ℝ}
    (ha : WeightTypeSpec a ca Ca Lambdaa) (hb : ModifierSpec b)
    {p i : ℕ} (hp : p.Prime) (hi : 1 ≤ i) :
    Summable fun j : ℕ =>
      a (p ^ (i + j)) * b (p ^ j) * (1 + j * Real.log p) / (p : ℝ) ^ j := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  let r : ℝ := 1 / (p : ℝ)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    dsimp [r]
    rw [div_lt_one hp0]
    linarith
  have hgeom : Summable fun j : ℕ => r ^ j := summable_geometric_of_lt_one hr0 hr1
  have hrnorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hweighted : Summable fun j : ℕ => (j : ℝ) * r ^ j :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hrnorm).summable
  have hmajorant : Summable fun j : ℕ =>
      Lambdaa * (1 + (j : ℝ) * Real.log p) * r ^ j := by
    convert (hgeom.mul_left Lambdaa).add
      (hweighted.mul_left (Lambdaa * Real.log p)) using 1
    funext j
    ring
  refine .of_norm_bounded hmajorant ?_
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg (numerator_term_nonnegative ha hb hp hi j)]
  have hai : 1 ≤ i + j := le_add_right hi
  have haB := (ha.prime_power_bounds p hp (i + j) hai).2
  have hbB := (hb.prime_power_bounds p hp j).2
  have hb0 := (hb.prime_power_bounds p hp j).1
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  calc
    a (p ^ (i + j)) * b (p ^ j) * (1 + (j : ℝ) * Real.log p) /
        (p : ℝ) ^ j
        ≤ Lambdaa * 1 * (1 + (j : ℝ) * Real.log p) / (p : ℝ) ^ j := by
          gcongr
          exact ha.Lambda_pos.le
    _ = Lambdaa * (1 + (j : ℝ) * Real.log p) * r ^ j := by
      dsimp [r]
      simp [div_eq_mul_inv, inv_pow]

lemma shiftSpecification_of_weight_modifier
    {a b : ArithmeticWeight} {ca Ca Lambdaa : ℝ}
    (ha : WeightTypeSpec a ca Ca Lambdaa) (hb : ModifierSpec b) :
    ShiftSpecification a b := by
  have hadm : ShiftAdmissible a b := by
    refine
      { a_nonnegative_multiplicative := ha.nonnegative_multiplicative
        b_nonnegative_multiplicative := hb.nonnegative_multiplicative
        local_bounds := ?_
        numerator_summable := ?_
        denominator_summable := ?_
        denominator_positive := ?_ }
    · exact ⟨
        { cA := ca
          cA_pos := ha.c_pos
          CA := Ca
          CA_pos := ha.C_pos
          LambdaA := Lambdaa
          LambdaA_pos := ha.Lambda_pos
          a_one := ha.normalized
          a_type := ha.prime_power
          a_prime_power_bound := ha.prime_power_bounds
          b_one := hb.normalized
          b_prime_power_bound := hb.prime_power_bounds }⟩
    · intro p hp i hi
      exact numerator_summable ha hb hp hi
    · intro p hp
      exact denominator_summable ha hb hp
    · intro p hp
      exact lt_of_lt_of_le (by norm_num) (p051B a ca Ca Lambdaa ha b hb p hp).lower
  have hlocal_nonneg : ∀ p : ℕ, p.Prime → ∀ i : ℕ, 1 ≤ i →
      0 ≤ localShift a b p i := by
    intro p hp i hi
    exact div_nonneg
      (tsum_nonneg fun j => numerator_term_nonnegative ha hb hp hi j)
      (le_of_lt (hadm.denominator_positive p hp))
  refine
    { admissible := hadm
      shift_nonnegative_multiplicative := ?_
      maxShift_nonnegative_multiplicative := ?_
      shift_prime_power := ?_
      maxShift_prime_power := ?_ }
  · exact multiplicativeExtension_weight _ hlocal_nonneg
  · apply multiplicativeExtension_weight
    intro p hp i hi
    exact le_max_of_le_left (hlocal_nonneg p hp i hi)
  · intro p hp i hi
    exact multiplicativeExtension_prime_pow _ hp hi
  · intro p hp i hi
    simpa [maxShift] using (multiplicativeExtension_prime_pow
      (fun p i => max (localShift a b p i) (a (p ^ i))) hp hi)

lemma numerator_tail_bound
    {a b : ArithmeticWeight} {ca Ca Lambdaa : ℝ}
    (ha : WeightTypeSpec a ca Ca Lambdaa) (hb : ModifierSpec b)
    {p i : ℕ} (hp : p.Prime) (hi : 1 ≤ i) :
    (∑' j : ℕ,
        a (p ^ (i + (j + 1))) * b (p ^ (j + 1)) *
          (1 + (j + 1) * Real.log p) / (p : ℝ) ^ (j + 1)) ≤
      Lambdaa *
        (1 / ((p : ℝ) - 1) + (p : ℝ) * Real.log p / ((p : ℝ) - 1) ^ 2) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  let r : ℝ := 1 / (p : ℝ)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    dsimp [r]
    rw [div_lt_one hp0]
    linarith
  have hrnorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hgeom : Summable fun j : ℕ => r ^ j := summable_geometric_of_lt_one hr0 hr1
  have hweighted : Summable fun j : ℕ => (j : ℝ) * r ^ j :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hrnorm).summable
  have hgeomShift : Summable fun j : ℕ => r ^ (j + 1) :=
    hgeom.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hweightedShift : Summable fun j : ℕ => ((j + 1 : ℕ) : ℝ) * r ^ (j + 1) :=
    hweighted.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  let f : ℕ → ℝ := fun j =>
    a (p ^ (i + (j + 1))) * b (p ^ (j + 1)) *
      (1 + (j + 1) * Real.log p) / (p : ℝ) ^ (j + 1)
  let g : ℕ → ℝ := fun j =>
    Lambdaa * (1 + ((j + 1 : ℕ) : ℝ) * Real.log p) * r ^ (j + 1)
  have hg : Summable g := by
    dsimp [g]
    convert (hgeomShift.mul_left Lambdaa).add
      (hweightedShift.mul_left (Lambdaa * Real.log p)) using 1
    funext j
    push_cast
    ring
  have hfg : ∀ j : ℕ, f j ≤ g j := by
    intro j
    have hai : 1 ≤ i + (j + 1) := by omega
    have haB := (ha.prime_power_bounds p hp _ hai).2
    have hbB := (hb.prime_power_bounds p hp (j + 1)).2
    have hb0 := (hb.prime_power_bounds p hp (j + 1)).1
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    calc
      f j ≤ Lambdaa * 1 * (1 + ((j + 1 : ℕ) : ℝ) * Real.log p) /
          (p : ℝ) ^ (j + 1) := by
            dsimp [f]
            push_cast
            gcongr
            exact ha.Lambda_pos.le
      _ = g j := by
        dsimp [g, r]
        simp [div_eq_mul_inv, inv_pow]
  have hf : Summable f := by
    refine Summable.of_nonneg_of_le ?_ hfg hg
    intro j
    dsimp [f]
    simpa only [Nat.cast_add, Nat.cast_one] using
      numerator_term_nonnegative ha hb hp hi (j + 1)
  have hsum_le : (∑' j : ℕ, f j) ≤ ∑' j : ℕ, g j := hf.tsum_le_tsum hfg hg
  have hgeomShiftValue : (∑' j : ℕ, r ^ (j + 1)) =
      (1 - r)⁻¹ - 1 := by
    have h := hgeom.tsum_eq_zero_add
    rw [tsum_geometric_of_lt_one hr0 hr1] at h
    apply eq_sub_iff_add_eq.mpr
    simpa [add_comm] using h.symm
  have hweightedShiftValue :
      (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * r ^ (j + 1)) =
        r / (1 - r) ^ 2 := by
    have h := hweighted.tsum_eq_zero_add
    rw [tsum_coe_mul_geometric_of_norm_lt_one hrnorm] at h
    norm_num at h
    simpa using h.symm
  have hgValue : (∑' j : ℕ, g j) =
      Lambdaa *
        (1 / ((p : ℝ) - 1) + (p : ℝ) * Real.log p / ((p : ℝ) - 1) ^ 2) := by
    calc
      (∑' j : ℕ, g j) =
          ∑' j : ℕ, (Lambdaa * r ^ (j + 1) +
            (Lambdaa * Real.log p) * (((j + 1 : ℕ) : ℝ) * r ^ (j + 1))) := by
              apply tsum_congr
              intro j
              dsimp [g]
              ring
      _ = (∑' j : ℕ, Lambdaa * r ^ (j + 1)) +
          ∑' j : ℕ, (Lambdaa * Real.log p) *
            (((j + 1 : ℕ) : ℝ) * r ^ (j + 1)) := by
              exact (hgeomShift.mul_left Lambdaa).tsum_add
                (hweightedShift.mul_left (Lambdaa * Real.log p))
      _ = Lambdaa * (∑' j : ℕ, r ^ (j + 1)) +
          (Lambdaa * Real.log p) *
            ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) * r ^ (j + 1) := by
              congr 1
              · exact _root_.tsum_mul_left
              · exact _root_.tsum_mul_left
      _ = Lambdaa * ((1 - r)⁻¹ - 1) +
          (Lambdaa * Real.log p) * (r / (1 - r) ^ 2) := by
              rw [hgeomShiftValue, hweightedShiftValue]
      _ = Lambdaa *
          (1 / ((p : ℝ) - 1) + (p : ℝ) * Real.log p / ((p : ℝ) - 1) ^ 2) := by
            dsimp [r]
            have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0
            have hpmne : (p : ℝ) - 1 ≠ 0 := by linarith
            field_simp [hpne, hpmne]
            ring
  simpa [f] using hsum_le.trans_eq hgValue

lemma inv_le_rpow_neg_half {x : ℝ} (hx : 1 ≤ x) :
    1 / x ≤ x ^ (-(1 / 2 : ℝ)) := by
  simpa [one_div, Real.rpow_neg_one] using
    (Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (-1 : ℝ) ≤ -(1 / 2 : ℝ)))

lemma log_div_le_two_rpow_neg_half {x : ℝ} (hx : 1 ≤ x) :
    Real.log x / x ≤ 2 * x ^ (-(1 / 2 : ℝ)) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlog := Real.log_le_rpow_div (x := x) hx0.le (by norm_num : (0 : ℝ) < 1 / 2)
  calc
    Real.log x / x ≤ (x ^ (1 / 2 : ℝ) / (1 / 2 : ℝ)) / x := by
      exact div_le_div_of_nonneg_right hlog hx0.le
    _ = 2 * x ^ (-(1 / 2 : ℝ)) := by
      calc
        (x ^ (1 / 2 : ℝ) / (1 / 2 : ℝ)) / x =
            2 * (x ^ (1 / 2 : ℝ) * x ^ (-1 : ℝ)) := by
              rw [div_eq_mul_inv, ← Real.rpow_neg_one]
              norm_num
              ring
        _ = 2 * x ^ (-(1 / 2 : ℝ)) := by
          rw [← Real.rpow_add hx0]
          norm_num

lemma numerator_tail_uniform_bound
    {a b : ArithmeticWeight} {ca Ca Lambdaa : ℝ}
    (ha : WeightTypeSpec a ca Ca Lambdaa) (hb : ModifierSpec b)
    {p i : ℕ} (hp : p.Prime) (hi : 1 ≤ i) :
    (∑' j : ℕ,
        a (p ^ (i + (j + 1))) * b (p ^ (j + 1)) *
          (1 + (j + 1) * Real.log p) / (p : ℝ) ^ (j + 1)) ≤
      10 * Lambdaa * (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hfrac1 : 1 / ((p : ℝ) - 1) ≤ 2 / (p : ℝ) := by
    rw [div_le_div_iff₀ hpm1 hp0]
    nlinarith
  have hfrac2 : (p : ℝ) / ((p : ℝ) - 1) ^ 2 ≤ 4 / (p : ℝ) := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hpm1) hp0]
    nlinarith [sq_nonneg ((p : ℝ) - 2)]
  have hinv := inv_le_rpow_neg_half (show (1 : ℝ) ≤ p by linarith)
  have hlog := log_div_le_two_rpow_neg_half (show (1 : ℝ) ≤ p by linarith)
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hinside :
      1 / ((p : ℝ) - 1) + (p : ℝ) * Real.log p / ((p : ℝ) - 1) ^ 2 ≤
        10 * (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
    calc
      1 / ((p : ℝ) - 1) + (p : ℝ) * Real.log p / ((p : ℝ) - 1) ^ 2
          = 1 / ((p : ℝ) - 1) + Real.log p *
              ((p : ℝ) / ((p : ℝ) - 1) ^ 2) := by ring
      _ ≤ 2 / (p : ℝ) + Real.log p * (4 / (p : ℝ)) := by
        gcongr
      _ = 2 * (1 / (p : ℝ)) + 4 * (Real.log p / (p : ℝ)) := by ring
      _ ≤ 2 * (p : ℝ) ^ (-(1 / 2 : ℝ)) +
          4 * (2 * (p : ℝ) ^ (-(1 / 2 : ℝ))) := by gcongr
      _ = 10 * (p : ℝ) ^ (-(1 / 2 : ℝ)) := by ring
  exact (numerator_tail_bound ha hb hp hi).trans <| by
    calc
      Lambdaa *
          (1 / ((p : ℝ) - 1) + (p : ℝ) * Real.log p / ((p : ℝ) - 1) ^ 2)
          ≤ Lambdaa * (10 * (p : ℝ) ^ (-(1 / 2 : ℝ))) := by
            gcongr
            exact ha.Lambda_pos.le
      _ = 10 * Lambdaa * (p : ℝ) ^ (-(1 / 2 : ℝ)) := by ring

theorem p051C : P051CStatement := by
  intro a ca Ca Lambdaa ha
  let csh : ℝ := min ca (1 / 2)
  let Csh : ℝ := Ca + 10 * Lambdaa + 2 * Lambdaa ^ 2
  let Lambdash : ℝ := 1 + Csh
  have hcsh : 0 < csh := by
    dsimp [csh]
    exact lt_min ha.c_pos (by norm_num)
  have hCsh : 0 < Csh := by
    dsimp [Csh]
    nlinarith [ha.C_pos, ha.Lambda_pos, sq_nonneg Lambdaa]
  have hLambdash : 0 < Lambdash := by dsimp [Lambdash]; linarith
  refine ⟨csh, Csh, Lambdash, rfl, hcsh, hCsh, hLambdash, ?_⟩
  intro b hb
  let hspec : ShiftSpecification a b := shiftSpecification_of_weight_modifier ha hb
  refine ⟨hspec, ?_⟩
  have hprime : ∀ p : ℕ, p.Prime → ∀ i : ℕ, 1 ≤ i →
      |shift a b (p ^ i) - 1 / (i + 1 : ℕ)| ≤ Csh * (p : ℝ).rpow (-csh) := by
    intro p hp i hi
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    have hp1 : (1 : ℝ) ≤ p := by linarith
    let fd : ℕ → ℝ := fun j => a (p ^ j) * b (p ^ j) / (p : ℝ) ^ j
    let fn : ℕ → ℝ := fun j =>
      a (p ^ (i + j)) * b (p ^ j) * (1 + j * Real.log p) / (p : ℝ) ^ j
    let U : ℝ := ∑' j : ℕ, fd (j + 1)
    let T : ℝ := ∑' j : ℕ, fn (j + 1)
    have hfd : Summable fd := denominator_summable ha hb hp
    have hfn : Summable fn := numerator_summable ha hb hp hi
    have hU0 : 0 ≤ U := tsum_nonneg fun j => denominator_term_nonnegative ha hb hp (j + 1)
    have hT0 : 0 ≤ T := tsum_nonneg fun j => by
      dsimp [fn]
      simpa only [Nat.cast_add, Nat.cast_one] using
        numerator_term_nonnegative ha hb hp hi (j + 1)
    have hD : shiftDenominator a b p = 1 + U := by
      rw [shiftDenominator,
        show (fun j => a (p ^ j) * b (p ^ j) / (p : ℝ) ^ j) = fd from rfl,
        hfd.tsum_eq_zero_add]
      simp [fd, U, ha.normalized, hb.normalized]
    have hN : shiftNumerator a b p i = a (p ^ i) + T := by
      rw [shiftNumerator,
        show (fun j => a (p ^ (i + j)) * b (p ^ j) *
          (1 + j * Real.log p) / (p : ℝ) ^ j) = fn from rfl,
        hfn.tsum_eq_zero_add]
      simp [fn, T, ha.normalized, hb.normalized]
    have hDlower := (p051B a ca Ca Lambdaa ha b hb p hp).lower
    have hDpos : 0 < shiftDenominator a b p := lt_of_lt_of_le (by norm_num) hDlower
    have hUbound : U ≤ 2 * Lambdaa * (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
      have hUpper := (p051B a ca Ca Lambdaa ha b hb p hp).upper_geometric
      have hfrac : 1 / ((p : ℝ) - 1) ≤ 2 / (p : ℝ) := by
        have hp0 : (0 : ℝ) < p := by linarith
        have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
        rw [div_le_div_iff₀ hpm1 hp0]
        nlinarith
      have hinv := inv_le_rpow_neg_half hp1
      rw [hD] at hUpper
      calc
        U ≤ Lambdaa / ((p : ℝ) - 1) := by linarith
        _ = Lambdaa * (1 / ((p : ℝ) - 1)) := by ring
        _ ≤ Lambdaa * (2 / (p : ℝ)) := by gcongr; exact ha.Lambda_pos.le
        _ = 2 * Lambdaa * (1 / (p : ℝ)) := by ring
        _ ≤ 2 * Lambdaa * (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hinv (by nlinarith [ha.Lambda_pos])
    have hTbound : T ≤ 10 * Lambdaa * (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
      simpa [T, fn, Nat.cast_add, Nat.cast_one, add_assoc] using
        numerator_tail_uniform_bound ha hb hp hi
    have hai0 := (ha.prime_power_bounds p hp i hi).1
    have haiB := (ha.prime_power_bounds p hp i hi).2
    have herrLocal : |localShift a b p i - a (p ^ i)| ≤ T + a (p ^ i) * U := by
      have hform : localShift a b p i - a (p ^ i) =
          (T - a (p ^ i) * U) / shiftDenominator a b p := by
        rw [localShift, hN, hD]
        field_simp [ne_of_gt hDpos]
        ring
      rw [hform, abs_div, abs_of_pos hDpos]
      calc
        |T - a (p ^ i) * U| / shiftDenominator a b p
            ≤ (T + a (p ^ i) * U) / shiftDenominator a b p := by
              gcongr
              simpa [abs_of_nonneg hT0, abs_of_nonneg (mul_nonneg hai0 hU0)] using
                (abs_sub T (a (p ^ i) * U))
        _ ≤ T + a (p ^ i) * U := div_le_self
          (add_nonneg hT0 (mul_nonneg hai0 hU0)) hDlower
    have hrateA : (p : ℝ) ^ (-ca) ≤ (p : ℝ) ^ (-csh) := by
      apply Real.rpow_le_rpow_of_exponent_le hp1
      dsimp [csh]
      exact neg_le_neg (min_le_left _ _)
    have hrateHalf : (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (p : ℝ) ^ (-csh) := by
      apply Real.rpow_le_rpow_of_exponent_le hp1
      dsimp [csh]
      exact neg_le_neg (min_le_right _ _)
    have hinput := ha.prime_power p hp i hi
    calc
      |shift a b (p ^ i) - 1 / (i + 1 : ℕ)| =
          |localShift a b p i - 1 / (i + 1 : ℕ)| := by rw [hspec.shift_prime_power p hp i hi]
      _ ≤ |localShift a b p i - a (p ^ i)| +
          |a (p ^ i) - 1 / (i + 1 : ℕ)| := by
            apply abs_le.mpr
            constructor
            · nlinarith [neg_abs_le (localShift a b p i - a (p ^ i)),
                neg_abs_le (a (p ^ i) - 1 / (i + 1 : ℕ))]
            · nlinarith [le_abs_self (localShift a b p i - a (p ^ i)),
                le_abs_self (a (p ^ i) - 1 / (i + 1 : ℕ))]
      _ ≤ (T + a (p ^ i) * U) + Ca * (p : ℝ) ^ (-ca) := by
        exact add_le_add herrLocal hinput
      _ ≤ (10 * Lambdaa + 2 * Lambdaa ^ 2) *
          (p : ℝ) ^ (-(1 / 2 : ℝ)) + Ca * (p : ℝ) ^ (-ca) := by
            have hr0 := Real.rpow_nonneg (Nat.cast_nonneg p) (-(1 / 2 : ℝ))
            nlinarith [mul_le_mul_of_nonneg_left hUbound hai0,
              mul_le_mul_of_nonneg_right haiB hU0]
      _ ≤ (10 * Lambdaa + 2 * Lambdaa ^ 2) * (p : ℝ) ^ (-csh) +
          Ca * (p : ℝ) ^ (-csh) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hrateHalf (by
                nlinarith [ha.Lambda_pos, sq_nonneg Lambdaa])
            · exact mul_le_mul_of_nonneg_left hrateA ha.C_pos.le
      _ = Csh * (p : ℝ) ^ (-csh) := by dsimp [Csh]; ring
  refine
    { c_pos := hcsh
      C_pos := hCsh
      Lambda_pos := hLambdash
      nonnegative_multiplicative := hspec.shift_nonnegative_multiplicative
      normalized := hspec.shift_nonnegative_multiplicative.multiplicative.1
      prime_power := hprime
      prime_power_bounds := ?_ }
  intro p hp i hi
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have hnonneg := hspec.shift_nonnegative_multiplicative.nonnegative (p ^ i)
    (pow_pos hp.pos i)
  have herr := hprime p hp i hi
  constructor
  · exact hnonneg
  · have hmain : (1 / (i + 1 : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]
      norm_num
    have hrate : (p : ℝ) ^ (-csh) ≤ 1 := by
      exact Real.rpow_le_one_of_one_le_of_nonpos hp1 (neg_nonpos.mpr hcsh.le)
    rw [abs_sub_le_iff] at herr
    have hprod : Csh * (p : ℝ) ^ (-csh) ≤ Csh := by
      calc
        Csh * (p : ℝ) ^ (-csh) ≤ Csh * 1 :=
          mul_le_mul_of_nonneg_left hrate hCsh.le
        _ = Csh := by ring
    calc
      shift a b (p ^ i) ≤ 1 / (i + 1 : ℕ) + Csh * (p : ℝ) ^ (-csh) := by
        exact sub_le_iff_le_add'.mp herr.1
      _ ≤ 1 + Csh := add_le_add hmain hprod
      _ = Lambdash := by rfl

lemma abs_max_sub_le {x y m E : ℝ}
    (hx : |x - m| ≤ E) (hy : |y - m| ≤ E) :
    |max x y - m| ≤ E := by
  rw [abs_sub_le_iff] at hx hy ⊢
  constructor
  · apply sub_le_iff_le_add'.mpr
    exact max_le (sub_le_iff_le_add'.mp hx.1) (sub_le_iff_le_add'.mp hy.1)
  · exact (sub_le_sub_left (le_max_left x y) m).trans hx.2

theorem p051D : P051DStatement := by
  intro a b ca Ca Lambdaa csh Csh Lambdash ha hb hspec hshiftType
  have hc : 0 < min ca csh := lt_min ha.c_pos hshiftType.c_pos
  have hC : 0 < max Ca Csh := lt_max_of_lt_left ha.C_pos
  have hLambda : 0 < max Lambdaa Lambdash := lt_max_of_lt_left ha.Lambda_pos
  refine ⟨?_, ?_⟩
  · refine
      { c_pos := hc
        C_pos := hC
        Lambda_pos := hLambda
        nonnegative_multiplicative := hspec.maxShift_nonnegative_multiplicative
        normalized := hspec.maxShift_nonnegative_multiplicative.multiplicative.1
        prime_power := ?_
        prime_power_bounds := ?_ }
    · intro p hp i hi
      have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
      have hrateA : (p : ℝ) ^ (-ca) ≤ (p : ℝ) ^ (-(min ca csh)) := by
        exact Real.rpow_le_rpow_of_exponent_le hpR (neg_le_neg (min_le_left _ _))
      have hrateS : (p : ℝ) ^ (-csh) ≤ (p : ℝ) ^ (-(min ca csh)) := by
        exact Real.rpow_le_rpow_of_exponent_le hpR (neg_le_neg (min_le_right _ _))
      have hAe : Ca * (p : ℝ) ^ (-ca) ≤
          max Ca Csh * (p : ℝ) ^ (-(min ca csh)) := by
        calc
          Ca * (p : ℝ) ^ (-ca) ≤ max Ca Csh * (p : ℝ) ^ (-ca) := by
            exact mul_le_mul_of_nonneg_right (le_max_left _ _)
              (Real.rpow_nonneg (Nat.cast_nonneg p) _)
          _ ≤ max Ca Csh * (p : ℝ) ^ (-(min ca csh)) := by
            exact mul_le_mul_of_nonneg_left hrateA hC.le
      have hSe : Csh * (p : ℝ) ^ (-csh) ≤
          max Ca Csh * (p : ℝ) ^ (-(min ca csh)) := by
        calc
          Csh * (p : ℝ) ^ (-csh) ≤ max Ca Csh * (p : ℝ) ^ (-csh) := by
            exact mul_le_mul_of_nonneg_right (le_max_right _ _)
              (Real.rpow_nonneg (Nat.cast_nonneg p) _)
          _ ≤ max Ca Csh * (p : ℝ) ^ (-(min ca csh)) := by
            exact mul_le_mul_of_nonneg_left hrateS hC.le
      rw [hspec.maxShift_prime_power p hp i hi]
      have hlocal := hshiftType.prime_power p hp i hi
      rw [hspec.shift_prime_power p hp i hi] at hlocal
      exact abs_max_sub_le (hlocal.trans hSe) ((ha.prime_power p hp i hi).trans hAe)
    · intro p hp i hi
      rw [hspec.maxShift_prime_power p hp i hi]
      have hlocal0 := hshiftType.prime_power_bounds p hp i hi
      rw [hspec.shift_prime_power p hp i hi] at hlocal0
      have ha0 := ha.prime_power_bounds p hp i hi
      exact ⟨le_max_of_le_left hlocal0.1,
        max_le (hlocal0.2.trans (le_max_right _ _))
          (ha0.2.trans (le_max_left _ _))⟩
  · intro K hK
    constructor
    · rw [multiplicative_weight_eq_extension _
          hspec.shift_nonnegative_multiplicative.multiplicative hK]
      simpa [maxShift] using
        (multiplicativeExtension_mono
          (fun p i => shift a b (p ^ i))
          (fun p i => max (localShift a b p i) (a (p ^ i))) hK
          (fun p hp i hi => hspec.shift_nonnegative_multiplicative.nonnegative _
            (pow_pos hp.pos i))
          (fun p hp i hi => by
            change shift a b (p ^ i) ≤ max (localShift a b p i) (a (p ^ i))
            rw [hspec.shift_prime_power p hp i hi]
            exact le_max_left _ _))
    · simpa [maxShift] using
        (weight_le_extension a ha.nonnegative_multiplicative
          (fun p i => max (localShift a b p i) (a (p ^ i))) hK
          (fun p hp i hi => le_max_right _ _))

theorem p051E : P051EStatement := by
  intro a1 a2 c C Lambda h1 h2
  let m : ArithmeticWeight :=
    multiplicativeExtension fun p i => max (a1 (p ^ i)) (a2 (p ^ i))
  have hmWeight : NonnegativeMultiplicativeWeight m := by
    dsimp [m]
    apply multiplicativeExtension_weight
    intro p hp i hi
    exact le_max_of_le_left (h1.prime_power_bounds p hp i hi).1
  have hmPrime : ∀ p : ℕ, p.Prime → ∀ i : ℕ, 1 ≤ i →
      m (p ^ i) = max (a1 (p ^ i)) (a2 (p ^ i)) := by
    intro p hp i hi
    exact multiplicativeExtension_prime_pow _ hp hi
  refine ⟨?_, hmPrime, ?_⟩
  · refine
      { c_pos := h1.c_pos
        C_pos := h1.C_pos
        Lambda_pos := h1.Lambda_pos
        nonnegative_multiplicative := hmWeight
        normalized := hmWeight.multiplicative.1
        prime_power := ?_
        prime_power_bounds := ?_ }
    · intro p hp i hi
      change |m (p ^ i) - 1 / (i + 1 : ℕ)| ≤ C * (p : ℝ).rpow (-c)
      rw [hmPrime p hp i hi]
      exact abs_max_sub_le (h1.prime_power p hp i hi) (h2.prime_power p hp i hi)
    · intro p hp i hi
      change 0 ≤ m (p ^ i) ∧ m (p ^ i) ≤ Lambda
      rw [hmPrime p hp i hi]
      have h1b := h1.prime_power_bounds p hp i hi
      have h2b := h2.prime_power_bounds p hp i hi
      exact ⟨le_max_of_le_left h1b.1, max_le h1b.2 h2b.2⟩
  · intro K hK
    constructor
    · simpa [m] using
        (weight_le_extension a1 h1.nonnegative_multiplicative
          (fun p i => max (a1 (p ^ i)) (a2 (p ^ i))) hK
          (fun p hp i hi => le_max_left _ _))
    · simpa [m] using
        (weight_le_extension a2 h2.nonnegative_multiplicative
          (fun p i => max (a1 (p ^ i)) (a2 (p ^ i))) hK
          (fun p hp i hi => le_max_right _ _))

/-- Recovery-local mirror of the historical CU exports structure
(field-identical). It rebinds the downstream recovered construction without
the retired CU contract surface. -/
structure P051AEExports : Prop where
  p051A : P051AStatement
  p051B : P051BStatement
  p051C : P051CStatement
  p051D : P051DStatement
  p051E : P051EStatement

/-- The recovered construction, assembled exactly as the verified CU proof
assembled its exports. -/
@[expose] def recoveredExports : P051AEExports :=
  { p051A := p051A
    p051B := p051B
    p051C := p051C
    p051D := p051D
    p051E := p051E }

theorem node_p051A : P051AStatement := recoveredExports.p051A
theorem node_p051B : P051BStatement := recoveredExports.p051B
theorem node_p051C : P051CStatement := recoveredExports.p051C
theorem node_p051D : P051DStatement := recoveredExports.p051D
theorem node_p051E : P051EStatement := recoveredExports.p051E

end

end Erdos448.Stage7.ROOT05.Recovered.P051AE
