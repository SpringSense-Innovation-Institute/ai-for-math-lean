module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-05».recovered.P051AE

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT05.Recovered.P051VF4

open Finset Set
open scoped BigOperators NNReal

noncomputable section

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Erdos448.Stage6.TaskContracts

theorem p051B : P051BStatement :=
  Erdos448.Stage7.ROOT05.Recovered.P051AE.node_p051B

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

theorem shiftStabilityExplicit
    (a : ArithmeticWeight) (ca Ca Lambdaa : ℝ)
    (ha : WeightTypeSpec a ca Ca Lambdaa)
    (b : ArithmeticWeight) (hb : ModifierSpec b) :
    ShiftSpecification a b ∧
      WeightTypeSpec (shift a b)
        (min ca (1 / 2))
        (Ca + 10 * Lambdaa + 2 * Lambdaa ^ 2)
        (1 + (Ca + 10 * Lambdaa + 2 * Lambdaa ^ 2)) := by
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

lemma omegaBelowRaw_mul_of_coprime
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (u : ℝ) :
    omegaBelowRaw (a * b) u = omegaBelowRaw a u + omegaBelowRaw b u := by
  have ha0 : a ≠ 0 := Nat.ne_of_gt ha
  have hb0 : b ≠ 0 := Nat.ne_of_gt hb
  simp only [omegaBelowRaw, dif_pos ha, dif_pos hb, dif_pos (Nat.mul_pos ha hb), omegaBelow]
  rw [hab.primeFactors_mul,
    Finset.sum_union ((Nat.disjoint_primeFactors ha0 hb0).2 hab)]
  congr 1
  · apply Finset.sum_congr rfl
    intro p hp
    by_cases hpu : (p : ℝ) < u
    · simp only [hpu, if_true]
      exact Nat.factorization_eq_of_coprime_left hab (List.mem_toFinset.mp hp)
    · simp only [hpu, if_false]
  · apply Finset.sum_congr rfl
    intro p hp
    by_cases hpu : (p : ℝ) < u
    · simp only [hpu, if_true]
      exact Nat.factorization_eq_of_coprime_right hab (List.mem_toFinset.mp hp)
    · simp only [hpu, if_false]

lemma isRough_mul_iff (a b : ℕ) (s : ℝ) :
    IsRough (a * b) s ↔ IsRough a s ∧ IsRough b s := by
  constructor
  · intro h
    constructor
    · intro p hp hpa
      exact h p hp (dvd_mul_of_dvd_left hpa b)
    · intro p hp hpb
      exact h p hp (dvd_mul_of_dvd_right hpb a)
  · rintro ⟨ha, hb⟩ p hp hpab
    rcases hp.dvd_mul.mp hpab with hpa | hpb
    · exact ha p hp hpa
    · exact hb p hp hpb

lemma roughIndicator_mul (a b : ℕ) (s : ℝ) :
    roughIndicator (a * b) s = roughIndicator a s * roughIndicator b s := by
  by_cases ha : IsRough a s
  · by_cases hb : IsRough b s
    · have hab : IsRough (a * b) s := (isRough_mul_iff a b s).2 ⟨ha, hb⟩
      simp [roughIndicator, ha, hb, hab]
    · have hab : ¬IsRough (a * b) s := fun h => hb ((isRough_mul_iff a b s).1 h).2
      simp [roughIndicator, ha, hb, hab]
  · by_cases hb : IsRough b s
    · have hab : ¬IsRough (a * b) s := fun h => ha ((isRough_mul_iff a b s).1 h).1
      simp [roughIndicator, ha, hb, hab]
    · have hab : ¬IsRough (a * b) s := fun h => ha ((isRough_mul_iff a b s).1 h).1
      simp [roughIndicator, ha, hb, hab]

theorem p051V : P051VStatement := by
  intro q
  refine
    { nonnegative_multiplicative := ?_
      normalized := ?_
      prime_power_bounds := ?_ }
  · refine ⟨?_, ?_⟩
    · intro n hn
      simp only [modifierWeight, if_pos hn]
      exact mul_nonneg (Real.rpow_nonneg q.y_pos.le _)
        (Nat.cast_nonneg (roughIndicator n q.sigma))
    · refine ⟨?_, ?_⟩
      · have hrough1 : IsRough 1 q.sigma := by
          intro p hp hpd
          have hp1 : p = 1 := Nat.dvd_one.mp hpd
          subst p
          exact (Nat.not_prime_one hp).elim
        simp [modifierWeight, omegaBelowRaw, omegaBelow, roughIndicator, hrough1]
      · intro a b ha hb hab
        simp only [modifierWeight, if_pos ha, if_pos hb, if_pos (Nat.mul_pos ha hb)]
        rw [omegaBelowRaw_mul_of_coprime ha hb hab, Nat.cast_add]
        have hyadd :
            q.y.rpow ((omegaBelowRaw a (q.theta ^ q.k) : ℝ) +
              (omegaBelowRaw b (q.theta ^ q.k) : ℝ)) =
              q.y.rpow (omegaBelowRaw a (q.theta ^ q.k) : ℝ) *
                q.y.rpow (omegaBelowRaw b (q.theta ^ q.k) : ℝ) := by
          exact Real.rpow_add q.y_pos _ _
        rw [hyadd, roughIndicator_mul]
        push_cast
        ring
  · have hrough1 : IsRough 1 q.sigma := by
      intro p hp hpd
      have hp1 : p = 1 := Nat.dvd_one.mp hpd
      subst p
      exact (Nat.not_prime_one hp).elim
    simp [modifierWeight, omegaBelowRaw, omegaBelow, roughIndicator, hrough1]
  · intro p hp j
    have hpj : 0 < p ^ j := pow_pos hp.pos j
    simp only [modifierWeight, if_pos hpj]
    have hy0 : 0 ≤ q.y.rpow (omegaBelowRaw (p ^ j) (q.theta ^ q.k) : ℝ) :=
      Real.rpow_nonneg q.y_pos.le _
    have hy1 : q.y.rpow (omegaBelowRaw (p ^ j) (q.theta ^ q.k) : ℝ) ≤ 1 :=
      Real.rpow_le_one q.y_pos.le q.y_lt_one.le (Nat.cast_nonneg _)
    unfold roughIndicator
    split_ifs <;> simp_all

theorem p051F1
    (upstream : P051AE.P051AEExports) : P051F1Statement := by
  rcases upstream.p051A with ⟨ha0, _⟩
  have hone : ModifierSpec oneWeight := by
    refine
      { nonnegative_multiplicative := ?_
        normalized := ?_
        prime_power_bounds := ?_ }
    · exact ⟨by simp [NonnegativeWeight, oneWeight],
        by simp [MultiplicativeWeight, oneWeight]⟩
    · simp [oneWeight]
    · simp [oneWeight]
  rcases upstream.p051C a0Weight 1 1 1 ha0 with
    ⟨csh, Csh, Lambdash, _, _, _, _, hshift⟩
  rcases hshift oneWeight hone with ⟨hspec, hshiftType⟩
  rcases upstream.p051D a0Weight oneWeight 1 1 1 csh Csh Lambdash
      ha0 hone hspec hshiftType with ⟨hmaxType, hdom⟩
  refine ⟨min 1 csh, max 1 Csh, max 1 Lambdash, ?_, hspec, ?_⟩
  · simpa [w1Weight] using hmaxType
  · intro K hK
    have h := hdom K hK
    simpa [w1Weight] using And.intro h.2 h.1

theorem p051F2
    (upstream : P051AE.P051AEExports) : P051F2Statement := by
  intro c1 C1 Lambda1 hw1
  rcases upstream.p051C w1Weight c1 C1 Lambda1 hw1 with
    ⟨csh, Csh, Lambdash, _, hcsh, hCsh, hLambdash, hshift⟩
  refine ⟨min c1 csh, max C1 Csh, max Lambda1 Lambdash,
    lt_min hw1.c_pos hcsh, lt_max_of_lt_left hw1.C_pos,
    lt_max_of_lt_left hw1.Lambda_pos, ?_⟩
  intro q
  have hmodifier := p051V q
  rcases hshift (modifierWeight q) hmodifier with ⟨hspec, hshiftType⟩
  rcases upstream.p051D w1Weight (modifierWeight q)
      c1 C1 Lambda1 csh Csh Lambdash hw1 hmodifier hspec hshiftType with
    ⟨hmaxType, hdom⟩
  refine ⟨hmodifier, hspec, ?_, ?_⟩
  · simpa [w2Weight] using hmaxType
  · intro K hK
    have h := hdom K hK
    simpa [w2Weight] using And.intro h.2 h.1

theorem p051F3
    (upstream : P051AE.P051AEExports) : P051F3Statement := by
  intro c C Lambda hw1 hw2 q
  simpa [w3Weight] using upstream.p051E w1Weight (w2Weight q) c C Lambda hw1 (hw2 q)

theorem p051F4
    (upstream : P051AE.P051AEExports) : P051F4Statement := by
  intro c3 C3 Lambda3 hw3
  let csh : ℝ := min c3 (1 / 2)
  let Csh : ℝ := C3 + 10 * Lambda3 + 2 * Lambda3 ^ 2
  let Lambdash : ℝ := 1 + Csh
  let q0 : WeightParameters :=
    { theta := 2
      theta_ge_two := le_rfl
      y := 1 / 2
      y_pos := by norm_num
      y_lt_one := by norm_num
      k := 1
      k_pos := le_rfl
      sigma := 2
      sigma_ge_theta := le_rfl }
  have hbase := hw3 q0
  refine ⟨min c3 csh, max C3 Csh, max Lambda3 Lambdash,
    lt_min hbase.c_pos (by
      dsimp [csh]
      exact lt_min hbase.c_pos (by norm_num)),
    lt_max_of_lt_left hbase.C_pos,
    lt_max_of_lt_left hbase.Lambda_pos, ?_⟩
  intro q
  have hmodifier := p051V q
  have hshift := shiftStabilityExplicit (w3Weight q) c3 C3 Lambda3 (hw3 q)
    (modifierWeight q) hmodifier
  rcases hshift with ⟨hspec, hshiftType⟩
  rcases upstream.p051D (w3Weight q) (modifierWeight q)
      c3 C3 Lambda3 csh Csh Lambdash (hw3 q) hmodifier hspec hshiftType with
    ⟨hmaxType, hdom⟩
  refine ⟨hspec, ?_, ?_⟩
  · simpa [csh, Csh, Lambdash, w4Weight] using hmaxType
  · intro K hK
    have h := hdom K hK
    simpa [w4Weight] using And.intro h.2 h.1

lemma weightTypeSpec_weaken
    {w : ArithmeticWeight} {c C Lambda c' C' Lambda' : ℝ}
    (h : WeightTypeSpec w c C Lambda)
    (hc' : 0 < c') (hcc : c' ≤ c)
    (hC' : 0 < C') (hCC : C ≤ C')
    (hLambda' : 0 < Lambda') (hLL : Lambda ≤ Lambda') :
    WeightTypeSpec w c' C' Lambda' := by
  refine
    { c_pos := hc'
      C_pos := hC'
      Lambda_pos := hLambda'
      nonnegative_multiplicative := h.nonnegative_multiplicative
      normalized := h.normalized
      prime_power := ?_
      prime_power_bounds := ?_ }
  · intro p hp i hi
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hr : (p : ℝ).rpow (-c) ≤ (p : ℝ).rpow (-c') :=
      Real.rpow_le_rpow_of_exponent_le hp1 (neg_le_neg hcc)
    calc
      |w (p ^ i) - 1 / (i + 1 : ℕ)| ≤ C * (p : ℝ).rpow (-c) :=
        h.prime_power p hp i hi
      _ ≤ C' * (p : ℝ).rpow (-c') := by
        exact mul_le_mul hCC hr (Real.rpow_nonneg (Nat.cast_nonneg p) _)
          (h.C_pos.le.trans hCC)
  · intro p hp i hi
    exact ⟨(h.prime_power_bounds p hp i hi).1,
      (h.prime_power_bounds p hp i hi).2.trans hLL⟩

/-- Recovery-local mirror of the historical CU exports structure
(field-identical, including the concrete weight-chain data). -/
structure P051VF4Exports where
  p051V : P051VStatement
  p051F1 : P051F1Statement
  p051F2 : P051F2Statement
  p051F3 : P051F3Statement
  p051F4 : P051F4Statement
  weightChain : WeightChainSpec

/-- The recovered construction, proving existence of the mirrored exports
exactly as the verified CU proof did. -/
theorem recoveredExports : Nonempty P051VF4Exports := by
  let upstream : P051AE.P051AEExports :=
    P051AE.recoveredExports
  have hF1 : P051F1Statement := p051F1 upstream
  rcases hF1 with ⟨c1, C1, Lambda1, hw1, hw1Shift, hw1Dom⟩
  have hF2all : P051F2Statement := p051F2 upstream
  rcases hF2all c1 C1 Lambda1 hw1 with
    ⟨c2, C2, Lambda2, hc2, hC2, hLambda2, hw2all⟩
  let c3 : ℝ := min c1 c2
  let C3 : ℝ := max C1 C2
  let Lambda3 : ℝ := max Lambda1 Lambda2
  have hc3 : 0 < c3 := by dsimp [c3]; exact lt_min hw1.c_pos hc2
  have hC3 : 0 < C3 := by dsimp [C3]; exact lt_max_of_lt_left hw1.C_pos
  have hLambda3 : 0 < Lambda3 := by
    dsimp [Lambda3]
    exact lt_max_of_lt_left hw1.Lambda_pos
  have hw1Common : WeightTypeSpec w1Weight c3 C3 Lambda3 :=
    weightTypeSpec_weaken hw1 hc3 (by dsimp [c3]; exact min_le_left _ _)
      hC3 (by dsimp [C3]; exact le_max_left _ _)
      hLambda3 (by dsimp [Lambda3]; exact le_max_left _ _)
  have hw2Common : ∀ q : WeightParameters, WeightTypeSpec (w2Weight q) c3 C3 Lambda3 := by
    intro q
    exact weightTypeSpec_weaken (hw2all q).2.2.1 hc3
      (by dsimp [c3]; exact min_le_right _ _)
      hC3 (by dsimp [C3]; exact le_max_right _ _)
      hLambda3 (by dsimp [Lambda3]; exact le_max_right _ _)
  have hF3all : P051F3Statement := p051F3 upstream
  have hw3all := hF3all c3 C3 Lambda3 hw1Common hw2Common
  have hF4all : P051F4Statement := p051F4 upstream
  rcases hF4all c3 C3 Lambda3 (fun q => (hw3all q).1) with
    ⟨c4, C4, Lambda4, hc4, hC4, hLambda4, hw4all⟩
  refine ⟨{
    p051V := p051V
    p051F1 := p051F1 upstream
    p051F2 := p051F2 upstream
    p051F3 := p051F3 upstream
    p051F4 := p051F4 upstream
    weightChain := {
      c1 := c1
      C1 := C1
      Lambda1 := Lambda1
      c1_pos := hw1.c_pos
      C1_pos := hw1.C_pos
      Lambda1_pos := hw1.Lambda_pos
      w1_type := hw1
      w1_shift := hw1Shift
      w1_dom_a0 := fun K hK => (hw1Dom K hK).1
      w1_dom_shift := fun K hK => (hw1Dom K hK).2
      c2 := c2
      C2 := C2
      Lambda2 := Lambda2
      c2_pos := hc2
      C2_pos := hC2
      Lambda2_pos := hLambda2
      w2_type := fun q => (hw2all q).2.2.1
      w2_shift := fun q => (hw2all q).2.1
      w2_dom_w1 := fun q K hK => ((hw2all q).2.2.2 K hK).1
      w2_dom_shift := fun q K hK => ((hw2all q).2.2.2 K hK).2
      c3 := c3
      C3 := C3
      Lambda3 := Lambda3
      c3_pos := hc3
      C3_pos := hC3
      Lambda3_pos := hLambda3
      w3_type := fun q => (hw3all q).1
      w3_prime_power := fun q => (hw3all q).2.1
      w3_dom_w1 := fun q K hK => ((hw3all q).2.2 K hK).1
      w3_dom_w2 := fun q K hK => ((hw3all q).2.2 K hK).2
      c4 := c4
      C4 := C4
      Lambda4 := Lambda4
      c4_pos := hc4
      C4_pos := hC4
      Lambda4_pos := hLambda4
      w4_type := fun q => (hw4all q).2.1
      w4_shift := fun q => (hw4all q).1
      w4_dom_w3 := fun q K hK => ((hw4all q).2.2 K hK).1
      w4_dom_shift := fun q K hK => ((hw4all q).2.2 K hK).2
      modifier := fun q => (hw2all q).1
    }
  }⟩

theorem node_p051V : P051VStatement := p051V
theorem node_p051F1 : P051F1Statement := p051F1 P051AE.recoveredExports
theorem node_p051F2 : P051F2Statement := p051F2 P051AE.recoveredExports
theorem node_p051F3 : P051F3Statement := p051F3 P051AE.recoveredExports
theorem node_p051F4 : P051F4Statement := p051F4 P051AE.recoveredExports

/-- The concrete recovered weight-chain witness (shared identity preserved:
downstream nodes must thread this exact value). -/
@[expose] def weightChainWitness : WeightChainSpec :=
  recoveredExports.some.weightChain

end

end Erdos448.Stage7.ROOT05.Recovered.P051VF4
