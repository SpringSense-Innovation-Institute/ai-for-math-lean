module

import all Mathlib.Basic.Real.Basic
public import Erdos448.dependencies.«DP-MEAN».stage6.shared.TaskInterfaces

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.DPMean.TaskT08

@[expose] abbrev PublicTarget : Prop := Erdos448.DPMean.S6.T08Target

open Erdos448.DPMean

noncomputable section

lemma localSeriesSummable
    {lambda1 lambda2 : ℝ} (range : ParameterRange lambda1 lambda2)
    (h : ArithmeticFunction) (hgeom : PrimePowerGeometricBound h lambda1 lambda2)
    (p : ℕ) (hp : Nat.Prime p) :
    Summable (fun j : ℕ => eulerTerm h p j) := by
  have hp_real : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp_pos : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hp_real
  have ratio_nonneg : 0 ≤ lambda2 / (p : ℝ) :=
    div_nonneg range.lambda2_nonnegative hp_pos.le
  have ratio_lt_one : lambda2 / (p : ℝ) < 1 := by
    apply (div_lt_one hp_pos).2
    exact lt_of_lt_of_le range.lambda2_lt_two hp_real
  apply Summable.of_nonneg_of_le
      (f := fun j : ℕ => lambda1 * (lambda2 / (p : ℝ)) ^ j)
  · intro j
    exact div_nonneg (hgeom p hp j).1 (pow_nonneg hp_pos.le j)
  · intro j
    calc
      eulerTerm h p j
          ≤ (lambda1 * lambda2 ^ j) / (p : ℝ) ^ j :=
            div_le_div_of_nonneg_right (hgeom p hp j).2 (pow_nonneg hp_pos.le j)
      _ = lambda1 * (lambda2 / (p : ℝ)) ^ j := by
        rw [div_pow]
        ring
  · exact (summable_geometric_of_lt_one ratio_nonneg ratio_lt_one).mul_left lambda1

@[expose] def inclusiveEmbedding (x : ℝ) :
    {n // n ∈ inclusiveNatDomain x} ↪
      Nat.factoredNumbers (inclusiveNatDomain x) where
  toFun n := ⟨n, by
    rcases Finset.mem_filter.1 n.property with ⟨hn_range, hn_pos⟩
    apply Nat.mem_factoredNumbers_iff_forall_le.2
    refine ⟨Nat.ne_of_gt hn_pos, ?_⟩
    intro p hp_le hp_prime hp_dvd
    apply Finset.mem_filter.2
    refine ⟨?_, hp_prime.pos⟩
    apply Finset.mem_range.2
    have hn_floor : n.1 ≤ Nat.floor x := by
      rw [Finset.mem_range, Nat.lt_succ_iff] at hn_range
      exact hn_range
    omega⟩
  inj' := by
    intro a b hab
    apply Subtype.ext
    exact congrArg
      (fun n : Nat.factoredNumbers (inclusiveNatDomain x) => (n : ℕ)) hab

lemma reciprocalMultiplicative
    {h : ArithmeticFunction} (hmul : Multiplicative h) {a b : ℕ}
    (hab : Nat.Coprime a b) :
    h (a * b) / ((a * b : ℕ) : ℝ) =
      (h a / (a : ℝ)) * (h b / (b : ℝ)) := by
  by_cases ha : a = 0
  · subst a
    simp
  by_cases hb : b = 0
  · subst b
    simp
  rw [hmul.2 a b (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb) hab]
  push_cast
  ring

lemma eulerDomination
    {h : ArithmeticFunction} {lambda1 lambda2 x : ℝ}
    (assumptions : MeanAssumptions h lambda1 lambda2) (hx : 1 ≤ x) :
    EulerDominationPayload h x := by
  let f : ℕ → ℝ := fun n => h n / (n : ℝ)
  have f_one : f 1 = 1 := by
    simp [f, assumptions.h_nonnegative_multiplicative.multiplicative.1]
  have f_mul : ∀ {a b : ℕ}, Nat.Coprime a b → f (a * b) = f a * f b := by
    intro a b hab
    exact reciprocalMultiplicative
      assumptions.h_nonnegative_multiplicative.multiplicative hab
  have local_series : ∀ p : ℕ, Nat.Prime p →
      Summable (fun j : ℕ => eulerTerm h p j) :=
    localSeriesSummable assumptions.parameter_range h
      assumptions.prime_power_geometric_bound
  refine {
    local_summable := fun p hp _ => local_series p hp
    domination := ?_
  }
  have local_norm : ∀ {p : ℕ}, Nat.Prime p →
      Summable (fun j : ℕ => ‖f (p ^ j)‖) := by
    intro p hp
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hnonneg : ∀ j : ℕ, 0 ≤ eulerTerm h p j := fun j =>
      div_nonneg (assumptions.prime_power_geometric_bound p hp j).1
        (pow_nonneg hp_pos.le j)
    convert local_series p hp using 1
    funext j
    simpa only [f, eulerTerm, Nat.cast_pow, Real.norm_eq_abs] using
      (abs_of_nonneg (hnonneg j))
  have expansion :=
    EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
      f_one f_mul local_norm (inclusiveNatDomain x)
  have factored_nonneg : ∀ n : Nat.factoredNumbers (inclusiveNatDomain x),
      0 ≤ f n := by
    intro n
    have hn_pos : 0 < (n : ℕ) := Nat.pos_of_ne_zero n.property.1
    exact div_nonneg
      (assumptions.h_nonnegative_multiplicative.nonnegative n hn_pos)
      (Nat.cast_nonneg n)
  have finite_le :
      (∑ n ∈ inclusiveNatDomain x, f n) ≤
        ∑' n : Nat.factoredNumbers (inclusiveNatDomain x), f n := by
    calc
      (∑ n ∈ inclusiveNatDomain x, f n) =
          ∑ n ∈ (inclusiveNatDomain x).attach.map (inclusiveEmbedding x), f n := by
            rw [Finset.sum_map]
            simpa [inclusiveEmbedding] using
              (Finset.sum_attach (inclusiveNatDomain x) f).symm
      _ ≤ ∑' n : Nat.factoredNumbers (inclusiveNatDomain x), f n := by
        exact expansion.1.of_norm.sum_le_tsum _
          (fun n _ => factored_nonneg n)
  have product_eq :
      inclusiveEulerProduct h x =
        ∑' n : Nat.factoredNumbers (inclusiveNatDomain x), f n := by
    unfold inclusiveEulerProduct inclusivePrimeDomain
    rw [expansion.2.tsum_eq]
    apply Finset.prod_congr rfl
    intro p hp
    apply tsum_congr
    intro j
    simp [f, eulerTerm, Nat.cast_pow]
  unfold reciprocalMean
  simpa only [f] using finite_le.trans_eq product_eq.symm

theorem publicTarget : PublicTarget := by
  intro h lambda1 lambda2 x assumptions hx
  exact eulerDomination assumptions hx

end

end Erdos448.DPMean.TaskT08
