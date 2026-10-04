module

public import Erdos745.WrapUp.Contracts

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


/-!
The exact algebraic front end of W04.  The remaining estimate is not an
interface projection: it requires the finite logarithmic, entropy, mixed
subtraction, and conditioned-tail arguments supplied in the W04 packet.
-/
namespace Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_Foundation

noncomputable section
open scoped BigOperators

theorem cayley_pos {k : ℕ} (hk : 0 < k) : 0 < cayley k := by
  simp only [cayley]
  split
  · omega
  split
  · simp_all
  · exact Nat.pow_pos hk

theorem exactTupleFormula
    (hF : FiniteEnumerationStatement)
    (n M q : ℕ) (ks : Fin q → ℕ) (hM : M ≤ capacity n)
    (hpos : ∀ i, 0 < ks i)
    (hKn : (∑ i, ks i) ≤ n)
    (hKM : (∑ i, ks i) ≤ M + q) :
    tupleMoment n M q ks =
      (falling n (∑ i, ks i) : ℝ) *
        (∏ i, (cayley (ks i) : ℝ) / ((ks i).factorial : ℝ)) *
        (((n - ∑ i, ks i).choose 2).choose (M + q - ∑ i, ks i) : ℝ) /
          ((capacity n).choose M : ℝ) := by
  rw [hF.2.2.2.2.2.1 n M q ks hM]
  simp [tupleFormula, hpos, hKn, hKM]

theorem tupleMoment_eq_zero_of_guard_failure
    (hF : FiniteEnumerationStatement)
    (n M q : ℕ) (ks : Fin q → ℕ) (hM : M ≤ capacity n)
    (hbad : ¬ ((∀ i, 0 < ks i) ∧ (∑ i, ks i) ≤ n ∧
      (∑ i, ks i) ≤ M + q)) :
    tupleMoment n M q ks = 0 := by
  rw [hF.2.2.2.2.2.1 n M q ks hM]
  simp [tupleFormula, hbad]

theorem tupleLeading_exact
    (n M q : ℕ) (ks : Fin q → ℕ) (hpos : ∀ i, 0 < ks i) :
    tupleLeading n M q ks =
      ((n : ℝ) / degreeAt n M) ^ q *
        (∏ i, (cayley (ks i) : ℝ) / ((ks i).factorial : ℝ)) *
        (degreeAt n M * Real.exp (-degreeAt n M)) ^ (∑ i, ks i) := by
  simp only [tupleLeading, treeLeading, if_neg (Nat.ne_of_gt (hpos _))]
  rw [show (∏ i : Fin q,
      ((n : ℝ) / degreeAt n M * (cayley (ks i) : ℝ) /
        ((ks i).factorial : ℝ) *
        (degreeAt n M * Real.exp (-degreeAt n M)) ^ ks i)) =
      (∏ i : Fin q, ((n : ℝ) / degreeAt n M)) *
      (∏ i : Fin q, ((cayley (ks i) : ℝ) / ((ks i).factorial : ℝ))) *
      (∏ i : Fin q, (degreeAt n M * Real.exp (-degreeAt n M)) ^ ks i) by
        rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro i hi
        ring]
  rw [Finset.prod_const, Finset.prod_pow_eq_pow_sum]
  simp

theorem tupleLeading_pos
    (n M q : ℕ) (ks : Fin q → ℕ) (hn : 0 < n)
    (hlam : 0 < degreeAt n M) (hpos : ∀ i, 0 < ks i) :
    0 < tupleLeading n M q ks := by
  unfold tupleLeading
  apply Finset.prod_pos
  intro i hi
  rw [treeLeading, if_neg (Nat.ne_of_gt (hpos i))]
  have hc : 0 < cayley (ks i) := cayley_pos (hpos i)
  positivity

theorem falling_pos {n K : ℕ} (hKn : K ≤ n) : 0 < falling n K := by
  unfold falling
  apply Finset.prod_pos
  intro j hj
  rw [Finset.mem_range] at hj
  omega

theorem tupleFactor_pos
    (q : ℕ) (ks : Fin q → ℕ) (hpos : ∀ i, 0 < ks i) :
    0 < ∏ i, (cayley (ks i) : ℝ) / ((ks i).factorial : ℝ) := by
  apply Finset.prod_pos
  intro i hi
  exact div_pos (Nat.cast_pos.mpr (cayley_pos (hpos i)))
    (Nat.cast_pos.mpr (Nat.factorial_pos _))

theorem tupleMoment_pos
    (hF : FiniteEnumerationStatement)
    (n M q : ℕ) (ks : Fin q → ℕ) (hM : M ≤ capacity n)
    (hpos : ∀ i, 0 < ks i)
    (hKn : (∑ i, ks i) ≤ n)
    (hKM : (∑ i, ks i) ≤ M + q)
    (hb : M + q - ∑ i, ks i ≤ (n - ∑ i, ks i).choose 2) :
    0 < tupleMoment n M q ks := by
  rw [exactTupleFormula hF n M q ks hM hpos hKn hKM]
  have hchoose : 0 < (((n - ∑ i, ks i).choose 2).choose
      (M + q - ∑ i, ks i) : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos hb)
  have hden : 0 < ((capacity n).choose M : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos hM)
  exact div_pos
    (mul_pos (mul_pos (Nat.cast_pos.mpr (falling_pos hKn))
      (tupleFactor_pos q ks hpos)) hchoose) hden

private theorem ratio_cancel
    (a b c d n lam : ℝ) (q K : ℕ)
    (hc : c ≠ 0) (hd : d ≠ 0) (hn : n ≠ 0) (hlam : lam ≠ 0) :
    (a * c * b / d) /
        ((n / lam) ^ q * c * (lam * Real.exp (-lam)) ^ K) =
      (a * b / d) * (lam / n) ^ q * Real.exp (lam * K) / lam ^ K := by
  have hnl : n / lam ≠ 0 := div_ne_zero hn hlam
  have he : Real.exp (-lam) ≠ 0 := Real.exp_ne_zero _
  have hpow : (n / lam) ^ q * (lam / n) ^ q = 1 := by
    rw [← mul_pow]
    field_simp
    simp
  have hpow' : (lam / n) ^ q * (n / lam) ^ q = 1 := by
    simpa [mul_comm] using! hpow
  apply (div_eq_iff (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hnl) hc)
    (pow_ne_zero _ (mul_ne_zero hlam he)))).2
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_eq_div_iff hd (pow_ne_zero _ hlam)]
  rw [mul_pow, ← Real.exp_nat_mul]
  rw [show (K : ℝ) * -lam = -(lam * K) by ring, Real.exp_neg]
  field_simp [Real.exp_ne_zero]
  calc
    a * b = a * b * 1 := by ring
    _ = a * b * ((lam / n) ^ q * (n / lam) ^ q) := by rw [hpow']
    _ = _ := by ring

theorem tupleRatio_exact
    (hF : FiniteEnumerationStatement)
    (n M q : ℕ) (ks : Fin q → ℕ) (hM : M ≤ capacity n)
    (hpos : ∀ i, 0 < ks i)
    (hKn : (∑ i, ks i) ≤ n)
    (hKM : (∑ i, ks i) ≤ M + q)
    (hn : 0 < n) (hlam : 0 < degreeAt n M) :
    tupleMoment n M q ks / tupleLeading n M q ks =
      ((falling n (∑ i, ks i) : ℝ) *
          (((n - ∑ i, ks i).choose 2).choose
            (M + q - ∑ i, ks i) : ℝ) /
          ((capacity n).choose M : ℝ)) *
        (degreeAt n M / (n : ℝ)) ^ q *
        Real.exp (degreeAt n M * (∑ i, ks i : ℕ)) /
        degreeAt n M ^ (∑ i, ks i) := by
  rw [exactTupleFormula hF n M q ks hM hpos hKn hKM]
  rw [tupleLeading_exact n M q ks hpos]
  have hprod : 0 < ∏ i, (cayley (ks i) : ℝ) /
      ((ks i).factorial : ℝ) := tupleFactor_pos q ks hpos
  have hden : 0 < ((capacity n).choose M : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos hM)
  exact ratio_cancel _ _ _ _ _ _ _ _ (ne_of_gt hprod) (ne_of_gt hden)
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)) (ne_of_gt hlam)

private theorem log_ratio_expand
    (a b d n lam : ℝ) (q K : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (hn : 0 < n) (hlam : 0 < lam) :
    Real.log (((a * b / d) * (lam / n) ^ q *
        Real.exp (lam * K)) / lam ^ K) =
      Real.log a + Real.log b - Real.log d +
        (q : ℝ) * (Real.log lam - Real.log n) +
        lam * K - (K : ℝ) * Real.log lam := by
  have ha0 := ne_of_gt ha
  have hb0 := ne_of_gt hb
  have hd0 := ne_of_gt hd
  have hn0 := ne_of_gt hn
  have hlam0 := ne_of_gt hlam
  have habd : a * b / d ≠ 0 :=
    div_ne_zero (mul_ne_zero ha0 hb0) hd0
  have hln : lam / n ≠ 0 := div_ne_zero hlam0 hn0
  rw [Real.log_div
    (mul_ne_zero (mul_ne_zero habd (pow_ne_zero _ hln))
      (Real.exp_ne_zero _))
    (pow_ne_zero _ hlam0)]
  rw [Real.log_mul (mul_ne_zero habd (pow_ne_zero _ hln))
    (Real.exp_ne_zero _)]
  rw [Real.log_mul habd (pow_ne_zero _ hln)]
  rw [Real.log_div (mul_ne_zero ha0 hb0) hd0]
  rw [Real.log_mul ha0 hb0, Real.log_pow, Real.log_div hlam0 hn0]
  rw [Real.log_exp, Real.log_pow]

theorem log_tupleRatio_exact
    (hF : FiniteEnumerationStatement)
    (n M q : ℕ) (ks : Fin q → ℕ) (hM : M ≤ capacity n)
    (hpos : ∀ i, 0 < ks i)
    (hKn : (∑ i, ks i) ≤ n)
    (hKM : (∑ i, ks i) ≤ M + q)
    (hb : M + q - ∑ i, ks i ≤ (n - ∑ i, ks i).choose 2)
    (hn : 0 < n) (hlam : 0 < degreeAt n M) :
    Real.log (tupleMoment n M q ks / tupleLeading n M q ks) =
      Real.log (falling n (∑ i, ks i) : ℝ) +
      Real.log ((((n - ∑ i, ks i).choose 2).choose
        (M + q - ∑ i, ks i) : ℕ) : ℝ) -
      Real.log (((capacity n).choose M : ℕ) : ℝ) +
      (q : ℝ) * (Real.log (degreeAt n M) - Real.log (n : ℝ)) +
      degreeAt n M * (∑ i, ks i : ℕ) -
      ((∑ i, ks i : ℕ) : ℝ) * Real.log (degreeAt n M) := by
  rw [tupleRatio_exact hF n M q ks hM hpos hKn hKM hn hlam]
  exact log_ratio_expand _ _ _ _ _ _ _
    (Nat.cast_pos.mpr (falling_pos hKn))
    (Nat.cast_pos.mpr (Nat.choose_pos hb))
    (Nat.cast_pos.mpr (Nat.choose_pos hM))
    (Nat.cast_pos.mpr hn) hlam

end

end Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_Foundation


/-!
The analytic core of the W04 local estimate.  The finite combinatorial
logarithm is handled separately; this file proves the exact entropy
derivatives and the uniform cancellation estimate used after that finite
logarithm has been reduced to the entropy normal form.
-/
namespace Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_Local

noncomputable section
open scoped BigOperators

open W04_TUPLES_Foundation

theorem log_one_sub_remainder {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    |Real.log (1 - u) + u| ≤ u ^ 2 / (1 - u) := by
  have h := Real.abs_log_sub_add_sum_range_le
    (show |u| < 1 by rwa [abs_of_nonneg hu0]) 1
  norm_num [abs_of_nonneg hu0] at h
  simpa [add_comm] using! h

theorem finite_log_sum_remainder {s : ℕ} {u : ℕ → ℝ}
    (hu0 : ∀ j < s, 0 ≤ u j) (hu1 : ∀ j < s, u j < 1) :
    |∑ j ∈ Finset.range s, (Real.log (1 - u j) + u j)| ≤
      ∑ j ∈ Finset.range s, (u j) ^ 2 / (1 - u j) := by
  calc
    |∑ j ∈ Finset.range s, (Real.log (1 - u j) + u j)| ≤
        ∑ j ∈ Finset.range s, |Real.log (1 - u j) + u j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range s, (u j) ^ 2 / (1 - u j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact log_one_sub_remainder (hu0 j (Finset.mem_range.mp hj))
        (hu1 j (Finset.mem_range.mp hj))

def logFallingSum (X : ℝ) (s : ℕ) : ℝ :=
  ∑ j ∈ Finset.range s, Real.log (1 - (j : ℝ) / X)

private def logIntegralPrimitive (X x : ℝ) : ℝ :=
  -(X - x) * Real.log (1 - x / X) - x

private theorem hasDerivAt_logOneSubDiv {X x : ℝ}
    (hX : 0 < X) (hx : x < X) :
    HasDerivAt (fun y : ℝ => Real.log (1 - y / X))
      ((-X⁻¹) / (1 - x / X)) x := by
  have hu : 1 - x / X ≠ 0 :=
    ne_of_gt (sub_pos.mpr ((div_lt_one hX).2 hx))
  convert (((hasDerivAt_const x (1 : ℝ)).sub
    ((hasDerivAt_id x).div_const X)).log hu) using 1
  all_goals simp [id_eq]

private theorem hasDerivAt_logIntegralPrimitive {X x : ℝ}
    (hX : 0 < X) (hx : x < X) :
    HasDerivAt (logIntegralPrimitive X)
      (Real.log (1 - x / X)) x := by
  have hX0 : X ≠ 0 := ne_of_gt hX
  have hdiff : X - x ≠ 0 := ne_of_gt (sub_pos.mpr hx)
  have hlog := hasDerivAt_logOneSubDiv hX hx
  have hratio : (X - x) * X⁻¹ / (1 - x / X) = 1 := by
    field_simp [hX0, hdiff]
  unfold logIntegralPrimitive
  have hmain := (((hasDerivAt_const x X).sub
    (hasDerivAt_id x)).neg.mul hlog).sub (hasDerivAt_id x)
  convert! hmain using 1
  simp only [Pi.neg_apply, Pi.sub_apply, id_eq, zero_sub, neg_neg, one_mul]
  rw [show -(X - x) * (-X⁻¹ / (1 - x / X)) =
      (X - x) * X⁻¹ / (1 - x / X) by ring, hratio]
  ring

theorem integral_logOneSubDiv {X S : ℝ}
    (hX : 0 < X) (hS0 : 0 ≤ S) (hS : S < X) :
    (∫ x : ℝ in (0 : ℝ)..S, Real.log (1 - x / X)) =
      -(X - S) * Real.log (1 - S / X) - S := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) S,
      HasDerivAt (logIntegralPrimitive X)
        (Real.log (1 - x / X)) x := by
    intro x hx
    rw [Set.uIcc_of_le hS0] at hx
    exact hasDerivAt_logIntegralPrimitive hX (lt_of_le_of_lt hx.2 hS)
  have hcont : ContinuousOn (fun x : ℝ => Real.log (1 - x / X))
      (Set.uIcc (0 : ℝ) S) := by
    intro x hx
    rw [Set.uIcc_of_le hS0] at hx
    exact (hasDerivAt_logOneSubDiv hX
      (lt_of_le_of_lt hx.2 hS)).continuousAt.continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hcont.intervalIntegrable]
  simp [logIntegralPrimitive]

theorem log_sum_integral_remainder {X : ℝ} {s : ℕ}
    (hX : 0 < X) (hs : (s : ℝ) < X) :
    |logFallingSum X s -
        (∫ x : ℝ in (0 : ℝ)..(s : ℝ), Real.log (1 - x / X))| ≤
      -Real.log (1 - (s : ℝ) / X) := by
  let f : ℝ → ℝ := fun x => Real.log (1 - x / X)
  have hanti : AntitoneOn f (Set.Icc (0 : ℝ) (s : ℝ)) := by
    intro x hx y hy hxy
    apply Real.strictMonoOn_log.monotoneOn
    · exact sub_pos.mpr ((div_lt_one hX).2 (lt_of_le_of_lt hy.2 hs))
    · exact sub_pos.mpr ((div_lt_one hX).2 (lt_of_le_of_lt hx.2 hs))
    · exact sub_le_sub_left (div_le_div_of_nonneg_right hxy hX.le) 1
  have hanti' : AntitoneOn f
      (Set.Icc (0 : ℝ) ((0 : ℝ) + (s : ℝ))) := by
    simpa using! hanti
  have hlower := hanti'.integral_le_sum
  have hshift := hanti'.sum_le_integral
  simp only [zero_add, f] at hlower hshift
  have htel :
      (∑ j ∈ Finset.range s, f (j : ℝ)) -
          (∑ j ∈ Finset.range s, f ((j + 1 : ℕ) : ℝ)) =
        f 0 - f (s : ℝ) := by
    have h1 := Finset.sum_range_succ (fun j : ℕ => f (j : ℝ)) s
    have h2 := Finset.sum_range_succ' (fun j : ℕ => f (j : ℝ)) s
    norm_num at h1 h2 ⊢
    linarith
  have hnonneg : 0 ≤
      (∑ j ∈ Finset.range s, f (j : ℝ)) -
        (∫ x : ℝ in (0 : ℝ)..(s : ℝ), f x) := by
    linarith
  change |(∑ j ∈ Finset.range s, f (j : ℝ)) -
    (∫ x : ℝ in (0 : ℝ)..(s : ℝ), f x)| ≤ _
  rw [abs_of_nonneg hnonneg]
  have hupp :
      (∑ j ∈ Finset.range s, f (j : ℝ)) -
          (∫ x : ℝ in (0 : ℝ)..(s : ℝ), f x) ≤
        f 0 - f (s : ℝ) := by
    linarith
  simpa [f, logFallingSum] using! hupp

private theorem neg_log_one_sub_le {u : ℝ}
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) :
    -Real.log (1 - u) ≤ 2 * u := by
  have hpos : 0 < 1 - u := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at h
  apply le_trans h
  rw [show (1 - u)⁻¹ - 1 = u / (1 - u) by field_simp; ring]
  apply (div_le_iff₀ hpos).2
  nlinarith

theorem log_sum_integral_remainder_le {X : ℝ} {s : ℕ}
    (hX : 0 < X) (hs : 2 * (s : ℝ) ≤ X) :
    |logFallingSum X s -
        (-(X - s) * Real.log (1 - (s : ℝ) / X) - s)| ≤
      2 * (s : ℝ) / X := by
  have hslt : (s : ℝ) < X := by
    have hs0 : 0 ≤ (s : ℝ) := Nat.cast_nonneg _
    nlinarith
  rw [← integral_logOneSubDiv hX (Nat.cast_nonneg _) hslt]
  apply le_trans (log_sum_integral_remainder hX hslt)
  convert neg_log_one_sub_le (u := (s : ℝ) / X)
    (div_nonneg (Nat.cast_nonneg _) hX.le)
    ((div_le_iff₀ hX).2 (by linarith)) using 1
  ring

theorem sparse_log_sum_remainder {X : ℝ} {s : ℕ}
    (hX : 0 < X) (hs : 2 * (s : ℝ) ≤ X) :
    |∑ j ∈ Finset.range s,
        (Real.log (1 - (j : ℝ) / X) + (j : ℝ) / X)| ≤
      2 * (s : ℝ) ^ 3 / X ^ 2 := by
  have hbase := finite_log_sum_remainder
    (u := fun j => (j : ℝ) / X)
    (fun j _ => div_nonneg (Nat.cast_nonneg _) hX.le)
    (fun j hj => by
      apply lt_of_le_of_lt _ (show (1 : ℝ) / 2 < 1 by norm_num)
      apply (div_le_iff₀ hX).2
      have hjle : (j : ℝ) ≤ (s : ℝ) := by
        exact_mod_cast Nat.le_of_lt hj
      nlinarith)
  apply le_trans hbase
  calc
    ∑ j ∈ Finset.range s,
        ((j : ℝ) / X) ^ 2 / (1 - (j : ℝ) / X) ≤
        ∑ _j ∈ Finset.range s, 2 * ((s : ℝ) / X) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.mem_range] at hj
      have hjle : (j : ℝ) ≤ (s : ℝ) := by
        exact_mod_cast Nat.le_of_lt hj
      have hu0 : 0 ≤ (j : ℝ) / X :=
        div_nonneg (Nat.cast_nonneg _) hX.le
      have hus : (j : ℝ) / X ≤ (s : ℝ) / X :=
        div_le_div_of_nonneg_right hjle hX.le
      have hsHalf : (s : ℝ) / X ≤ 1 / 2 :=
        (div_le_iff₀ hX).2 (by linarith)
      have hden : 0 < 1 - (j : ℝ) / X := by linarith
      apply (div_le_iff₀ hden).2
      nlinarith [sq_nonneg ((s : ℝ) / X - (j : ℝ) / X)]
    _ = 2 * (s : ℝ) ^ 3 / X ^ 2 := by
      simp
      field_simp

private theorem falling_eq_descFactorial (n s : ℕ) :
    falling n s = n.descFactorial s := by
  unfold falling
  rw [Nat.descFactorial_eq_prod_range]

theorem log_falling_eq_sum {n s : ℕ} (hn : 0 < n) (hs : s ≤ n) :
    Real.log (falling n s : ℝ) =
      (s : ℝ) * Real.log (n : ℝ) + logFallingSum n s := by
  unfold falling logFallingSum
  rw [Nat.cast_prod, Real.log_prod]
  · calc
      ∑ j ∈ Finset.range s, Real.log ((n - j : ℕ) : ℝ) =
          ∑ j ∈ Finset.range s,
            (Real.log (n : ℝ) + Real.log (1 - (j : ℝ) / n)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mem_range] at hj
        have hjnlt : j < n := lt_of_lt_of_le hj hs
        have hjn : j ≤ n := Nat.le_of_lt hjnlt
        rw [Nat.cast_sub hjn]
        have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
        have hterm : 0 < 1 - (j : ℝ) / n :=
          sub_pos.mpr ((div_lt_one (Nat.cast_pos.mpr hn)).2
            (Nat.cast_lt.mpr hjnlt))
        rw [show (n : ℝ) - j =
            (n : ℝ) * (1 - (j : ℝ) / n) by field_simp]
        rw [Real.log_mul hn0 (ne_of_gt hterm)]
      _ = (s : ℝ) * Real.log (n : ℝ) +
          ∑ j ∈ Finset.range s, Real.log (1 - (j : ℝ) / n) := by
        rw [Finset.sum_add_distrib]
        simp
  · intro j hj
    rw [Finset.mem_range] at hj
    exact_mod_cast Nat.ne_of_gt
      (Nat.sub_pos_of_lt (lt_of_lt_of_le hj hs))

private theorem log_choose_eq_log_falling {n s : ℕ} (hs : s ≤ n) :
    Real.log ((n.choose s : ℕ) : ℝ) =
      Real.log (falling n s : ℝ) - Real.log (s.factorial : ℝ) := by
  have hmulNat : n.choose s * s.factorial = falling n s := by
    rw [falling_eq_descFactorial,
      Nat.choose_eq_descFactorial_div_factorial]
    exact Nat.div_mul_cancel (Nat.factorial_dvd_descFactorial n s)
  have hc : 0 < n.choose s := Nat.choose_pos hs
  have hf : 0 < s.factorial := Nat.factorial_pos s
  have hmul := congrArg (fun z : ℕ => Real.log (z : ℝ)) hmulNat
  change Real.log ((n.choose s * s.factorial : ℕ) : ℝ) =
    Real.log (falling n s : ℝ) at hmul
  rw [Nat.cast_mul, Real.log_mul
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hc))
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hf))] at hmul
  linarith

private theorem log_factorial_sub_eq_log_falling {M r : ℕ} (hr : r ≤ M) :
    Real.log (M.factorial : ℝ) - Real.log ((M - r).factorial : ℝ) =
      Real.log (falling M r : ℝ) := by
  have hmulNat : falling M r * (M - r).factorial = M.factorial := by
    rw [falling_eq_descFactorial, Nat.descFactorial_eq_div hr]
    exact Nat.div_mul_cancel
      (Nat.factorial_dvd_factorial (Nat.sub_le M r))
  have hfall : 0 < falling M r := falling_pos hr
  have hfac : 0 < (M - r).factorial := Nat.factorial_pos _
  have hmul := congrArg (fun z : ℕ => Real.log (z : ℝ)) hmulNat
  change Real.log ((falling M r * (M - r).factorial : ℕ) : ℝ) =
    Real.log (M.factorial : ℝ) at hmul
  rw [Nat.cast_mul, Real.log_mul
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hfall))
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hfac))] at hmul
  linarith

theorem log_tupleRatio_falling_form
    (hF : FiniteEnumerationStatement)
    (n M q : ℕ) (ks : Fin q → ℕ) (hM : M ≤ capacity n)
    (hpos : ∀ i, 0 < ks i)
    (hKn : (∑ i, ks i) ≤ n)
    (hKM : (∑ i, ks i) ≤ M + q)
    (hb : M + q - ∑ i, ks i ≤ (n - ∑ i, ks i).choose 2)
    (hn : 0 < n) (hlam : 0 < degreeAt n M)
    (hqK : q ≤ ∑ i, ks i) :
    Real.log (tupleMoment n M q ks / tupleLeading n M q ks) =
      Real.log (falling n (∑ i, ks i) : ℝ) +
      Real.log (falling ((n - ∑ i, ks i).choose 2)
        (M + q - ∑ i, ks i) : ℝ) +
      Real.log (falling M ((∑ i, ks i) - q) : ℝ) -
      Real.log (falling (capacity n) M : ℝ) +
      (q : ℝ) * (Real.log (degreeAt n M) - Real.log (n : ℝ)) +
      degreeAt n M * (∑ i, ks i : ℕ) -
      ((∑ i, ks i : ℕ) : ℝ) * Real.log (degreeAt n M) := by
  rw [log_tupleRatio_exact hF n M q ks hM hpos hKn hKM hb hn hlam]
  rw [log_choose_eq_log_falling hb, log_choose_eq_log_falling hM]
  have hr : (∑ i, ks i) - q ≤ M := by omega
  have hb_eq : M + q - ∑ i, ks i = M - ((∑ i, ks i) - q) := by
    omega
  rw [hb_eq, ← log_factorial_sub_eq_log_falling hr]
  ring

def integralFallingMain (X : ℝ) (s : ℕ) : ℝ :=
  (s : ℝ) * Real.log X -
    (X - s) * Real.log (1 - (s : ℝ) / X) - s

def sparseFallingMain (X : ℝ) (s : ℕ) : ℝ :=
  (s : ℝ) * Real.log X -
    ∑ j ∈ Finset.range s, (j : ℝ) / X

theorem log_falling_integral_remainder {n s : ℕ}
    (hn : 0 < n) (hsn : s ≤ n)
    (hs : 2 * (s : ℝ) ≤ n) :
    |Real.log (falling n s : ℝ) - integralFallingMain n s| ≤
      2 * (s : ℝ) / n := by
  rw [log_falling_eq_sum hn hsn]
  unfold integralFallingMain
  convert log_sum_integral_remainder_le (X := (n : ℝ)) (s := s)
    (Nat.cast_pos.mpr hn) hs using 1
  congr 1
  ring

theorem log_falling_sparse_remainder {n s : ℕ}
    (hn : 0 < n) (hsn : s ≤ n)
    (hs : 2 * (s : ℝ) ≤ n) :
    |Real.log (falling n s : ℝ) - sparseFallingMain n s| ≤
      2 * (s : ℝ) ^ 3 / (n : ℝ) ^ 2 := by
  rw [log_falling_eq_sum hn hsn]
  unfold sparseFallingMain logFallingSum
  have h := sparse_log_sum_remainder (X := (n : ℝ))
    (Nat.cast_pos.mpr hn) hs
  simpa [Finset.sum_add_distrib, div_eq_mul_inv, add_comm] using! h

def tupleFiniteMain (n M q K : ℕ) : ℝ :=
  let A := (n - K).choose 2
  let b := M + q - K
  let r := K - q
  integralFallingMain n K + sparseFallingMain A b +
    integralFallingMain M r - sparseFallingMain (capacity n) M +
    (q : ℝ) * (Real.log (degreeAt n M) - Real.log (n : ℝ)) +
    degreeAt n M * K - (K : ℝ) * Real.log (degreeAt n M)

theorem tupleLog_to_finiteMain
    (hF : FiniteEnumerationStatement)
    (n M q : ℕ) (ks : Fin q → ℕ)
    (hM : M ≤ capacity n) (hpos : ∀ i, 0 < ks i)
    (hKn : (∑ i, ks i) ≤ n)
    (hKM : (∑ i, ks i) ≤ M + q)
    (hb : M + q - ∑ i, ks i ≤ (n - ∑ i, ks i).choose 2)
    (hn : 0 < n) (hMpos : 0 < M)
    (hApos : 0 < (n - ∑ i, ks i).choose 2)
    (hNpos : 0 < capacity n)
    (hlam : 0 < degreeAt n M) (hqK : q ≤ ∑ i, ks i)
    (h2K : 2 * ((∑ i, ks i : ℕ) : ℝ) ≤ n)
    (h2r : 2 * (((∑ i, ks i) - q : ℕ) : ℝ) ≤ M)
    (h2b : 2 * ((M + q - ∑ i, ks i : ℕ) : ℝ) ≤
      ((n - ∑ i, ks i).choose 2 : ℕ))
    (h2M : 2 * (M : ℝ) ≤ capacity n) :
    |Real.log (tupleMoment n M q ks / tupleLeading n M q ks) -
        tupleFiniteMain n M q (∑ i, ks i)| ≤
      2 * ((∑ i, ks i : ℕ) : ℝ) / n +
      2 * ((M + q - ∑ i, ks i : ℕ) : ℝ) ^ 3 /
        (((n - ∑ i, ks i).choose 2 : ℕ) : ℝ) ^ 2 +
      2 * (((∑ i, ks i) - q : ℕ) : ℝ) / M +
      2 * (M : ℝ) ^ 3 / (capacity n : ℝ) ^ 2 := by
  let K := ∑ i, ks i
  let A := (n - K).choose 2
  let b := M + q - K
  let r := K - q
  have hrM : r ≤ M := by
    dsimp only [r, K]
    omega
  have hKn' : K ≤ n := by simpa [K] using! hKn
  have hbA : b ≤ A := by simpa [b, A, K] using! hb
  have hmain := log_tupleRatio_falling_form hF n M q ks hM hpos hKn
    hKM hb hn hlam hqK
  have eK := log_falling_integral_remainder hn hKn' h2K
  have eA := log_falling_sparse_remainder hApos hbA h2b
  have er := log_falling_integral_remainder hMpos hrM h2r
  have eN := log_falling_sparse_remainder hNpos hM h2M
  rw [hmain]
  change |(Real.log (falling n K : ℝ) +
      Real.log (falling A b : ℝ) + Real.log (falling M r : ℝ) -
      Real.log (falling (capacity n) M : ℝ) +
      (q : ℝ) * (Real.log (degreeAt n M) - Real.log (n : ℝ)) +
      degreeAt n M * K - (K : ℝ) * Real.log (degreeAt n M)) -
      tupleFiniteMain n M q K| ≤ _
  rw [show
    (Real.log (falling n K : ℝ) + Real.log (falling A b : ℝ) +
      Real.log (falling M r : ℝ) -
      Real.log (falling (capacity n) M : ℝ) +
      (q : ℝ) * (Real.log (degreeAt n M) - Real.log (n : ℝ)) +
      degreeAt n M * K - (K : ℝ) * Real.log (degreeAt n M)) -
      tupleFiniteMain n M q K =
    (Real.log (falling n K : ℝ) - integralFallingMain n K) +
      (Real.log (falling A b : ℝ) - sparseFallingMain A b) +
      (Real.log (falling M r : ℝ) - integralFallingMain M r) -
      (Real.log (falling (capacity n) M : ℝ) -
        sparseFallingMain (capacity n) M) by
      simp only [tupleFiniteMain]
      ring]
  calc
    _ ≤ |Real.log (falling n K : ℝ) - integralFallingMain n K| +
        |Real.log (falling A b : ℝ) - sparseFallingMain A b| +
        |Real.log (falling M r : ℝ) - integralFallingMain M r| +
        |Real.log (falling (capacity n) M : ℝ) -
          sparseFallingMain (capacity n) M| := by
      calc
        _ ≤ |(Real.log (falling n K : ℝ) - integralFallingMain n K) +
              (Real.log (falling A b : ℝ) - sparseFallingMain A b) +
              (Real.log (falling M r : ℝ) - integralFallingMain M r)| +
            |Real.log (falling (capacity n) M : ℝ) -
              sparseFallingMain (capacity n) M| := abs_sub _ _
        _ ≤ _ := by
          have h₁ := abs_add_le
            ((Real.log (falling n K : ℝ) - integralFallingMain n K) +
              (Real.log (falling A b : ℝ) - sparseFallingMain A b))
            (Real.log (falling M r : ℝ) - integralFallingMain M r)
          have h₂ := abs_add_le
            (Real.log (falling n K : ℝ) - integralFallingMain n K)
            (Real.log (falling A b : ℝ) - sparseFallingMain A b)
          linarith
    _ ≤ _ := by
      exact add_le_add (add_le_add (add_le_add eK eA) er) eN

def entropyCore (lam t : ℝ) : ℝ :=
  t * Real.log lam - t + (lam - 1 - t) * Real.log (1 - t) -
    (lam / 2 - t) * Real.log (1 - 2 * t / lam)

def entropySlope (lam t : ℝ) : ℝ :=
  -rate ((lam - 2 * t) / (1 - t))

def entropyCurvature (lam t : ℝ) : ℝ :=
  (2 - lam) * (lam - 1 - t) /
    ((1 - t) ^ 2 * (lam - 2 * t))

@[simp] theorem entropyCore_zero (lam : ℝ) : entropyCore lam 0 = 0 := by
  simp [entropyCore]

@[simp] theorem entropySlope_zero (lam : ℝ) : entropySlope lam 0 = -rate lam := by
  simp [entropySlope]

theorem hasDerivAt_entropyCore {lam t : ℝ}
    (hlam : 0 < lam) (ht : t < 1) (h2t : 2 * t < lam) :
    HasDerivAt (entropyCore lam) (entropySlope lam t) t := by
  have hlam0 : lam ≠ 0 := ne_of_gt hlam
  have h1pos : 0 < 1 - t := sub_pos.mpr ht
  have h1 : 1 - t ≠ 0 := ne_of_gt h1pos
  have h2pos : 0 < 1 - 2 * t / lam :=
    sub_pos.mpr ((div_lt_one hlam).2 h2t)
  have h2 : 1 - 2 * t / lam ≠ 0 := ne_of_gt h2pos
  have hd : lam - 2 * t ≠ 0 := ne_of_gt (sub_pos.mpr h2t)
  have hy : (lam - 2 * t) / (1 - t) =
      lam * (1 - 2 * t / lam) / (1 - t) := by
    field_simp
  have hlogy : Real.log ((lam - 2 * t) / (1 - t)) =
      Real.log lam + Real.log (1 - 2 * t / lam) - Real.log (1 - t) := by
    rw [hy, Real.log_div (mul_ne_zero hlam0 h2) h1,
      Real.log_mul hlam0 h2]
  have hlog1 : HasDerivAt (fun x : ℝ => Real.log (1 - x))
      (-1 / (1 - t)) t := by
    convert (((hasDerivAt_const t (1 : ℝ)).sub
      (hasDerivAt_id t)).log h1) using 1
    all_goals simp [id_eq]
  have hlog2 : HasDerivAt (fun x : ℝ => Real.log (1 - 2 * x / lam))
      ((-2 / lam) / (1 - 2 * t / lam)) t := by
    convert (((hasDerivAt_const t (1 : ℝ)).sub
      (((hasDerivAt_const t (2 : ℝ)).mul
        (hasDerivAt_id t)).div_const lam))).log h2 using 1
    all_goals simp [id_eq]
    all_goals field_simp
  have hmain :=
    (((hasDerivAt_id t).mul_const (Real.log lam)).sub
      (hasDerivAt_id t)).add
      (((hasDerivAt_const t (lam - 1)).sub
        (hasDerivAt_id t)).mul hlog1) |>.sub
      (((hasDerivAt_const t (lam / 2)).sub
        (hasDerivAt_id t)).mul hlog2)
  have hmain' : HasDerivAt (entropyCore lam)
      (Real.log lam - 1 - Real.log (1 - t) -
        (lam - 1 - t) / (1 - t) + Real.log (1 - 2 * t / lam) +
        (lam / 2 - t) * (2 / lam) / (1 - 2 * t / lam)) t := by
    convert! hmain using 1
    all_goals simp only [Pi.sub_apply, id_eq]
    all_goals ring
  have hrat : -(lam - 2 * t) / (1 - t) + 1 =
      -1 - (lam - 1 - t) / (1 - t) +
        (lam / 2 - t) * (2 / lam) / (1 - 2 * t / lam) := by
    field_simp [hlam0, h1, hd]
    ring
  convert hmain' using 1
  rw [show entropySlope lam t =
      -(lam - 2 * t) / (1 - t) + 1 +
        Real.log ((lam - 2 * t) / (1 - t)) by
      simp [entropySlope, rate]
      ring]
  rw [hlogy, hrat]
  ring

theorem hasDerivAt_entropySlope {lam t : ℝ}
    (ht : t < 1) (h2t : 2 * t < lam) :
    HasDerivAt (entropySlope lam) (entropyCurvature lam t) t := by
  have h1 : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht)
  have hd : lam - 2 * t ≠ 0 := ne_of_gt (sub_pos.mpr h2t)
  have hy0 : (lam - 2 * t) / (1 - t) ≠ 0 := div_ne_zero hd h1
  have hyderiv : HasDerivAt (fun x : ℝ => (lam - 2 * x) / (1 - x))
      ((lam - 2) / (1 - t) ^ 2) t := by
    convert! (((hasDerivAt_const t lam).sub
      ((hasDerivAt_const t (2 : ℝ)).mul (hasDerivAt_id t))).div
      ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)) h1) using 1
    all_goals simp [id_eq]
    all_goals field_simp [h1]
    all_goals ring
  have hrate : HasDerivAt rate
      (1 - 1 / ((lam - 2 * t) / (1 - t)))
      ((lam - 2 * t) / (1 - t)) := by
    unfold rate
    exact (((hasDerivAt_id _).sub_const 1).sub
      ((hasDerivAt_id _).log hy0))
  have hcomp := (hrate.comp t hyderiv).neg
  unfold entropySlope entropyCurvature
  convert! hcomp using 1
  field_simp [h1, hd]
  ring

theorem entropyCurvature_bound {lam t : ℝ}
    (hlo : (1 : ℝ) / 2 ≤ lam) (hhi : lam ≤ (3 : ℝ) / 2)
    (ht0 : 0 ≤ t) (ht : t ≤ (1 : ℝ) / 16) :
    |entropyCurvature lam t| ≤ 32 * (|lam - 1| + t) := by
  have hA : (1 : ℝ) / 2 ≤ 1 - t := by linarith
  have hB : (1 : ℝ) / 4 ≤ lam - 2 * t := by linarith
  have hA0 : 0 ≤ 1 - t := le_trans (by norm_num) hA
  have hB0 : 0 ≤ lam - 2 * t := le_trans (by norm_num) hB
  have hsq : (1 : ℝ) / 4 ≤ (1 - t) ^ 2 := by nlinarith
  have hden : (1 : ℝ) / 16 ≤ (1 - t) ^ 2 * (lam - 2 * t) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsq) hB0,
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) (sub_nonneg.mpr hB)]
  have hden0 : 0 < (1 - t) ^ 2 * (lam - 2 * t) :=
    lt_of_lt_of_le (by norm_num) hden
  have hfac : |2 - lam| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hlin : |lam - 1 - t| ≤ |lam - 1| + t := by
    calc
      |lam - 1 - t| ≤ |lam - 1| + |t| := abs_sub _ _
      _ = |lam - 1| + t := by rw [abs_of_nonneg ht0]
  have hS : 0 ≤ |lam - 1| + t := add_nonneg (abs_nonneg _) ht0
  have hnum : |(2 - lam) * (lam - 1 - t)| ≤
      2 * (|lam - 1| + t) := by
    rw [abs_mul]
    nlinarith [mul_nonneg (sub_nonneg.mpr hfac)
        (abs_nonneg (lam - 1 - t)),
      mul_nonneg (abs_nonneg (2 - lam)) (sub_nonneg.mpr hlin)]
  unfold entropyCurvature
  rw [abs_div, abs_of_pos hden0]
  apply (div_le_iff₀ hden0).2
  nlinarith [mul_nonneg hS (sub_nonneg.mpr hden)]

theorem entropy_cancellation_bound {lam t : ℝ}
    (hlo : (1 : ℝ) / 2 ≤ lam) (hhi : lam ≤ (3 : ℝ) / 2)
    (ht0 : 0 ≤ t) (ht : t ≤ (1 : ℝ) / 16) :
    |entropyCore lam t + rate lam * t| ≤
      32 * (|lam - 1| * t ^ 2 + t ^ 3) := by
  have hlam : 0 < lam := lt_of_lt_of_le (by norm_num) hlo
  have firstDerivative : ∀ x ∈ Set.Icc (0 : ℝ) t,
      HasDerivWithinAt (entropySlope lam) (entropyCurvature lam x)
        (Set.Icc (0 : ℝ) t) x := by
    intro x hx
    apply (hasDerivAt_entropySlope
      (by linarith [hx.2, ht]) (by linarith [hx.2, ht, hlo])).hasDerivWithinAt
  have curvatureBound : ∀ x ∈ Set.Ico (0 : ℝ) t,
      ‖entropyCurvature lam x‖ ≤ 32 * (|lam - 1| + t) := by
    intro x hx
    rw [Real.norm_eq_abs]
    calc
      |entropyCurvature lam x| ≤ 32 * (|lam - 1| + x) :=
        entropyCurvature_bound hlo hhi hx.1 (le_trans hx.2.le ht)
      _ ≤ 32 * (|lam - 1| + t) := by
        gcongr
        exact hx.2.le
  have slopeBound : ∀ x ∈ Set.Icc (0 : ℝ) t,
      ‖entropySlope lam x - entropySlope lam 0‖ ≤
        (32 * (|lam - 1| + t)) * x := by
    intro x hx
    simpa using! norm_image_sub_le_of_norm_deriv_le_segment'
      firstDerivative curvatureBound x hx
  have secondDerivative : ∀ x ∈ Set.Icc (0 : ℝ) t,
      HasDerivWithinAt
        (fun y => entropyCore lam y + rate lam * y)
        (entropySlope lam x + rate lam) (Set.Icc (0 : ℝ) t) x := by
    intro x hx
    convert ((hasDerivAt_entropyCore hlam
      (by linarith [hx.2, ht]) (by linarith [hx.2, ht, hlo])).add
      ((hasDerivAt_id x).const_mul (rate lam))).hasDerivWithinAt using 1
    all_goals simp
  have slopeBound' : ∀ x ∈ Set.Ico (0 : ℝ) t,
      ‖entropySlope lam x + rate lam‖ ≤
        (32 * (|lam - 1| + t)) * t := by
    intro x hx
    rw [← sub_neg_eq_add, ← entropySlope_zero]
    exact le_trans (slopeBound x ⟨hx.1, hx.2.le⟩)
      (mul_le_mul_of_nonneg_left hx.2.le (by positivity))
  have hmain := norm_image_sub_le_of_norm_deriv_le_segment'
    secondDerivative slopeBound' t ⟨ht0, le_rfl⟩
  rw [entropyCore_zero] at hmain
  simp only [mul_zero, add_zero, sub_zero, Real.norm_eq_abs] at hmain
  convert hmain using 1
  all_goals ring

theorem scaled_entropy_cancellation {n lam K : ℝ}
    (hn : 0 < n)
    (hlo : (1 : ℝ) / 2 ≤ lam) (hhi : lam ≤ (3 : ℝ) / 2)
    (hK0 : 0 ≤ K) (hK : K ≤ n / 16) :
    |n * entropyCore lam (K / n) + rate lam * K| ≤
      32 * (|lam - 1| * K ^ 2 / n + K ^ 3 / n ^ 2) := by
  have ht0 : 0 ≤ K / n := div_nonneg hK0 hn.le
  have ht : K / n ≤ (1 : ℝ) / 16 := (div_le_iff₀ hn).2 (by linarith)
  have h := entropy_cancellation_bound hlo hhi ht0 ht
  have heq : n * (entropyCore lam (K / n) + rate lam * (K / n)) =
      n * entropyCore lam (K / n) + rate lam * K := by
    field_simp
  rw [← heq, abs_mul, abs_of_pos hn]
  calc
    n * |entropyCore lam (K / n) + rate lam * (K / n)| ≤
        n * (32 * (|lam - 1| * (K / n) ^ 2 + (K / n) ^ 3)) :=
      mul_le_mul_of_nonneg_left h hn.le
    _ = 32 * (|lam - 1| * K ^ 2 / n + K ^ 3 / n ^ 2) := by
      field_simp

theorem finiteLog_to_local {L n lam K C : ℝ}
    (hn : 0 < n)
    (hlo : (1 : ℝ) / 2 ≤ lam) (hhi : lam ≤ (3 : ℝ) / 2)
    (hK0 : 0 ≤ K) (hK : K ≤ n / 16)
    (hfinite : |L - (n * entropyCore lam (K / n) + rate lam * K)| ≤
      C * K / n) :
    |L| ≤ C * K / n +
      32 * (|lam - 1| * K ^ 2 / n + K ^ 3 / n ^ 2) := by
  have hent := scaled_entropy_cancellation hn hlo hhi hK0 hK
  calc
    |L| = |(L - (n * entropyCore lam (K / n) + rate lam * K)) +
        (n * entropyCore lam (K / n) + rate lam * K)| := by ring_nf
    _ ≤ |L - (n * entropyCore lam (K / n) + rate lam * K)| +
        |n * entropyCore lam (K / n) + rate lam * K| := abs_add_le _ _
    _ ≤ C * K / n +
        32 * (|lam - 1| * K ^ 2 / n + K ^ 3 / n ^ 2) :=
      add_le_add hfinite hent

end

end Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_Local


/-!
Exact algebra for the mixed W04 logarithm.  No estimate is used here: the
ordered-pair leading term factors, and positivity permits subtraction of the
three exact logarithmic ratios.
-/
namespace Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_Mixed

noncomputable section
open scoped BigOperators

open W04_TUPLES_Foundation

theorem pairLeading_exact (n M k l : ℕ) :
    let pair : Fin 2 → ℕ := fun i => if i.val = 0 then k else l
    tupleLeading n M 2 pair =
      tupleLeading n M 1 (fun _ => k) *
        tupleLeading n M 1 (fun _ => l) := by
  simp [tupleLeading, Fin.prod_univ_two]

private theorem log_mixed_subtract
    (J₂ Jk Jl L₂ Lk Ll : ℝ)
    (hJ₂ : 0 < J₂) (hJk : 0 < Jk) (hJl : 0 < Jl)
    (hL₂ : 0 < L₂) (hLk : 0 < Lk) (hLl : 0 < Ll)
    (hfac : L₂ = Lk * Ll) :
    Real.log (J₂ / (Jk * Jl)) =
      Real.log (J₂ / L₂) - Real.log (Jk / Lk) -
        Real.log (Jl / Ll) := by
  have J₂0 := ne_of_gt hJ₂
  have Jk0 := ne_of_gt hJk
  have Jl0 := ne_of_gt hJl
  have L₂0 := ne_of_gt hL₂
  have Lk0 := ne_of_gt hLk
  have Ll0 := ne_of_gt hLl
  rw [Real.log_div J₂0 (mul_ne_zero Jk0 Jl0)]
  rw [Real.log_mul Jk0 Jl0]
  rw [Real.log_div J₂0 L₂0, Real.log_div Jk0 Lk0,
    Real.log_div Jl0 Ll0]
  rw [hfac, Real.log_mul Lk0 Ll0]
  ring

theorem mixedLog_subtract
    (n M k l : ℕ)
    (hn : 0 < n) (hlam : 0 < degreeAt n M)
    (hk : 0 < k) (hl : 0 < l)
    (hJ₂ : 0 < tupleMoment n M 2
      (fun i => if i.val = 0 then k else l))
    (hJk : 0 < tupleMoment n M 1 (fun _ => k))
    (hJl : 0 < tupleMoment n M 1 (fun _ => l)) :
    let pair : Fin 2 → ℕ := fun i => if i.val = 0 then k else l
    Real.log (tupleMoment n M 2 pair /
        (tupleMoment n M 1 (fun _ => k) *
          tupleMoment n M 1 (fun _ => l))) =
      Real.log (tupleMoment n M 2 pair / tupleLeading n M 2 pair) -
        Real.log (tupleMoment n M 1 (fun _ => k) /
          tupleLeading n M 1 (fun _ => k)) -
        Real.log (tupleMoment n M 1 (fun _ => l) /
          tupleLeading n M 1 (fun _ => l)) := by
  dsimp only
  apply log_mixed_subtract
  · exact hJ₂
  · exact hJk
  · exact hJl
  · exact tupleLeading_pos n M 2
      (fun i => if i.val = 0 then k else l) hn hlam (by
        intro i
        fin_cases i <;> simp [hk, hl])
  · exact tupleLeading_pos n M 1 (fun _ => k) hn hlam (fun _ => hk)
  · exact tupleLeading_pos n M 1 (fun _ => l) hn hlam (fun _ => hl)
  · exact pairLeading_exact n M k l

end

end Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_Mixed
