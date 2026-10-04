module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-04».Helpers

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT04.Pointwise

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Erdos448.Stage7.ROOT04.Helpers

noncomputable section

lemma theta_pos (q : Lemma4Parameters) : 0 < q.theta :=
  lt_of_lt_of_le (by norm_num) q.theta_ge_two

lemma high_cutoff (q : Lemma4Parameters) (k : ℕ)
    (hk : (Real.log q.sigma / Real.log q.theta) * Real.log q.xi ≤ k) :
    goodU0 q.toGoodParameters ≤ q.theta ^ k := by
  have hlt : 0 < Real.log q.theta := Real.log_pos
    (lt_of_lt_of_le (by norm_num) q.theta_ge_two)
  have hls := log_sigma_pos q.toGoodParameters
  have hli := log_xi_pos q.toGoodParameters
  have hexp : Real.log q.xi * Real.log q.sigma ≤ (k : ℝ) * Real.log q.theta := by
    have hk' : (Real.log q.xi * Real.log q.sigma) / Real.log q.theta ≤ (k : ℝ) := by
      calc
        (Real.log q.xi * Real.log q.sigma) / Real.log q.theta =
            (Real.log q.sigma / Real.log q.theta) * Real.log q.xi := by ring
        _ ≤ (k : ℝ) := hk
    have := (div_le_iff₀ hlt).mp hk'
    nlinarith
  rw [goodU0, ← Real.exp_log (pow_pos (theta_pos q) k), Real.exp_le_exp,
    Real.log_pow]
  simpa [mul_comm] using hexp

lemma low_cutoff (q : Lemma4Parameters) (k : ℕ)
    (hk : (k : ℝ) <
      (Real.log q.sigma / Real.log q.theta) * Real.log q.xi) :
    q.theta ^ k < goodU0 q.toGoodParameters := by
  have hlt : 0 < Real.log q.theta := Real.log_pos
    (lt_of_lt_of_le (by norm_num) q.theta_ge_two)
  have hexp : (k : ℝ) * Real.log q.theta <
      Real.log q.xi * Real.log q.sigma := by
    have hk' : (k : ℝ) <
        (Real.log q.xi * Real.log q.sigma) / Real.log q.theta := by
      calc
        (k : ℝ) < (Real.log q.sigma / Real.log q.theta) * Real.log q.xi := hk
        _ = (Real.log q.xi * Real.log q.sigma) / Real.log q.theta := by ring
    exact (lt_div_iff₀ hlt).mp hk'
  rw [goodU0, ← Real.exp_log (pow_pos (theta_pos q) k), Real.exp_lt_exp,
    Real.log_pow]
  simpa [mul_comm] using hexp

lemma log_goodU_ratio (q : Lemma4Parameters) :
    Real.log (goodU0 q.toGoodParameters) / Real.log q.sigma = Real.log q.xi := by
  have hls : Real.log q.sigma ≠ 0 := ne_of_gt (log_sigma_pos q.toGoodParameters)
  have hp : 0 < Real.log q.xi * Real.log q.sigma :=
    mul_pos (log_xi_pos q.toGoodParameters) (log_sigma_pos q.toGoodParameters)
  rw [goodU0, Real.log_exp]
  field_simp

theorem pointwise_bound
    (q : Lemma4Parameters) (y : ℝ) (hy0 : 0 < y) (hy1 : y < 1)
    (n m : PosNat) (hn : goodU0 q.toGoodParameters < n.1)
    (hgood : Good q.toGoodParameters n m) (k : ℕ) (hk1 : 1 ≤ k)
    (hhalf : (1 / 2 : ℝ) * Real.log q.sigma / Real.log q.theta ≤ k)
    (_hpow : q.theta ^ k ≤ (m.1 : ℝ)) (hpow_n : q.theta ^ k < n.1) :
    1 ≤ goodPowerMajorant q y k m := by
  let Q : ℝ := 1 / 2 + q.epsilonInt
  let B : ℝ := 2 * k * Real.log q.xi * Real.log q.theta / Real.log q.sigma
  have hli := log_xi_pos q.toGoodParameters
  have hlt := log_sigma_pos
    ({ epsilonInt := q.epsilonInt, epsilonInt_pos := q.epsilonInt_pos,
       epsilonInt_le_tenth := q.epsilonInt_le_tenth, xi := q.xi,
       xi_gt_one := q.xi_gt_one, sigma := q.theta,
       sigma_ge_two := q.theta_ge_two } : GoodParameters)
  have hls := log_sigma_pos q.toGoodParameters
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk1)
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hlogxi1 := good_forces_one_le_log_xi q.toGoodParameters n m hn hgood
  have hQ0 : 0 ≤ Q := by
    dsimp [Q]
    linarith [q.epsilonInt_pos]
  have homega : (omegaBelow m (q.theta ^ k) : ℝ) ≤ Q * Real.log B := by
    by_cases hhigh :
        (Real.log q.sigma / Real.log q.theta) * Real.log q.xi ≤ (k : ℝ)
    · have hU := high_cutoff q k hhigh
      have hupp := good_upper q.toGoodParameters n m hgood hU hpow_n
      have hratio : Real.log (q.theta ^ k) / Real.log q.sigma =
          (k : ℝ) * Real.log q.theta / Real.log q.sigma := by
        rw [Real.log_pow]
      rw [hratio] at hupp
      have hR : 0 < (k : ℝ) * Real.log q.theta / Real.log q.sigma := by positivity
      have hRB : (k : ℝ) * Real.log q.theta / Real.log q.sigma ≤ B := by
        dsimp [B]
        have hfac : 1 ≤ 2 * Real.log q.xi := by linarith
        have := mul_le_mul_of_nonneg_right hfac (le_of_lt hR)
        field_simp at this ⊢
        nlinarith
      have hlog : Real.log ((k : ℝ) * Real.log q.theta / Real.log q.sigma) ≤
          Real.log B := Real.log_le_log hR hRB
      exact hupp.trans (mul_le_mul_of_nonneg_left hlog hQ0)
    · have hlow : (k : ℝ) <
          (Real.log q.sigma / Real.log q.theta) * Real.log q.xi :=
        lt_of_not_ge hhigh
      have hcut := low_cutoff q k hlow
      have hmono : omegaBelow m (q.theta ^ k) ≤
          omegaBelow m (goodU0 q.toGoodParameters) :=
        omegaBelow_mono (le_of_lt hcut)
      have hupp := good_upper q.toGoodParameters n m hgood le_rfl hn
      rw [log_goodU_ratio q] at hupp
      have hxiB : Real.log q.xi ≤ B := by
        have hfac : 1 ≤ 2 * (k : ℝ) * Real.log q.theta / Real.log q.sigma := by
          have := (div_le_iff₀ hlt).mp hhalf
          dsimp at this
          have hls0 : 0 ≤ Real.log q.sigma := le_of_lt hls
          field_simp at this ⊢
          nlinarith
        dsimp [B]
        have := mul_le_mul_of_nonneg_left hfac (le_of_lt hli)
        field_simp at this ⊢
        nlinarith
      have hlog : Real.log (Real.log q.xi) ≤ Real.log B :=
        Real.log_le_log hli hxiB
      calc
        (omegaBelow m (q.theta ^ k) : ℝ) ≤ omegaBelow m (goodU0 q.toGoodParameters) := by
          exact_mod_cast hmono
        _ ≤ Q * Real.log (Real.log q.xi) := hupp
        _ ≤ Q * Real.log B := mul_le_mul_of_nonneg_left hlog hQ0
  unfold goodPowerMajorant
  change 1 ≤ B.rpow (-Q * Real.log y) * y.rpow (omegaBelow m (q.theta ^ k) : ℝ)
  exact one_le_rpow_product hB hy0 hy1 homega

end

end Erdos448.Stage7.ROOT04.Pointwise
