module

public import LeanProject.ErdosProblems.P732.ProjectivePlane
public import Mathlib.NumberTheory.Bertrand
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

noncomputable section
open scoped Filter
open Filter

namespace ErdosProblems
namespace P732

/-!
Arithmetic and asymptotic estimates for the final lower bound.

The constants are intentionally coarse. Bertrand's postulate gives a prime
`q` comparable to `sqrt n`; a crude binomial estimate then dominates
`exp (c * sqrt n * log n)` for a fixed positive `c`.
-/

theorem binomial_lower_bound_pow (q : ℕ) (hq : 2 ≤ q) :
    ((q : ℝ) ^ (q - 2)) ≤
      (Nat.choose ((q ^ 2 + q + 1) + q - 2) (q - 2) : ℝ) := by
  let r := q - 2
  let M := (q ^ 2 + q + 1) + q - 2
  have hchoose :
      ((((M + 1 - r) ^ r : ℕ) : ℝ) / (Nat.factorial r : ℝ)) ≤
        (Nat.choose M r : ℝ) := by
    simpa [M, r] using (Nat.pow_le_choose (α := ℝ) r M)
  have hrleq : r ≤ q := by simp [r]
  have hfact_nat : Nat.factorial r ≤ q ^ r := by
    calc
      Nat.factorial r ≤ r ^ r := Nat.factorial_le_pow r
      _ ≤ q ^ r := Nat.pow_le_pow_left hrleq r
  have hfact : (Nat.factorial r : ℝ) ≤ (q : ℝ) ^ r := by
    exact_mod_cast hfact_nat
  have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
  have hqpow_nonneg : 0 ≤ (q : ℝ) ^ r := pow_nonneg hq_nonneg r
  have hbase_nat : q ^ 2 ≤ M + 1 - r := by
    simp [M, r]
    omega
  have hbase : (q : ℝ) ^ 2 ≤ (((M + 1 - r) : ℕ) : ℝ) := by
    exact_mod_cast hbase_nat
  have hpoweq : (q : ℝ) ^ r * (q : ℝ) ^ r = ((q : ℝ) ^ 2) ^ r := by
    rw [← pow_add, ← pow_mul]
    congr 1
    omega
  have hmul :
      (Nat.factorial r : ℝ) * (q : ℝ) ^ r ≤
        (((M + 1 - r) ^ r : ℕ) : ℝ) := by
    calc
      (Nat.factorial r : ℝ) * (q : ℝ) ^ r ≤
          (q : ℝ) ^ r * (q : ℝ) ^ r := by
        exact mul_le_mul_of_nonneg_right hfact hqpow_nonneg
      _ = ((q : ℝ) ^ 2) ^ r := hpoweq
      _ ≤ (((M + 1 - r) : ℕ) : ℝ) ^ r := by
        exact pow_le_pow_left₀ (sq_nonneg (q : ℝ)) hbase r
      _ = (((M + 1 - r) ^ r : ℕ) : ℝ) := by
        norm_num
  have hdiv :
      (q : ℝ) ^ r ≤
        ((((M + 1 - r) ^ r : ℕ) : ℝ) / (Nat.factorial r : ℝ)) := by
    rw [le_div_iff₀' (by exact_mod_cast Nat.factorial_pos r)]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  simpa [M, r] using hdiv.trans hchoose

theorem prime_for_large_n (n : ℕ) (hnlarge : 1024 ^ 2 ≤ n) :
    ∃ q : ℕ, Nat.Prime q ∧ 64 ≤ q ∧ q ^ 2 + q + 1 ≤ n ∧
      Real.sqrt (n : ℝ) ≤ 64 * (q : ℝ) ∧ (n : ℝ) ≤ (q : ℝ) ^ 4 := by
  let s := Nat.sqrt n
  let m := s / 16
  have hs_ge : 1024 ≤ s := by
    rw [Nat.le_sqrt']
    exact hnlarge
  have hm_pos : m ≠ 0 := by
    have hm_ge_one : 1 ≤ m := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 16)]
      omega
    omega
  rcases Nat.exists_prime_lt_and_le_two_mul m hm_pos with ⟨q, hqprime, _hmq, hqle⟩
  have hm_ge64 : 64 ≤ m := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 16)]
    omega
  have hq64 : 64 ≤ q := by omega
  have hs_divmod : 16 * m + s % 16 = s := by
    simpa [m] using Nat.div_add_mod s 16
  have hsmod : s % 16 < 16 := Nat.mod_lt s (by norm_num : 0 < 16)
  have hs_succ_le16q : s + 1 ≤ 16 * q := by omega
  have h8q_le_s : 8 * q ≤ s := by
    have h8q_le : 8 * q ≤ 8 * (2 * m) := Nat.mul_le_mul_left 8 hqle
    have h16m_le_s : 16 * m ≤ s := by omega
    omega
  have hgeom_piece : q ^ 2 + q + 1 ≤ (8 * q) ^ 2 := by
    nlinarith [show 1 ≤ q by omega]
  have hgeom : q ^ 2 + q + 1 ≤ n := by
    calc
      q ^ 2 + q + 1 ≤ (8 * q) ^ 2 := hgeom_piece
      _ ≤ s ^ 2 := Nat.pow_le_pow_left h8q_le_s 2
      _ ≤ n := Nat.sqrt_le' n
  have hsqrt_le : Real.sqrt (n : ℝ) ≤ 64 * (q : ℝ) := by
    have hsqrt_le_succ : Real.sqrt (n : ℝ) ≤ (s : ℝ) + 1 := by
      simpa [s] using (Real.real_sqrt_lt_nat_sqrt_succ (a := n)).le
    have hs_succ_real : (s : ℝ) + 1 ≤ 16 * (q : ℝ) := by
      exact_mod_cast hs_succ_le16q
    calc
      Real.sqrt (n : ℝ) ≤ (s : ℝ) + 1 := hsqrt_le_succ
      _ ≤ 16 * (q : ℝ) := hs_succ_real
      _ ≤ 64 * (q : ℝ) := by
        nlinarith [show (0 : ℝ) ≤ q by positivity]
  have hn_le_q4 : (n : ℝ) ≤ (q : ℝ) ^ 4 := by
    have hn_le_succ_sq_nat : n ≤ (s + 1) ^ 2 :=
      Nat.le_of_lt (by simpa [s] using Nat.lt_succ_sqrt' n)
    have hn_le_succ_sq : (n : ℝ) ≤ ((s + 1 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast hn_le_succ_sq_nat
    have hs_succ_real : ((s + 1 : ℕ) : ℝ) ≤ 16 * (q : ℝ) := by
      exact_mod_cast hs_succ_le16q
    have hsucc_nonneg : 0 ≤ ((s + 1 : ℕ) : ℝ) := by positivity
    have hsq_le : ((s + 1 : ℕ) : ℝ) ^ 2 ≤ (16 * (q : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hsucc_nonneg hs_succ_real 2
    have hlast : (16 * (q : ℝ)) ^ 2 ≤ (q : ℝ) ^ 4 := by
      nlinarith [sq_nonneg ((q : ℝ)), sq_nonneg ((q : ℝ) - 16),
        show (16 : ℝ) ≤ q by exact_mod_cast (show 16 ≤ q by omega)]
    exact hn_le_succ_sq.trans (hsq_le.trans hlast)
  exact ⟨q, hqprime, hq64, hgeom, hsqrt_le, hn_le_q4⟩

theorem binomial_exponential_lower_bound {n q : ℕ} (hn : 1 ≤ n) (hq : 64 ≤ q)
    (hsqrt : Real.sqrt (n : ℝ) ≤ 64 * (q : ℝ))
    (hn_le : (n : ℝ) ≤ (q : ℝ) ^ 4) :
    Real.exp ((1 / 4096 : ℝ) * Real.sqrt (n : ℝ) * Real.log (n : ℝ))
      ≤ (Nat.choose ((q ^ 2 + q + 1) + q - 2) (q - 2) : ℝ) := by
  have hqpos_nat : 0 < q := by omega
  have hq2 : 2 ≤ q := by omega
  have hq4 : 4 ≤ q := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hqpos_nat
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hlogq_nonneg : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqone
  have hlogn_le : Real.log (n : ℝ) ≤ 4 * Real.log (q : ℝ) := by
    calc
      Real.log (n : ℝ) ≤ Real.log ((q : ℝ) ^ 4) := Real.log_le_log hnpos hn_le
      _ = 4 * Real.log (q : ℝ) := by
        rw [Real.log_pow]
        norm_num
  have hqminus : (q : ℝ) / 2 ≤ ((q - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hq2]
    nlinarith [show (4 : ℝ) ≤ (q : ℝ) by exact_mod_cast hq4]
  have hmain :
      (1 / 4096 : ℝ) * Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤
        ((q - 2 : ℕ) : ℝ) * Real.log (q : ℝ) := by
    calc
      (1 / 4096 : ℝ) * Real.sqrt (n : ℝ) * Real.log (n : ℝ)
          ≤ (1 / 4096 : ℝ) * (64 * (q : ℝ)) * Real.log (n : ℝ) := by
        gcongr
      _ ≤ (1 / 4096 : ℝ) * (64 * (q : ℝ)) * (4 * Real.log (q : ℝ)) := by
        gcongr
      _ = ((q : ℝ) / 16) * Real.log (q : ℝ) := by ring
      _ ≤ ((q : ℝ) / 2) * Real.log (q : ℝ) := by
        gcongr
        nlinarith [show 0 ≤ (q : ℝ) by positivity]
      _ ≤ ((q - 2 : ℕ) : ℝ) * Real.log (q : ℝ) := by
        exact mul_le_mul_of_nonneg_right hqminus hlogq_nonneg
  have hpowpos : 0 < (q : ℝ) ^ (q - 2) := pow_pos hqpos _
  have hexp_pow :
      Real.exp ((1 / 4096 : ℝ) * Real.sqrt (n : ℝ) * Real.log (n : ℝ)) ≤
        (q : ℝ) ^ (q - 2) := by
    calc
      Real.exp ((1 / 4096 : ℝ) * Real.sqrt (n : ℝ) * Real.log (n : ℝ))
          ≤ Real.exp (((q - 2 : ℕ) : ℝ) * Real.log (q : ℝ)) :=
        Real.exp_le_exp.mpr hmain
      _ = (q : ℝ) ^ (q - 2) := by
        rw [← Real.log_pow, Real.exp_log hpowpos]
  exact hexp_pow.trans (binomial_lower_bound_pow q hq2)

theorem eventually_exists_primePower_lower_bound :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∃ q : ℕ, PrimePower q ∧
          q ^ 2 + q + 1 ≤ n ∧
          Real.exp (c * Real.sqrt (n : ℝ) * Real.log (n : ℝ))
            ≤ (Nat.choose ((q ^ 2 + q + 1) + q - 2) (q - 2) : ℝ) := by
  refine ⟨1 / 4096, by norm_num, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (1024 ^ 2)] with n hnlarge
  rcases prime_for_large_n n hnlarge with
    ⟨q, hqprime, hq64, hgeom, hsqrt, hn_le_q4⟩
  have hn : 1 ≤ n := by omega
  refine ⟨q, ?_, hgeom, ?_⟩
  · exact ⟨q, 1, hqprime, by norm_num, by simp⟩
  · exact binomial_exponential_lower_bound hn hq64 hsqrt hn_le_q4

end P732
end ErdosProblems
