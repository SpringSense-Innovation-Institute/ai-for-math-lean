module

import all Mathlib.Basic.Real.Basic
public import Erdos448.dependencies.«DP-MERTENS».stage5.LoweringInterfaces
public import Mathlib.NumberTheory.Chebyshev

public section

set_option backward.isDefEq.respectTransparency false

open Finset
open scoped BigOperators

namespace Erdos448.DPMertens.Tasks.MSCChebyshev

noncomputable section

open Erdos448.DPMertens
open Erdos448.DPMertens.Lowering

/- The project cutoff is extensionally the cutoff used by mathlib's Chebyshev
function.  In particular, filtering out nonprimes removes the possible zero
endpoint in `Ioc 0 ⌊x⌋₊`. -/
lemma theta_eq_chebyshevTheta (x : ℝ) :
    theta x = Chebyshev.theta x := by
  unfold theta primesLE Chebyshev.theta
  congr 1
  ext p
  simp only [mem_filter, mem_range, mem_Ioc]
  constructor
  · rintro ⟨hp_lt, hp⟩
    exact ⟨⟨hp.pos, Nat.lt_succ_iff.mp hp_lt⟩, hp⟩
  · rintro ⟨⟨_, hp_le⟩, hp⟩
    exact ⟨Nat.lt_succ_iff.mpr hp_le, hp⟩

/- The exact cell estimate `n < p ≤ 2n`: `primorial_add_le` is proved by
putting every prime in that cell into the central binomial coefficient. -/
lemma theta_two_mul_sub_theta_le (n : ℕ) (hn : 0 < n) :
    theta (2 * n) - theta n ≤ (n : ℝ) * Real.log 4 := by
  rw [theta_eq_chebyshevTheta, theta_eq_chebyshevTheta,
    Chebyshev.theta_eq_log_primorial, Chebyshev.theta_eq_log_primorial]
  have hfloor : ⌊(2 : ℝ) * (n : ℝ)⌋₊ = 2 * n := by
    rw [show (2 : ℝ) * (n : ℝ) = ((2 * n : ℕ) : ℝ) by norm_num,
      Nat.floor_natCast]
  rw [hfloor, Nat.floor_natCast]
  have hprim :
      primorial (2 * n) ≤ primorial n * Nat.choose (2 * n) n := by
    rw [Nat.two_mul]
    exact primorial_add_le (m := n) (n := n) (le_refl n)
  have hchoose_pos : 0 < Nat.choose (2 * n) n :=
    Nat.choose_pos (by omega)
  have hchoose : Nat.choose (2 * n) n ≤ 4 ^ n := by
    calc
      Nat.choose (2 * n) n ≤ 2 ^ (2 * n) := Nat.choose_le_two_pow _ _
      _ = 4 ^ n := by rw [pow_mul]; norm_num
  have hlogprim :
      Real.log (primorial (2 * n) : ℝ) ≤
        Real.log ((primorial n * Nat.choose (2 * n) n : ℕ) : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast primorial_pos (2 * n)
    · exact_mod_cast hprim
  have hlogchoose :
      Real.log (Nat.choose (2 * n) n : ℝ) ≤ Real.log ((4 : ℝ) ^ n) := by
    apply Real.log_le_log
    · exact_mod_cast hchoose_pos
    · exact_mod_cast hchoose
  calc
    Real.log (primorial (2 * n) : ℝ) -
          Real.log (primorial n : ℝ)
        ≤ Real.log ((primorial n * Nat.choose (2 * n) n : ℕ) : ℝ) -
          Real.log (primorial n : ℝ) := sub_le_sub_right hlogprim _
    _ = Real.log (Nat.choose (2 * n) n : ℝ) := by
      rw [Nat.cast_mul, Real.log_mul]
      · ring
      · exact_mod_cast (primorial_pos n).ne'
      · exact_mod_cast hchoose_pos.ne'
    _ ≤ Real.log ((4 : ℝ) ^ n) := hlogchoose
    _ = (n : ℝ) * Real.log 4 := by rw [Real.log_pow]

/-- The direct, predecessor-free implementation of the frozen output. -/
@[expose] def result : Erdos448.DPMertens.Lowering.TASK_MSC_CHEBYSHEV_Target where
  increment := theta_two_mul_sub_theta_le
  C_vartheta := Real.log 4
  C_vartheta_pos := Real.log_pos (by norm_num)
  weak_bound := by
    intro t ht
    rw [theta_eq_chebyshevTheta]
    exact Chebyshev.theta_le_log4_mul_x (by positivity)

end

end Erdos448.DPMertens.Tasks.MSCChebyshev
