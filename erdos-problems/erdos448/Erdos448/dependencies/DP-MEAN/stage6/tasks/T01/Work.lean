module

import all Mathlib.Basic.Real.Basic
public import Erdos448.dependencies.«DP-MEAN».stage6.shared.TaskInterfaces

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.DPMean.TaskT01

@[expose] abbrev PublicTarget : Prop := Erdos448.DPMean.S6.T01Target

open Erdos448.DPMean

lemma inclusivePrimeDomain_eq_chebyshev (y : ℝ) :
    inclusivePrimeDomain y =
      (Finset.Icc 0 (Nat.floor y)).filter Nat.Prime := by
  ext p
  simp only [inclusivePrimeDomain, inclusiveNatDomain, Finset.mem_filter,
    Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hp_succ, hp_pos⟩, hp_prime⟩
    exact ⟨⟨Nat.zero_le p, Nat.lt_succ_iff.mp hp_succ⟩, hp_prime⟩
  · rintro ⟨⟨_, hp_floor⟩, hp_prime⟩
    exact ⟨⟨Nat.lt_succ_iff.mpr hp_floor, hp_prime.pos⟩, hp_prime⟩

lemma theta_eq_chebyshev (y : ℝ) :
    theta y = Chebyshev.theta y := by
  rw [theta, inclusivePrimeDomain_eq_chebyshev,
    Chebyshev.theta_eq_sum_Icc]

theorem p001_proof : P001Statement := by
  intro y hy
  rw [theta_eq_chebyshev]
  have hy_nonneg : 0 ≤ y := by linarith
  have hsharp := Chebyshev.theta_le_log4_mul_x hy_nonneg
  have hlog_two : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc
    Chebyshev.theta y ≤ Real.log 4 * y := hsharp
    _ = (2 * Real.log 2) * y := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    _ ≤ chebyshevConstant * y := by
      simp only [chebyshevConstant]
      nlinarith

theorem p003_proof : P003Statement := by
  intro h lambda1 lambda2 y _ hgeom hrange hy
  have hcoeff : 0 ≤ lambda1 * lambda2 :=
    mul_nonneg hrange.lambda1_nonnegative hrange.lambda2_nonnegative
  have hweighted :
      (∑ p ∈ inclusivePrimeDomain y,
          h p * Real.log (p : ℝ)) ≤
        (lambda1 * lambda2) * theta y := by
    rw [theta, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hp_prime : Nat.Prime p := by
      exact (Finset.mem_filter.mp hp).2
    have hp_log : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hp_prime.one_le)
    have hp_bound : h p ≤ lambda1 * lambda2 ^ (1 : ℕ) := by
      simpa using (hgeom p hp_prime 1).2
    calc
      h p * Real.log (p : ℝ) ≤
          (lambda1 * lambda2 ^ (1 : ℕ)) * Real.log (p : ℝ) :=
        mul_le_mul_of_nonneg_right hp_bound hp_log
      _ = (lambda1 * lambda2) * Real.log (p : ℝ) := by ring
  calc
    (∑ p ∈ inclusivePrimeDomain y,
        h p * Real.log (p : ℝ)) ≤
        (lambda1 * lambda2) * theta y := hweighted
    _ ≤ (lambda1 * lambda2) * (chebyshevConstant * y) :=
      mul_le_mul_of_nonneg_left (p001_proof y hy) hcoeff
    _ = firstPowerConstant lambda1 lambda2 * y := by
      simp only [firstPowerConstant]
      ring

theorem target : PublicTarget :=
  ⟨p001_proof, p003_proof⟩

end Erdos448.DPMean.TaskT01

#print axioms Erdos448.DPMean.TaskT01.target
