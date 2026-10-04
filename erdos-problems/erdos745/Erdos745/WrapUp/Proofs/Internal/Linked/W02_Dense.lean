module

public import Erdos745.WrapUp.Contracts

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


/-!
# The finite counting boundary for the dense-excess branch

The dense branch of W02 does not pass through the kernel expansion.  This
module records the direct finite estimate obtained by forgetting connectedness
and then forgetting the exact size of the ambient edge type.  The deliberately
coarse square bound is sufficient for the later numerical absorption because
the final exponential constant is very large.
-/

noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Dense

open Erdos745.WrapUp

private theorem card_edge_le_sq (k : ℕ) :
    Fintype.card (Edge k) ≤ k * k := by
  change Fintype.card {e : Fin k × Fin k // e.1 < e.2} ≤ _
  calc
    _ ≤ Fintype.card (Fin k × Fin k) := Fintype.card_subtype_le _
    _ = k * k := by simp

private theorem connectedCount_le_chooseCard (k m : ℕ) :
    connectedCount k m ≤ (Fintype.card (Edge k)).choose m := by
  classical
  unfold connectedCount
  calc
    ((fixedGraphs k m).filter
      (fun G => 0 < k ∧ ∀ u v : Fin k, reach G u v)).card
        ≤ (fixedGraphs k m).card := Finset.card_filter_le _ _
    _ = (Fintype.card (Edge k)).choose m := by
      unfold fixedGraphs allGraphs
      rw [show (Finset.univ : Finset (Edge k)).powerset.filter
          (fun G => G.card = m) =
          Finset.powersetCard m (Finset.univ : Finset (Edge k)) by
        symm
        exact Finset.powersetCard_eq_filter]
      simp

/-- A direct fixed-edge-count bound.  It is independent of the
pruning/suppression construction used in the sparse branch. -/
theorem connectedCount_le_sq_pow_div_factorial (k m : ℕ) :
    (connectedCount k m : ℝ) ≤
      ((k * k : ℕ) : ℝ) ^ m / (m.factorial : ℝ) := by
  calc
    (connectedCount k m : ℝ) ≤
        ((Fintype.card (Edge k)).choose m : ℝ) := by
      exact_mod_cast connectedCount_le_chooseCard k m
    _ ≤ (Fintype.card (Edge k) : ℝ) ^ m / (m.factorial : ℝ) :=
      Nat.choose_le_pow_div m (Fintype.card (Edge k))
    _ ≤ ((k * k : ℕ) : ℝ) ^ m / (m.factorial : ℝ) := by
      gcongr
      exact_mod_cast card_edge_le_sq k

private theorem factorial_lower (n : ℕ) (hn : 0 < n) :
    ((n : ℝ) / 3) ^ n ≤ (n.factorial : ℝ) := by
  have hbase : (n : ℝ) / 3 ≤ (n : ℝ) / Real.exp 1 := by
    gcongr
    exact Real.exp_one_lt_three.le
  have hp : ((n : ℝ) / 3) ^ n ≤ ((n : ℝ) / Real.exp 1) ^ n :=
    pow_le_pow_left₀ (by positivity) hbase n
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (n : ℝ)) := by
    rw [Real.one_le_sqrt]
    have hpi : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  calc
    ((n : ℝ) / 3) ^ n ≤ ((n : ℝ) / Real.exp 1) ^ n := hp
    _ ≤ Real.sqrt (2 * Real.pi * (n : ℝ)) *
        ((n : ℝ) / Real.exp 1) ^ n := by
      exact le_mul_of_one_le_left (by positivity) hsqrt
    _ ≤ (n.factorial : ℝ) := Stirling.le_factorial_stirling n

/-- The elementary dense bound preceding the final power absorption. -/
theorem connectedCount_le_dense_base (k r : ℕ) (hk : 0 < k) (hr : 0 < r) :
    (connectedCount k (k + r) : ℝ) ≤
      (3 * (k : ℝ) ^ 2 / (r : ℝ)) ^ (k + r) := by
  have hf := factorial_lower (k + r) (by omega)
  calc
    (connectedCount k (k + r) : ℝ) ≤
        ((k * k : ℕ) : ℝ) ^ (k + r) / ((k + r).factorial : ℝ) :=
      connectedCount_le_sq_pow_div_factorial k (k + r)
    _ ≤ ((k * k : ℕ) : ℝ) ^ (k + r) /
        (((k + r : ℕ) : ℝ) / 3) ^ (k + r) := by
      gcongr
    _ = (3 * (k : ℝ) ^ 2 / ((k + r : ℕ) : ℝ)) ^ (k + r) := by
      rw [← div_pow]
      congr 1
      push_cast
      field_simp
    _ ≤ (3 * (k : ℝ) ^ 2 / (r : ℝ)) ^ (k + r) := by
      gcongr
      omega

end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Dense


/-!
# Exact dense-excess absorption

This module closes the `r ≥ k` half of the final W02 estimate.  The proof is
kept in logarithmic form: the direct fixed-edge-count estimate is positive,
and the only loss beyond it is the elementary bound `k ≤ 2^r`.
-/

noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_DenseFinal

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Dense

private theorem cast_le_two_pow (k r : ℕ) (hkr : k ≤ r) :
    (k : ℝ) ≤ (2 : ℝ) ^ r := by
  calc
    (k : ℝ) ≤ (r : ℝ) := by exact_mod_cast hkr
    _ ≤ (2 : ℝ) ^ r / ((2 : ℝ) - 1) :=
      Nat.cast_le_pow_div_sub (by norm_num : (1 : ℝ) < 2) r
    _ = (2 : ℝ) ^ r := by ring

private theorem half_log_cast_le (k r : ℕ) (hk : 0 < k) (hkr : k ≤ r) :
    (1 / 2 : ℝ) * Real.log (k : ℝ) ≤ (r : ℝ) * Real.log 2 := by
  have hkR : (0 : ℝ) < k := by positivity
  have hpowR : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have hlog : Real.log (k : ℝ) ≤ Real.log ((2 : ℝ) ^ r) :=
    (Real.log_le_log_iff hkR hpowR).2 (cast_le_two_pow k r hkr)
  rw [Real.log_pow] at hlog
  have hlog_nonneg : 0 ≤ Real.log (k : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast hk)
  nlinarith

private theorem log_eighteen :
    Real.log (18 : ℝ) = 2 * Real.log 3 + Real.log 2 := by
  calc
    Real.log (18 : ℝ) = Real.log ((3 : ℝ) ^ 2 * 2) := by norm_num
    _ = Real.log ((3 : ℝ) ^ 2) + Real.log 2 := by
      rw [Real.log_mul] <;> norm_num
    _ = 2 * Real.log 3 + Real.log 2 := by rw [Real.log_pow]; norm_num

private theorem dense_log_bound (k r : ℕ) (hk : 0 < k) (hr : 0 < r)
    (hkr : k ≤ r) :
    ((k + r : ℕ) : ℝ) *
        Real.log (3 * (k : ℝ) ^ 2 / (r : ℝ)) ≤
      Real.log 18 * (r : ℝ) +
        Real.log (r : ℝ) * (-(r : ℝ) / 2) +
        Real.log (k : ℝ) *
          ((k : ℝ) + (3 * (r : ℝ) - 1) / 2) := by
  have hkR : (0 : ℝ) < k := by positivity
  have hrR : (0 : ℝ) < r := by positivity
  have hkrR : (k : ℝ) ≤ r := by exact_mod_cast hkr
  have hlogkr : Real.log (k : ℝ) - Real.log (r : ℝ) ≤ 0 := by
    have := (Real.log_le_log_iff hkR hrR).2 hkrR
    linarith
  have hcoef : 0 ≤ (k : ℝ) + (r : ℝ) / 2 := by positivity
  have hratio :
      ((k : ℝ) + (r : ℝ) / 2) *
          (Real.log (k : ℝ) - Real.log (r : ℝ)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hcoef hlogkr
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hsum3 :
      ((k : ℝ) + (r : ℝ)) * Real.log 3 ≤
        2 * (r : ℝ) * Real.log 3 := by
    exact mul_le_mul_of_nonneg_right (by linarith) hlog3
  have hhalf := half_log_cast_le k r hk hkr
  have hbase :
      Real.log (3 * (k : ℝ) ^ 2 / (r : ℝ)) =
        Real.log 3 + 2 * Real.log (k : ℝ) - Real.log (r : ℝ) := by
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    ring
  rw [hbase, log_eighteen]
  push_cast
  nlinarith

private theorem dense_scale_as_exp (k r : ℕ) (hk : 0 < k) (hr : 0 < r) :
    (18 : ℝ) ^ r *
        Real.rpow (r : ℝ) (-(r : ℝ) / 2) *
        Real.rpow (k : ℝ) ((k : ℝ) + (3 * (r : ℝ) - 1) / 2) =
      Real.exp
        (Real.log 18 * (r : ℝ) +
          Real.log (r : ℝ) * (-(r : ℝ) / 2) +
          Real.log (k : ℝ) *
            ((k : ℝ) + (3 * (r : ℝ) - 1) / 2)) := by
  change (18 : ℝ) ^ r *
      ((r : ℝ) ^ (-(r : ℝ) / 2) : ℝ) *
      ((k : ℝ) ^ ((k : ℝ) + (3 * (r : ℝ) - 1) / 2) : ℝ) = _
  rw [← Real.rpow_natCast]
  rw [Real.rpow_def_of_pos (x := (18 : ℝ)) (by norm_num) (r : ℝ),
    Real.rpow_def_of_pos (x := (r : ℝ)) (by positivity) (-(r : ℝ) / 2),
    Real.rpow_def_of_pos (x := (k : ℝ)) (by positivity)
      ((k : ℝ) + (3 * (r : ℝ) - 1) / 2)]
  rw [← Real.exp_add, ← Real.exp_add]

/-- Dense-excess half of the final public scale, with a small base `18`.
The public constant is much larger, so this theorem can be inserted directly
into the final two-regime assembly. -/
theorem connectedCount_le_dense_target (k r : ℕ) (hk : 0 < k) (hr : 0 < r)
    (hkr : k ≤ r) :
    (connectedCount k (k + r) : ℝ) ≤
      (18 : ℝ) ^ r *
        Real.rpow (r : ℝ) (-(r : ℝ) / 2) *
        Real.rpow (k : ℝ) ((k : ℝ) + (3 * (r : ℝ) - 1) / 2) := by
  have hbase : 0 < 3 * (k : ℝ) ^ 2 / (r : ℝ) := by positivity
  calc
    (connectedCount k (k + r) : ℝ) ≤
        (3 * (k : ℝ) ^ 2 / (r : ℝ)) ^ (k + r) :=
      connectedCount_le_dense_base k r hk hr
    _ = Real.exp
        (((k + r : ℕ) : ℝ) *
          Real.log (3 * (k : ℝ) ^ 2 / (r : ℝ))) := by
      rw [← Real.rpow_natCast,
        Real.rpow_def_of_pos hbase]
      ring_nf
    _ ≤ Real.exp
        (Real.log 18 * (r : ℝ) +
          Real.log (r : ℝ) * (-(r : ℝ) / 2) +
          Real.log (k : ℝ) *
            ((k : ℝ) + (3 * (r : ℝ) - 1) / 2)) := by
      exact Real.exp_le_exp.mpr (dense_log_bound k r hk hr hkr)
    _ = (18 : ℝ) ^ r *
        Real.rpow (r : ℝ) (-(r : ℝ) / 2) *
        Real.rpow (k : ℝ) ((k : ℝ) + (3 * (r : ℝ) - 1) / 2) :=
      (dense_scale_as_exp k r hk hr).symm

end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_DenseFinal
