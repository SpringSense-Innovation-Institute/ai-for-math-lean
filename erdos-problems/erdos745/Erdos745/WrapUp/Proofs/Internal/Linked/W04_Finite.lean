module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W04_Foundation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


/-!
Elementary bounds used to retain the fixed `q` cancellations in the finite
tuple logarithm.  In particular, the shift from `K` to `K-q` must be cancelled
before absolute values are taken.
-/
namespace Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_FiniteBounds

noncomputable section

open W04_TUPLES_Local

theorem abs_log_one_sub_le {u : ℝ}
    (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) :
    |Real.log (1 - u)| ≤ 2 * u := by
  have hu1 : u < 1 := lt_of_le_of_lt hu (by norm_num)
  have hrem := log_one_sub_remainder hu0 hu1
  calc
    |Real.log (1 - u)| = |(Real.log (1 - u) + u) - u| := by ring_nf
    _ ≤ |Real.log (1 - u) + u| + |u| := abs_sub _ _
    _ ≤ u ^ 2 / (1 - u) + u := by
      rw [abs_of_nonneg hu0]
      gcongr
    _ ≤ 2 * u := by
      have hden : 0 < 1 - u := by linarith
      have hfrac : u ^ 2 / (1 - u) ≤ u := by
        apply (div_le_iff₀ hden).2
        nlinarith [sq_nonneg u]
      linarith

theorem shifted_log_cancellation {b Q : ℝ}
    (hQ : 0 ≤ Q) (hQb : Q ≤ b / 2) :
    |b * Real.log (1 - Q / b) + Q| ≤ 2 * Q ^ 2 / b := by
  by_cases hQ0 : Q = 0
  · subst Q
    simp
  have hb : 0 < b := by
    have hQpos : 0 < Q := lt_of_le_of_ne hQ (Ne.symm hQ0)
    linarith
  have hu0 : 0 ≤ Q / b := div_nonneg hQ hb.le
  have hu : Q / b ≤ 1 / 2 := (div_le_iff₀ hb).2 (by
    simpa [div_eq_mul_inv, mul_comm] using! hQb)
  have hu1 : Q / b < 1 := lt_of_le_of_lt hu (by norm_num)
  have hrem := log_one_sub_remainder hu0 hu1
  have heq : b * Real.log (1 - Q / b) + Q =
      b * (Real.log (1 - Q / b) + Q / b) := by
    field_simp
  rw [heq, abs_mul, abs_of_pos hb]
  calc
    b * |Real.log (1 - Q / b) + Q / b| ≤
        b * ((Q / b) ^ 2 / (1 - Q / b)) :=
      mul_le_mul_of_nonneg_left hrem hb.le
    _ ≤ b * (2 * (Q / b) ^ 2) := by
      gcongr
      have hden : 0 < 1 - Q / b := by linarith
      apply (div_le_iff₀ hden).2
      nlinarith [sq_nonneg (Q / b)]
    _ = 2 * Q ^ 2 / b := by
      field_simp

theorem adjacent_log_difference {n K : ℝ}
    (hn : 2 ≤ n) (hK0 : 0 ≤ K) (hK : K ≤ n / 16) :
    |Real.log (1 - K / (n - 1)) - Real.log (1 - K / n)| ≤
      8 * K / n ^ 2 := by
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n - 1 := by linarith
  have hnK : 0 < n - K := by linarith
  have hleft : 0 < 1 - K / (n - 1) := by
    apply sub_pos.mpr
    apply (div_lt_one hn1).2
    linarith
  have hright : 0 < 1 - K / n := by
    apply sub_pos.mpr
    exact (div_lt_one hn0).2 (by linarith)
  let u : ℝ := K / ((n - 1) * (n - K))
  have hden : 0 < (n - 1) * (n - K) := mul_pos hn1 hnK
  have hu0 : 0 ≤ u := div_nonneg hK0 hden.le
  have hdenLower : n ^ 2 / 4 ≤ (n - 1) * (n - K) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) (sub_nonneg.mpr hK)]
  have huHalf : u ≤ 1 / 2 := by
    dsimp [u]
    apply (div_le_iff₀ hden).2
    nlinarith [sq_nonneg n]
  have hratio : (1 - K / (n - 1)) / (1 - K / n) = 1 - u := by
    dsimp [u]
    field_simp
    ring
  rw [← Real.log_div (ne_of_gt hleft) (ne_of_gt hright), hratio]
  calc
    |Real.log (1 - u)| ≤ 2 * u := abs_log_one_sub_le hu0 huHalf
    _ ≤ 8 * K / n ^ 2 := by
      dsimp [u]
      have hnSq : 0 < n ^ 2 := sq_pos_of_pos hn0
      rw [show 2 * (K / ((n - 1) * (n - K))) =
        (2 * K) / ((n - 1) * (n - K)) by ring]
      apply (le_div_iff₀ hnSq).2
      rw [show (2 * K / ((n - 1) * (n - K))) * n ^ 2 =
        (2 * K * n ^ 2) / ((n - 1) * (n - K)) by ring]
      apply (div_le_iff₀ hden).2
      nlinarith [mul_nonneg hK0 (sub_nonneg.mpr hdenLower)]

theorem log_succ_ratio_bound {n : ℝ} (hn : 2 ≤ n) :
    |Real.log (n / (n - 1))| ≤ 2 / n := by
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n - 1 := by linarith
  have hform : n / (n - 1) = (1 - 1 / n)⁻¹ := by
    field_simp
  rw [hform, Real.log_inv]
  rw [abs_neg]
  convert abs_log_one_sub_le (u := 1 / n) (by positivity)
    ((div_le_iff₀ hn0).2 (by linarith)) using 1 <;> ring

theorem log_small_ratio_bound {X s : ℝ}
    (hX : 0 < X) (hs0 : 0 ≤ s) (hs : s ≤ X / 2) :
    |Real.log (1 - s / X)| ≤ 2 * s / X := by
  convert abs_log_one_sub_le (div_nonneg hs0 hX.le)
    ((div_le_iff₀ hX).2 (by
      simpa [div_eq_mul_inv, mul_comm] using! hs)) using 1 <;> ring

theorem sparse_correction_difference
    {n K M b N A : ℝ}
    (hn : 0 < n) (hK0 : 0 ≤ K)
    (hM1 : 1 ≤ M) (hb1 : 1 ≤ b) (hbM : b ≤ M)
    (hMb0 : 0 ≤ M - b) (hMb : M - b ≤ K)
    (hN0 : 0 < N) (hA0 : 0 < A)
    (hNlower : n ^ 2 / 4 ≤ N) (hAlower : n ^ 2 / 4 ≤ A)
    (hNupper : N ≤ n ^ 2)
    (hNA0 : 0 ≤ N - A) (hNA : N - A ≤ K * n)
    (hMn : M ≤ n) :
    |M * (M - 1) / (2 * N) - b * (b - 1) / (2 * A)| ≤
      32 * K / n := by
  have hn0 : 0 ≤ n := hn.le
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM1
  have hb0 : 0 ≤ b := le_trans (by norm_num) hb1
  have hMsub0 : 0 ≤ M - 1 := sub_nonneg.mpr hM1
  have hbsub0 : 0 ≤ b - 1 := sub_nonneg.mpr hb1
  have hMn0 : 0 ≤ n - M := sub_nonneg.mpr hMn
  have hMsq : M * (M - 1) ≤ n ^ 2 := by
    nlinarith [mul_nonneg hM0 hMsub0, mul_nonneg hM0 hMn0,
      sq_nonneg (n - M)]
  have hdiffFactor : M * (M - 1) - b * (b - 1) =
      (M - b) * (M + b - 1) := by ring
  have hsum : M + b - 1 ≤ 2 * n := by linarith
  have hsum0 : 0 ≤ M + b - 1 := by linarith
  have hfactorBound :
      0 ≤ M * (M - 1) - b * (b - 1) ∧
      M * (M - 1) - b * (b - 1) ≤ 2 * K * n := by
    rw [hdiffFactor]
    constructor
    · exact mul_nonneg hMb0 hsum0
    · nlinarith [mul_nonneg (sub_nonneg.mpr hMb) hsum0,
        mul_nonneg hMb0 (sub_nonneg.mpr hsum)]
  have hnum :
      |M * (M - 1) * A - b * (b - 1) * N| ≤ 4 * K * n ^ 3 := by
    rw [show M * (M - 1) * A - b * (b - 1) * N =
      -(M * (M - 1) * (N - A)) +
        (M * (M - 1) - b * (b - 1)) * N by ring]
    calc
      |-(M * (M - 1) * (N - A)) +
          (M * (M - 1) - b * (b - 1)) * N| ≤
          |M * (M - 1) * (N - A)| +
            |(M * (M - 1) - b * (b - 1)) * N| := by
              simpa only [abs_neg] using! abs_add_le
                (-(M * (M - 1) * (N - A)))
                ((M * (M - 1) - b * (b - 1)) * N)
      _ ≤ n ^ 2 * (K * n) + (2 * K * n) * n ^ 2 := by
        rw [abs_mul, abs_mul, abs_mul]
        rw [abs_of_nonneg hM0, abs_of_nonneg hMsub0,
          abs_of_nonneg hNA0, abs_of_nonneg hfactorBound.1,
          abs_of_pos hN0]
        exact add_le_add
          (mul_le_mul hMsq hNA hNA0 (sq_nonneg n))
          (mul_le_mul hfactorBound.2 hNupper hN0.le
            (by positivity))
      _ ≤ 4 * K * n ^ 3 := by
        nlinarith [mul_nonneg hK0 hn0, sq_nonneg n]
  have hden : 0 < 2 * N * A := by positivity
  have hdenLower : n ^ 4 / 8 ≤ 2 * N * A := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hNlower) hA0.le,
      mul_nonneg (by positivity : 0 ≤ n ^ 2 / 4)
        (sub_nonneg.mpr hAlower)]
  rw [show M * (M - 1) / (2 * N) - b * (b - 1) / (2 * A) =
      (M * (M - 1) * A - b * (b - 1) * N) / (2 * N * A) by
        field_simp]
  rw [abs_div, abs_of_pos hden]
  calc
    |M * (M - 1) * A - b * (b - 1) * N| / (2 * N * A) ≤
        (4 * K * n ^ 3) / (2 * N * A) :=
      div_le_div_of_nonneg_right hnum hden.le
    _ ≤ 32 * K / n := by
      have hn4 : 0 < n ^ 4 := pow_pos hn 4
      apply (div_le_iff₀ hden).2
      rw [show 32 * K / n * (2 * N * A) =
        (32 * K * (2 * N * A)) / n by ring]
      apply (le_div_iff₀ hn).2
      nlinarith [mul_nonneg (mul_nonneg hK0 hn0)
        (sub_nonneg.mpr hdenLower)]

end

end Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_FiniteBounds


/-!
An exact real-algebra normal form for the finite tuple logarithm.  The normal
form exposes the cancellation between the fixed shift `q` and the logarithm
whose arguments differ by that shift.
-/
namespace Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_FiniteBridge

noncomputable section

open W04_TUPLES_Local
open W04_TUPLES_FiniteBounds

def realIntegralMain (X s : ℝ) : ℝ :=
  s * Real.log X - (X - s) * Real.log (1 - s / X) - s

def realSparseMain (X s : ℝ) : ℝ :=
  s * Real.log X - s * (s - 1) / (2 * X)

def realTupleFiniteMain
    (n M lam N A K Q r b : ℝ) : ℝ :=
  realIntegralMain n K + realSparseMain A b +
    realIntegralMain M r - realSparseMain N M +
    Q * (Real.log lam - Real.log n) + lam * K - K * Real.log lam

theorem sum_range_div_eq (X : ℝ) (s : ℕ) :
    (∑ j ∈ Finset.range s, (j : ℝ) / X) =
      (s : ℝ) * ((s : ℝ) - 1) / (2 * X) := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

theorem sparseFallingMain_eq_real (X s : ℕ) :
    sparseFallingMain X s = realSparseMain X s := by
  unfold sparseFallingMain realSparseMain
  rw [sum_range_div_eq]

theorem integralFallingMain_eq_real (X s : ℕ) :
    integralFallingMain X s = realIntegralMain X s := by
  rfl

theorem tupleFiniteMain_eq_real (n M q K : ℕ) :
    tupleFiniteMain n M q K =
      realTupleFiniteMain (n : ℝ) (M : ℝ) (degreeAt n M)
        (capacity n : ℝ) (((n - K).choose 2 : ℕ) : ℝ)
        (K : ℝ) (q : ℝ) ((K - q : ℕ) : ℝ)
        ((M + q - K : ℕ) : ℝ) := by
  simp only [tupleFiniteMain, realTupleFiniteMain]
  rw [integralFallingMain_eq_real, sparseFallingMain_eq_real,
    integralFallingMain_eq_real, sparseFallingMain_eq_real]

theorem realTupleFiniteMain_residual_identity
    {n M lam N A K Q r b : ℝ}
    (hr : r = K - Q) (hb : b = M - r)
    (hn : n ≠ 0) (hlam : lam ≠ 0)
    (hM : 2 * M = lam * n)
    (hlogA : Real.log A = Real.log N + Real.log (1 - K / n) +
      Real.log (1 - K / (n - 1)))
    (hbalance : Real.log n + Real.log M - Real.log N - Real.log lam =
      Real.log (n / (n - 1))) :
    realTupleFiniteMain n M lam N A K Q r b -
        (n * entropyCore lam (K / n) + rate lam * K) =
      b * (Real.log (1 - K / (n - 1)) - Real.log (1 - K / n)) +
      b * (Real.log (1 - K / M) - Real.log (1 - r / M)) +
      2 * Q * Real.log (1 - K / n) -
      Q * Real.log (1 - K / M) +
      r * Real.log (n / (n - 1)) + Q +
      (M * (M - 1) / (2 * N) - b * (b - 1) / (2 * A)) := by
  subst r
  subst b
  have hM0 : M ≠ 0 := by
    intro hzero
    rw [hzero] at hM
    simp only [mul_zero, zero_eq_mul] at hM
    rcases hM with h | h
    · exact hlam h
    · exact hn h
  have hlamEq : lam = 2 * M / n := by
    apply (eq_div_iff hn).2
    linarith
  rw [hlamEq] at hbalance ⊢
  unfold realTupleFiniteMain realIntegralMain realSparseMain entropyCore rate
  rw [hlogA]
  have hz : 1 - 2 * (K / n) / (2 * M / n) = 1 - K / M := by
    field_simp [hn, hM0]
  rw [hz]
  rw [← hbalance]
  field_simp [hn, hM0]
  ring

theorem shifted_middle_identity {M K Q : ℝ}
    (hb : 0 < M - K + Q) (hMQ : M - K ≠ 0) (hM : M ≠ 0) :
    (M - K + Q) *
        (Real.log (1 - K / M) - Real.log (1 - (K - Q) / M)) + Q =
      (M - K + Q) * Real.log (1 - Q / (M - K + Q)) + Q := by
  have hleft : 1 - K / M ≠ 0 := by
    rw [show 1 - K / M = (M - K) / M by field_simp]
    exact div_ne_zero hMQ hM
  have hright : 1 - (K - Q) / M ≠ 0 := by
    rw [show 1 - (K - Q) / M = (M - K + Q) / M by
      field_simp [hM]
      ring]
    exact div_ne_zero (ne_of_gt hb) hM
  have hratio : (1 - K / M) / (1 - (K - Q) / M) =
      1 - Q / (M - K + Q) := by
    rw [show 1 - K / M = (M - K) / M by field_simp [hM]]
    rw [show 1 - (K - Q) / M = (M - K + Q) / M by
      field_simp [hM]
      ring]
    field_simp [hM, hMQ, ne_of_gt hb]
    ring
  rw [← Real.log_div hleft hright]
  rw [hratio]

theorem shifted_middle_bound {M K Q : ℝ}
    (hM : 0 < M) (hQ : 0 ≤ Q) (hKM : K < M)
    (hQK : Q ≤ K) (hhalf : Q ≤ (M - K + Q) / 2) :
    |(M - K + Q) *
        (Real.log (1 - K / M) - Real.log (1 - (K - Q) / M)) + Q| ≤
      2 * Q ^ 2 / (M - K + Q) := by
  have hb : 0 < M - K + Q := by
    linarith
  have hMK : M - K ≠ 0 := ne_of_gt (sub_pos.mpr hKM)
  rw [shifted_middle_identity hb hMK (ne_of_gt hM)]
  exact shifted_log_cancellation hQ hhalf

private theorem abs_five_add_le (a b c d e : ℝ) :
    |a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  calc
    |a + b + c + d + e| ≤ |a + b + c + d| + |e| := abs_add_le _ _
    _ ≤ (|a + b + c| + |d|) + |e| := by gcongr; exact abs_add_le _ _
    _ ≤ ((|a + b| + |c|) + |d|) + |e| := by gcongr; exact abs_add_le _ _
    _ ≤ (((|a| + |b|) + |c|) + |d|) + |e| := by gcongr; exact abs_add_le _ _
    _ = _ := by ring

set_option maxHeartbeats 800000 in
theorem realTupleFiniteMain_local_remainder
    {n M lam N A K Q r b : ℝ}
    (hr : r = K - Q) (hb : b = M - r)
    (hn8 : 8 ≤ n) (hK0 : 0 ≤ K) (hK : K ≤ n / 16)
    (hQ0 : 0 ≤ Q) (hQK : Q ≤ K)
    (hMlo : n / 4 ≤ M) (hMhi : M ≤ n)
    (hbLo : n / 8 ≤ b) (hbM : b ≤ M)
    (hQhalf : Q ≤ b / 2)
    (hN0 : 0 < N) (hA0 : 0 < A)
    (hNlower : n ^ 2 / 4 ≤ N) (hAlower : n ^ 2 / 4 ≤ A)
    (hNupper : N ≤ n ^ 2)
    (hNA0 : 0 ≤ N - A) (hNA : N - A ≤ K * n)
    (hn0 : n ≠ 0) (hlam0 : lam ≠ 0)
    (hdegree : 2 * M = lam * n)
    (hlogA : Real.log A = Real.log N + Real.log (1 - K / n) +
      Real.log (1 - K / (n - 1)))
    (hbalance : Real.log n + Real.log M - Real.log N - Real.log lam =
      Real.log (n / (n - 1))) :
    |realTupleFiniteMain n M lam N A K Q r b -
        (n * entropyCore lam (K / n) + rate lam * K)| ≤
      64 * (Q + 1) * K / n := by
  have hn : 0 < n := by linarith
  have hn2 : 2 ≤ n := by linarith
  have hM : 0 < M := lt_of_lt_of_le (by positivity) hMlo
  have hKM : K < M := by linarith
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) hbLo
  have hM1 : 1 ≤ M := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hMb0 : 0 ≤ M - b := sub_nonneg.mpr hbM
  have hMb : M - b ≤ K := by rw [hb, hr]; linarith
  have hbN : b ≤ n := le_trans hbM hMhi
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hrK : r ≤ K := by rw [hr]; linarith
  have hmain := realTupleFiniteMain_residual_identity hr hb hn0 hlam0
    hdegree hlogA hbalance
  rw [hmain]
  let t1 := b * (Real.log (1 - K / (n - 1)) - Real.log (1 - K / n))
  let t2 := b * (Real.log (1 - K / M) - Real.log (1 - r / M)) + Q
  let t3 := 2 * Q * Real.log (1 - K / n) - Q * Real.log (1 - K / M)
  let t4 := r * Real.log (n / (n - 1))
  let t5 := M * (M - 1) / (2 * N) - b * (b - 1) / (2 * A)
  have heq :
      b * (Real.log (1 - K / (n - 1)) - Real.log (1 - K / n)) +
        b * (Real.log (1 - K / M) - Real.log (1 - r / M)) +
        2 * Q * Real.log (1 - K / n) - Q * Real.log (1 - K / M) +
        r * Real.log (n / (n - 1)) + Q +
        (M * (M - 1) / (2 * N) - b * (b - 1) / (2 * A)) =
      t1 + t2 + t3 + t4 + t5 := by
    dsimp [t1, t2, t3, t4, t5]
    ring
  rw [heq]
  have ht1 : |t1| ≤ 8 * K / n := by
    dsimp [t1]
    rw [abs_mul, abs_of_pos hb0]
    calc
      b * |Real.log (1 - K / (n - 1)) - Real.log (1 - K / n)| ≤
          b * (8 * K / n ^ 2) :=
        mul_le_mul_of_nonneg_left (adjacent_log_difference hn2 hK0 hK) hb0.le
      _ ≤ 8 * K / n := by
        field_simp [ne_of_gt hn]
        nlinarith [mul_nonneg (sub_nonneg.mpr hbN) hK0]
  have ht2 : |t2| ≤ 16 * Q * K / n := by
    dsimp [t2]
    have hbEq : b = M - K + Q := by rw [hb, hr]; ring
    rw [hbEq, hr]
    have hs := shifted_middle_bound hM hQ0 hKM hQK (by
      rw [← hbEq]
      exact hQhalf)
    apply le_trans hs
    rw [← hbEq]
    have hQsq : Q ^ 2 ≤ Q * K := by nlinarith [mul_nonneg hQ0 (sub_nonneg.mpr hQK)]
    have hbn : n ≤ 8 * b := by linarith
    field_simp [ne_of_gt hb0, ne_of_gt hn]
    nlinarith [mul_nonneg hQ0 hK0,
      mul_nonneg (sub_nonneg.mpr hQsq) (sub_nonneg.mpr hbn)]
  have hlogn : |Real.log (1 - K / n)| ≤ 2 * K / n :=
    log_small_ratio_bound hn hK0 (by linarith)
  have hlogM : |Real.log (1 - K / M)| ≤ 2 * K / M :=
    log_small_ratio_bound hM hK0 (by linarith)
  have hMratio : 2 * K / M ≤ 8 * K / n := by
    field_simp [ne_of_gt hM, ne_of_gt hn]
    nlinarith [mul_nonneg hK0 (sub_nonneg.mpr hMlo)]
  have ht3 : |t3| ≤ 12 * Q * K / n := by
    dsimp [t3]
    calc
      |2 * Q * Real.log (1 - K / n) - Q * Real.log (1 - K / M)| ≤
          |2 * Q * Real.log (1 - K / n)| +
            |Q * Real.log (1 - K / M)| := abs_sub _ _
      _ = 2 * Q * |Real.log (1 - K / n)| +
          Q * |Real.log (1 - K / M)| := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hQ0]
            norm_num
      _ ≤ 2 * Q * (2 * K / n) + Q * (8 * K / n) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hlogn (mul_nonneg (by norm_num) hQ0))
          (mul_le_mul_of_nonneg_left (le_trans hlogM hMratio) hQ0)
      _ = 12 * Q * K / n := by ring
  have ht4 : |t4| ≤ 2 * K / n := by
    dsimp [t4]
    rw [abs_mul, abs_of_nonneg hr0]
    calc
      r * |Real.log (n / (n - 1))| ≤ r * (2 / n) :=
        mul_le_mul_of_nonneg_left (log_succ_ratio_bound hn2) hr0
      _ ≤ 2 * K / n := by
        have hn' : 0 ≤ 2 / n := by positivity
        convert mul_le_mul_of_nonneg_right hrK hn' using 1 <;> ring
  have ht5 : |t5| ≤ 32 * K / n := by
    dsimp [t5]
    exact sparse_correction_difference hn hK0 hM1 hb1 hbM hMb0 hMb
      hN0 hA0 hNlower hAlower hNupper hNA0 hNA hMhi
  calc
    |t1 + t2 + t3 + t4 + t5| ≤
        |t1| + |t2| + |t3| + |t4| + |t5| := abs_five_add_le _ _ _ _ _
    _ ≤ 8 * K / n + 16 * Q * K / n + 12 * Q * K / n +
          2 * K / n + 32 * K / n := by linarith
    _ ≤ 64 * (Q + 1) * K / n := by
      field_simp [ne_of_gt hn]
      nlinarith [mul_nonneg hQ0 hK0]

set_option maxHeartbeats 800000 in
theorem tupleFiniteMain_local_remainder
    {n M q K : ℕ}
    (hn32 : 32 ≤ n) (hqK : q ≤ K)
    (hqSmall : (q : ℝ) ≤ (n : ℝ) / 16)
    (hK : (K : ℝ) ≤ (n : ℝ) / 16)
    (hlo : (1 : ℝ) / 2 ≤ degreeAt n M)
    (hhi : degreeAt n M ≤ (3 : ℝ) / 2) :
    |tupleFiniteMain n M q K -
        ((n : ℝ) * entropyCore (degreeAt n M) ((K : ℝ) / n) +
          rate (degreeAt n M) * K)| ≤
      64 * ((q : ℝ) + 1) * K / n := by
  let nr : ℝ := n
  let mr : ℝ := M
  let kr : ℝ := K
  let qr : ℝ := q
  let rr : ℝ := (K - q : ℕ)
  let br : ℝ := (M + q - K : ℕ)
  let Nr : ℝ := capacity n
  let Ar : ℝ := (n - K).choose 2
  have hn : 0 < nr := by dsimp [nr]; positivity
  have hn32r : 32 ≤ nr := by dsimp [nr]; exact_mod_cast hn32
  have hn8 : 8 ≤ nr := by linarith
  have hn0 : nr ≠ 0 := ne_of_gt hn
  have hK0 : 0 ≤ kr := by positivity
  have hq0 : 0 ≤ qr := by positivity
  have hqKr : qr ≤ kr := by dsimp [qr, kr]; exact_mod_cast hqK
  have hKn : K ≤ n := by
    exact_mod_cast (le_trans hK (by nlinarith : (n : ℝ) / 16 ≤ n))
  have hMlo : nr / 4 ≤ mr := by
    dsimp [nr, mr] at hn ⊢
    unfold degreeAt at hlo
    field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt (lt_of_lt_of_le (by omega) hn32))] at hlo
    linarith
  have hMhi : mr ≤ nr := by
    dsimp [nr, mr] at hn ⊢
    unfold degreeAt at hhi
    field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt (lt_of_lt_of_le (by omega) hn32))] at hhi
    linarith
  have hKMnat : K ≤ M := by
    have hkMreal : kr ≤ mr := by
      dsimp [kr]
      exact le_trans hK (le_trans (by dsimp [nr]; nlinarith) hMlo)
    dsimp [kr, mr] at hkMreal
    exact_mod_cast hkMreal
  have hrNat : K - q ≤ M := by omega
  have hbNat : M + q - K = M - (K - q) := by omega
  have hrr : rr = kr - qr := by
    dsimp [rr, kr, qr]
    rw [Nat.cast_sub hqK]
  have hbrr : br = mr - rr := by
    dsimp [br, mr]
    rw [hbNat, Nat.cast_sub hrNat]
  have hbM : br ≤ mr := by
    rw [hbrr]
    have : 0 ≤ rr := by positivity
    linarith
  have hbLo : nr / 8 ≤ br := by
    rw [hbrr, hrr]
    nlinarith
  have hqHalf : qr ≤ br / 2 := by
    nlinarith
  have hdegree : 2 * mr = degreeAt n M * nr := by
    dsimp [mr, nr]
    unfold degreeAt
    field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt (lt_of_lt_of_le (by omega) hn32))]
  have hlam0 : degreeAt n M ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hlo)
  have hNr : Nr = nr * (nr - 1) / 2 := by
    dsimp [Nr, nr, capacity]
    rw [Nat.cast_choose_two]
  have hAr : Ar = (nr - kr) * (nr - kr - 1) / 2 := by
    dsimp [Ar, nr, kr]
    rw [Nat.cast_choose_two, Nat.cast_sub hKn]
  have hNr0 : 0 < Nr := by
    rw [hNr]
    have : 0 < nr - 1 := by linarith
    positivity
  have hAr0 : 0 < Ar := by
    rw [hAr]
    have hx : 0 < nr - kr := by nlinarith
    have hy : 0 < nr - kr - 1 := by nlinarith
    positivity
  have hNlower : nr ^ 2 / 4 ≤ Nr := by
    rw [hNr]
    nlinarith [sq_nonneg nr]
  have hAlower : nr ^ 2 / 4 ≤ Ar := by
    rw [hAr]
    have hx : 15 * nr / 16 ≤ nr - kr := by nlinarith
    have hy : 7 * nr / 8 ≤ nr - kr - 1 := by nlinarith
    have hp := mul_le_mul hx hy (by positivity) (by nlinarith)
    nlinarith [sq_nonneg nr]
  have hNupper : Nr ≤ nr ^ 2 := by
    rw [hNr]
    nlinarith [sq_nonneg nr]
  have hNA0 : 0 ≤ Nr - Ar := by
    rw [hNr, hAr]
    nlinarith [mul_nonneg hK0 (sub_nonneg.mpr hK)]
  have hNA : Nr - Ar ≤ kr * nr := by
    rw [hNr, hAr]
    nlinarith [mul_nonneg hK0 (sub_nonneg.mpr hK)]
  have hAeq : Ar = Nr * (1 - kr / nr) * (1 - kr / (nr - 1)) := by
    rw [hNr, hAr]
    have hn1 : nr - 1 ≠ 0 := ne_of_gt (by linarith)
    field_simp [hn0, hn1]
    ring
  have hx0 : 1 - kr / nr ≠ 0 := by
    have : kr < nr := by nlinarith
    exact ne_of_gt (sub_pos.mpr ((div_lt_one hn).2 this))
  have hw0 : 1 - kr / (nr - 1) ≠ 0 := by
    have hn1 : 0 < nr - 1 := by linarith
    have : kr < nr - 1 := by nlinarith
    exact ne_of_gt (sub_pos.mpr ((div_lt_one hn1).2 this))
  have hlogA : Real.log Ar = Real.log Nr + Real.log (1 - kr / nr) +
      Real.log (1 - kr / (nr - 1)) := by
    rw [hAeq, Real.log_mul (mul_ne_zero (ne_of_gt hNr0) hx0) hw0,
      Real.log_mul (ne_of_gt hNr0) hx0]
  have hmr0 : mr ≠ 0 := ne_of_gt (lt_of_lt_of_le (by positivity) hMlo)
  have hn1r : nr - 1 ≠ 0 := ne_of_gt (by linarith)
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hMform : mr = degreeAt n M * nr / 2 := by
    rw [← hdegree]
    ring
  have hNform : Nr = nr * (nr - 1) / 2 := hNr
  have hlogBalance : Real.log nr + Real.log mr - Real.log Nr -
      Real.log (degreeAt n M) = Real.log (nr / (nr - 1)) := by
    rw [hMform, hNform]
    rw [Real.log_div (mul_ne_zero hlam0 hn0) htwo,
      Real.log_mul hlam0 hn0]
    rw [Real.log_div (mul_ne_zero hn0 hn1r) htwo,
      Real.log_mul hn0 hn1r]
    rw [Real.log_div hn0 hn1r]
    ring
  rw [tupleFiniteMain_eq_real]
  exact realTupleFiniteMain_local_remainder hrr hbrr hn8 hK0 hK hq0 hqKr
    hMlo hMhi hbLo hbM hqHalf hNr0 hAr0 hNlower hAlower hNupper hNA0 hNA
    hn0 hlam0 hdegree hlogA hlogBalance

end

end Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_FiniteBridge
