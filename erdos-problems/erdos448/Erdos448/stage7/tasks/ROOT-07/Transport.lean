module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage6.TaskContracts

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT07.Transport

open Finset
open scoped BigOperators

open Erdos448.Stage4
open Erdos448.Stage4.Contracts

noncomputable section

lemma safeLog_rpow_nonneg (z e : ℝ) :
    0 <= (safeLog z).rpow e :=
  Real.rpow_nonneg (by simp [safeLog]) e

lemma mem_positiveNatsBelow {z : ℝ} {n : ℕ} :
    n ∈ positiveNatsBelow z ↔ 0 < n ∧ (n : ℝ) < z := by
  constructor
  · intro hn
    exact (Finset.mem_filter.mp hn).2
  · rintro ⟨hn, hnz⟩
    rw [positiveNatsBelow, Finset.mem_filter]
    exact ⟨by simpa using Nat.lt_ceil.mpr hnz, hn, hnz⟩

theorem p062 (h055 : P055Statement) : P062Statement := by
  intro theta htheta
  obtain ⟨C, hC, hbound⟩ := h055 theta htheta
  refine ⟨C, hC, ?_⟩
  intro q hq hSigma x hx
  classical
  simp only [smoothedRegular, substitutedRegular, partitionAccepts]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d' hd'
  by_cases hd0 : 0 < d
  · by_cases hd'0 : 0 < d'
    · by_cases houter : q.theta ^ q.k <= (d : ℝ) ∧
          Close q.theta ⟨d, hd0⟩ ⟨d', hd'0⟩
      · simp only [hd0, hd'0, houter, true_and, and_true, dite_true, if_true]
        let A : ℝ := (roughIndicator d q.sigma : ℝ) *
          q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ)
        let L : ℝ := (Real.log q.sigma).rpow (-q.y / 2) *
          (q.k : ℝ).rpow ((q.y - 1) / 2) * w2Weight q (d * d')
        have hA : 0 <= A := by
          exact mul_nonneg (by positivity) (Real.rpow_nonneg (le_of_lt q.y_pos) _)
        have hsum :
            (∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
              if q.theta ^ q.k <= zValue x m d d' then
                (safeLog m).rpow (-1 / 2) *
                  shiftedMean q (zValue x m d d')
                    ⟨d * d', Nat.mul_pos hd0 hd'0⟩
              else 0) <=
            ∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
              C * L *
                (if q.theta ^ q.k <= zValue x m d d' then
                  (safeLog m).rpow (-1 / 2) * zValue x m d d' *
                    (safeLog (zValue x m d d')).rpow (-1 / 2)
                else 0) := by
          apply Finset.sum_le_sum
          intro m hm
          by_cases hz : q.theta ^ q.k <= zValue x m d d'
          · simp only [hz, true_and, and_true, if_true]
            have hzbound := hbound q hq
              ⟨d * d', Nat.mul_pos hd0 hd'0⟩ (zValue x m d d') hz hSigma
            have hsafe : 0 <= (safeLog (m : ℝ)).rpow (-1 / 2) :=
              safeLog_rpow_nonneg _ _
            dsimp [L]
            calc
              (safeLog (m : ℝ)).rpow (-1 / 2) *
                    shiftedMean q (zValue x m d d')
                      ⟨d * d', Nat.mul_pos hd0 hd'0⟩
                  <= (safeLog (m : ℝ)).rpow (-1 / 2) *
                    (C * zValue x m d d' * w2Weight q (d * d') *
                      (Real.log q.sigma).rpow (-q.y / 2) *
                      (q.k : ℝ).rpow ((q.y - 1) / 2) *
                      (safeLog (zValue x m d d')).rpow (-1 / 2)) :=
                mul_le_mul_of_nonneg_left hzbound hsafe
              _ = C *
                    ((Real.log q.sigma).rpow (-q.y / 2) *
                      (q.k : ℝ).rpow ((q.y - 1) / 2) * w2Weight q (d * d')) *
                    ((safeLog (m : ℝ)).rpow (-1 / 2) * zValue x m d d' *
                      (safeLog (zValue x m d d')).rpow (-1 / 2)) := by ring
          · simp [hz]
        calc
          A * (∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                if q.theta ^ q.k <= zValue x m d d' then
                  (safeLog m).rpow (-1 / 2) *
                    shiftedMean q (zValue x m d d')
                      ⟨d * d', Nat.mul_pos hd0 hd'0⟩
                else 0)
              <= A * (∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                C * L *
                  (if q.theta ^ q.k <= zValue x m d d' then
                    (safeLog m).rpow (-1 / 2) * zValue x m d d' *
                      (safeLog (zValue x m d d')).rpow (-1 / 2)
                  else 0)) := mul_le_mul_of_nonneg_left hsum hA
          _ = C * (A *
                ((Real.log q.sigma).rpow (-q.y / 2) *
                  (q.k : ℝ).rpow ((q.y - 1) / 2) * w2Weight q (d * d') *
                  ∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                    if q.theta ^ q.k <= zValue x m d d' then
                      (safeLog m).rpow (-1 / 2) * zValue x m d d' *
                        (safeLog (zValue x m d d')).rpow (-1 / 2)
                    else 0)) := by
              dsimp [A, L]
              rw [← Finset.mul_sum]
              ring
      · simp [hd0, hd'0, houter]
    · simp [hd'0]
  · simp [hd0]

theorem p064 (h056 : P056Statement) : P064Statement := by
  intro theta htheta
  obtain ⟨C, hC, hbound⟩ := h056 theta htheta
  refine ⟨C, hC, ?_⟩
  intro q hq hSigma x hx
  classical
  simp only [smoothedRegular, substitutedRegular, partitionAccepts]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d' hd'
  by_cases hd0 : 0 < d
  · by_cases hd'0 : 0 < d'
    · by_cases houter : q.theta ^ q.k <= (d : ℝ) ∧
          Close q.theta ⟨d, hd0⟩ ⟨d', hd'0⟩
      · simp only [hd0, hd'0, houter, true_and, and_true, dite_true, if_true]
        letI (p : Prop) : Decidable p := Classical.propDecidable p
        let A : ℝ := (roughIndicator d q.sigma : ℝ) *
          q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ)
        let L : ℝ := (Real.log q.sigma).rpow (-q.y / 2) *
          w2Weight q (d * d')
        have hA : 0 <= A := by
          exact mul_nonneg (by positivity) (Real.rpow_nonneg (le_of_lt q.y_pos) _)
        have hsum :
            (∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
              if q.sigma <= zValue x m d d' ∧
                  zValue x m d d' < q.theta ^ q.k then
                (safeLog m).rpow (-1 / 2) *
                  shiftedMean q (zValue x m d d')
                    ⟨d * d', Nat.mul_pos hd0 hd'0⟩
              else 0) <=
            ∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
              C * L *
                (if q.sigma <= zValue x m d d' ∧
                    zValue x m d d' < q.theta ^ q.k then
                  (safeLog m).rpow (-1 / 2) * zValue x m d d' *
                    (safeLog (zValue x m d d')).rpow (q.y / 2 - 1)
                else 0) := by
          apply Finset.sum_le_sum
          intro m hm
          by_cases hz : q.sigma <= zValue x m d d' ∧
              zValue x m d d' < q.theta ^ q.k
          · simp only [hz, true_and, and_true, if_true]
            have hzpos : 0 < zValue x m d d' :=
              lt_of_lt_of_le
                (lt_of_lt_of_le (by norm_num) q.theta_ge_two)
                (q.sigma_ge_theta.trans hz.1)
            have hzbound := hbound q hq
              ⟨d * d', Nat.mul_pos hd0 hd'0⟩ (zValue x m d d') hzpos hz.1 hz.2
            have hsafe : 0 <= (safeLog (m : ℝ)).rpow (-1 / 2) :=
              safeLog_rpow_nonneg _ _
            dsimp [L]
            calc
              (safeLog (m : ℝ)).rpow (-1 / 2) *
                    shiftedMean q (zValue x m d d')
                      ⟨d * d', Nat.mul_pos hd0 hd'0⟩
                  <= (safeLog (m : ℝ)).rpow (-1 / 2) *
                    (C * zValue x m d d' * w2Weight q (d * d') *
                      (Real.log q.sigma).rpow (-q.y / 2) *
                      (safeLog (zValue x m d d')).rpow (q.y / 2 - 1)) :=
                mul_le_mul_of_nonneg_left hzbound hsafe
              _ = C *
                    ((Real.log q.sigma).rpow (-q.y / 2) * w2Weight q (d * d')) *
                    ((safeLog (m : ℝ)).rpow (-1 / 2) * zValue x m d d' *
                      (safeLog (zValue x m d d')).rpow (q.y / 2 - 1)) := by ring
          · simp [hz]
        calc
          A * (∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                if q.sigma <= zValue x m d d' ∧
                    zValue x m d d' < q.theta ^ q.k then
                  (safeLog m).rpow (-1 / 2) *
                    shiftedMean q (zValue x m d d')
                      ⟨d * d', Nat.mul_pos hd0 hd'0⟩
                else 0)
              <= A * (∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                C * L *
                  (if q.sigma <= zValue x m d d' ∧
                      zValue x m d d' < q.theta ^ q.k then
                    (safeLog m).rpow (-1 / 2) * zValue x m d d' *
                      (safeLog (zValue x m d d')).rpow (q.y / 2 - 1)
                  else 0)) := mul_le_mul_of_nonneg_left hsum hA
          _ = C * (A *
                ((Real.log q.sigma).rpow (-q.y / 2) * w2Weight q (d * d') *
                  ∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                    if q.sigma <= zValue x m d d' ∧
                        zValue x m d d' < q.theta ^ q.k then
                      (safeLog m).rpow (-1 / 2) * zValue x m d d' *
                        (safeLog (zValue x m d d')).rpow (q.y / 2 - 1)
                    else 0)) := by
              dsimp [A, L]
              rw [← Finset.mul_sum]
              ring
        simp [A]
      · simp [hd0, hd'0, houter]
    · simp [hd'0]
  · simp [hd0]

theorem p066 (h057 : P057Statement) : P066Statement := by
  intro q hSigma x hx
  classical
  simp only [smoothedRegular, substitutedRegular, partitionAccepts]
  apply Finset.sum_le_sum
  intro d hd
  apply Finset.sum_le_sum
  intro d' hd'
  by_cases hd0 : 0 < d
  · by_cases hd'0 : 0 < d'
    · by_cases houter : q.theta ^ q.k <= (d : ℝ) ∧
          Close q.theta ⟨d, hd0⟩ ⟨d', hd'0⟩
      · simp only [hd0, hd'0, houter, true_and, and_true, dite_true, if_true]
        let A : ℝ := (roughIndicator d q.sigma : ℝ) *
          q.y.rpow (omegaBelowRaw d (q.theta ^ q.k) : ℝ)
        have hA : 0 <= A := by
          exact mul_nonneg (by positivity) (Real.rpow_nonneg (le_of_lt q.y_pos) _)
        have hsum :
            (∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
              if zValue x m d d' < q.sigma then
                (safeLog m).rpow (-1 / 2) *
                  shiftedMean q (zValue x m d d')
                    ⟨d * d', Nat.mul_pos hd0 hd'0⟩
              else 0) <=
            w1Weight (d * d') *
              ∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
                if zValue x m d d' < q.sigma then
                  (safeLog m).rpow (-1 / 2)
                else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro m hm
          by_cases hz : zValue x m d d' < q.sigma
          · simp only [hz, if_true]
            have hmPos : 0 < m := (mem_positiveNatsBelow.mp hm).1
            have hzPos : 0 < zValue x m d d' := by
              unfold zValue
              have hxPos : 0 < x := by
                have htheta_pos : 0 < q.theta :=
                  lt_of_lt_of_le (by norm_num) q.theta_ge_two
                have hpow_pos : 0 < q.theta ^ (2 * q.k - 1) :=
                  pow_pos htheta_pos _
                linarith
              positivity
            have hzbound := h057 q
              ⟨d * d', Nat.mul_pos hd0 hd'0⟩ (zValue x m d d') hzPos hz
            calc
              (safeLog (m : ℝ)).rpow (-1 / 2) *
                    shiftedMean q (zValue x m d d')
                      ⟨d * d', Nat.mul_pos hd0 hd'0⟩
                  <= (safeLog (m : ℝ)).rpow (-1 / 2) * w1Weight (d * d') :=
                mul_le_mul_of_nonneg_left hzbound
                  (safeLog_rpow_nonneg (m : ℝ) (-1 / 2))
              _ = w1Weight (d * d') * (safeLog (m : ℝ)).rpow (-1 / 2) := by ring
          · simp [hz]
        exact mul_le_mul_of_nonneg_left hsum hA
      · simp [hd0, hd'0, houter]
    · simp [hd'0]
  · simp [hd0]

end

end Erdos448.Stage7.ROOT07.Transport
