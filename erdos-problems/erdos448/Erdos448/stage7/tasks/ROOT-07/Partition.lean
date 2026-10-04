module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage6.TaskContracts

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT07.Partition

open Finset
open scoped BigOperators

open Erdos448.Stage4
open Erdos448.Stage4.Contracts

noncomputable section

lemma inner_partition
    (q : WeightParameters) (hSigma : q.sigma <= q.theta ^ q.k)
    (x : ℝ) (d d' : ℕ) (hd : 0 < d) (hd' : 0 < d') :
    (∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
        (safeLog m).rpow (-1 / 2) *
          shiftedMean q (zValue x m d d')
            ⟨d * d', Nat.mul_pos hd hd'⟩) =
      (∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
        if q.theta ^ q.k <= zValue x m d d' then
          (safeLog m).rpow (-1 / 2) *
            shiftedMean q (zValue x m d d') ⟨d * d', Nat.mul_pos hd hd'⟩
        else 0) +
      (∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
        if q.sigma <= zValue x m d d' ∧
            zValue x m d d' < q.theta ^ q.k then
          (safeLog m).rpow (-1 / 2) *
            shiftedMean q (zValue x m d d') ⟨d * d', Nat.mul_pos hd hd'⟩
        else 0) +
      (∑ m ∈ positiveNatsBelow (x / (d * d' : ℕ)),
        if zValue x m d d' < q.sigma then
          (safeLog m).rpow (-1 / 2) *
            shiftedMean q (zValue x m d d') ⟨d * d', Nat.mul_pos hd hd'⟩
        else 0) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hu : q.theta ^ q.k <= zValue x m d d'
  · have hnm : ¬(q.sigma <= zValue x m d d' ∧
        zValue x m d d' < q.theta ^ q.k) := fun h => (not_lt_of_ge hu) h.2
    have hnt : ¬zValue x m d d' < q.sigma :=
      not_lt_of_ge (hSigma.trans hu)
    simp [hu, hnm, hnt]
  · have hlt : zValue x m d d' < q.theta ^ q.k := lt_of_not_ge hu
    by_cases hm : q.sigma <= zValue x m d d'
    · have hnt : ¬zValue x m d d' < q.sigma := not_lt_of_ge hm
      simp [hu, hm, hlt, hnt]
    · have ht : zValue x m d d' < q.sigma := lt_of_not_ge hm
      simp [hu, hm, ht]

theorem p061 : P061Statement := by
  intro q hSigma x hx
  classical
  simp only [smoothedRegular, partitionAccepts]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d' hd'
  by_cases hd0 : 0 < d
  · by_cases hd'0 : 0 < d'
    · by_cases houter : q.theta ^ q.k <= (d : ℝ) ∧
          Close q.theta ⟨d, hd0⟩ ⟨d', hd'0⟩
      · simp only [hd0, hd'0, houter, true_and, and_true, dite_true, if_true]
        rw [inner_partition q hSigma x d d' hd0 hd'0]
        ring
      · simp [hd0, hd'0, houter]
    · simp [hd'0]
  · simp [hd0]

end

end Erdos448.Stage7.ROOT07.Partition
