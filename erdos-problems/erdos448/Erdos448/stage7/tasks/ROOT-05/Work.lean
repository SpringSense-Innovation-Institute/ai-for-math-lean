module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-05».Recovered
public import Erdos448.stage7.tasks.«ROOT-05».candidates.«CU-P051G-H.Result»
public import Erdos448.stage7.tasks.«ROOT-05».candidates.«P050.Reindex»

public section

set_option backward.isDefEq.respectTransparency false

/-!
ROOT-05 worker surface (pre-CU ROOT ownership restored).

The recovered verified nodes imported above are immutable solved
prerequisites — see `RECOVERY_STATE.md` and
`Erdos448/stage7/recovery/PRE_CU_PROOF_RECOVERY.json`. Do not re-prove them.

Remaining nodes (in construction order): P-050, P-001C, P-051G, P-051H.
The final deliverable is `Erdos448.Stage7.ROOT05.Work.result` proving
`Erdos448.Stage6.TaskContracts.ROOT05Target`, threading the recovered
`Recovered.weightChain` witness into the export assembly.
-/

namespace Erdos448.Stage7.ROOT05.Work

open Finset Set
open scoped BigOperators NNReal

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Erdos448.Stage6.TaskContracts
open Erdos448.Stage7.ROOT05.Recovered

noncomputable section

local instance instPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

lemma mem_positiveNatsBelow {x : ℝ} {n : ℕ} :
    n ∈ positiveNatsBelow x ↔ 0 < n ∧ (n : ℝ) < x := by
  constructor
  · intro hn
    exact (Finset.mem_filter.mp hn).2
  · rintro ⟨hn, hnx⟩
    rw [positiveNatsBelow, Finset.mem_filter]
    exact ⟨by simpa using Nat.lt_ceil.mpr hnx, hn, hnx⟩

lemma mem_positiveNatsUpTo {N n : ℕ} :
    n ∈ positiveNatsUpTo N ↔ 0 < n ∧ n ≤ N := by
  simp [positiveNatsUpTo, and_comm]

lemma positiveNatsBelow_eq_empty_of_le_one {z : ℝ} (hz : z ≤ 1) :
    positiveNatsBelow z = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro n hn
  ·
    have hn' := mem_positiveNatsBelow.mp hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn'.1
    exact (not_lt_of_ge hn1 (hn'.2.trans_le hz)).elim

lemma isRough_mul_iff (a b : ℕ) (s : ℝ) :
    IsRough (a * b) s ↔ IsRough a s ∧ IsRough b s := by
  constructor
  · intro h
    constructor
    · intro p hp hpa
      exact h p hp (dvd_mul_of_dvd_left hpa b)
    · intro p hp hpb
      exact h p hp (dvd_mul_of_dvd_right hpb a)
  · rintro ⟨ha, hb⟩ p hp hpab
    rcases hp.dvd_mul.mp hpab with hpa | hpb
    · exact ha p hp hpa
    · exact hb p hp hpb

lemma roughIndicator_mul (a b : ℕ) (s : ℝ) :
    roughIndicator (a * b) s = roughIndicator a s * roughIndicator b s := by
  by_cases ha : IsRough a s
  · by_cases hb : IsRough b s
    · have hab : IsRough (a * b) s := (isRough_mul_iff a b s).2 ⟨ha, hb⟩
      simp [roughIndicator, ha, hb, hab]
    · have hab : ¬IsRough (a * b) s := fun h => hb ((isRough_mul_iff a b s).1 h).2
      simp [roughIndicator, ha, hb, hab]
  · by_cases hb : IsRough b s
    · have hab : ¬IsRough (a * b) s := fun h => ha ((isRough_mul_iff a b s).1 h).1
      simp [roughIndicator, ha, hb, hab]
    · have hab : ¬IsRough (a * b) s := fun h => ha ((isRough_mul_iff a b s).1 h).1
      simp [roughIndicator, ha, hb, hab]

@[expose] def p050Base (q : WeightParameters) (d d' : ℕ)
    (hd : 0 < d) (hd' : 0 < d') : Prop :=
  q.theta ^ q.k ≤ (d : ℝ) ∧ (d : ℝ) < q.theta ^ (q.k + 1) ∧
    Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩

@[expose] def sharpTerm (q : WeightParameters) (n d d' t : ℕ) : ℝ :=
  if hd : 0 < d then
    if hd' : 0 < d' then
      if d * d' * t ∣ n ∧ p050Base q d d' hd hd' then
        a0Weight n * (roughIndicator d q.sigma : ℝ) *
          q.y.rpow (omegaBelowRaw (d * t) (q.theta ^ q.k) : ℝ) *
          roughIndicator t q.sigma
      else 0
    else 0
  else 0

@[expose] def inversionTerm (q : WeightParameters) (x : ℝ) (d d' t : ℕ) : ℝ :=
  if hd : 0 < d then
    if hd' : 0 < d' then
      if p050Base q d d' hd hd' then
        (roughIndicator (d * t) q.sigma : ℝ) *
          q.y.rpow (omegaBelowRaw (d * t) (q.theta ^ q.k) : ℝ) *
          ∑ m ∈ positiveNatsBelow (x / (d * d' * t : ℕ)),
            a0Weight (m * (d * d' * t))
      else 0
    else 0
  else 0

lemma sharpTerm_zero_of_d_not_upTo (q : WeightParameters) {n d d' t : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hdnot : d ∉ positiveNatsUpTo n) :
    sharpTerm q n d d' t = 0 := by
  have hdnle : ¬d ≤ n := fun h => hdnot (mem_positiveNatsUpTo.mpr ⟨hd, h⟩)
  unfold sharpTerm
  simp only [dif_pos hd]
  by_cases hd' : 0 < d'
  · simp only [dif_pos hd']
    rw [if_neg]
    intro h
    apply hdnle
    exact Nat.le_of_dvd hn
      ((dvd_mul_right d (d' * t)).trans (by simpa [mul_assoc] using h.1))
  · simp [hd']

lemma sharpTerm_zero_of_d'_not_upTo (q : WeightParameters) {n d d' t : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hd' : 0 < d')
    (hd'not : d' ∉ positiveNatsUpTo n) : sharpTerm q n d d' t = 0 := by
  have hd'nle : ¬d' ≤ n := fun h => hd'not (mem_positiveNatsUpTo.mpr ⟨hd', h⟩)
  unfold sharpTerm
  simp only [dif_pos hd, dif_pos hd']
  rw [if_neg]
  intro h
  apply hd'nle
  exact Nat.le_of_dvd hn
    ((dvd_mul_left d' (d * t)).trans
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using h.1))

lemma sharpTerm_zero_of_t_not_upTo (q : WeightParameters) {n d d' t : ℕ}
    (hn : 0 < n) (hd : 0 < d) (hd' : 0 < d') (ht : 0 < t)
    (htnot : t ∉ positiveNatsUpTo n) : sharpTerm q n d d' t = 0 := by
  have htnle : ¬t ≤ n := fun h => htnot (mem_positiveNatsUpTo.mpr ⟨ht, h⟩)
  unfold sharpTerm
  simp only [dif_pos hd, dif_pos hd']
  rw [if_neg]
  intro h
  apply htnle
  exact Nat.le_of_dvd hn
    ((dvd_mul_left t (d * d')).trans
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using h.1))

lemma sharpTriple_extend (q : WeightParameters) {x : ℝ} {n : ℕ}
    (hnP : n ∈ positiveNatsBelow x) :
    (∑ d ∈ positiveNatsUpTo n, ∑ d' ∈ positiveNatsUpTo n,
      ∑ t ∈ positiveNatsUpTo n, sharpTerm q n d d' t) =
    ∑ d ∈ positiveNatsBelow x, ∑ d' ∈ positiveNatsBelow x,
      ∑ t ∈ positiveNatsBelow x, sharpTerm q n d d' t := by
  have hn := mem_positiveNatsBelow.mp hnP
  have hsub : positiveNatsUpTo n ⊆ positiveNatsBelow x := by
    intro a ha
    have ha' := mem_positiveNatsUpTo.mp ha
    apply mem_positiveNatsBelow.mpr
    refine ⟨ha'.1, ?_⟩
    have han : (a : ℝ) ≤ n := by exact_mod_cast ha'.2
    exact han.trans_lt hn.2
  calc
    (∑ d ∈ positiveNatsUpTo n, ∑ d' ∈ positiveNatsUpTo n,
        ∑ t ∈ positiveNatsUpTo n, sharpTerm q n d d' t) =
      ∑ d ∈ positiveNatsUpTo n, ∑ d' ∈ positiveNatsUpTo n,
        ∑ t ∈ positiveNatsBelow x, sharpTerm q n d d' t := by
          apply Finset.sum_congr rfl
          intro d hdU
          apply Finset.sum_congr rfl
          intro d' hd'U
          apply Finset.sum_subset hsub
          intro t htP htU
          exact sharpTerm_zero_of_t_not_upTo q hn.1
            (mem_positiveNatsUpTo.mp hdU).1 (mem_positiveNatsUpTo.mp hd'U).1
            (mem_positiveNatsBelow.mp htP).1 htU
    _ = ∑ d ∈ positiveNatsUpTo n, ∑ d' ∈ positiveNatsBelow x,
        ∑ t ∈ positiveNatsBelow x, sharpTerm q n d d' t := by
          apply Finset.sum_congr rfl
          intro d hdU
          apply Finset.sum_subset hsub
          intro d' hd'P hd'U
          apply Finset.sum_eq_zero
          intro t htP
          exact sharpTerm_zero_of_d'_not_upTo q hn.1
            (mem_positiveNatsUpTo.mp hdU).1 (mem_positiveNatsBelow.mp hd'P).1 hd'U
    _ = ∑ d ∈ positiveNatsBelow x, ∑ d' ∈ positiveNatsBelow x,
        ∑ t ∈ positiveNatsBelow x, sharpTerm q n d d' t := by
          apply Finset.sum_subset hsub
          intro d hdP hdU
          apply Finset.sum_eq_zero
          intro d' hd'P
          apply Finset.sum_eq_zero
          intro t htP
          exact sharpTerm_zero_of_d_not_upTo q hn.1
            (mem_positiveNatsBelow.mp hdP).1 hdU

lemma sum_rotate_four (s : Finset ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℝ) :
    (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s, f a b c d) =
      ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s, ∑ a ∈ s, f a b c d := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.sum_comm]

lemma sharpInner_reindex (q : WeightParameters) {x : ℝ} {d d' t : ℕ}
    (hdP : d ∈ positiveNatsBelow x) (hd'P : d' ∈ positiveNatsBelow x)
    (htP : t ∈ positiveNatsBelow x) :
    (∑ n ∈ positiveNatsBelow x, sharpTerm q n d d' t) =
      inversionTerm q x d d' t := by
  have hd := (mem_positiveNatsBelow.mp hdP).1
  have hd' := (mem_positiveNatsBelow.mp hd'P).1
  have ht := (mem_positiveNatsBelow.mp htP).1
  have ha : 0 < d * d' * t := Nat.mul_pos (Nat.mul_pos hd hd') ht
  by_cases hbase : p050Base q d d' hd hd'
  · simp_rw [sharpTerm, dif_pos hd, dif_pos hd', hbase, and_true]
    rw [Erdos448.Stage7.ROOT05.P050Reindex.sum_multiples
      (fun n => a0Weight n * (roughIndicator d q.sigma : ℝ) *
        q.y.rpow (omegaBelowRaw (d * t) (q.theta ^ q.k) : ℝ) *
        roughIndicator t q.sigma) ha x]
    unfold inversionTerm
    simp only [dif_pos hd, dif_pos hd', if_pos hbase]
    rw [roughIndicator_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    norm_num [Nat.cast_mul]
    ring
  · simp [sharpTerm, inversionTerm, hd, hd', hbase]

lemma tRange_restrict (q : WeightParameters) {x : ℝ} {d d' : ℕ}
    (hd : 0 < d) (hd' : 0 < d') :
    (∑ t ∈ positiveNatsBelow x, inversionTerm q x d d' t) =
      ∑ t ∈ positiveNatsBelow (x / (d * d' : ℕ)), inversionTerm q x d d' t := by
  have hdd' : 0 < d * d' := Nat.mul_pos hd hd'
  have hdd'R : (0 : ℝ) < (d * d' : ℕ) := by exact_mod_cast hdd'
  have hsub : positiveNatsBelow (x / (d * d' : ℕ)) ⊆ positiveNatsBelow x := by
    intro t ht
    have ht' := mem_positiveNatsBelow.mp ht
    apply mem_positiveNatsBelow.mpr
    refine ⟨ht'.1, ?_⟩
    have hmul : (t : ℝ) * (d * d' : ℕ) < x := (lt_div_iff₀ hdd'R).mp ht'.2
    have hdd'1 : (1 : ℝ) ≤ (d * d' : ℕ) := by exact_mod_cast hdd'
    calc
      (t : ℝ) = (t : ℝ) * 1 := by ring
      _ ≤ (t : ℝ) * (d * d' : ℕ) :=
        mul_le_mul_of_nonneg_left hdd'1 (Nat.cast_nonneg t)
      _ < x := hmul
  symm
  apply Finset.sum_subset hsub
  intro t htP htT
  have ht := (mem_positiveNatsBelow.mp htP).1
  have hnotlt : ¬(t : ℝ) < x / (d * d' : ℕ) := fun h =>
    htT (mem_positiveNatsBelow.mpr ⟨ht, h⟩)
  have hxle : x ≤ (t : ℝ) * (d * d' : ℕ) :=
    (div_le_iff₀ hdd'R).mp (le_of_not_gt hnotlt)
  have ha : 0 < d * d' * t := Nat.mul_pos hdd' ht
  have haR : (0 : ℝ) < (d * d' * t : ℕ) := by exact_mod_cast ha
  have hq : x / (d * d' * t : ℕ) ≤ 1 := by
    apply (div_le_one haR).2
    simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hxle
  have hempty := positiveNatsBelow_eq_empty_of_le_one hq
  have hempty' :
      positiveNatsBelow (x / ((d : ℝ) * (d' : ℝ) * (t : ℝ))) = ∅ := by
    simpa [Nat.cast_mul] using hempty
  unfold inversionTerm
  simp only [dif_pos hd, dif_pos hd']
  split_ifs
  · rw [hempty]
    simp
  · rfl

lemma close_upper_cutoff (q : WeightParameters) {d d' : ℕ}
    (hd : 0 < d) (hd' : 0 < d')
    (hdUpper : (d : ℝ) < q.theta ^ (q.k + 1))
    (hclose : Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩) :
    (d' : ℝ) < q.theta ^ (q.k + 2) := by
  have htheta : 0 < q.theta := lt_of_lt_of_le (by norm_num) q.theta_ge_two
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hfirst : (d' : ℝ) < q.theta * d := (div_lt_iff₀ hdR).mp hclose.2.2
  calc
    (d' : ℝ) < q.theta * d := hfirst
    _ < q.theta * q.theta ^ (q.k + 1) := by
      have hprod : 0 < q.theta * (q.theta ^ (q.k + 1) - d) :=
        mul_pos htheta (sub_pos.mpr hdUpper)
      nlinarith
    _ = q.theta ^ (q.k + 2) := by
      rw [show q.k + 2 = (q.k + 1) + 1 by omega, pow_succ]
      ring

@[expose] def tBlock (q : WeightParameters) (x : ℝ) (d d' : ℕ) : ℝ :=
  ∑ t ∈ positiveNatsBelow (x / (d * d' : ℕ)), inversionTerm q x d d' t

lemma tBlock_zero_of_cutoff_le_one (q : WeightParameters) {x : ℝ} {d d' : ℕ}
    (h : x / (d * d' : ℕ) ≤ 1) : tBlock q x d d' = 0 := by
  have h' : x / ((d : ℝ) * d') ≤ 1 := by simpa [Nat.cast_mul] using h
  simp [tBlock, positiveNatsBelow_eq_empty_of_le_one h']

lemma tBlock_zero_of_d_outside_x (q : WeightParameters) {x : ℝ} {d d' : ℕ}
    (hd : 0 < d) (hd' : 0 < d') (hdx : ¬(d : ℝ) < x) :
    tBlock q x d d' = 0 := by
  have hdd' : 0 < d * d' := Nat.mul_pos hd hd'
  have hdenR : (0 : ℝ) < (d * d' : ℕ) := by exact_mod_cast hdd'
  have hd'1 : (1 : ℝ) ≤ d' := by exact_mod_cast hd'
  have hxdd' : x ≤ (d * d' : ℕ) := by
    calc
      x ≤ (d : ℝ) := le_of_not_gt hdx
      _ = (d : ℝ) * 1 := by ring
      _ ≤ (d : ℝ) * d' := mul_le_mul_of_nonneg_left hd'1 (by positivity)
      _ = (d * d' : ℕ) := by norm_num
  exact tBlock_zero_of_cutoff_le_one q ((div_le_one hdenR).2 hxdd')

lemma tBlock_zero_of_d'_outside_x (q : WeightParameters) {x : ℝ} {d d' : ℕ}
    (hd : 0 < d) (hd' : 0 < d') (hd'x : ¬(d' : ℝ) < x) :
    tBlock q x d d' = 0 := by
  have hdd' : 0 < d * d' := Nat.mul_pos hd hd'
  have hdenR : (0 : ℝ) < (d * d' : ℕ) := by exact_mod_cast hdd'
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hxdd' : x ≤ (d * d' : ℕ) := by
    calc
      x ≤ (d' : ℝ) := le_of_not_gt hd'x
      _ = 1 * (d' : ℝ) := by ring
      _ ≤ (d : ℝ) * d' := mul_le_mul_of_nonneg_right hd1 (by positivity)
      _ = (d * d' : ℕ) := by norm_num
  exact tBlock_zero_of_cutoff_le_one q ((div_le_one hdenR).2 hxdd')

lemma tBlock_zero_of_d_outside_bin (q : WeightParameters) {x : ℝ} {d d' : ℕ}
    (hd : 0 < d) (hd' : 0 < d')
    (hdBin : d ∉ positiveNatsBelow (q.theta ^ (q.k + 1))) :
    tBlock q x d d' = 0 := by
  unfold tBlock
  apply Finset.sum_eq_zero
  intro t ht
  unfold inversionTerm
  simp only [dif_pos hd, dif_pos hd']
  rw [if_neg]
  intro hbase
  exact hdBin (mem_positiveNatsBelow.mpr ⟨hd, hbase.2.1⟩)

lemma tBlock_zero_of_d'_outside_bin (q : WeightParameters) {x : ℝ} {d d' : ℕ}
    (hd : 0 < d) (hd' : 0 < d')
    (hd'Bin : d' ∉ positiveNatsBelow (q.theta ^ (q.k + 2))) :
    tBlock q x d d' = 0 := by
  unfold tBlock
  apply Finset.sum_eq_zero
  intro t ht
  unfold inversionTerm
  simp only [dif_pos hd, dif_pos hd']
  rw [if_neg]
  intro hbase
  exact hd'Bin (mem_positiveNatsBelow.mpr
    ⟨hd', close_upper_cutoff q hd hd' hbase.2.1 hbase.2.2⟩)

theorem p050 : P050Statement := by
  intro q x hx
  have htheta : 0 < q.theta := lt_of_lt_of_le (by norm_num) q.theta_ge_two
  have hx0 : 0 < x := (pow_pos htheta _).trans hx
  let P := positiveNatsBelow x
  let D := positiveNatsBelow (q.theta ^ (q.k + 1))
  let D' := positiveNatsBelow (q.theta ^ (q.k + 2))
  have hcommon : proposition3Subject q x =
      ∑ n ∈ P, ∑ d ∈ P, ∑ d' ∈ P, ∑ t ∈ P, sharpTerm q n d d' t := by
    unfold proposition3Subject
    apply Finset.sum_congr rfl
    intro n hnP
    have hn := mem_positiveNatsBelow.mp hnP
    simp only [dif_pos hn.1]
    unfold fkSharp
    rw [← sharpTriple_extend q hnP]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hdU
    apply Finset.sum_congr rfl
    intro d' hd'U
    apply Finset.sum_congr rfl
    intro t htU
    unfold sharpTerm p050Base
    split_ifs <;> simp [a0Weight, hn.1] <;> ring
  have hreindexed : proposition3Subject q x =
      ∑ d ∈ P, ∑ d' ∈ P, ∑ t ∈ P, inversionTerm q x d d' t := by
    rw [hcommon, sum_rotate_four]
    apply Finset.sum_congr rfl
    intro d hdP
    apply Finset.sum_congr rfl
    intro d' hd'P
    apply Finset.sum_congr rfl
    intro t htP
    exact sharpInner_reindex q hdP hd'P htP
  have htRestricted :
      (∑ d ∈ P, ∑ d' ∈ P, ∑ t ∈ P, inversionTerm q x d d' t) =
        ∑ d ∈ P, ∑ d' ∈ P, tBlock q x d d' := by
    apply Finset.sum_congr rfl
    intro d hdP
    apply Finset.sum_congr rfl
    intro d' hd'P
    exact tRange_restrict q (mem_positiveNatsBelow.mp hdP).1
      (mem_positiveNatsBelow.mp hd'P).1
  have hdRestricted :
      (∑ d ∈ P, ∑ d' ∈ P, tBlock q x d d') =
        ∑ d ∈ D, ∑ d' ∈ P, tBlock q x d d' := by
    let U := P ∪ D
    have hPU : P ⊆ U := Finset.subset_union_left
    have hDU : D ⊆ U := Finset.subset_union_right
    calc
      (∑ d ∈ P, ∑ d' ∈ P, tBlock q x d d') =
          ∑ d ∈ U, ∑ d' ∈ P, tBlock q x d d' := by
        apply Finset.sum_subset hPU
        intro d hdU hdP
        have hdD : d ∈ D := (Finset.mem_union.mp hdU).resolve_left hdP
        have hd := (mem_positiveNatsBelow.mp hdD).1
        have hdx : ¬(d : ℝ) < x := fun h => hdP (mem_positiveNatsBelow.mpr ⟨hd, h⟩)
        apply Finset.sum_eq_zero
        intro d' hd'P
        exact tBlock_zero_of_d_outside_x q hd
          (mem_positiveNatsBelow.mp hd'P).1 hdx
      _ = ∑ d ∈ D, ∑ d' ∈ P, tBlock q x d d' := by
        symm
        apply Finset.sum_subset hDU
        intro d hdU hdD
        have hdP : d ∈ P := (Finset.mem_union.mp hdU).resolve_right hdD
        apply Finset.sum_eq_zero
        intro d' hd'P
        exact tBlock_zero_of_d_outside_bin q
          (mem_positiveNatsBelow.mp hdP).1 (mem_positiveNatsBelow.mp hd'P).1 hdD
  have hd'Restricted :
      (∑ d ∈ D, ∑ d' ∈ P, tBlock q x d d') =
        ∑ d ∈ D, ∑ d' ∈ D', tBlock q x d d' := by
    apply Finset.sum_congr rfl
    intro d hdD
    let U := P ∪ D'
    have hPU : P ⊆ U := Finset.subset_union_left
    have hD'U : D' ⊆ U := Finset.subset_union_right
    calc
      (∑ d' ∈ P, tBlock q x d d') = ∑ d' ∈ U, tBlock q x d d' := by
        apply Finset.sum_subset hPU
        intro d' hd'U hd'P
        have hd'D : d' ∈ D' := (Finset.mem_union.mp hd'U).resolve_left hd'P
        exact tBlock_zero_of_d'_outside_x q (mem_positiveNatsBelow.mp hdD).1
          (mem_positiveNatsBelow.mp hd'D).1
          (fun h => hd'P (mem_positiveNatsBelow.mpr
            ⟨(mem_positiveNatsBelow.mp hd'D).1, h⟩))
      _ = ∑ d' ∈ D', tBlock q x d d' := by
        symm
        apply Finset.sum_subset hD'U
        intro d' hd'U hd'D
        have hd'P : d' ∈ P := (Finset.mem_union.mp hd'U).resolve_right hd'D
        exact tBlock_zero_of_d'_outside_bin q (mem_positiveNatsBelow.mp hdD).1
          (mem_positiveNatsBelow.mp hd'P).1 hd'D
  rw [hreindexed, htRestricted, hdRestricted, hd'Restricted]
  unfold fourVariableInversion tBlock
  apply Finset.sum_congr rfl
  intro d hdD
  apply Finset.sum_congr rfl
  intro d' hd'D
  have hd := (mem_positiveNatsBelow.mp hdD).1
  have hd' := (mem_positiveNatsBelow.mp hd'D).1
  have hdUpper := (mem_positiveNatsBelow.mp hdD).2
  simp only [dif_pos hd, dif_pos hd']
  by_cases hout : q.theta ^ q.k ≤ (d : ℝ) ∧
      Close q.theta ⟨d, hd⟩ ⟨d', hd'⟩
  · have hbase : p050Base q d d' hd hd' := ⟨hout.1, hdUpper, hout.2⟩
    rw [if_pos hout]
    apply Finset.sum_congr rfl
    intro t ht
    unfold inversionTerm
    simp only [dif_pos hd, dif_pos hd', if_pos hbase]
    congr 1
    apply Finset.sum_congr
    · congr 1
      norm_num [mul_comm, mul_left_comm, mul_assoc]
    · intro m hm
      congr 1
      ac_rfl
  · have hbase : ¬p050Base q d d' hd hd' := fun h => hout ⟨h.1, h.2.2⟩
    rw [if_neg hout]
    simp [inversionTerm, hd, hd', hbase]

theorem p001C (h001A : P001AStatement) : P001CStatement := by
  intro Ksh z hz hz2
  let gLeft : ArithmeticWeight := fun m => a0Weight (m * Ksh.1)
  let gRight : ArithmeticWeight := fun m => (safeLog m).rpow (-1 / 2)
  have hgLeft : NonnegativeWeight gLeft := by
    intro m hm
    exact p051A.1.nonnegative_multiplicative.nonnegative (m * Ksh.1)
      (Nat.mul_pos hm Ksh.2)
  have hgRight : NonnegativeWeight gRight := by
    intro m hm
    exact Real.rpow_nonneg (by simp [safeLog]) _
  have hLeft := h001A gLeft hgLeft z hz
  have hRight := h001A gRight hgRight z hz
  by_cases hz1 : z ≤ 1
  · have hl0 : (∑ m ∈ positiveNatsBelow z, a0Weight (m * Ksh.1)) = 0 := by
      simpa [initialSegment, strictMean, gLeft] using hLeft.1 hz1
    have hr0 : (∑ m ∈ positiveNatsBelow z, (safeLog m).rpow (-1 / 2)) = 0 := by
      simpa [initialSegment, strictMean, gRight] using hRight.1 hz1
    rw [hl0, hr0, mul_zero]
  · have hzgt : 1 < z := lt_of_not_ge hz1
    have hl1 : (∑ m ∈ positiveNatsBelow z, a0Weight (m * Ksh.1)) =
        a0Weight Ksh.1 := by
      simpa [initialSegment, strictMean, gLeft] using hLeft.2 hzgt hz2
    have hr1 : (∑ m ∈ positiveNatsBelow z, (safeLog m).rpow (-1 / 2)) = 1 := by
      simpa [initialSegment, strictMean, gRight, safeLog] using hRight.2 hzgt hz2
    rw [hl1, hr1, mul_one]
    exact weightChain.w1_dom_a0 Ksh.1 Ksh.2

@[expose] def commonWeights : CommonWeightWitnesses :=
  Erdos448.Stage7.ROOT05.CUP051GH.commonWeights

theorem p051H : P051HStatement :=
  Erdos448.Stage7.ROOT05.CUP051GH.p051H

theorem result : ROOT05Target := by
  intro h001A
  exact ⟨
    { p050 := p050
      weightChain := weightChain
      p001C := p001C h001A
      commonWeights := commonWeights
      p051H := p051H }⟩

end

end Erdos448.Stage7.ROOT05.Work
