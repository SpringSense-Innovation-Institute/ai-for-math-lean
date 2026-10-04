module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W08_Near
public import Erdos745.WrapUp.Proofs.Internal.Linked.W08_Fixed

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


namespace Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_FixedMass

noncomputable section
open Filter
open scoped BigOperators Topology
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Finite
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Bounds
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_FixedLocal
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Complex
open Erdos745.WrapUp.Proofs.W06_POISSON

set_option maxHeartbeats 2000000

private lemma tree_tail_single_le (n M power k : ℕ) (B : ℝ)
    (hk : 0 < k) (hkn : k ≤ n) (hfar : B * Real.log n < (k : ℝ)) :
    (k : ℝ) ^ power * treeMomentOne n M k ≤ treeTailOne n M power B := by
  let i : Fin (n + 1) := ⟨k, by omega⟩
  have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin (n + 1))),
      0 ≤ (if 0 < j.val ∧ B * Real.log n < (j.val : ℝ) then
        (j.val : ℝ) ^ power * treeMomentOne n M j.val else 0) := by
    intro j hj
    split_ifs
    · exact mul_nonneg (by positivity)
        (tupleMoment_nonneg n M 1 (fun _ => j.val))
    · exact le_rfl
  have h := Finset.single_le_sum hnonneg (Finset.mem_univ i)
  simpa only [treeTailOne, i, hk, hfar, and_self, if_true] using! h

private lemma tree_tail_nonneg (n M power : ℕ) (B : ℝ) :
    0 ≤ treeTailOne n M power B := by
  unfold treeTailOne
  exact Finset.sum_nonneg fun j _ => by
    split_ifs
    · exact mul_nonneg (by positivity) (tupleMoment_nonneg n M 1 (fun _ => j.val))
    · exact le_rfl

private lemma sum_Icc_le_tsum_nat_add (g : ℕ → ℝ) (H N : ℕ)
    (hg : ∀ k, 0 ≤ g k) (hs : Summable g) :
    (∑ k ∈ Finset.Icc H N, g k) ≤ ∑' j : ℕ, g (j + H) := by
  let s := Finset.Icc H N
  have hinj : Set.InjOn (fun k : ℕ => k - H) s := by
    intro a ha b hb hab
    have haH : H ≤ a := (Finset.mem_Icc.mp ha).1
    have hbH : H ≤ b := (Finset.mem_Icc.mp hb).1
    calc
      a = a - H + H := (Nat.sub_add_cancel haH).symm
      _ = b - H + H := by simpa only using! congrArg (fun x : ℕ => x + H) hab
      _ = b := Nat.sub_add_cancel hbH
  have hshift : Summable (fun j => g (j + H)) :=
    (summable_nat_add_iff H).2 hs
  calc
    (∑ k ∈ s, g k) = ∑ k ∈ s, g ((k - H) + H) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkh : H ≤ k := (Finset.mem_Icc.mp hk).1
      congr 1
      omega
    _ = ∑ j ∈ s.image (fun k => k - H), g (j + H) := by
      rw [Finset.sum_image hinj]
    _ ≤ ∑' j : ℕ, g (j + H) :=
      hshift.sum_le_tsum _ (fun j _ => hg _)

private lemma fixed_cyclic_local_bound
    (hF : FiniteEnumerationStatement) (CU D a U : ℝ)
    (hCU : 0 < CU) (hD : 0 < D) (hU : 1 ≤ U)
    (hCUb : ∀ k : ℕ, 3 ≤ k → (connectedCount k k : ℝ) ≤
      CU * Real.rpow (k : ℝ) ((k : ℝ) - 1 / 2))
    {n M k : ℕ} (hM : M ≤ capacity n)
    (hn : 32 * (U + 1) ≤ (n : ℝ)) (hMU : (M : ℝ) ≤ U * n)
    (hk : 3 ≤ k) (hkn : k ≤ n) (hkhalf : k ≤ n / 2)
    (htree : treeMomentOne n M k ≤ D * n *
      Real.rpow (k : ℝ) (-5 / 2 : ℝ) * Real.exp (-a * k)) :
    (k : ℝ) * cyclicFormula n M k ≤
      (32 * (U + 1) * CU * D) * Real.exp (-a * k) := by
  by_cases hkM : k ≤ M
  · obtain ⟨hsQ, hratio⟩ := bounded_degree_complement_ratio hU hn hMU hkhalf
    have hcyc := component_ratio_unicyclic hF CU hCUb hM hk hkn hkM hsQ
    have htree0 : 0 ≤ treeMomentOne n M k :=
      tupleMoment_nonneg n M 1 (fun _ => k)
    have hkpos : 0 < (k : ℝ) := by positivity
    have hnpos : 0 < (n : ℝ) := by linarith
    have hrpow : Real.rpow (k : ℝ) (-5 / 2 : ℝ) *
        Real.rpow (k : ℝ) (3 / 2 : ℝ) * k = 1 := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_add hkpos, ← Real.rpow_one k]
      norm_num [Real.rpow_neg_one, hkpos.ne']
    have hcyc' : cyclicFormula n M k ≤
        treeMomentOne n M k * (CU * Real.rpow (k : ℝ) (3 / 2 : ℝ)) *
          (((M - k + 1 : ℕ) : ℝ) /
            (((n - k).choose 2 - (M - k + 1) + 1 : ℕ) : ℝ)) := by
      simpa only [mul_div_assoc] using! hcyc
    calc
      (k : ℝ) * cyclicFormula n M k ≤
          k * (treeMomentOne n M k *
            (CU * Real.rpow (k : ℝ) (3 / 2 : ℝ)) *
            (((M - k + 1 : ℕ) : ℝ) /
              (((n - k).choose 2 - (M - k + 1) + 1 : ℕ) : ℝ))) := by
        exact mul_le_mul_of_nonneg_left hcyc' hkpos.le
      _ ≤ k * ((D * n * Real.rpow (k : ℝ) (-5 / 2 : ℝ) *
            Real.exp (-a * k)) *
            (CU * Real.rpow (k : ℝ) (3 / 2 : ℝ)) *
            ((32 * (U + 1)) / n)) := by
        have hcoef : 0 ≤ CU * Real.rpow (k : ℝ) (3 / 2 : ℝ) :=
          mul_nonneg hCU.le (Real.rpow_nonneg hkpos.le _)
        have hratio0 : 0 ≤ (((M - k + 1 : ℕ) : ℝ) /
            (((n - k).choose 2 - (M - k + 1) + 1 : ℕ) : ℝ)) := by positivity
        have hT0 : 0 ≤ D * n * Real.rpow (k : ℝ) (-5 / 2 : ℝ) *
            Real.exp (-a * k) := by
          exact mul_nonneg
            (mul_nonneg (mul_nonneg hD.le (by positivity))
              (Real.rpow_nonneg hkpos.le _)) (Real.exp_nonneg _)
        have hstep1 := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right htree hcoef) hratio0
        have hstep2 := mul_le_mul_of_nonneg_left hratio (mul_nonneg hT0 hcoef)
        exact mul_le_mul_of_nonneg_left (hstep1.trans hstep2) hkpos.le
      _ = (32 * (U + 1) * CU * D) * Real.exp (-a * k) := by
        field_simp [hnpos.ne']
        nlinarith [hrpow]
  · have hz : cyclicFormula n M k = 0 := by
      unfold cyclicFormula componentFormula
      simp [Nat.lt_of_not_ge hkM]
    rw [hz, mul_zero]
    positivity

private lemma fixed_cyclic_far_bound
    (hF : FiniteEnumerationStatement) (CU U B B3 B0 : ℝ)
    (hCU : 0 < CU) (hU : 1 ≤ U)
    (hCUb : ∀ k : ℕ, 3 ≤ k → (connectedCount k k : ℝ) ≤
      CU * Real.rpow (k : ℝ) ((k : ℝ) - 1 / 2))
    {n M k : ℕ} (hM : M ≤ capacity n) (hMU : (M : ℝ) ≤ U * n)
    (hn : 1 ≤ n) (hlog : 1 ≤ Real.log n)
    (hB3 : B3 ≤ B) (hB0 : B0 + 4 ≤ B)
    (hk : 8 ≤ k) (hkn : k ≤ n) (hfar : B * Real.log n < (k : ℝ)) :
    (k : ℝ) * cyclicFormula n M k ≤
      (CU * (U + 1) * n) * treeTailOne n M 3 B3 +
      (CU * Real.exp 8 * (n : ℝ) ^ 11) * treeTailOne n M 0 B0 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have htail3 : (k : ℝ) ^ 3 * treeMomentOne n M k ≤
      treeTailOne n M 3 B3 := by
    exact tree_tail_single_le n M 3 k B3 (by omega) hkn
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hB3 (by positivity)) hfar)
  have htail0 : treeMomentOne n M (k - 4) ≤ treeTailOne n M 0 B0 := by
    have hjfar : B0 * Real.log n < ((k - 4 : ℕ) : ℝ) := by
      have hsub : ((k - 4 : ℕ) : ℝ) = (k : ℝ) - 4 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      rw [hsub]
      nlinarith [mul_nonneg (sub_nonneg.mpr hB0) (sub_nonneg.mpr hlog)]
    simpa using! tree_tail_single_le n M 0 (k - 4) B0 (by omega) (by omega) hjfar
  by_cases hkM : k ≤ M
  swap
  · have hz : cyclicFormula n M k = 0 := by
      unfold cyclicFormula componentFormula
      simp [Nat.lt_of_not_ge hkM]
    rw [hz, mul_zero]
    exact add_nonneg
      (mul_nonneg (by positivity) (tree_tail_nonneg n M 3 B3))
      (mul_nonneg (by positivity) (tree_tail_nonneg n M 0 B0))
  by_cases hsQ : M - k + 1 ≤ (n - k).choose 2
  · have hcyc := component_ratio_unicyclic hF CU hCUb hM (by omega)
      hkn hkM hsQ
    have hsreal : (((M - k + 1 : ℕ) : ℝ)) ≤ (U + 1) * n := by
      have hsNat : M - k + 1 ≤ M + 1 := by omega
      have hs : (((M - k + 1 : ℕ) : ℝ)) ≤ (M + 1 : ℝ) := by
        exact_mod_cast hsNat
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    have hden : (1 : ℝ) ≤
        (((n - k).choose 2 - (M - k + 1) + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega :
          1 ≤ (n - k).choose 2 - (M - k + 1) + 1)
    have hratio : (((M - k + 1 : ℕ) : ℝ) /
        (((n - k).choose 2 - (M - k + 1) + 1 : ℕ) : ℝ)) ≤
        (U + 1) * n := by
      apply (div_le_iff₀ (by linarith : (0 : ℝ) <
        (((n - k).choose 2 - (M - k + 1) + 1 : ℕ) : ℝ))).2
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (U + 1) * n)
        (sub_nonneg.mpr hden)]
    have hkpow : (k : ℝ) * Real.rpow (k : ℝ) (3 / 2 : ℝ) ≤
        (k : ℝ) ^ 3 := by
      have hkp : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
      have hp := Real.rpow_le_rpow_of_exponent_le hkp (by norm_num : (3 / 2 : ℝ) ≤ 2)
      have hh := mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ k)
      calc
        (k : ℝ) * Real.rpow (k : ℝ) (3 / 2 : ℝ) ≤
            (k : ℝ) * Real.rpow (k : ℝ) (2 : ℝ) := hh
        _ = (k : ℝ) ^ 3 := by norm_num [Real.rpow_natCast]; ring
    have htree : 0 ≤ treeMomentOne n M k :=
      tupleMoment_nonneg n M 1 (fun _ => k)
    have hcyc' : cyclicFormula n M k ≤
        treeMomentOne n M k * (CU * Real.rpow (k : ℝ) (3 / 2 : ℝ)) *
          (((M - k + 1 : ℕ) : ℝ) /
            (((n - k).choose 2 - (M - k + 1) + 1 : ℕ) : ℝ)) := by
      simpa only [mul_div_assoc] using! hcyc
    calc
      (k : ℝ) * cyclicFormula n M k ≤
          k * (treeMomentOne n M k *
            (CU * Real.rpow (k : ℝ) (3 / 2 : ℝ)) *
            (((M - k + 1 : ℕ) : ℝ) /
              (((n - k).choose 2 - (M - k + 1) + 1 : ℕ) : ℝ))) := by
        exact mul_le_mul_of_nonneg_left hcyc' (by positivity)
      _ ≤ k * (treeMomentOne n M k *
            (CU * Real.rpow (k : ℝ) (3 / 2 : ℝ)) * ((U + 1) * n)) := by
        have hcoef : 0 ≤ CU * Real.rpow (k : ℝ) (3 / 2 : ℝ) :=
          mul_nonneg hCU.le (Real.rpow_nonneg (by positivity) _)
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hratio (mul_nonneg htree hcoef))
          (by positivity)
      _ = (CU * (U + 1) * n) *
            (((k : ℝ) * Real.rpow (k : ℝ) (3 / 2 : ℝ)) * treeMomentOne n M k) := by
        ring
      _ ≤ (CU * (U + 1) * n) * ((k : ℝ) ^ 3 * treeMomentOne n M k) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hkpow htree) (by positivity)
      _ ≤ (CU * (U + 1) * n) * treeTailOne n M 3 B3 := by gcongr
      _ ≤ _ := le_add_of_nonneg_right
        (mul_nonneg (by positivity) (tree_tail_nonneg n M 0 B0))
  · by_cases hbad : (n - k).choose 2 = M - k
    · have hshift := bad_unicyclic_shift_le hF CU hCU hCUb hM hk hkn hbad
      calc
        (k : ℝ) * cyclicFormula n M k ≤
            (CU * Real.exp 8 * (n : ℝ) ^ 11) * treeMomentOne n M (k - 4) := hshift
        _ ≤ (CU * Real.exp 8 * (n : ℝ) ^ 11) * treeTailOne n M 0 B0 := by
          gcongr
        _ ≤ _ := le_add_of_nonneg_left
          (mul_nonneg (by positivity) (tree_tail_nonneg n M 3 B3))
    · have hgt : (n - k).choose 2 < M - k := by omega
      have hz : cyclicFormula n M k = 0 := by
        unfold cyclicFormula componentFormula
        simp [hkn, hkM, Nat.choose_eq_zero_of_lt hgt]
      rw [hz, mul_zero]
      exact add_nonneg
        (mul_nonneg (by positivity) (tree_tail_nonneg n M 3 B3))
        (mul_nonneg (by positivity) (tree_tail_nonneg n M 0 B0))

lemma fixed_unicyclic_tendsto
    (hF : FiniteEnumerationStatement) (hRate : RateStatement)
    (hT : TupleEstimatesStatement) (M : NatSeq) (lam : ℝ)
    (hadm : admissible M) (hlam : 0 < lam) (hlam1 : lam ≠ 1)
    (hdeg : Tendsto (degree M) atTop (𝓝 lam)) :
    Summable (unicyclicLimitTerm lam) ∧
    Tendsto (fun n => expectM n (M n) unicyclicMass)
      atTop (𝓝 (unicyclicLimit lam)) := by
  obtain ⟨CU, hCU, hCUb⟩ := enum_unicyclic_bound hF
  obtain ⟨lo, hi, a0, hlo, hlohi, ha0, hcompact⟩ :=
    fixed_compact_data hRate hlam hlam1 hdeg
  let delta := |lam - 1| / 2
  have habs : 0 < |lam - 1| := abs_pos.mpr (sub_ne_zero.mpr hlam1)
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hsep : ∀ᶠ n in atTop, delta ≤ |degree M n - 1| := by
    have ht : Tendsto (fun n => |degree M n - 1|) atTop (𝓝 |lam - 1|) := by
      simpa using! (hdeg.sub_const 1).abs
    exact ((tendsto_order.1 ht).1 delta (by dsimp [delta]; linarith)).mono fun _ h => h.le
  obtain ⟨B3, hB3, n3, htail3⟩ :=
    hT.2.2.2 lo hi delta 6 1 3 hlo hlohi hdelta (by norm_num) (by omega)
  obtain ⟨B0, hB0, n0, htail0⟩ :=
    hT.2.2.2 lo hi delta 15 1 0 hlo hlohi hdelta (by norm_num) (by omega)
  let B := max 1 (max B3 (B0 + 4))
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hB3le : B3 ≤ B :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hB0le : B0 + 4 ≤ B :=
    (le_max_right _ _).trans (le_max_right _ _)
  let U := max 1 hi
  let c := 32 * (U + 1)
  have hU : 1 ≤ U := le_max_left _ _
  have hc : 0 < c := by dsimp [c]; linarith
  obtain ⟨D, a, hD, ha, nLocal, hlocal⟩ :=
    fixed_local_tree_bound hT hRate hlam hlam1 hB hadm hdeg
  let L := c * CU * D
  have hL : 0 < L := by dsimp [L]; positivity
  have hlarge : ∀ᶠ n : ℕ in atTop, c ≤ (n : ℝ) :=
    (tendsto_atTop.1 tendsto_natCast_atTop_atTop) c
  have hloghalf : ∀ᶠ n : ℕ in atTop, B * Real.log n ≤ (n : ℝ) / 2 := by
    have ht := ((isLittleO_log_rpow_atTop (r := (1 : ℝ)) (by norm_num)).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop
    have htB : Tendsto (fun n : ℕ => B * Real.log n / n) atTop (𝓝 0) := by
      convert ht.const_mul B using 1 <;> simp [Real.rpow_one, mul_div_assoc]
    have hev := ((tendsto_order.1 htB).2 (1 / 2) (by norm_num)).mono fun _ h => h.le
    filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
    have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    simpa only [one_div, one_mul, mul_comm] using! (div_le_iff₀ hnR).1 hn
  have hloglarge : ∀ᶠ n : ℕ in atTop,
      1 ≤ Real.log n ∧ 8 ≤ B * Real.log n := by
    have ht := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hev := (tendsto_atTop.1 ht) (max 1 (8 / B))
    filter_upwards [hev] with n hn
    constructor
    · exact (le_max_left _ _).trans hn
    · have hh := (le_max_right _ _).trans hn
      simpa only [Function.comp_apply, mul_comm] using! (div_le_iff₀ hB).1 hh
  have hgeomSum : Summable (fun k : ℕ => L * Real.exp (-a * k)) := by
    have hs : Summable (fun k : ℕ => L * Real.exp (k * (-a))) :=
      (Real.summable_exp_nat_mul_iff.mpr (by linarith)).mul_left L
    convert hs using 1
    ext k
    congr 1
    ring
  have hmajor : Summable (unicyclicLimitTerm lam) := by
    apply Summable.of_nonneg_of_le
    · exact unicyclicLimitTerm_nonneg lam hlam
    · intro k
      have hlim := fixed_cyclic_term_tendsto hF hT hadm hlam hdeg k
      have hbound : ∀ᶠ n in atTop,
          (if k ≤ n then (k : ℝ) * cyclicFormula n (M n) k else 0) ≤
            L * Real.exp (-a * k) := by
        filter_upwards [hadm, hcompact, hlarge, hloghalf, eventually_ge_atTop (max nLocal
          (max (2 * k + 16) ⌈Real.exp ((k : ℝ) / B)⌉₊))]
          with n hMn hcomp hnlarge hnlog hn
        simp only [if_pos (by omega : k ≤ n)]
        by_cases hk3 : 3 ≤ k
        · have hklog : (k : ℝ) ≤ B * Real.log n := by
            have hex : Real.exp ((k : ℝ) / B) ≤ n :=
              (Nat.le_ceil _).trans (by exact_mod_cast (by omega :
                ⌈Real.exp ((k : ℝ) / B)⌉₊ ≤ n))
            have hnR : (0 : ℝ) < n := lt_of_lt_of_le hc hnlarge
            have hh := (Real.le_log_iff_exp_le hnR).2 hex
            simpa only [mul_comm] using! (div_le_iff₀ hB).1 hh
          have ht := hlocal n k (by omega) (by omega) (by omega) hklog
          have hnR : (0 : ℝ) < n := lt_of_lt_of_le hc hnlarge
          have hMU : (M n : ℝ) ≤ U * n := by
            have hd := hcomp.2.1.trans (show hi ≤ U from le_max_right _ _)
            unfold degree at hd
            have hh := (div_le_iff₀ hnR).1 hd
            nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ U) hnR.le]
          have hkhalf : k ≤ n / 2 := by
            have hk2 : (2 * k : ℕ) ≤ n := by
              exact_mod_cast (by nlinarith : (2 : ℝ) * k ≤ n)
            omega
          exact fixed_cyclic_local_bound hF CU D a U hCU hD hU hCUb
            hMn hnlarge hMU hk3 (by omega) hkhalf ht
        · have hz : cyclicFormula n (M n) k = 0 :=
            cyclicFormula_small (by omega)
          rw [hz]
          simpa only [mul_zero] using! (mul_pos hL (Real.exp_pos (-a * k))).le
      exact le_of_tendsto hlim hbound
    · exact hgeomSum
  refine ⟨hmajor, ?_⟩
  have htarget : Tendsto (fun n => ∑ k ∈ Finset.range (n + 1),
      (k : ℝ) * cyclicFormula n (M n) k) atTop (𝓝 (unicyclicLimit lam)) := by
    let f : ℕ → ℕ → ℝ := fun n k => if k ≤ n then (k : ℝ) * cyclicFormula n (M n) k else 0
    have hpoint : ∀ k, Tendsto (fun n => f n k) atTop (𝓝 (unicyclicLimitTerm lam k)) :=
      fun k => fixed_cyclic_term_tendsto hF hT hadm hlam hdeg k
    apply Metric.tendsto_atTop.2
    intro eps heps
    have hlimitEventually : ∀ᶠ H : ℕ in atTop,
        |(∑' k, unicyclicLimitTerm lam k) -
          ∑ k ∈ Finset.range H, unicyclicLimitTerm lam k| < eps / 3 := by
      have ht := hmajor.hasSum.tendsto_sum_nat.eventually
        (Metric.ball_mem_nhds _ (by positivity : 0 < eps / 3))
      filter_upwards [ht] with H hH
      simpa only [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using! hH
    have hgeomEventually : ∀ᶠ H : ℕ in atTop,
        (∑' j : ℕ, L * Real.exp (-a * (j + H))) < eps / 6 := by
      simpa only [Nat.cast_add] using!
        (tendsto_order.1 (tendsto_sum_nat_add
          (fun k : ℕ => L * Real.exp (-a * k)))).2 (eps / 6) (by positivity)
    obtain ⟨H0, hH0⟩ := eventually_atTop.1 (hlimitEventually.and hgeomEventually)
    let H := max 8 H0
    have hH := hH0 H (le_max_right _ _)
    have hlimitTail := hH.1
    have hgeomTail := hH.2
    have hfinite : Tendsto (fun n => ∑ k ∈ Finset.range H, f n k)
        atTop (𝓝 (∑ k ∈ Finset.range H, unicyclicLimitTerm lam k)) := by
      exact tendsto_finset_sum _ fun k _ => hpoint k
    have hfiniteClose := hfinite.eventually
      (Metric.ball_mem_nhds _ (by positivity : 0 < eps / 3))
    have htailSmall : ∀ᶠ n in atTop,
        (∑ k ∈ Finset.range (n + 1),
          if H ≤ k then (k : ℝ) * cyclicFormula n (M n) k else 0) < eps / 3 := by
      have hfar3 : ∀ᶠ n in atTop, treeTailOne n (M n) 3 B3 ≤
          Real.rpow (n : ℝ) (-6) := by
        filter_upwards [hadm, hcompact, hsep, eventually_ge_atTop n3] with n hm hc hs hn
        rw [← tupleTail_one_eq]
        exact htail3 n (M n) hn hm hc.1 hc.2.1 hs
      have hfar0 : ∀ᶠ n in atTop, treeTailOne n (M n) 0 B0 ≤
          Real.rpow (n : ℝ) (-15) := by
        filter_upwards [hadm, hcompact, hsep, eventually_ge_atTop n0] with n hm hc hs hn
        rw [← tupleTail_one_eq]
        exact htail0 n (M n) hn hm hc.1 hc.2.1 hs
      have hpolyzero : Tendsto (fun n : ℕ =>
          (2 * CU * (U + 1)) * (n : ℝ) ^ 2 * Real.rpow (n : ℝ) (-6) +
          (2 * CU * Real.exp 8) * (n : ℝ) ^ 12 * Real.rpow (n : ℝ) (-15))
          atTop (𝓝 0) := by
        have ht4 := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 4 by norm_num)).comp
          tendsto_natCast_atTop_atTop
        have ht3 := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 3 by norm_num)).comp
          tendsto_natCast_atTop_atTop
        have ht := (ht4.const_mul (2 * CU * (U + 1))).add
          (ht3.const_mul (2 * CU * Real.exp 8))
        have ht' : Tendsto (fun n : ℕ =>
            (2 * CU * (U + 1)) * Real.rpow (n : ℝ) (-4) +
            (2 * CU * Real.exp 8) * Real.rpow (n : ℝ) (-3))
            atTop (𝓝 (0 : ℝ)) := by simpa only [Function.comp_apply, mul_zero, zero_add] using! ht
        apply ht'.congr'
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        have hp2 : (n : ℝ) ^ 2 * Real.rpow (n : ℝ) (-6) =
            Real.rpow (n : ℝ) (-4) := by
          calc
            _ = Real.rpow (n : ℝ) (2 : ℝ) * Real.rpow (n : ℝ) (-6) := by
              norm_num [Real.rpow_natCast]
            _ = Real.rpow (n : ℝ) (2 + -6) :=
              (Real.rpow_add hnR (2 : ℝ) (-6 : ℝ)).symm
            _ = _ := by norm_num
        have hp12 : (n : ℝ) ^ 12 * Real.rpow (n : ℝ) (-15) =
            Real.rpow (n : ℝ) (-3) := by
          calc
            _ = Real.rpow (n : ℝ) (12 : ℝ) * Real.rpow (n : ℝ) (-15) := by
              norm_num [Real.rpow_natCast]
            _ = Real.rpow (n : ℝ) (12 + -15) :=
              (Real.rpow_add hnR (12 : ℝ) (-15 : ℝ)).symm
            _ = _ := by norm_num
        calc
          (2 * CU * (U + 1)) * Real.rpow (n : ℝ) (-4) +
              (2 * CU * Real.exp 8) * Real.rpow (n : ℝ) (-3) =
              (2 * CU * (U + 1)) *
                ((n : ℝ) ^ 2 * Real.rpow (n : ℝ) (-6)) +
              (2 * CU * Real.exp 8) *
                ((n : ℝ) ^ 12 * Real.rpow (n : ℝ) (-15)) := by
            rw [hp2, hp12]
          _ = _ := by ring
      have hpolySmall := (tendsto_order.1 hpolyzero).2 (eps / 6) (by positivity)
      have hlocalTail : ∀ n : ℕ,
          ∑ k ∈ Finset.Icc H ⌊B * Real.log n⌋₊,
            L * Real.exp (-a * k) < eps / 6 := by
        intro n
        have hle : (∑ k ∈ Finset.Icc H ⌊B * Real.log n⌋₊,
            L * Real.exp (-a * k)) ≤
            ∑' j : ℕ, L * Real.exp (-a * ((j + H : ℕ) : ℝ)) :=
          sum_Icc_le_tsum_nat_add
            (fun k : ℕ => L * Real.exp (-a * k)) H ⌊B * Real.log n⌋₊
            (fun _ => by positivity) hgeomSum
        apply lt_of_le_of_lt hle
        simpa only [Nat.cast_add] using! hgeomTail
      filter_upwards [hadm, hcompact, hlarge, hloghalf, hloglarge,
        eventually_ge_atTop nLocal, eventually_ge_atTop (max 16 H),
        hfar3, hfar0, hpolySmall]
        with n hMn hc hnlarge hnlog hlog hnL hn h3 h0 hp
      have hl := hlocalTail n
      have hsplit : (∑ k ∈ Finset.range (n + 1),
          if H ≤ k then (k : ℝ) * cyclicFormula n (M n) k else 0) ≤
          (∑ k ∈ Finset.Icc H ⌊B * Real.log n⌋₊, L * Real.exp (-a * k)) +
          (2 * CU * (U + 1)) * (n : ℝ) ^ 2 * treeTailOne n (M n) 3 B3 +
          (2 * CU * Real.exp 8) * (n : ℝ) ^ 12 * treeTailOne n (M n) 0 B0 := by
        let localTerm : ℕ → ℝ := fun k =>
          if H ≤ k ∧ (k : ℝ) ≤ B * Real.log n then L * Real.exp (-a * k) else 0
        let far : ℝ :=
          (CU * (U + 1) * n) * treeTailOne n (M n) 3 B3 +
          (CU * Real.exp 8 * (n : ℝ) ^ 11) * treeTailOne n (M n) 0 B0
        have hMU : (M n : ℝ) ≤ U * n := by
          have hnR : (0 : ℝ) < n := by
            exact_mod_cast (by omega : 0 < n)
          have hd := hc.2.1.trans (show hi ≤ U from le_max_right _ _)
          unfold degree at hd
          have hh := (div_le_iff₀ hnR).1 hd
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ U) hnR.le]
        have hfar0nonneg : 0 ≤ far := by
          dsimp [far]
          have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
          exact add_nonneg
            (mul_nonneg (by positivity) (tree_tail_nonneg n (M n) 3 B3))
            (mul_nonneg (by positivity) (tree_tail_nonneg n (M n) 0 B0))
        have hpoint : ∀ k ∈ Finset.range (n + 1),
            (if H ≤ k then (k : ℝ) * cyclicFormula n (M n) k else 0) ≤
              localTerm k + far := by
          intro k hk
          have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
          by_cases hkH : H ≤ k
          swap
          · simp [localTerm, hkH]
            exact hfar0nonneg
          by_cases hsmall : (k : ℝ) ≤ B * Real.log n
          · have hk3 : 3 ≤ k := by
              have hH8 : 8 ≤ H := le_max_left _ _
              omega
            have hkhalf : k ≤ n / 2 := by
              have hk2 : (2 * k : ℕ) ≤ n := by
                exact_mod_cast (by nlinarith : (2 : ℝ) * k ≤ n)
              omega
            have ht := hlocal n k (by omega) hkn (by omega) hsmall
            have hb := fixed_cyclic_local_bound hF CU D a U hCU hD hU hCUb
              hMn hnlarge hMU hk3 hkn hkhalf ht
            simp only [if_pos hkH, localTerm,
              if_pos (And.intro hkH hsmall)]
            exact hb.trans (le_add_of_nonneg_right hfar0nonneg)
          · have hk8 : 8 ≤ k := by
              have hb := hlog.2
              exact_mod_cast (by linarith : (8 : ℝ) ≤ k)
            have hb := fixed_cyclic_far_bound hF CU U B B3 B0 hCU hU hCUb
              hMn hMU (by omega) hlog.1 hB3le hB0le hk8 hkn
              (lt_of_not_ge hsmall)
            have hnot : ¬(H ≤ k ∧ (k : ℝ) ≤ B * Real.log n) :=
              fun h => hsmall h.2
            simp only [if_pos hkH]
            change (k : ℝ) * cyclicFormula n (M n) k ≤ localTerm k + far
            rw [show localTerm k = 0 by simp [localTerm, hnot], zero_add]
            exact hb
        have hlocalSum : (∑ k ∈ Finset.range (n + 1), localTerm k) ≤
            ∑ k ∈ Finset.Icc H ⌊B * Real.log n⌋₊,
              L * Real.exp (-a * k) := by
          simp only [localTerm, ← Finset.sum_filter]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk
            simp only [Finset.mem_filter, Finset.mem_range, and_assoc] at hk
            simp only [Finset.mem_Icc]
            exact ⟨hk.2.1, Nat.le_floor hk.2.2⟩
          · intro k hk _
            positivity
        have hfarSum : (∑ k ∈ Finset.range (n + 1), far) ≤
            (2 * CU * (U + 1)) * (n : ℝ) ^ 2 * treeTailOne n (M n) 3 B3 +
            (2 * CU * Real.exp 8) * (n : ℝ) ^ 12 * treeTailOne n (M n) 0 B0 := by
          simp only [Finset.sum_const_zero, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul]
          have htrees3 : 0 ≤ treeTailOne n (M n) 3 B3 := by
            unfold treeTailOne
            exact Finset.sum_nonneg fun j _ => by
              split_ifs
              · exact mul_nonneg (by positivity) (tupleMoment_nonneg n (M n) 1 (fun _ => j.val))
              · exact le_rfl
          have htrees0 : 0 ≤ treeTailOne n (M n) 0 B0 := by
            unfold treeTailOne
            exact Finset.sum_nonneg fun j _ => by
              split_ifs
              · exact mul_nonneg (by positivity) (tupleMoment_nonneg n (M n) 1 (fun _ => j.val))
              · exact le_rfl
          have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
          dsimp [far]
          push_cast
          nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ CU * (U + 1)) htrees3,
            mul_nonneg (by positivity : (0 : ℝ) ≤ CU * Real.exp 8) htrees0]
        calc
          (∑ k ∈ Finset.range (n + 1),
            if H ≤ k then (k : ℝ) * cyclicFormula n (M n) k else 0) ≤
              ∑ k ∈ Finset.range (n + 1), (localTerm k + far) :=
            Finset.sum_le_sum hpoint
          _ = (∑ k ∈ Finset.range (n + 1), localTerm k) +
              ∑ k ∈ Finset.range (n + 1), far := Finset.sum_add_distrib
          _ ≤ _ := by simpa only [add_assoc] using! add_le_add hlocalSum hfarSum
      have htail3nonneg : 0 ≤ treeTailOne n (M n) 3 B3 := by
        unfold treeTailOne
        exact Finset.sum_nonneg fun j _ => by
          split_ifs
          · exact mul_nonneg (by positivity) (tupleMoment_nonneg n (M n) 1 (fun _ => j.val))
          · exact le_rfl
      have htail0nonneg : 0 ≤ treeTailOne n (M n) 0 B0 := by
        unfold treeTailOne
        exact Finset.sum_nonneg fun j _ => by
          split_ifs
          · exact mul_nonneg (by positivity) (tupleMoment_nonneg n (M n) 1 (fun _ => j.val))
          · exact le_rfl
      have hpoly :
          (2 * CU * (U + 1)) * (n : ℝ) ^ 2 * treeTailOne n (M n) 3 B3 +
          (2 * CU * Real.exp 8) * (n : ℝ) ^ 12 * treeTailOne n (M n) 0 B0 <
          eps / 6 := by
        have hp3 := mul_le_mul_of_nonneg_left h3
          (by positivity : (0 : ℝ) ≤ (2 * CU * (U + 1)) * (n : ℝ) ^ 2)
        have hp0 := mul_le_mul_of_nonneg_left h0
          (by positivity : (0 : ℝ) ≤ (2 * CU * Real.exp 8) * (n : ℝ) ^ 12)
        nlinarith [hp]
      exact lt_of_le_of_lt hsplit (by linarith [hl, hpoly])
    obtain ⟨N, hN⟩ := eventually_atTop.1
      (hfiniteClose.and (htailSmall.and (eventually_ge_atTop H)))
    refine ⟨N, ?_⟩
    intro n hn
    obtain ⟨hf, ht, hHn⟩ := hN n hn
    have hdecomp : (∑ k ∈ Finset.range (n + 1),
        (k : ℝ) * cyclicFormula n (M n) k) =
        (∑ k ∈ Finset.range H, f n k) +
          ∑ k ∈ Finset.range (n + 1),
            if H ≤ k then (k : ℝ) * cyclicFormula n (M n) k else 0 := by
      have hHn' : H ≤ n + 1 := by omega
      have hfirst : (∑ k ∈ Finset.range (n + 1),
          if k < H then (k : ℝ) * cyclicFormula n (M n) k else 0) =
          ∑ k ∈ Finset.range H, f n k := by
        rw [← Finset.sum_filter]
        have hset : (Finset.range (n + 1)).filter (fun k => k < H) =
            Finset.range H := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_range]
          omega
        rw [hset]
        apply Finset.sum_congr rfl
        intro k hk
        have hkn : k ≤ n := by
          have hkH := Finset.mem_range.mp hk
          omega
        simp [f, hkn]
      calc
        (∑ k ∈ Finset.range (n + 1),
          (k : ℝ) * cyclicFormula n (M n) k) =
            ∑ k ∈ Finset.range (n + 1),
              ((if k < H then (k : ℝ) * cyclicFormula n (M n) k else 0) +
               (if H ≤ k then (k : ℝ) * cyclicFormula n (M n) k else 0)) := by
          apply Finset.sum_congr rfl
          intro k hk
          by_cases h : k < H
          · simp [h, show ¬H ≤ k by omega]
          · simp [h, show H ≤ k by omega]
        _ = (∑ k ∈ Finset.range (n + 1),
              if k < H then (k : ℝ) * cyclicFormula n (M n) k else 0) +
            ∑ k ∈ Finset.range (n + 1),
              if H ≤ k then (k : ℝ) * cyclicFormula n (M n) k else 0 :=
          Finset.sum_add_distrib
        _ = _ := by rw [hfirst]
    rw [hdecomp, unicyclicLimit_eq_tsum]
    rw [Real.dist_eq] at hf
    have htailNonneg : 0 ≤
        ∑ k ∈ Finset.range (n + 1),
          if H ≤ k then (k : ℝ) * cyclicFormula n (M n) k else 0 := by
      exact Finset.sum_nonneg fun k _ => by
        split_ifs
        · exact mul_nonneg (by positivity) (cyclicFormula_nonneg n (M n) k)
        · exact le_rfl
    rw [Real.dist_eq]
    let A : ℝ := ∑ k ∈ Finset.range H, f n k
    let V : ℝ := ∑ k ∈ Finset.range H, unicyclicLimitTerm lam k
    let T : ℝ := ∑ k ∈ Finset.range (n + 1),
      if H ≤ k then (k : ℝ) * cyclicFormula n (M n) k else 0
    let S : ℝ := ∑' k, unicyclicLimitTerm lam k
    change |A + T - S| < eps
    have hf' : |A - V| < eps / 3 := hf
    have hv' : |V - S| < eps / 3 := by
      simpa only [abs_sub_comm] using! hlimitTail
    have ht' : T < eps / 3 := ht
    have ht0 : 0 ≤ T := htailNonneg
    have htri1 := abs_add_le (A - V) ((V - S) + T)
    have htri2 := abs_add_le (V - S) T
    have hid : A + T - S = (A - V) + ((V - S) + T) := by ring
    rw [abs_of_nonneg ht0] at htri2
    rw [hid]
    nlinarith
  exact htarget.congr' (hadm.mono fun n hn => (expect_unicyclicMass_eq hF hn).symm)

lemma fixed_cyclic_tail
    (hF : FiniteEnumerationStatement) (hRate : RateStatement)
    {M : NatSeq} {lam : ℝ} (hadm : admissible M) (hlam : 0 < lam)
    (hlam1 : lam ≠ 1) (hdeg : Tendsto (degree M) atTop (𝓝 lam))
    (hmass : Tendsto (fun n => expectM n (M n) unicyclicMass)
      atTop (𝓝 (unicyclicLimit lam)))
    (ns h : NatSeq) (ell : ℝ) (hns : StrictMono ns)
    (hoff : Tendsto (fun j => (h j : ℝ) - center M (ns j)) atTop (𝓝 ell)) :
    Tendsto (fun j => probM (ns j) (M (ns j))
      (fun G => cyclicAbove G (h j))) atTop (𝓝 0) := by
  have hhTop := (fixedDensity_threshold_asymptotics hRate M ns h lam ell hlam
    hlam1 hdeg hns hoff).2
  have hmassSub := hmass.comp hns.tendsto_atTop
  have hquot : Tendsto (fun j => expectM (ns j) (M (ns j)) unicyclicMass /
      (h j : ℝ)) atTop (𝓝 0) := hmassSub.div_atTop
    (tendsto_natCast_atTop_iff.mpr hhTop)
  have hadmSub : ∀ᶠ j in atTop, M (ns j) ≤ capacity (ns j) :=
    hadm.filter_mono hns.tendsto_atTop
  have hhpos : ∀ᶠ j in atTop, 0 < h j :=
    ((tendsto_atTop.1 hhTop) 1).mono fun _ hj => lt_of_lt_of_le Nat.zero_lt_one hj
  apply squeeze_zero'
  · filter_upwards with j
    unfold probM
    positivity
  · filter_upwards [hadmSub, hhpos] with j hm hh
    exact prob_cyclicAbove_le_mass_div hF hm (by exact_mod_cast hh)
  · exact hquot

end
end Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_FixedMass
