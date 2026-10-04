module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage6.TaskContracts
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.FoundationP068P069.Work

open Finset Set
open scoped BigOperators

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Erdos448.Stage6.TaskContracts

noncomputable section

lemma one_le_safeLog (t : ℝ) : 1 ≤ safeLog t := le_max_left _ _

lemma safeLog_pos (t : ℝ) : 0 < safeLog t :=
  zero_lt_one.trans_le (one_le_safeLog t)

lemma safeLog_nonneg (t : ℝ) : 0 ≤ safeLog t :=
  (safeLog_pos t).le

lemma mem_positiveNatsBelow {T : ℝ} {n : ℕ} :
    n ∈ positiveNatsBelow T ↔ 0 < n ∧ (n : ℝ) < T := by
  rw [positiveNatsBelow, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hn, hnpos, hnT⟩
    exact ⟨hnpos, hnT⟩
  · rintro ⟨hnpos, hnT⟩
    exact ⟨Nat.lt_ceil.mpr hnT, hnpos, hnT⟩

lemma positiveNatsBelow_eq_Ico (T : ℝ) :
    positiveNatsBelow T = Finset.Ico 1 (Nat.ceil T) := by
  ext n
  rw [mem_positiveNatsBelow, Finset.mem_Ico]
  constructor
  · rintro ⟨hn, hnT⟩
    exact ⟨hn, Nat.lt_ceil.mpr hnT⟩
  · rintro ⟨hn, hnT⟩
    exact ⟨hn, Nat.lt_ceil.mp hnT⟩

lemma safeLog_le_two_one_add_log {t : ℝ} (ht : 1 ≤ t) :
    safeLog t ≤ 2 * (1 + Real.log t) := by
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  unfold safeLog
  apply max_le
  · linarith
  · linarith

lemma one_add_log_le_two_safeLog {t : ℝ} (ht : 1 ≤ t) :
    1 + Real.log t ≤ 2 * safeLog t := by
  have h1 := one_le_safeLog t
  have hlog : Real.log t ≤ safeLog t := le_max_right _ _
  linarith

lemma inv_sqrt_safeLog_le_two {t : ℝ} (ht : 1 ≤ t) :
    (safeLog t).rpow (-1 / 2) ≤
      2 * (1 + Real.log t).rpow (-1 / 2) := by
  have ha : 0 < 1 + Real.log t := by
    have := Real.log_nonneg ht
    linarith
  have h := one_add_log_le_two_safeLog ht
  have hhalf : (1 + Real.log t) / 2 ≤ safeLog t := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    simpa [mul_comm] using h
  have hp := Real.rpow_le_rpow_of_nonpos (div_pos ha (by norm_num : (0 : ℝ) < 2))
    hhalf
    (by norm_num : (-1 / 2 : ℝ) ≤ 0)
  calc
    (safeLog t).rpow (-1 / 2) ≤ ((1 + Real.log t) / 2).rpow (-1 / 2) := hp
    _ = (2 : ℝ).rpow (1 / 2) * (1 + Real.log t).rpow (-1 / 2) := by
      change ((1 + Real.log t) / 2) ^ (-1 / 2 : ℝ) =
        (2 : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log t) ^ (-1 / 2 : ℝ)
      rw [Real.div_rpow ha.le (by norm_num : (0 : ℝ) ≤ 2)]
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      rw [div_inv_eq_mul]
      ring
    _ ≤ 2 * (1 + Real.log t).rpow (-1 / 2) := by
      have hsqrt : (2 : ℝ).rpow (1 / 2) ≤ 2 := by
        change (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2
        rw [← Real.sqrt_eq_rpow]
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
      exact mul_le_mul_of_nonneg_right hsqrt (Real.rpow_nonneg ha.le _)

@[expose] def logHarmonicMajorant (t : ℝ) : ℝ :=
  2 * (1 + Real.log t).rpow (-1 / 2) / t

@[expose] def logHarmonicPrimitive (t : ℝ) : ℝ :=
  4 * (1 + Real.log t).rpow (1 / 2)

lemma hasDerivAt_logHarmonicPrimitive {t : ℝ} (ht : 1 ≤ t) :
    HasDerivAt logHarmonicPrimitive (logHarmonicMajorant t) t := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hu : 0 < 1 + Real.log t := by
    have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
    linarith
  have hbase : HasDerivAt (fun s : ℝ => 1 + Real.log s) t⁻¹ t := by
    simpa only [Pi.add_def, zero_add] using
      (hasDerivAt_const t (1 : ℝ)).add (Real.hasDerivAt_log ht0.ne')
  have hp := (hbase.rpow_const (p := (1 / 2 : ℝ)) (Or.inl hu.ne')).const_mul 4
  unfold logHarmonicPrimitive logHarmonicMajorant
  convert hp using 1
  field_simp [ht0.ne']
  norm_num [div_eq_mul_inv]

lemma integral_logHarmonicMajorant {N : ℝ} (hN : 1 ≤ N) :
    (∫ t in (1 : ℝ)..N, logHarmonicMajorant t) =
      logHarmonicPrimitive N - logHarmonicPrimitive 1 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [Set.uIcc_of_le hN] at ht
    exact hasDerivAt_logHarmonicPrimitive ht.1
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hN]
    apply ContinuousOn.div
    · apply continuousOn_const.mul
      apply ContinuousOn.rpow_const
      · exact continuousOn_const.add
          (Real.continuousOn_log.mono fun t ht => ne_of_gt (zero_lt_one.trans_le ht.1))
      · intro t ht
        left
        have hlog := Real.log_nonneg ht.1
        linarith
    · exact continuousOn_id
    · intro t ht
      exact ne_of_gt (zero_lt_one.trans_le ht.1)

lemma logHarmonicMajorant_antitoneOn {N : ℝ} (hN : 1 ≤ N) :
    AntitoneOn logHarmonicMajorant (Set.Icc 1 N) := by
  intro a ha b hb hab
  have ha0 : 0 < a := by linarith [ha.1]
  have hb0 : 0 < b := by linarith [hb.1]
  have hla : 0 < 1 + Real.log a := by
    have := Real.log_nonneg ha.1
    linarith
  have hlb : 0 < 1 + Real.log b := by
    have := Real.log_nonneg hb.1
    linarith
  have hlog : 1 + Real.log a ≤ 1 + Real.log b := by
    gcongr
  have hrpow : (1 + Real.log b).rpow (-1 / 2) ≤
      (1 + Real.log a).rpow (-1 / 2) :=
    Real.rpow_le_rpow_of_nonpos hla hlog (by norm_num)
  have hinv : b⁻¹ ≤ a⁻¹ := (inv_le_inv₀ hb0 ha0).2 hab
  unfold logHarmonicMajorant
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hrpow (by norm_num)) hinv
    (inv_nonneg.2 hb0.le) (mul_nonneg (by norm_num) (Real.rpow_nonneg hla.le _))

lemma log_harmonic_sum_bound {T : ℝ} (hT : 1 < T) :
    (∑ m ∈ positiveNatsBelow T,
        (safeLog m).rpow (-1 / 2) / (m : ℝ)) ≤
      8 * (safeLog (2 * T)).rpow (1 / 2) := by
  let N := Nat.ceil T
  have hN : 2 ≤ N := by
    have : 1 < (N : ℝ) := by
      exact lt_of_lt_of_le hT (Nat.le_ceil T)
    exact_mod_cast this
  rw [positiveNatsBelow_eq_Ico]
  rw [Finset.sum_Ico_eq_sum_range]
  rw [show N - 1 = (N - 2) + 1 by omega, Finset.sum_range_succ']
  have hpoint : ∀ i ∈ Finset.range (N - 2),
      (safeLog (2 + i)).rpow (-1 / 2) / (2 + i : ℕ) ≤
        logHarmonicMajorant (2 + (i : ℝ)) := by
    intro i hi
    have hi1 : (1 : ℝ) ≤ 2 + (i : ℝ) := by
      have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      linarith
    have hw := inv_sqrt_safeLog_le_two hi1
    unfold logHarmonicMajorant
    push_cast
    change (safeLog (2 + (i : ℝ))).rpow (-1 / 2) / (2 + (i : ℝ)) ≤
      2 * (1 + Real.log (2 + (i : ℝ))).rpow (-1 / 2) / (2 + (i : ℝ))
    exact div_le_div_of_nonneg_right hw (by positivity)
  have hsum := Finset.sum_le_sum hpoint
  have hant := logHarmonicMajorant_antitoneOn (N := (N : ℝ)) (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega : N ≠ 0)))
  have hint := AntitoneOn.sum_le_integral (x₀ := (1 : ℝ)) (a := N - 2)
    (f := logHarmonicMajorant) (hant.mono (by
      intro t ht
      constructor
      · exact ht.1
      · calc
          t ≤ 1 + (N - 2 : ℕ) := ht.2
          _ ≤ (N : ℝ) := by
            push_cast [Nat.cast_sub hN]
            linarith))
  let A : ℝ := 1 + (N - 2 : ℕ)
  have hA1 : 1 ≤ A := by
    dsimp [A]
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hAN : A ≤ (N : ℝ) := by
    dsimp [A]
    push_cast [Nat.cast_sub hN]
    linarith
  have hceil : (N : ℝ) < T + 1 := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ T)
  have htwoT : T + 1 ≤ 2 * T := by linarith
  have hlogle : 1 + Real.log (N : ℝ) ≤ 2 * safeLog (2 * T) := by
    apply le_trans (one_add_log_le_two_safeLog (t := (N : ℝ)) (by exact_mod_cast (show 1 ≤ N by omega)))
    gcongr
    unfold safeLog
    apply max_le_max_left
    apply Real.log_le_log (by positivity)
    exact le_trans (le_of_lt hceil) htwoT
  have hsqrtle : (1 + Real.log (N : ℝ)).rpow (1 / 2) ≤
      2 * (safeLog (2 * T)).rpow (1 / 2) := by
    have h := Real.rpow_le_rpow (by
      have := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast (show 1 ≤ N by omega))
      linarith) hlogle (by norm_num : (0 : ℝ) ≤ 1 / 2)
    calc
      (1 + Real.log (N : ℝ)).rpow (1 / 2) ≤
          (2 * safeLog (2 * T)).rpow (1 / 2) := h
      _ = (2 : ℝ).rpow (1 / 2) * (safeLog (2 * T)).rpow (1 / 2) := by
        change (2 * safeLog (2 * T)) ^ (1 / 2 : ℝ) =
          (2 : ℝ) ^ (1 / 2 : ℝ) * safeLog (2 * T) ^ (1 / 2 : ℝ)
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (safeLog_nonneg _)]
      _ ≤ 2 * (safeLog (2 * T)).rpow (1 / 2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (safeLog_nonneg _) _)
        change (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2
        rw [← Real.sqrt_eq_rpow]
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hmajor :
      (∑ i ∈ Finset.range (N - 2),
          logHarmonicMajorant (2 + (i : ℝ))) ≤
        ∫ t in (1 : ℝ)..A, logHarmonicMajorant t := by
    convert hint using 1 <;> simp [A, Nat.cast_add] <;> ring
  have hprimA : logHarmonicPrimitive A ≤ logHarmonicPrimitive (N : ℝ) := by
    unfold logHarmonicPrimitive
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.rpow_le_rpow
    · have hlogA := Real.log_nonneg hA1
      linarith
    · gcongr
    · norm_num
  calc
    (∑ x ∈ Finset.range (N - 2),
        (safeLog ((1 + (x + 1) : ℕ) : ℝ)).rpow (-1 / 2) /
          ((1 + (x + 1) : ℕ) : ℝ)) +
        (safeLog (((1 + 0 : ℕ) : ℕ) : ℝ)).rpow (-1 / 2) /
          (((1 + 0 : ℕ) : ℕ) : ℝ)
        = (∑ x ∈ Finset.range (N - 2),
            (safeLog ((2 + x : ℕ) : ℝ)).rpow (-1 / 2) / ((2 + x : ℕ) : ℝ)) + 1 := by
              simp only [show (1 + 0 : ℕ) = 1 by omega]
              congr 1
              · apply Finset.sum_congr rfl
                intro i hi
                congr 2 <;> push_cast <;> ring
              · simp [safeLog]
    _ ≤ (∑ i ∈ Finset.range (N - 2), logHarmonicMajorant (2 + (i : ℝ))) + 1 :=
      add_le_add (by simpa [Nat.cast_add] using hsum) le_rfl
    _ ≤ (∫ t in (1 : ℝ)..A, logHarmonicMajorant t) + 1 := add_le_add hmajor le_rfl
    _ = logHarmonicPrimitive A - logHarmonicPrimitive 1 + 1 := by
      rw [integral_logHarmonicMajorant hA1]
    _ ≤ logHarmonicPrimitive (N : ℝ) - logHarmonicPrimitive 1 + 1 := by linarith
    _ ≤ 8 * (safeLog (2 * T)).rpow (1 / 2) := by
      unfold logHarmonicPrimitive
      have hsafe : 1 ≤ (safeLog (2 * T)).rpow (1 / 2) := by
        have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
          (one_le_safeLog (2 * T)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        simpa using h
      norm_num at *
      nlinarith

@[expose] def endpointKernel (M beta t : ℝ) : ℝ :=
  4 * (1 + Real.log M - Real.log t).rpow (beta - 1) * t⁻¹

@[expose] def endpointPrimitive (M beta t : ℝ) : ℝ :=
  -(4 / beta) * (1 + Real.log M - Real.log t).rpow beta

@[expose] def endpointKernelDeriv (M beta t : ℝ) : ℝ :=
  4 * ((-t⁻¹) * (beta - 1) *
      (1 + Real.log M - Real.log t).rpow (beta - 2) * t⁻¹ +
    (1 + Real.log M - Real.log t).rpow (beta - 1) * (-1 * t⁻¹ ^ 2))

lemma endpoint_base_pos {M t : ℝ} (hM : 1 < M) (ht1 : 1 ≤ t)
    (htM : t ≤ M) : 0 < 1 + Real.log M - Real.log t := by
  have hlog : Real.log t ≤ Real.log M := by
    exact Real.strictMonoOn_log.monotoneOn (zero_lt_one.trans_le ht1)
      (lt_trans zero_lt_one hM) htM
  linarith

lemma hasDerivAt_endpointPrimitive {M beta t : ℝ}
    (hM : 1 < M) (hbeta : 0 < beta) (ht1 : 1 ≤ t) (htM : t ≤ M) :
    HasDerivAt (endpointPrimitive M beta) (endpointKernel M beta t) t := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hu := endpoint_base_pos hM ht1 htM
  have hbase : HasDerivAt (fun s : ℝ => 1 + Real.log M - Real.log s) (-t⁻¹) t := by
    convert (hasDerivAt_const t (1 + Real.log M)).sub (Real.hasDerivAt_log ht0.ne') using 1 <;>
      simp
  have hp := (hbase.rpow_const (p := beta) (Or.inl hu.ne')).const_mul (-(4 / beta))
  unfold endpointPrimitive endpointKernel
  convert hp using 1
  field_simp [hbeta.ne', ht0.ne']
  congr 1

lemma endpointKernel_antitoneOn {M beta : ℝ}
    (hM : 1 < M) (hbeta : 0 < beta) (hbeta_one : beta ≤ 1) :
    AntitoneOn (endpointKernel M beta) (Set.Icc 1 M) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := endpointKernelDeriv M beta)
    (convex_Icc 1 M)
  · apply ContinuousOn.div
    · apply continuousOn_const.mul
      apply ContinuousOn.rpow_const
      · exact ((continuousOn_const.add continuousOn_const).sub
          (Real.continuousOn_log.mono fun t ht =>
            ne_of_gt (zero_lt_one.trans_le ht.1)))
      · intro t ht
        left
        exact (endpoint_base_pos hM ht.1 ht.2).ne'
    · exact continuousOn_id
    · intro t ht
      exact ne_of_gt (zero_lt_one.trans_le ht.1)
  · intro t ht
    have htI : t ∈ Set.Icc (1 : ℝ) M := interior_subset ht
    have ht0 : 0 < t := zero_lt_one.trans_le htI.1
    have hu := endpoint_base_pos hM htI.1 htI.2
    have hbase : HasDerivAt (fun s : ℝ => 1 + Real.log M - Real.log s) (-t⁻¹) t := by
      convert (hasDerivAt_const t (1 + Real.log M)).sub (Real.hasDerivAt_log ht0.ne') using 1 <;>
        simp
    have hp := hbase.rpow_const (p := beta - 1) (Or.inl hu.ne')
    have hi : HasDerivAt (fun s : ℝ => s⁻¹) (-1 / t ^ 2) t := by
      simpa only [id_eq, Pi.inv_def] using (hasDerivAt_id t).inv ht0.ne'
    have hd := (hp.mul hi).const_mul 4
    have hd' : HasDerivAt (endpointKernel M beta) (endpointKernelDeriv M beta t) t := by
      convert hd using 1
      · funext y
        unfold endpointKernel
        dsimp
        ring
      · simp [endpointKernelDeriv, div_eq_mul_inv,
          show beta - 1 - 1 = beta - 2 by ring, mul_assoc]
    exact hd'.hasDerivWithinAt
  · intro t ht
    have htI : t ∈ Set.Icc (1 : ℝ) M := interior_subset ht
    have ht0 : 0 < t := zero_lt_one.trans_le htI.1
    have hu := endpoint_base_pos hM htI.1 htI.2
    have hsum : 0 < (1 + Real.log M - Real.log t) + beta - 1 := by
      have hlog : 0 ≤ Real.log M - Real.log t := by
        have := Real.strictMonoOn_log.monotoneOn ht0 (lt_trans zero_lt_one hM) htI.2
        linarith
      linarith
    have hpadd : (1 + Real.log M - Real.log t).rpow (beta - 1) =
        (1 + Real.log M - Real.log t).rpow (beta - 2) *
          (1 + Real.log M - Real.log t) := by
      calc
        _ = (1 + Real.log M - Real.log t).rpow ((beta - 2) + 1) := by congr 1 <;> ring
        _ = (1 + Real.log M - Real.log t).rpow (beta - 2) *
            (1 + Real.log M - Real.log t).rpow 1 := Real.rpow_add hu _ _
        _ = _ := by norm_num [Real.rpow_one]
    unfold endpointKernelDeriv
    rw [hpadd]
    have htinv : 0 ≤ t⁻¹ := inv_nonneg.2 ht0.le
    have hpow : 0 ≤ (1 + Real.log M - Real.log t).rpow (beta - 2) :=
      Real.rpow_nonneg hu.le _
    field_simp [ht0.ne']
    nlinarith [mul_nonneg hpow hsum.le]

lemma endpoint_sum_bound {M beta : ℝ} (hM : 1 < M)
    (hbeta : 0 < beta) (hbeta_one : beta ≤ 1) :
    (∑ m ∈ positiveNatsBelow M,
        (safeLog (M / m)).rpow (beta - 1) / (m : ℝ)) ≤
      (16 / beta) * (safeLog (2 * M)).rpow beta := by
  let N := Nat.ceil M
  have hN : 2 ≤ N := by
    have : 1 < (N : ℝ) := lt_of_lt_of_le hM (Nat.le_ceil M)
    exact_mod_cast this
  have hNm : (N - 1 : ℝ) < M := by
    have hceil : (N : ℝ) < M + 1 := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ M)
    push_cast [Nat.cast_sub (show 1 ≤ N by omega)]
    linarith
  rw [positiveNatsBelow_eq_Ico, Finset.sum_Ico_eq_sum_range]
  rw [show N - 1 = (N - 2) + 1 by omega, Finset.sum_range_succ']
  have hpoint : ∀ i ∈ Finset.range (N - 2),
      (safeLog (M / (2 + i : ℕ))).rpow (beta - 1) / (2 + i : ℕ) ≤
        endpointKernel M beta (2 + (i : ℝ)) := by
    intro i hi
    have hiNat : 2 + i ≤ N - 1 := by
      have hi' := Finset.mem_range.mp hi
      omega
    have hi2 : (2 + (i : ℝ)) ≤ (N : ℝ) - 1 := by
      have hiN : 2 + i + 1 ≤ N := by omega
      have hiCast : (((2 + i + 1 : ℕ) : ℝ)) ≤ (N : ℝ) := by exact_mod_cast hiN
      push_cast at hiCast
      linarith
    have ht1 : (1 : ℝ) ≤ 2 + (i : ℝ) := by
      have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      linarith
    have htM : 2 + (i : ℝ) < M := lt_of_le_of_lt hi2 hNm
    have hratio : 1 ≤ M / (2 + (i : ℝ)) := by
      apply (le_div_iff₀ (show (0 : ℝ) < 2 + (i : ℝ) by positivity)).2
      simpa using htM.le
    have hu := endpoint_base_pos hM ht1 htM.le
    have hsafe := one_add_log_le_two_safeLog hratio
    have hexp : -1 ≤ beta - 1 := by linarith
    have hnexp : beta - 1 ≤ 0 := by linarith
    have hhalf : (1 + Real.log (M / (2 + (i : ℝ)))) / 2 ≤
        safeLog (M / (2 + (i : ℝ))) := by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      simpa [mul_comm] using hsafe
    have hhalf' : (1 + Real.log M - Real.log (2 + (i : ℝ))) / 2 ≤
        safeLog (M / (2 + (i : ℝ))) := by
      rw [Real.log_div (lt_trans zero_lt_one hM).ne' (by positivity : (2 + (i : ℝ)) ≠ 0)] at hhalf
      simpa only [add_sub] using hhalf
    have hr := Real.rpow_le_rpow_of_nonpos (div_pos hu (by norm_num : (0 : ℝ) < 2)) hhalf' hnexp
    let u : ℝ := 1 + Real.log M - Real.log (2 + (i : ℝ))
    have htwo : (u / 2).rpow (beta - 1) ≤ 4 * u.rpow (beta - 1) := by
      have hu0 : 0 ≤ u := by exact hu.le
      have h2pow : ((2 : ℝ).rpow (beta - 1))⁻¹ ≤ 4 := by
        have hExp : -(beta - 1) ≤ 1 := by linarith
        calc
          ((2 : ℝ).rpow (beta - 1))⁻¹ = (2 : ℝ).rpow (-(beta - 1)) := by
            symm
            exact Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (beta - 1)
          _ ≤ (2 : ℝ).rpow 1 := Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp
          _ ≤ 4 := by norm_num
      calc
        (u / 2).rpow (beta - 1) = u.rpow (beta - 1) / (2 : ℝ).rpow (beta - 1) :=
          Real.div_rpow hu0 (by norm_num) (beta - 1)
        _ = ((2 : ℝ).rpow (beta - 1))⁻¹ * u.rpow (beta - 1) := by
          rw [div_eq_mul_inv]
          ring
        _ ≤ 4 * u.rpow (beta - 1) :=
          mul_le_mul_of_nonneg_right h2pow (Real.rpow_nonneg hu0 _)
    have huEq : 1 + Real.log (M / (2 + (i : ℝ))) = u := by
      dsimp [u]
      rw [Real.log_div (lt_trans (by positivity) hM).ne' (by positivity : (2 + (i : ℝ)) ≠ 0)]
      ring
    have htwo' : ((1 + Real.log M - Real.log (2 + (i : ℝ))) / 2).rpow (beta - 1) ≤
        4 * (1 + Real.log M - Real.log (2 + (i : ℝ))).rpow (beta - 1) := by
      simpa [u] using htwo
    unfold endpointKernel
    push_cast
    exact mul_le_mul_of_nonneg_right (hr.trans htwo') (inv_nonneg.2 (by positivity))
  have hsum := Finset.sum_le_sum hpoint
  have hant := endpointKernel_antitoneOn hM hbeta hbeta_one
  let A : ℝ := 1 + (N - 2 : ℕ)
  have hA1 : 1 ≤ A := by dsimp [A]; exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hAM : A < M := by
    dsimp [A]
    push_cast [Nat.cast_sub hN]
    linarith
  have hint := AntitoneOn.sum_le_integral (x₀ := (1 : ℝ)) (a := N - 2)
    (f := endpointKernel M beta) (hant.mono (by
      intro t ht
      exact ⟨ht.1, le_trans ht.2 hAM.le⟩))
  have hint' : (∑ i ∈ Finset.range (N - 2), endpointKernel M beta (2 + (i : ℝ))) ≤
      ∫ t in (1 : ℝ)..A, endpointKernel M beta t := by
    convert hint using 1 <;> simp [A, Nat.cast_add] <;> ring
  have hintEq : (∫ t in (1 : ℝ)..A, endpointKernel M beta t) =
      endpointPrimitive M beta A - endpointPrimitive M beta 1 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le hA1] at ht
      exact hasDerivAt_endpointPrimitive hM hbeta ht.1 (le_trans ht.2 hAM.le)
    · apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hA1]
      apply ContinuousOn.div
      · apply continuousOn_const.mul
        apply ContinuousOn.rpow_const
        · exact ((continuousOn_const.add continuousOn_const).sub
            (Real.continuousOn_log.mono fun t ht =>
              ne_of_gt (zero_lt_one.trans_le ht.1)))
        · intro t ht
          left
          exact (endpoint_base_pos hM ht.1 (le_trans ht.2 hAM.le)).ne'
      · exact continuousOn_id
      · intro t ht
        exact ne_of_gt (zero_lt_one.trans_le ht.1)
  have hfirst : (safeLog M).rpow (beta - 1) ≤
      4 * (safeLog (2 * M)).rpow beta := by
    have hleft : (safeLog M).rpow (beta - 1) ≤ 1 := by
      have := Real.rpow_le_rpow_of_nonpos zero_lt_one (one_le_safeLog M)
        (by linarith : beta - 1 ≤ 0)
      simpa using this
    have hright : 1 ≤ (safeLog (2 * M)).rpow beta := by
      have := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
        (one_le_safeLog (2 * M)) hbeta.le
      simpa using this
    nlinarith
  have hprim : endpointPrimitive M beta A - endpointPrimitive M beta 1 ≤
      (8 / beta) * (safeLog (2 * M)).rpow beta := by
    unfold endpointPrimitive
    have hnonneg := Real.rpow_nonneg (endpoint_base_pos hM hA1 hAM.le).le beta
    have hbase : 1 + Real.log M ≤ 2 * safeLog (2 * M) := by
      have hm2 : 1 ≤ 2 * M := by linarith
      calc
        1 + Real.log M ≤ 1 + Real.log (2 * M) := by gcongr <;> linarith
        _ ≤ 2 * safeLog (2 * M) := one_add_log_le_two_safeLog hm2
    have hp := Real.rpow_le_rpow (by have := Real.log_pos hM; linarith) hbase hbeta.le
    have htwo : (2 * safeLog (2 * M)).rpow beta ≤
        2 * (safeLog (2 * M)).rpow beta := by
      change (2 * safeLog (2 * M)) ^ beta ≤ 2 * safeLog (2 * M) ^ beta
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (safeLog_nonneg _)]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num : (1 : ℝ) ≤ 2) hbeta_one)
        (Real.rpow_nonneg (safeLog_nonneg _) _)
    have hcoef : 0 < 4 / beta := div_pos (by norm_num) hbeta
    have hu1 : (1 + Real.log M - Real.log (1 : ℝ)).rpow beta ≤
        2 * (safeLog (2 * M)).rpow beta := by
      simpa using hp.trans htwo
    have hdrop : endpointPrimitive M beta A - endpointPrimitive M beta 1 ≤
        (4 / beta) * (1 + Real.log M - Real.log (1 : ℝ)).rpow beta := by
      unfold endpointPrimitive
      calc
        -(4 / beta) * (1 + Real.log M - Real.log A).rpow beta -
            -(4 / beta) * (1 + Real.log M - Real.log 1).rpow beta =
            (4 / beta) * (1 + Real.log M - Real.log 1).rpow beta -
              (4 / beta) * (1 + Real.log M - Real.log A).rpow beta := by ring
        _ ≤ (4 / beta) * (1 + Real.log M - Real.log 1).rpow beta :=
          sub_le_self _ (mul_nonneg hcoef.le hnonneg)
    calc
      _ ≤ (4 / beta) * (1 + Real.log M - Real.log 1).rpow beta := hdrop
      _ ≤ (4 / beta) * (2 * (safeLog (2 * M)).rpow beta) :=
        mul_le_mul_of_nonneg_left hu1 hcoef.le
      _ = (8 / beta) * (safeLog (2 * M)).rpow beta := by ring
  have hy : 0 ≤ (safeLog (2 * M)).rpow beta := Real.rpow_nonneg (safeLog_nonneg _) _
  have h4 : 4 ≤ 8 / beta := by
    apply (le_div_iff₀ hbeta).2
    nlinarith [hbeta_one]
  have htail : 4 * (safeLog (2 * M)).rpow beta ≤
      (8 / beta) * (safeLog (2 * M)).rpow beta :=
    mul_le_mul_of_nonneg_right h4 hy
  change ((∑ x ∈ Finset.range (N - 2),
      (safeLog (M / ((1 + (x + 1) : ℕ) : ℝ))).rpow (beta - 1) /
        ((1 + (x + 1) : ℕ) : ℝ)) +
      (safeLog (M / (((1 + 0 : ℕ) : ℕ) : ℝ))).rpow (beta - 1) /
        (((1 + 0 : ℕ) : ℕ) : ℝ)) ≤ _
  calc
    _ ≤ (∑ i ∈ Finset.range (N - 2), endpointKernel M beta (2 + (i : ℝ))) +
        (safeLog M).rpow (beta - 1) := by
      apply add_le_add
      · convert hsum using 1 <;> simp [Nat.cast_add] <;> ring
      · simp
    _ ≤ (∫ t in (1 : ℝ)..A, endpointKernel M beta t) +
        4 * (safeLog (2 * M)).rpow beta := add_le_add hint' hfirst
    _ = (endpointPrimitive M beta A - endpointPrimitive M beta 1) +
        4 * (safeLog (2 * M)).rpow beta := by rw [hintEq]
    _ ≤ (8 / beta) * (safeLog (2 * M)).rpow beta +
        (8 / beta) * (safeLog (2 * M)).rpow beta := add_le_add hprim htail
    _ = (16 / beta) * (safeLog (2 * M)).rpow beta := by ring

lemma safeLog_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    safeLog a ≤ safeLog b := by
  unfold safeLog
  exact max_le_max le_rfl (Real.log_le_log ha hab)

lemma safeLog_two_mul_le_four_sqrt {M : ℝ} (hM : 1 < M) :
    safeLog (2 * M) ≤ 4 * safeLog (Real.sqrt M) := by
  have hM0 : 0 < M := lt_trans zero_lt_one hM
  have hs : 0 < Real.sqrt M := Real.sqrt_pos.2 hM0
  have hlogM : Real.log M = 2 * Real.log (Real.sqrt M) := by
    calc
      Real.log M = Real.log ((Real.sqrt M) ^ 2) := by
        congr 1
        nlinarith [Real.sq_sqrt hM0.le]
      _ = (2 : ℕ) * Real.log (Real.sqrt M) := Real.log_pow _ _
      _ = 2 * Real.log (Real.sqrt M) := by norm_num
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog : Real.log (2 * M) ≤ 3 * safeLog (Real.sqrt M) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hM0.ne', hlogM]
    have hsafe1 := one_le_safeLog (Real.sqrt M)
    have hsafelog : Real.log (Real.sqrt M) ≤ safeLog (Real.sqrt M) := le_max_right _ _
    linarith
  unfold safeLog at *
  apply max_le
  · have := le_max_left (1 : ℝ) (Real.log (Real.sqrt M))
    linarith
  · have hsafe : 0 ≤ max 1 (Real.log √M) := by positivity
    linarith

lemma rpow_neg_compare_four {a L e : ℝ} (ha : 0 < a) (hL : 0 < L)
    (hcomp : L ≤ 4 * a) (he0 : e ≤ 0) (hem1 : -1 ≤ e) :
    a.rpow e ≤ 4 * L.rpow e := by
  have hquarter : L / 4 ≤ a := by linarith
  have hr := Real.rpow_le_rpow_of_nonpos (div_pos hL (by norm_num)) hquarter he0
  have h4 : ((4 : ℝ).rpow e)⁻¹ ≤ 4 := by
    calc
      ((4 : ℝ).rpow e)⁻¹ = (4 : ℝ).rpow (-e) := by
        symm
        exact Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4) e
      _ ≤ (4 : ℝ).rpow 1 := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 4 := by norm_num
  calc
    a.rpow e ≤ (L / 4).rpow e := hr
    _ = L.rpow e / (4 : ℝ).rpow e := Real.div_rpow hL.le (by norm_num) e
    _ = ((4 : ℝ).rpow e)⁻¹ * L.rpow e := by rw [div_eq_mul_inv]; ring
    _ ≤ 4 * L.rpow e :=
      mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hL.le _)

/- The full log-beta convolution estimate.  The proof splits at `sqrt M`;
the lower half uses `log_harmonic_sum_bound`, while the upper half is compared
with the derivative of `(1 + log (M/t))^beta`. -/
theorem log_beta_convolution_bound
    {M beta : ℝ} (hM : 1 < M) (hbeta : 0 < beta) (hbeta_half : beta ≤ 1 / 2) :
    (∑ m ∈ positiveNatsBelow M,
      (safeLog m).rpow (-1 / 2) / (m : ℝ) *
        (safeLog (M / m)).rpow (beta - 1)) ≤
      (128 / beta) * (safeLog (2 * M)).rpow (beta - 1 / 2) := by
  let s : Finset ℕ := positiveNatsBelow M
  let r := Real.sqrt M
  let L := safeLog (2 * M)
  let low : Finset ℕ := s.filter fun m => (m : ℝ) ≤ r
  let high : Finset ℕ := s.filter fun m => ¬(m : ℝ) ≤ r
  have hM0 : 0 < M := lt_trans zero_lt_one hM
  have hr0 : 0 < r := by dsimp [r]; exact Real.sqrt_pos.2 hM0
  have hL : 0 < L := by dsimp [L]; exact safeLog_pos _
  have hcompare : L ≤ 4 * safeLog r := by
    dsimp [L, r]
    exact safeLog_two_mul_le_four_sqrt hM
  have he0 : beta - 1 ≤ 0 := by linarith
  have hem1 : -1 ≤ beta - 1 := by linarith
  have hlowPoint : ∀ m ∈ low,
      (safeLog m).rpow (-1 / 2) / (m : ℝ) *
          (safeLog (M / m)).rpow (beta - 1) ≤
        (4 * L.rpow (beta - 1)) *
          ((safeLog m).rpow (-1 / 2) / (m : ℝ)) := by
    intro m hm
    have hmS := (Finset.mem_filter.mp hm).1
    have hmle := (Finset.mem_filter.mp hm).2
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (mem_positiveNatsBelow.mp hmS).1
    have hsqrt : r ≤ M / (m : ℝ) := by
      apply (le_div_iff₀ hmpos).2
      dsimp [r] at hmle ⊢
      nlinarith [Real.sq_sqrt hM0.le, Real.sqrt_nonneg M]
    have hsafe : safeLog r ≤ safeLog (M / (m : ℝ)) :=
      safeLog_mono hr0 hsqrt
    have hend : (safeLog (M / (m : ℝ))).rpow (beta - 1) ≤
        (safeLog r).rpow (beta - 1) :=
      Real.rpow_le_rpow_of_nonpos (safeLog_pos r) hsafe he0
    have hscale : (safeLog r).rpow (beta - 1) ≤ 4 * L.rpow (beta - 1) :=
      rpow_neg_compare_four (safeLog_pos r) hL hcompare he0 hem1
    have hweight : 0 ≤ (safeLog (m : ℝ)).rpow (-1 / 2) / (m : ℝ) :=
      div_nonneg (Real.rpow_nonneg (safeLog_nonneg _) _) hmpos.le
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hend.trans hscale) hweight
  have hlowSum :
      (∑ m ∈ low, (safeLog m).rpow (-1 / 2) / (m : ℝ) *
          (safeLog (M / m)).rpow (beta - 1)) ≤
        32 * L.rpow (beta - 1 / 2) := by
    have hs := Finset.sum_le_sum hlowPoint
    have hsubset : low ⊆ s := Finset.filter_subset _ _
    have hnonneg : ∀ m ∈ s, 0 ≤ (safeLog m).rpow (-1 / 2) / (m : ℝ) := by
      intro m hm
      have hmpos : (0 : ℝ) < m := by exact_mod_cast (mem_positiveNatsBelow.mp hm).1
      exact div_nonneg (Real.rpow_nonneg (safeLog_nonneg _) _) hmpos.le
    have hsubsum : (∑ m ∈ low, (safeLog m).rpow (-1 / 2) / (m : ℝ)) ≤
        ∑ m ∈ s, (safeLog m).rpow (-1 / 2) / (m : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro m hmS hmnot
        exact hnonneg m hmS)
    have hharm := log_harmonic_sum_bound hM
    dsimp [s] at hharm
    calc
      _ ≤ ∑ m ∈ low, (4 * L.rpow (beta - 1)) *
          ((safeLog m).rpow (-1 / 2) / (m : ℝ)) := hs
      _ = (4 * L.rpow (beta - 1)) *
          (∑ m ∈ low, (safeLog m).rpow (-1 / 2) / (m : ℝ)) := by
            rw [Finset.mul_sum]
      _ ≤ (4 * L.rpow (beta - 1)) *
          (∑ m ∈ s, (safeLog m).rpow (-1 / 2) / (m : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hsubsum
              (mul_nonneg (by norm_num) (Real.rpow_nonneg hL.le _))
      _ ≤ (4 * L.rpow (beta - 1)) * (8 * L.rpow (1 / 2)) := by
            exact mul_le_mul_of_nonneg_left hharm
              (mul_nonneg (by norm_num) (Real.rpow_nonneg hL.le _))
      _ = 32 * L.rpow (beta - 1 / 2) := by
        calc
          _ = 32 * (L.rpow (beta - 1) * L.rpow (1 / 2)) := by ring
          _ = 32 * L.rpow ((beta - 1) + 1 / 2) := by
            congr 1
            exact (Real.rpow_add hL (beta - 1) (1 / 2)).symm
          _ = _ := by congr 2 <;> ring
  have hhighPoint : ∀ m ∈ high,
      (safeLog m).rpow (-1 / 2) / (m : ℝ) *
          (safeLog (M / m)).rpow (beta - 1) ≤
        (4 * L.rpow (-1 / 2)) *
          ((safeLog (M / m)).rpow (beta - 1) / (m : ℝ)) := by
    intro m hm
    have hmS := (Finset.mem_filter.mp hm).1
    have hmgt : r < (m : ℝ) := lt_of_not_ge (Finset.mem_filter.mp hm).2
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (mem_positiveNatsBelow.mp hmS).1
    have hsafe : safeLog r ≤ safeLog (m : ℝ) := safeLog_mono hr0 hmgt.le
    have hfirst : (safeLog (m : ℝ)).rpow (-1 / 2) ≤
        (safeLog r).rpow (-1 / 2) :=
      Real.rpow_le_rpow_of_nonpos (safeLog_pos r) hsafe (by norm_num)
    have hscale : (safeLog r).rpow (-1 / 2) ≤ 4 * L.rpow (-1 / 2) :=
      rpow_neg_compare_four (safeLog_pos r) hL hcompare (by norm_num) (by norm_num)
    have hend : 0 ≤ (safeLog (M / (m : ℝ))).rpow (beta - 1) :=
      Real.rpow_nonneg (safeLog_nonneg _) _
    have hfirstScale : (safeLog (m : ℝ)).rpow (-1 / 2) ≤
        4 * L.rpow (-1 / 2) := hfirst.trans hscale
    calc
      _ ≤ (4 * L.rpow (-1 / 2)) / (m : ℝ) *
          (safeLog (M / m)).rpow (beta - 1) := by
            exact mul_le_mul_of_nonneg_right
              (div_le_div_of_nonneg_right hfirstScale hmpos.le) hend
      _ = (4 * L.rpow (-1 / 2)) *
          ((safeLog (M / m)).rpow (beta - 1) / (m : ℝ)) := by ring
  have hhighSum :
      (∑ m ∈ high, (safeLog m).rpow (-1 / 2) / (m : ℝ) *
          (safeLog (M / m)).rpow (beta - 1)) ≤
        (64 / beta) * L.rpow (beta - 1 / 2) := by
    have hs := Finset.sum_le_sum hhighPoint
    have hsubset : high ⊆ s := Finset.filter_subset _ _
    have hendNonneg : ∀ m ∈ s,
        0 ≤ (safeLog (M / m)).rpow (beta - 1) / (m : ℝ) := by
      intro m hm
      have hmpos : (0 : ℝ) < m := by exact_mod_cast (mem_positiveNatsBelow.mp hm).1
      exact div_nonneg (Real.rpow_nonneg (safeLog_nonneg _) _) hmpos.le
    have hsubsum : (∑ m ∈ high, (safeLog (M / m)).rpow (beta - 1) / (m : ℝ)) ≤
        ∑ m ∈ s, (safeLog (M / m)).rpow (beta - 1) / (m : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro m hmS hmnot
        exact hendNonneg m hmS)
    have hendSum := endpoint_sum_bound hM hbeta (le_trans hbeta_half (by norm_num))
    dsimp [s] at hendSum
    calc
      _ ≤ ∑ m ∈ high, (4 * L.rpow (-1 / 2)) *
          ((safeLog (M / m)).rpow (beta - 1) / (m : ℝ)) := hs
      _ = (4 * L.rpow (-1 / 2)) *
          (∑ m ∈ high, (safeLog (M / m)).rpow (beta - 1) / (m : ℝ)) := by
            rw [Finset.mul_sum]
      _ ≤ (4 * L.rpow (-1 / 2)) *
          (∑ m ∈ s, (safeLog (M / m)).rpow (beta - 1) / (m : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hsubsum
              (mul_nonneg (by norm_num) (Real.rpow_nonneg hL.le _))
      _ ≤ (4 * L.rpow (-1 / 2)) *
          ((16 / beta) * L.rpow beta) := by
            exact mul_le_mul_of_nonneg_left hendSum
              (mul_nonneg (by norm_num) (Real.rpow_nonneg hL.le _))
      _ = (64 / beta) * L.rpow (beta - 1 / 2) := by
        calc
          _ = (64 / beta) * (L.rpow (-1 / 2) * L.rpow beta) := by ring
          _ = (64 / beta) * L.rpow ((-1 / 2) + beta) := by
            congr 1
            exact (Real.rpow_add hL (-1 / 2) beta).symm
          _ = _ := by congr 2 <;> ring
  have hsplit :
      (∑ m ∈ s, (safeLog m).rpow (-1 / 2) / (m : ℝ) *
          (safeLog (M / m)).rpow (beta - 1)) =
        (∑ m ∈ low, (safeLog m).rpow (-1 / 2) / (m : ℝ) *
          (safeLog (M / m)).rpow (beta - 1)) +
        (∑ m ∈ high, (safeLog m).rpow (-1 / 2) / (m : ℝ) *
          (safeLog (M / m)).rpow (beta - 1)) := by
    dsimp [low, high]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  dsimp [s] at hsplit ⊢
  rw [hsplit]
  have hbetaInv : 1 ≤ 1 / beta := by
    apply (le_div_iff₀ hbeta).2
    linarith
  have hpnonneg : 0 ≤ L.rpow (beta - 1 / 2) := Real.rpow_nonneg hL.le _
  calc
    _ ≤ 32 * L.rpow (beta - 1 / 2) +
        (64 / beta) * L.rpow (beta - 1 / 2) := add_le_add hlowSum hhighSum
    _ ≤ (128 / beta) * L.rpow (beta - 1 / 2) := by
      have hcoeff : 32 ≤ 64 / beta := by
        apply (le_div_iff₀ hbeta).2
        nlinarith [hbeta_half]
      have h32 : 32 * L.rpow (beta - 1 / 2) ≤
          (64 / beta) * L.rpow (beta - 1 / 2) :=
        mul_le_mul_of_nonneg_right hcoeff hpnonneg
      calc
        _ ≤ (64 / beta) * L.rpow (beta - 1 / 2) +
            (64 / beta) * L.rpow (beta - 1 / 2) := add_le_add h32 le_rfl
        _ = _ := by ring

lemma theta_zpow (theta : ℝ) (htheta : 0 < theta) (k : ℕ) :
    theta ^ (1 - (2 : ℤ) * k) = theta / theta ^ (2 * k) := by
  have hne : theta ≠ 0 := ne_of_gt htheta
  rw [zpow_sub₀ hne, zpow_one]
  congr 1

lemma theta_zpow_three (theta : ℝ) (htheta : 0 < theta) (k : ℕ) :
    theta ^ (1 - (3 : ℤ) * k) = theta / theta ^ (3 * k) := by
  have hne : theta ≠ 0 := ne_of_gt htheta
  rw [zpow_sub₀ hne, zpow_one]
  congr 1

lemma normalized_endpoint_gt_one (q : WeightParameters) (x : ℝ)
    (hx : q.theta ^ (2 * q.k - 1) < x) :
    1 < x * q.theta ^ (1 - (2 : ℤ) * q.k) := by
  have ht : 0 < q.theta := lt_of_lt_of_le (by norm_num) q.theta_ge_two
  have hkpos := q.k_pos
  have hk : 2 * q.k = (2 * q.k - 1) + 1 := by omega
  rw [theta_zpow q.theta ht q.k]
  rw [hk, pow_add, pow_one]
  field_simp [ne_of_gt ht, ne_of_gt (pow_pos ht (2 * q.k - 1))]
  nlinarith [mul_pos (sub_pos.mpr hx) ht]

lemma convolutionA_inner_le (q : WeightParameters) (x : ℝ)
    (hx : q.theta ^ (2 * q.k - 1) < x) :
    (∑ m ∈ positiveNatsBelow (x * q.theta ^ (1 - (3 : ℤ) * q.k)),
      (safeLog m).rpow (-1 / 2) / m *
        (safeLog (x * q.theta ^ (1 - (2 : ℤ) * q.k) / m)).rpow (-1 / 2)) ≤ 256 := by
  let M := x * q.theta ^ (1 - (2 : ℤ) * q.k)
  have hM : 1 < M := normalized_endpoint_gt_one q x hx
  have ht : 0 < q.theta := lt_of_lt_of_le (by norm_num) q.theta_ge_two
  have hsubset : positiveNatsBelow (x * q.theta ^ (1 - (3 : ℤ) * q.k)) ⊆
      positiveNatsBelow M := by
    intro m hm
    apply mem_positiveNatsBelow.mpr
    have hm' := mem_positiveNatsBelow.mp hm
    refine ⟨hm'.1, lt_of_lt_of_le hm'.2 ?_⟩
    dsimp [M]
    rw [theta_zpow_three q.theta ht q.k, theta_zpow q.theta ht q.k]
    have hp : 1 ≤ q.theta ^ q.k := one_le_pow₀ (by linarith [q.theta_ge_two])
    have hx0 : 0 < x := lt_trans (pow_pos ht _) hx
    have h2 : 0 < q.theta ^ (2 * q.k) := pow_pos ht _
    have h3 : 0 < q.theta ^ (3 * q.k) := pow_pos ht _
    have h3eq : q.theta ^ (3 * q.k) = q.theta ^ (2 * q.k) * q.theta ^ q.k := by
      rw [show 3 * q.k = 2 * q.k + q.k by omega, pow_add]
    have hdiv := (div_le_div_iff_of_pos_left (mul_pos hx0 ht) h3 h2).2
      (by rw [h3eq]; exact le_mul_of_one_le_right h2.le hp)
    simpa [mul_div_assoc] using hdiv
  have hnonneg : ∀ m ∈ positiveNatsBelow M,
      0 ≤ (safeLog m).rpow (-1 / 2) / m *
        (safeLog (M / m)).rpow (-1 / 2) := by
    intro m hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (mem_positiveNatsBelow.mp hm).1
    exact mul_nonneg (div_nonneg (Real.rpow_nonneg (safeLog_nonneg _) _) hmpos.le)
      (Real.rpow_nonneg (safeLog_nonneg _) _)
  have hrestrict := Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
    intro m hmM hmnot
    exact hnonneg m hmM)
  have hbeta := log_beta_convolution_bound hM (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2)
  dsimp [M] at hrestrict hbeta ⊢
  have hbeta' :
      (∑ m ∈ positiveNatsBelow (x * q.theta ^ (1 - (2 : ℤ) * q.k)),
        (safeLog m).rpow (-1 / 2) / m *
          (safeLog (x * q.theta ^ (1 - (2 : ℤ) * q.k) / m)).rpow (-1 / 2)) ≤ 256 := by
    have hb := hbeta
    norm_num only [show (1 / 2 - 1 : ℝ) = -1 / 2 by ring,
      show (1 / 2 - 1 / 2 : ℝ) = 0 by ring,
      show (128 / (1 / 2) : ℝ) = 256 by norm_num] at hb
    have hb' :
        (∑ m ∈ positiveNatsBelow (x * q.theta ^ (1 - (2 : ℤ) * q.k)),
          (safeLog m).rpow (-1 / 2) / m *
            (safeLog (x * q.theta ^ (1 - (2 : ℤ) * q.k) / m)).rpow (-1 / 2)) ≤
          256 * (safeLog (2 * (x * q.theta ^ (1 - (2 : ℤ) * q.k)))).rpow 0 := by
      simpa only [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_eq_pow] using hb
    calc
      _ ≤ 256 * (safeLog (2 * (x * q.theta ^ (1 - (2 : ℤ) * q.k)))).rpow 0 := hb'
      _ = 256 * 1 := by
        exact congrArg (fun z : ℝ => 256 * z)
          (Real.rpow_zero (safeLog (2 * (x * q.theta ^ (1 - (2 : ℤ) * q.k)))))
      _ = 256 := by ring
  exact hrestrict.trans hbeta'

theorem p068 : P068Statement := by
  refine ⟨⟨256, by norm_num, ?_⟩⟩
  intro q x hx
  unfold convolutionA
  have hinner := convolutionA_inner_le q x hx
  have hx0 : 0 ≤ x := le_of_lt (lt_trans (pow_pos
    (lt_of_lt_of_le (by norm_num) q.theta_ge_two) _) hx)
  have hthetaPow : 0 < q.theta ^ (2 * q.k) := pow_pos
    (lt_of_lt_of_le (by norm_num) q.theta_ge_two) _
  have hkpow : 0 ≤ (q.k : ℝ).rpow ((q.y - 1) / 2) := Real.rpow_nonneg (by positivity) _
  have hcoeff : 0 ≤ x / q.theta ^ (2 * q.k) *
      (q.k : ℝ).rpow ((q.y - 1) / 2) :=
    mul_nonneg (div_nonneg hx0 hthetaPow.le) hkpow
  calc
    x / q.theta ^ (2 * q.k) * (q.k : ℝ).rpow ((q.y - 1) / 2) * _
        ≤ x / q.theta ^ (2 * q.k) * (q.k : ℝ).rpow ((q.y - 1) / 2) * 256 :=
          mul_le_mul_of_nonneg_left hinner hcoeff
    _ = 256 * (x / q.theta ^ (2 * q.k)) *
        (q.k : ℝ).rpow ((q.y - 1) / 2) := by ring

lemma middle_inner_le (q : WeightParameters) (x : ℝ)
    (hx : q.theta ^ (2 * q.k - 1) < x) :
    (∑ m ∈ positiveNatsBelow (x * q.theta ^ (1 - (2 : ℤ) * q.k)),
      (safeLog m).rpow (-1 / 2) / m *
        (safeLog (x * q.theta ^ (1 - (2 : ℤ) * q.k) / m)).rpow (q.y / 2 - 1)) ≤
      (256 / q.y) *
        (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow
          ((q.y - 1) / 2) := by
  let M := x * q.theta ^ (1 - (2 : ℤ) * q.k)
  have hM : 1 < M := normalized_endpoint_gt_one q x hx
  have hb : 0 < q.y / 2 := div_pos q.y_pos (by norm_num)
  have hbh : q.y / 2 ≤ 1 / 2 := by linarith [q.y_lt_one]
  have h := log_beta_convolution_bound hM hb hbh
  dsimp [M] at h ⊢
  calc
    _ ≤ (128 / (q.y / 2)) *
        (safeLog (2 * (x * q.theta ^ (1 - (2 : ℤ) * q.k)))).rpow
          (q.y / 2 - 1 / 2) := h
    _ = (256 / q.y) *
        (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow
          ((q.y - 1) / 2) := by
      field_simp [q.y_pos.ne']
      ring

theorem p069 : P069Statement := by
  refine ⟨⟨256, by norm_num, ?_⟩⟩
  constructor
  · intro q x hx
    unfold convolutionBSharp
    have hfull := middle_inner_le q x hx
    have hsum :
        (∑ m ∈ positiveNatsBelow (x * q.theta ^ (1 - (2 : ℤ) * q.k)),
          if x * q.theta ^ (1 - (3 : ℤ) * q.k) ≤ m then
            (safeLog m).rpow (-1 / 2) / m *
              (safeLog (x * q.theta ^ (1 - (2 : ℤ) * q.k) / m)).rpow (q.y / 2 - 1)
          else 0) ≤
        (∑ m ∈ positiveNatsBelow (x * q.theta ^ (1 - (2 : ℤ) * q.k)),
          (safeLog m).rpow (-1 / 2) / m *
            (safeLog (x * q.theta ^ (1 - (2 : ℤ) * q.k) / m)).rpow (q.y / 2 - 1)) := by
      apply Finset.sum_le_sum
      intro m hm
      split_ifs
      · rfl
      · have hmpos : (0 : ℝ) < m := by exact_mod_cast (mem_positiveNatsBelow.mp hm).1
        exact mul_nonneg (div_nonneg (Real.rpow_nonneg (safeLog_nonneg _) _) hmpos.le)
          (Real.rpow_nonneg (safeLog_nonneg _) _)
    have hpref : 0 ≤ x / q.theta ^ (2 * q.k) := by
      have hx0 : 0 < x := lt_trans (pow_pos
        (lt_of_lt_of_le (by norm_num) q.theta_ge_two) _) hx
      exact div_nonneg hx0.le (pow_nonneg (by linarith [q.theta_ge_two]) _)
    calc
      x / q.theta ^ (2 * q.k) * _ ≤
          x / q.theta ^ (2 * q.k) *
            ((256 / q.y) * (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow
              ((q.y - 1) / 2)) := mul_le_mul_of_nonneg_left (hsum.trans hfull) hpref
      _ = (256 / q.y) * (x / q.theta ^ (2 * q.k)) *
          (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow
            ((q.y - 1) / 2) := by ring
  · intro q x hx
    unfold convolutionBEnlarged
    have hfull := middle_inner_le q x hx
    have hsum :
        (∑ m ∈ positiveNatsBelow (x * q.theta ^ (1 - (2 : ℤ) * q.k)),
          if x * q.theta ^ (-((3 : ℤ) * q.k) - 3) < m then
            (safeLog m).rpow (-1 / 2) / m *
              (safeLog (x * q.theta ^ (1 - (2 : ℤ) * q.k) / m)).rpow (q.y / 2 - 1)
          else 0) ≤
        (∑ m ∈ positiveNatsBelow (x * q.theta ^ (1 - (2 : ℤ) * q.k)),
          (safeLog m).rpow (-1 / 2) / m *
            (safeLog (x * q.theta ^ (1 - (2 : ℤ) * q.k) / m)).rpow (q.y / 2 - 1)) := by
      apply Finset.sum_le_sum
      intro m hm
      split_ifs
      · rfl
      · have hmpos : (0 : ℝ) < m := by exact_mod_cast (mem_positiveNatsBelow.mp hm).1
        exact mul_nonneg (div_nonneg (Real.rpow_nonneg (safeLog_nonneg _) _) hmpos.le)
          (Real.rpow_nonneg (safeLog_nonneg _) _)
    have hpref : 0 ≤ x / q.theta ^ (2 * q.k) := by
      have hx0 : 0 < x := lt_trans (pow_pos
        (lt_of_lt_of_le (by norm_num) q.theta_ge_two) _) hx
      exact div_nonneg hx0.le (pow_nonneg (by linarith [q.theta_ge_two]) _)
    calc
      x / q.theta ^ (2 * q.k) * _ ≤
          x / q.theta ^ (2 * q.k) *
            ((256 / q.y) * (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow
              ((q.y - 1) / 2)) := mul_le_mul_of_nonneg_left (hsum.trans hfull) hpref
      _ = (256 / q.y) * (x / q.theta ^ (2 * q.k)) *
          (safeLog (2 * x * q.theta ^ (1 - (2 : ℤ) * q.k))).rpow
            ((q.y - 1) / 2) := by ring

/-- Public reuse surface for ROOT09. The existing private proof is unchanged;
no new foundation estimate, extra assumption, or absolute constant is added. -/
theorem logBetaConvolutionBound
    {M beta : ℝ} (hM : 1 < M) (hbeta : 0 < beta) (hbeta_half : beta ≤ 1 / 2) :
    (∑ m ∈ positiveNatsBelow M,
      (safeLog m).rpow (-1 / 2) / (m : ℝ) *
        (safeLog (M / m)).rpow (beta - 1)) ≤
      (128 / beta) * (safeLog (2 * M)).rpow (beta - 1 / 2) :=
  log_beta_convolution_bound hM hbeta hbeta_half

theorem result : FoundationP068P069Target :=
  ⟨p068, p069⟩

end

end Erdos448.Stage7.FoundationP068P069.Work
