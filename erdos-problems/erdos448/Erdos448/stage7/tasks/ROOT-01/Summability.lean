module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-01».EulerExpansion

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT01

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Finset Nat Set
open scoped BigOperators Topology

noncomputable section

lemma geometricLog_summable
    (A q B : ℝ) (hA : 0 ≤ A) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun j : ℕ => A * q ^ j * (1 + (j : ℝ) * B)) := by
  have hnorm : ‖q‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have hgeom : Summable (fun j : ℕ => q ^ j) := summable_geometric_of_norm_lt_one hnorm
  have hweighted : Summable (fun j : ℕ => (j : ℝ) * q ^ j) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable
  have hsum := (hgeom.mul_left A).add (hweighted.mul_left (A * B))
  apply hsum.congr
  intro j
  ring

lemma shiftedLocal_summable
    (lambdaSeq : ℕ → ℝ) (hlambdaSeq : ∀ i, 0 ≤ lambdaSeq i)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda2 : lambda < 2)
    (u v : ArithmeticWeight) (hbounds : ShiftedGeometricBounds u v lambdaSeq lambda)
    (p : ℕ) (hp : p.Prime) (i : ℕ) :
    Summable (fun j : ℕ =>
      u (p ^ (i + j)) * v (p ^ j) * (1 + j * Real.log p) / (p : ℝ) ^ j) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  let q : ℝ := lambda / (p : ℝ)
  have hq0 : 0 ≤ q := div_nonneg hlambda0 hp0.le
  have hq1 : q < 1 := by
    dsimp [q]
    rw [div_lt_one hp0]
    exact hlambda2.trans_le hp2
  have hmajor := geometricLog_summable (lambdaSeq i) q (Real.log p)
    (hlambdaSeq i) hq0 hq1
  apply hmajor.of_nonneg_of_le
  · intro j
    exact div_nonneg
      (mul_nonneg (hbounds p hp i j).1
        (add_nonneg zero_le_one
          (mul_nonneg (Nat.cast_nonneg j) (Real.log_natCast_nonneg p))))
      (pow_nonneg hp0.le j)
  · intro j
    have hbracket : 0 ≤ 1 + (j : ℝ) * Real.log p :=
      add_nonneg zero_le_one
        (mul_nonneg (Nat.cast_nonneg j) (Real.log_natCast_nonneg p))
    calc
      u (p ^ (i + j)) * v (p ^ j) * (1 + j * Real.log p) / (p : ℝ) ^ j
          ≤ (lambdaSeq i * lambda ^ j) * (1 + j * Real.log p) /
              (p : ℝ) ^ j := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hbounds p hp i j).2 hbracket)
              (pow_nonneg hp0.le j)
      _ = lambdaSeq i * q ^ j * (1 + j * Real.log p) := by
        dsimp [q]
        rw [div_pow]
        ring

lemma weight_eq_prod_over
    (w : ArithmeticWeight) (hw : MultiplicativeWeight w)
    {n : ℕ} (hn : 0 < n) {s : Finset ℕ} (hsub : n.primeFactors ⊆ s)
    (hsPrime : ∀ p ∈ s, p.Prime) :
    w n = ∏ p ∈ s, w (p ^ n.factorization p) := by
  rw [Nat.multiplicative_factorization w (fun x y hxy => by
      rcases eq_or_ne x 0 with rfl | hx
      · have : y = 1 := by simpa using hxy
        simp [this, hw.1]
      rcases eq_or_ne y 0 with rfl | hy
      · have : x = 1 := by simpa using hxy
        simp [this, hw.1]
      exact hw.2 x y (Nat.pos_of_ne_zero hx) (Nat.pos_of_ne_zero hy) hxy)
    hw.1 (Nat.ne_of_gt hn), Nat.prod_factorization_eq_prod_primeFactors]
  apply Finset.prod_subset hsub
  intro p hps hpn
  have hfac : n.factorization p = 0 := by
    exact Nat.factorization_eq_zero_of_not_dvd
      (fun hpdiv => hpn (Nat.mem_primeFactors.mpr
        ⟨hsPrime p hps, hpdiv, Nat.ne_of_gt hn⟩))
  simp [hfac, hw.1]

lemma logFactor_prod_over
    {d : ℕ} (hd : 0 < d) {s : Finset ℕ} (hsub : d.primeFactors ⊆ s)
    (hsPrime : ∀ p ∈ s, p.Prime) :
    (∏ p ∈ d.primeFactors,
      (1 + (d.factorization p : ℝ) * Real.log p)) =
    ∏ p ∈ s, (1 + (d.factorization p : ℝ) * Real.log p) := by
  apply Finset.prod_subset hsub
  intro p hps hpn
  have hfac : d.factorization p = 0 := by
    exact Nat.factorization_eq_zero_of_not_dvd
      (fun hpdiv => hpn (Nat.mem_primeFactors.mpr
        ⟨hsPrime p hps, hpdiv, Nat.ne_of_gt hd⟩))
  simp [hfac]

lemma coefficient_eq_enlarged
    (u v : ArithmeticWeight)
    (hu : NonnegativeMultiplicativeWeight u)
    (hv : NonnegativeMultiplicativeWeight v)
    (Ksh : PosNat) (d : factoredNumbers Ksh.1.primeFactors) :
    localCoefficientProduct
      (fun p j => u (p ^ (Ksh.1.factorization p + j)) * v (p ^ j) *
        (1 + (j : ℝ) * Real.log p) / (p : ℝ) ^ j)
      Ksh.1.primeFactors d.1 = enlargedShiftMajorant u v Ksh d.1 := by
  have hd : 0 < d.1 := Nat.pos_of_ne_zero d.2.1
  have hdsub : d.1.primeFactors ⊆ Ksh.1.primeFactors :=
    primeFactors_subset_of_mem_factoredNumbers d.2
  have hKmul : 0 < Ksh.1 * d.1 := Nat.mul_pos Ksh.2 hd
  have hKmulSub : (Ksh.1 * d.1).primeFactors ⊆ Ksh.1.primeFactors := by
    rw [Nat.primeFactors_mul (Nat.ne_of_gt Ksh.2) (Nat.ne_of_gt hd)]
    exact Finset.union_subset (fun _ h => h) hdsub
  have hKPrime : ∀ p ∈ Ksh.1.primeFactors, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors hp
  have huProd := weight_eq_prod_over u hu.multiplicative hKmul hKmulSub hKPrime
  have hvProd := weight_eq_prod_over v hv.multiplicative hd hdsub hKPrime
  have hfacMul : ∀ p : ℕ,
      (Ksh.1 * d.1).factorization p =
        Ksh.1.factorization p + d.1.factorization p := by
    intro p
    simpa using DFunLike.congr_fun
      (Nat.factorization_mul (Nat.ne_of_gt Ksh.2) (Nat.ne_of_gt hd)) p
  have hdCast : (d.1 : ℝ) =
      ∏ p ∈ Ksh.1.primeFactors, (p : ℝ) ^ d.1.factorization p := by
    calc
      (d.1 : ℝ) = (∏ p : d.1.primeFactors,
          ((p : ℕ) : ℝ) ^ d.1.factorization p) := by
        exact_mod_cast Nat.prod_pow_primeFactors_factorization (Nat.ne_of_gt hd)
      _ = ∏ p ∈ d.1.primeFactors, (p : ℝ) ^ d.1.factorization p := by
        exact (Finset.prod_subtype d.1.primeFactors (fun _ => Iff.rfl)
          (fun p => (p : ℝ) ^ d.1.factorization p)).symm
      _ = ∏ p ∈ Ksh.1.primeFactors, (p : ℝ) ^ d.1.factorization p := by
        apply Finset.prod_subset hdsub
        intro p hpK hpd
        have hfac : d.1.factorization p = 0 :=
          Nat.factorization_eq_zero_of_not_dvd
            (fun hpdiv => hpd (Nat.mem_primeFactors.mpr
              ⟨Nat.prime_of_mem_primeFactors hpK, hpdiv, Nat.ne_of_gt hd⟩))
        simp [hfac]
  have hlog := logFactor_prod_over hd hdsub hKPrime
  rw [enlargedShiftMajorant, dif_pos hd,
    if_pos (show HasPrimeSupportIn ⟨d.1, hd⟩ Ksh from hdsub)]
  rw [localCoefficientProduct, huProd, hvProd, hlog]
  simp_rw [hfacMul]
  rw [hdCast]
  simp only [Finset.prod_mul_distrib, Finset.prod_div_distrib]
  ring

lemma exactOuterSupport
    (u v : ArithmeticWeight) (Ksh : PosNat) (X : ℝ) :
    ∀ d : ℕ, commonPrimeTerm u v Ksh X d ≠ 0 →
      0 < d ∧ (d : ℝ) < X := by
  intro d hdne
  unfold commonPrimeTerm at hdne
  split_ifs at hdne with hd hsupp
  · refine ⟨hd, ?_⟩
    have hset : (positiveNatsBelow (X / (d : ℝ))).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hdne
      simp at hdne
    obtain ⟨m, hm⟩ := hset
    have hm' := mem_positiveNatsBelow.mp hm
    have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hm'.1
    have hquot : 1 < X / (d : ℝ) := hmOne.trans_lt hm'.2
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    rw [lt_div_iff₀ hdR] at hquot
    simpa using hquot
  · contradiction
  · contradiction

theorem p005A (hEXT001 : EXT001Statement) : P005AStatement := by
  intro lambdaSeq hlambdaSeq lambda hlambda0 hlambda2 u v hu hv hbounds Ksh X hX
  let h : ArithmeticWeight := fun n => u n * v n
  have hgeom : PrimePowerGeometricBound h (lambdaSeq 0) lambda := by
    intro p hp j
    simpa [h, zero_add] using hbounds p hp 0 j
  obtain ⟨meanProvider⟩ := hEXT001 (lambdaSeq 0) lambda
    ⟨hlambdaSeq 0, hlambda0, hlambda2⟩
  have hunshifted : ∀ p : ℕ, p.Prime →
      Summable (fun j : ℕ => u (p ^ j) * v (p ^ j) / (p : ℝ) ^ j) := by
    intro p hp
    simpa [h] using meanProvider.local_series_summable h hgeom p hp
  have hshifted : ∀ p : ℕ, p.Prime → ∀ i : ℕ,
      Summable (fun j : ℕ =>
        u (p ^ (i + j)) * v (p ^ j) * (1 + j * Real.log p) / (p : ℝ) ^ j) :=
    fun p hp i => shiftedLocal_summable lambdaSeq hlambdaSeq lambda hlambda0 hlambda2
      u v hbounds p hp i
  have houter := exactOuterSupport u v Ksh X
  let a : ℕ → ℕ → ℝ := fun p j =>
    u (p ^ (Ksh.1.factorization p + j)) * v (p ^ j) *
      (1 + (j : ℝ) * Real.log p) / (p : ℝ) ^ j
  have haNonneg : ∀ p ∈ Ksh.1.primeFactors, ∀ j : ℕ, 0 ≤ a p j := by
    intro p hpK j
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpK
    exact div_nonneg
      (mul_nonneg (hbounds p hp (Ksh.1.factorization p) j).1
        (add_nonneg zero_le_one
          (mul_nonneg (Nat.cast_nonneg j) (Real.log_natCast_nonneg p))))
      (pow_nonneg (Nat.cast_nonneg p) j)
  have haSum : ∀ p ∈ Ksh.1.primeFactors, Summable (a p) := by
    intro p hpK
    exact hshifted p (Nat.prime_of_mem_primeFactors hpK) (Ksh.1.factorization p)
  have hexpand := finiteEulerExpansion a Ksh.1.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp) haNonneg haSum
  have hcoeff : ∀ d : factoredNumbers Ksh.1.primeFactors,
      localCoefficientProduct a Ksh.1.primeFactors d.1 =
        enlargedShiftMajorant u v Ksh d.1 := by
    intro d
    exact coefficient_eq_enlarged u v hu hv Ksh d
  have henlargedIndicator : enlargedShiftMajorant u v Ksh =
      (factoredNumbers Ksh.1.primeFactors).indicator
        (fun d => localCoefficientProduct a Ksh.1.primeFactors d) := by
    funext d
    by_cases hdmem : d ∈ factoredNumbers Ksh.1.primeFactors
    · rw [Set.indicator_of_mem hdmem]
      exact (hcoeff ⟨d, hdmem⟩).symm
    · rw [Set.indicator_of_notMem hdmem]
      rw [enlargedShiftMajorant]
      split_ifs with hd hsupp
      · exact (hdmem (mem_factoredNumbers_of_primeFactors_subset
          (Nat.ne_of_gt hd) hsupp)).elim
      · rfl
      · rfl
  have henlargedSum : Summable (enlargedShiftMajorant u v Ksh) := by
    rw [henlargedIndicator]
    exact summable_subtype_iff_indicator.mp hexpand.1
  have henlargedFactor :
      ∑' d : ℕ, enlargedShiftMajorant u v Ksh d =
        ∏ p ∈ Ksh.1.primeFactors,
          shiftNumerator u v p (Ksh.1.factorization p) := by
    rw [henlargedIndicator, ← _root_.tsum_subtype]
    calc
      (∑' d : factoredNumbers Ksh.1.primeFactors,
          localCoefficientProduct a Ksh.1.primeFactors d.1) =
          ∏ p ∈ Ksh.1.primeFactors, ∑' j : ℕ, a p j := hexpand.2.tsum_eq
      _ = ∏ p ∈ Ksh.1.primeFactors,
          shiftNumerator u v p (Ksh.1.factorization p) := by
        apply Finset.prod_congr rfl
        intro p hp
        rfl
  refine
    { unshifted_local_summable := hunshifted
      shifted_local_summable := hshifted
      exact_outer_support := houter
      exact_outer_support_finite := ?_
      exact_outer_summable := ?_
      enlarged_majorant_nonnegative := ?_
      enlarged_majorant_summable := henlargedSum
      enlarged_majorant_factorization := henlargedFactor
      shift_denominator_positive := ?_ }
  · apply (positiveNatsBelow X).finite_toSet.subset
    intro d hdSupport
    exact mem_positiveNatsBelow.mpr (houter d hdSupport)
  · exact summable_of_finite_support
      ((positiveNatsBelow X).finite_toSet.subset fun d hdSupport =>
        mem_positiveNatsBelow.mpr (houter d hdSupport))
  · intro d
    by_cases hd : 0 < d
    · rw [enlargedShiftMajorant, dif_pos hd]
      split_ifs with hsupp
      · exact mul_nonneg
          (div_nonneg
            (mul_nonneg (hu.nonnegative _ (Nat.mul_pos Ksh.2 hd))
              (hv.nonnegative _ hd))
            (Nat.cast_nonneg d))
          (Finset.prod_nonneg fun p hpD =>
            add_nonneg zero_le_one
              (mul_nonneg (Nat.cast_nonneg (d.factorization p))
                (Real.log_natCast_nonneg p)))
      · exact le_rfl
    · rw [enlargedShiftMajorant, dif_neg hd]
  · intro p hp
    unfold shiftDenominator
    refine (hunshifted p hp).tsum_pos ?_ 0 ?_
    · intro j
      exact div_nonneg (by simpa using (hbounds p hp 0 j).1)
        (pow_nonneg (Nat.cast_nonneg p) j)
    · simpa [hu.multiplicative.1, hv.multiplicative.1]

end

end Erdos448.Stage7.ROOT01
