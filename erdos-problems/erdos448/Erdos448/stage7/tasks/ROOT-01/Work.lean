module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-01».IntervalProducts
public import Erdos448.stage7.tasks.«ROOT-01».ShiftedMean

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT01

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Finset Nat Set
open scoped BigOperators Topology

noncomputable section

lemma prod_nonnegative_le_one
    {s : Finset ℕ} {f : ℕ → ℝ}
    (hf0 : ∀ n ∈ s, 0 ≤ f n) (hf1 : ∀ n ∈ s, f n ≤ 1) :
    ∏ n ∈ s, f n ≤ 1 := by
  induction s using Finset.induction with
  | empty => simp
  | @insert n s hn ih =>
      rw [Finset.prod_insert hn]
      have h := mul_le_mul (hf1 n (mem_insert_self n s))
        (ih (fun i hi => hf0 i (mem_insert_of_mem hi))
          (fun i hi => hf1 i (mem_insert_of_mem hi)))
        (Finset.prod_nonneg fun i hi => hf0 i (mem_insert_of_mem hi)) zero_le_one
      simpa using h

lemma mertensFactor_pos_prime {p : ℕ} (hp : p.Prime) :
    0 < mertensFactor p := by
  unfold mertensFactor
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  apply sub_pos.mpr
  rw [div_lt_one hp0]
  exact_mod_cast hp.one_lt

lemma mertensFactor_le_one (p : ℕ) : mertensFactor p ≤ 1 := by
  unfold mertensFactor
  have : 0 ≤ (1 : ℝ) / p := by positivity
  linarith

lemma strictMertens_pos (x : ℝ) : 0 < mertensStrictProduct x := by
  unfold mertensStrictProduct
  exact Finset.prod_pos fun p hp =>
    mertensFactor_pos_prime (mem_strictPrimeRange.mp hp).1

lemma intervalMertens_from_two (x : ℝ) :
    primeIntervalProduct mertensFactor 2 x = mertensStrictProduct x := by
  unfold primeIntervalProduct mertensStrictProduct
  apply Finset.prod_congr rfl
  intro p hp
  simp [(mem_strictPrimeRange.mp hp).1.two_le]

lemma intervalMertens_ratio {A B : ℝ} (hA : 2 ≤ A) (hAB : A ≤ B) :
    primeIntervalProduct mertensFactor A B =
      mertensStrictProduct B / mertensStrictProduct A := by
  have h := primeIntervalProduct_div mertensFactor
    (fun p hp => mertensFactor_pos_prime hp)
    (A := (2 : ℝ)) (C := A) (B := B) hA hAB
  simpa only [intervalMertens_from_two] using h

lemma intervalMertens_le_one (A B : ℝ) :
    primeIntervalProduct mertensFactor A B ≤ 1 := by
  unfold primeIntervalProduct
  apply prod_nonnegative_le_one
  · intro p hp
    split_ifs
    · exact (mertensFactor_pos_prime (mem_strictPrimeRange.mp hp).1).le
    · exact zero_le_one
  · intro p hp
    split_ifs
    · exact mertensFactor_le_one p
    · exact le_rfl

structure MertensGlobalBounds where
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  bounds : ∀ A B : ℝ, 2 ≤ A → A < B →
    lower * (Real.log A / Real.log B) ≤
        primeIntervalProduct mertensFactor A B ∧
      primeIntervalProduct mertensFactor A B ≤
        upper * (Real.log A / Real.log B)

@[expose] noncomputable def globalMertensBounds (M : EXT002Output) : MertensGlobalBounds := by
  let sM := mertensStrictProduct M.X_M
  let hminus := min (sM * Real.log 2)
    (min 1 M.c_M_minus * sM * Real.log M.X_M)
  let hplus := max (Real.log M.X_M)
    (max 1 M.c_M_plus * sM * Real.log M.X_M)
  have hsM : 0 < sM := strictMertens_pos M.X_M
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogM : 0 < Real.log M.X_M :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) M.X_M_ge_two)
  have hhminus : 0 < hminus := by
    dsimp [hminus]
    exact lt_min (mul_pos hsM hlog2)
      (mul_pos (mul_pos (lt_min zero_lt_one M.c_M_minus_pos) hsM) hlogM)
  have hhplus : 0 < hplus := lt_of_lt_of_le hlogM (le_max_left _ _)
  have hH : ∀ x : ℝ, 2 ≤ x →
      hminus ≤ mertensStrictProduct x * Real.log x ∧
        mertensStrictProduct x * Real.log x ≤ hplus := by
    intro x hx
    have hlogx : 0 < Real.log x :=
      Real.log_pos (lt_of_lt_of_le (by norm_num) hx)
    by_cases hxM : x ≤ M.X_M
    · have hmul := primeIntervalProduct_mul mertensFactor hx hxM
      rw [intervalMertens_from_two, intervalMertens_from_two] at hmul
      have htail0 := primeIntervalProduct_pos mertensFactor
        (fun p hp => mertensFactor_pos_prime hp) x M.X_M
      have htail1 := intervalMertens_le_one x M.X_M
      have hsx : 0 < mertensStrictProduct x := strictMertens_pos x
      have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
      have hM0 : 0 < M.X_M := lt_of_lt_of_le (by norm_num) M.X_M_ge_two
      have hsMle : sM ≤ mertensStrictProduct x := by
        dsimp [sM]
        rw [hmul]
        nlinarith
      have hsxle : mertensStrictProduct x ≤ 1 := by
        rw [← intervalMertens_from_two]
        exact intervalMertens_le_one 2 x
      have hlogxle : Real.log x ≤ Real.log M.X_M :=
        Real.strictMonoOn_log.monotoneOn hx0 hM0 hxM
      constructor
      · exact (min_le_left _ _).trans
          (mul_le_mul hsMle
            (Real.strictMonoOn_log.monotoneOn (by norm_num) hx0 hx)
            hlog2.le (strictMertens_pos x).le)
      · exact (mul_le_mul hsxle hlogxle hlogx.le zero_le_one).trans
          (by
            dsimp [hplus]
            simpa using (le_max_left (Real.log M.X_M)
              (max 1 M.c_M_plus * sM * Real.log M.X_M)))
    · have hMx : M.X_M < x := lt_of_not_ge hxM
      have hcomp := M.interval_comparison M.X_M x le_rfl hMx
      rw [intervalMertens_ratio M.X_M_ge_two hMx.le] at hcomp
      have hlower : M.c_M_minus * sM * Real.log M.X_M ≤
          mertensStrictProduct x * Real.log x := by
        have h := (le_div_iff₀ hsM).mp hcomp.1
        have h' := mul_le_mul_of_nonneg_right h hlogx.le
        field_simp [ne_of_gt hlogx] at h'
        simpa [sM, mul_assoc, mul_left_comm, mul_comm] using h'
      have hupper : mertensStrictProduct x * Real.log x ≤
          M.c_M_plus * sM * Real.log M.X_M := by
        have h := (div_le_iff₀ hsM).mp hcomp.2
        have h' := mul_le_mul_of_nonneg_right h hlogx.le
        field_simp [ne_of_gt hlogx] at h'
        simpa [sM, mul_assoc, mul_left_comm, mul_comm] using h'
      constructor
      · apply (min_le_right _ _).trans
        calc
          min 1 M.c_M_minus * sM * Real.log M.X_M ≤
              M.c_M_minus * sM * Real.log M.X_M := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (min_le_right _ _) hsM.le) hlogM.le
          _ ≤ _ := hlower
      · apply hupper.trans
        calc
          M.c_M_plus * sM * Real.log M.X_M ≤
              max 1 M.c_M_plus * sM * Real.log M.X_M := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_right _ _) hsM.le) hlogM.le
          _ ≤ hplus := le_max_right _ _
  refine {
    lower := hminus / hplus
    upper := hplus / hminus
    lower_pos := div_pos hhminus hhplus
    upper_pos := div_pos hhplus hhminus
    bounds := ?_
  }
  intro A B hA hAB
  have hB : 2 ≤ B := hA.trans hAB.le
  have hlogA : 0 < Real.log A := Real.log_pos (lt_of_lt_of_le (by norm_num) hA)
  have hlogB : 0 < Real.log B := Real.log_pos (lt_of_lt_of_le (by norm_num) hB)
  have hSA : 0 < mertensStrictProduct A := strictMertens_pos A
  have hSB : 0 < mertensStrictProduct B := strictMertens_pos B
  have hHA := hH A hA
  have hHB := hH B hB
  rw [intervalMertens_ratio hA hAB.le]
  constructor
  · apply (le_div_iff₀ hSA).2
    field_simp [ne_of_gt hhplus, ne_of_gt hlogB]
    have hchain : hminus * Real.log A * mertensStrictProduct A ≤
        mertensStrictProduct B * hplus * Real.log B := by
      calc
        hminus * Real.log A * mertensStrictProduct A =
            hminus * (mertensStrictProduct A * Real.log A) := by ring
        _ ≤ hminus * hplus := mul_le_mul_of_nonneg_left hHA.2 hhminus.le
        _ ≤ (mertensStrictProduct B * Real.log B) * hplus :=
          mul_le_mul_of_nonneg_right hHB.1 hhplus.le
        _ = mertensStrictProduct B * hplus * Real.log B := by ring
    simpa [mul_assoc, mul_left_comm, mul_comm] using hchain
  · apply (div_le_iff₀ hSA).2
    field_simp [ne_of_gt hhminus, ne_of_gt hlogB]
    have hchain : mertensStrictProduct B * hminus * Real.log B ≤
        hplus * Real.log A * mertensStrictProduct A := by
      calc
        mertensStrictProduct B * hminus * Real.log B =
            hminus * (mertensStrictProduct B * Real.log B) := by ring
        _ ≤ hminus * hplus := mul_le_mul_of_nonneg_left hHB.2 hhminus.le
        _ ≤ (mertensStrictProduct A * Real.log A) * hplus :=
          mul_le_mul_of_nonneg_right hHA.1 hhplus.le
        _ = hplus * Real.log A * mertensStrictProduct A := by ring
    simpa [mul_assoc, mul_left_comm, mul_comm] using hchain

lemma rpow_log_ratio {A B c : ℝ} (hA : 1 < A) (hB : 1 < B) :
    (Real.log A / Real.log B).rpow (-c) =
      (Real.log B / Real.log A).rpow c := by
  change (Real.log A / Real.log B) ^ (-c) =
    (Real.log B / Real.log A) ^ c
  have hla : 0 ≤ Real.log A := (Real.log_pos hA).le
  have hlb : 0 ≤ Real.log B := (Real.log_pos hB).le
  rw [Real.div_rpow hla hlb, Real.div_rpow hlb hla]
  rw [Real.rpow_neg hla, Real.rpow_neg hlb]
  simp [div_eq_mul_inv]
  ring

lemma prod_rpow_nonnegative
    (s : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ p ∈ s, 0 ≤ f p) (c : ℝ) :
    (∏ p ∈ s, f p).rpow c = ∏ p ∈ s, (f p).rpow c := by
  induction s using Finset.induction with
  | empty => simp
  | @insert p s hps ih =>
      rw [Finset.prod_insert hps, Finset.prod_insert hps]
      change (f p * ∏ q ∈ s, f q) ^ c =
        f p ^ c * ∏ q ∈ s, f q ^ c
      rw [Real.mul_rpow
        (hf p (mem_insert_self p s))
        (Finset.prod_nonneg fun q hq => hf q (mem_insert_of_mem hq))]
      have ih' := ih (fun q hq => hf q (mem_insert_of_mem hq))
      change (∏ q ∈ s, f q) ^ c = ∏ q ∈ s, f q ^ c at ih'
      rw [ih']

lemma normalized_product_identity
    (L : ℕ → ℝ) (c A B : ℝ) :
    primeIntervalProduct (fun p => L p * (mertensFactor p).rpow c) A B =
      primeIntervalProduct L A B *
        (primeIntervalProduct mertensFactor A B).rpow c := by
  unfold primeIntervalProduct
  rw [prod_rpow_nonnegative (strictPrimeRange B)
    (fun p => if A ≤ (p : ℝ) then mertensFactor p else 1)
    (fun p hp => by
      split_ifs
      · exact (mertensFactor_pos_prime (mem_strictPrimeRange.mp hp).1).le
      · exact zero_le_one) c]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  by_cases hpA : A ≤ (p : ℝ) <;> simp [hpA]

lemma log_one_sub_quadratic'
    {x : ℝ} (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    |Real.log (1 - x) + x| ≤ 2 * x ^ 2 := by
  have hxabs : |x| < 1 := by rw [abs_of_nonneg hx0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hxabs 1
  norm_num at h
  rw [abs_of_nonneg hx0] at h
  have hden : 1 / 2 ≤ 1 - x := by linarith
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  calc
    |Real.log (1 - x) + x| = |x + Real.log (1 - x)| := by rw [add_comm]
    _ ≤ x ^ 2 / (1 - x) := h
    _ ≤ 2 * x ^ 2 := by
      apply (div_le_iff₀ (by linarith : 0 < 1 - x)).2
      nlinarith

lemma factor_exp_bounds {F e : ℝ}
    (hF : 0 < F) (he0 : 0 ≤ e) (hehalf : e ≤ 1 / 2)
    (herr : |F - 1| ≤ e) :
    Real.exp (-2 * e) ≤ F ∧ F ≤ Real.exp (2 * e) := by
  have hdeltaLower : 1 - e ≤ F := by
    have := (abs_le.mp herr).1
    linarith
  have hdeltaUpper : F ≤ 1 + e := by
    have := (abs_le.mp herr).2
    linarith
  constructor
  · have hone : 0 < 1 - e := by linarith
    have hlog : -2 * e ≤ Real.log (1 - e) := by
      have hq := log_one_sub_quadratic' he0 hehalf
      have habs := (abs_le.mp hq).1
      nlinarith [sq_nonneg e]
    calc
      Real.exp (-2 * e) ≤ Real.exp (Real.log (1 - e)) := Real.exp_le_exp.mpr hlog
      _ = 1 - e := Real.exp_log hone
      _ ≤ F := hdeltaLower
  · calc
      F ≤ 1 + e := hdeltaUpper
      _ ≤ Real.exp e := by simpa [add_comm] using Real.add_one_le_exp e
      _ ≤ Real.exp (2 * e) := Real.exp_le_exp.mpr (by linarith)

lemma bounded_rpow_of_interval
    {d D z K c : ℝ} (hd : 0 < d) (hD : 0 < D)
    (hz0 : 0 < z) (hdz : d ≤ z) (hzD : z ≤ D)
    (hK : 0 ≤ K) (hc : |c| ≤ K) :
    Real.exp (-(|Real.log d| + |Real.log D|) * K) ≤ z.rpow c ∧
      z.rpow c ≤ Real.exp ((|Real.log d| + |Real.log D|) * K) := by
  have hlogd : Real.log d ≤ Real.log z :=
    Real.strictMonoOn_log.monotoneOn hd hz0 hdz
  have hlogD : Real.log z ≤ Real.log D :=
    Real.strictMonoOn_log.monotoneOn hz0 hD hzD
  have hlogabs : |Real.log z| ≤ |Real.log d| + |Real.log D| := by
    rw [abs_le]
    constructor
    · calc
        -(|Real.log d| + |Real.log D|) ≤ -|Real.log d| := by
          linarith [abs_nonneg (Real.log D)]
        _ ≤ Real.log d := neg_abs_le _
        _ ≤ Real.log z := hlogd
    · calc
        Real.log z ≤ Real.log D := hlogD
        _ ≤ |Real.log D| := le_abs_self _
        _ ≤ |Real.log d| + |Real.log D| := by
          linarith [abs_nonneg (Real.log d)]
  have hmulabs : |Real.log z * c| ≤
      (|Real.log d| + |Real.log D|) * K := by
    rw [abs_mul]
    exact mul_le_mul hlogabs hc (abs_nonneg c)
      (add_nonneg (abs_nonneg _) (abs_nonneg _))
  change Real.exp (-(|Real.log d| + |Real.log D|) * K) ≤ z ^ c ∧
    z ^ c ≤ Real.exp ((|Real.log d| + |Real.log D|) * K)
  rw [Real.rpow_def_of_pos hz0]
  constructor
  · apply Real.exp_le_exp.mpr
    simpa only [neg_mul] using (abs_le.mp hmulabs).1
  · apply Real.exp_le_exp.mpr
    exact (abs_le.mp hmulabs).2

lemma low_interval_bounds
    (F : ℕ → ℝ) {a b T A B : ℝ}
    (ha0 : 0 < a) (ha1 : a ≤ 1) (hb1 : 1 ≤ b)
    (hF : ∀ p : ℕ, p.Prime → a ≤ F p ∧ F p ≤ b)
    (hBT : B ≤ T) :
    a ^ (strictPrimeRange T).card ≤ primeIntervalProduct F A B ∧
      primeIntervalProduct F A B ≤ b ^ (strictPrimeRange T).card := by
  let s : Finset ℕ := (strictPrimeRange B).filter fun p => A ≤ (p : ℝ)
  have hsT : s ⊆ strictPrimeRange T := by
    intro p hp
    have hp' := mem_filter.mp hp
    exact mem_strictPrimeRange.mpr
      ⟨(mem_strictPrimeRange.mp hp'.1).1,
        (mem_strictPrimeRange.mp hp'.1).2.trans_le hBT⟩
  have hcard := Finset.card_le_card hsT
  have heq : primeIntervalProduct F A B = ∏ p ∈ s, F p := by
    unfold primeIntervalProduct s
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, mul_one]
  rw [heq]
  constructor
  · calc
      a ^ (strictPrimeRange T).card ≤ a ^ s.card :=
        pow_le_pow_of_le_one ha0.le ha1 hcard
      _ = ∏ _p ∈ s, a := by simp
      _ ≤ ∏ p ∈ s, F p := Finset.prod_le_prod₀
        (fun _ _ => ha0.le) (fun p hp => (hF p (mem_strictPrimeRange.mp
          (mem_filter.mp hp).1).1).1)
  · calc
      (∏ p ∈ s, F p) ≤ ∏ _p ∈ s, b := Finset.prod_le_prod₀
        (fun p hp => ha0.le.trans (hF p (mem_strictPrimeRange.mp
          (mem_filter.mp hp).1).1).1)
        (fun p hp => (hF p (mem_strictPrimeRange.mp
          (mem_filter.mp hp).1).1).2)
      _ = b ^ s.card := by simp
      _ ≤ b ^ (strictPrimeRange T).card := pow_le_pow_right₀ hb1 hcard

theorem compactProductComparison
    (M : EXT002Output) (Q : Type*)
    (K eta CErr Perr m U : ℝ)
    (hK : 0 ≤ K) (heta : 0 < eta) (hCErr : 0 < CErr)
    (hPerr : 2 ≤ Perr) (hm : 0 < m) (hmU : m ≤ U)
    (c : Q → ℝ) (hc : ∀ q, |c q| ≤ K)
    (L : Q → ℕ → ℝ)
    (hLU : ∀ q (p : ℕ), p.Prime → m ≤ L q p ∧ L q p ≤ U)
    (herr : ∀ q (p : ℕ), p.Prime → Perr ≤ (p : ℝ) →
      |L q p - (1 + c q / p)| ≤ CErr * (p : ℝ).rpow (-1 - eta)) :
    Nonempty (P008Output c L) := by
  let mu := min eta 1
  let D := CErr * Real.exp K + 20 * (K + 1) ^ 2
  let T := max Perr (max (4 * (K + 1)) (max 2 (2 * D)))
  let eps : ℕ → ℝ := fun n => D * (n : ℝ).rpow (-1 - mu)
  let S := ∑' n : ℕ, eps n
  let a := min 1 (m * Real.exp (-K))
  let b := max 1 (U * Real.exp K)
  let N := (strictPrimeRange T).card
  let gLower := a ^ N * Real.exp (-2 * S)
  let gUpper := b ^ N * Real.exp (2 * S)
  let MB := globalMertensBounds M
  let H := (|Real.log MB.lower| + |Real.log MB.upper|) * K
  let compLower := gLower * Real.exp (-H)
  let compUpper := gUpper * Real.exp H
  have hmu : 0 < mu := lt_min heta zero_lt_one
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hT2 : 2 ≤ T :=
    le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hTP : Perr ≤ T := le_max_left _ _
  have hTK : 4 * (K + 1) ≤ T :=
    le_max_of_le_right (le_max_of_le_left (le_refl _))
  have hTD : 2 * D ≤ T :=
    le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  have heps0 : ∀ n, 0 ≤ eps n := fun n => by
    dsimp [eps]
    positivity
  have hepsSum : Summable eps := by
    dsimp [eps]
    exact ((Real.summable_nat_rpow).2 (by dsimp [mu]; linarith [hmu])).mul_left D
  have hS0 : 0 ≤ S := tsum_nonneg heps0
  have ha0 : 0 < a := lt_min zero_lt_one (mul_pos hm (Real.exp_pos _))
  have ha1 : a ≤ 1 := min_le_left _ _
  have hb1 : 1 ≤ b := le_max_left _ _
  have hnormalized : ∀ q p, p.Prime →
      a ≤ L q p * (mertensFactor p).rpow (c q) ∧
        L q p * (mertensFactor p).rpow (c q) ≤ b := by
    intro q p hp
    have hrUpper := mertensFactor_rpow_upper hK (hc q) hp
    have hrNegUpper := mertensFactor_rpow_upper hK (by simpa using hc q) hp
      (c := -(c q))
    have hmf0 := mertensFactor_pos_prime hp
    have hr0 := Real.rpow_pos_of_pos hmf0 (c q)
    have hrLower : Real.exp (-K) ≤ (mertensFactor p).rpow (c q) := by
      have hinv : ((mertensFactor p).rpow (c q))⁻¹ ≤ Real.exp K := by
        simpa [Real.rpow_neg hmf0.le] using hrNegUpper
      have hone : 1 ≤ Real.exp K * (mertensFactor p).rpow (c q) := by
        exact (div_le_iff₀ hr0).mp (by simpa [one_div] using hinv)
      rw [Real.exp_neg, inv_eq_one_div]
      exact (div_le_iff₀ (Real.exp_pos K)).2 (by simpa [mul_comm] using hone)
    constructor
    · exact (min_le_right _ _).trans
        (mul_le_mul (hLU q p hp).1 hrLower (Real.exp_pos _).le
          (hm.le.trans (hLU q p hp).1))
    · exact (mul_le_mul (hLU q p hp).2 hrUpper hr0.le
        (le_trans hm.le hmU)).trans (le_max_right _ _)
  have hepsHalf : ∀ n : ℕ, T ≤ n → eps n ≤ 1 / 2 := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := one_le_two.trans (hT2.trans hn)
    have hpow : (n : ℝ).rpow (-1 - mu) ≤ (n : ℝ).rpow (-1) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [hmu])
    have hnD : 2 * D ≤ (n : ℝ) := hTD.trans hn
    dsimp [eps]
    calc
      D * (n : ℝ).rpow (-1 - mu) ≤ D * (n : ℝ).rpow (-1) :=
        mul_le_mul_of_nonneg_left hpow hD
      _ = D / (n : ℝ) := by
        change D * (n : ℝ) ^ (-1 : ℝ) = D / (n : ℝ)
        rw [Real.rpow_neg_one]
        ring
      _ ≤ 1 / 2 := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < n)).2
        nlinarith
  have htailPoint : ∀ q (p : ℕ), p.Prime → T ≤ (p : ℝ) →
      Real.exp (-2 * eps p) ≤
          L q p * (mertensFactor p).rpow (c q) ∧
        L q p * (mertensFactor p).rpow (c q) ≤ Real.exp (2 * eps p) := by
    intro q p hp hpT
    have hn := normalizedLocalFactor_bound hK (hc q) heta hCErr.le
      (L q) hp (hTK.trans hpT) (herr q p hp (hTP.trans hpT))
    have hpos := lt_of_lt_of_le ha0 (hnormalized q p hp).1
    exact factor_exp_bounds hpos (heps0 p) (hepsHalf p hpT) (by
      dsimp [eps, D, mu]
      exact hn)
  have htail : ∀ q A B, T ≤ A → A < B →
      Real.exp (-2 * S) ≤
          primeIntervalProduct (fun p => L q p * (mertensFactor p).rpow (c q)) A B ∧
        primeIntervalProduct (fun p => L q p * (mertensFactor p).rpow (c q)) A B ≤
          Real.exp (2 * S) := by
    intro q A B hTA hAB
    let s : Finset ℕ := (strictPrimeRange B).filter fun p => A ≤ (p : ℝ)
    have hsumle : ∑ p ∈ s, eps p ≤ S :=
      hepsSum.sum_le_tsum s (fun p hp => heps0 p)
    have heq : primeIntervalProduct
        (fun p => L q p * (mertensFactor p).rpow (c q)) A B =
        ∏ p ∈ s, L q p * (mertensFactor p).rpow (c q) := by
      unfold primeIntervalProduct s
      rw [Finset.prod_ite]
      simp only [Finset.prod_const_one, mul_one]
    rw [heq]
    constructor
    · calc
        Real.exp (-2 * S) ≤ Real.exp (-2 * ∑ p ∈ s, eps p) :=
          Real.exp_le_exp.mpr (by linarith)
        _ = ∏ p ∈ s, Real.exp (-2 * eps p) := by
          convert Real.exp_sum s (fun p => -2 * eps p) using 1
          simp [Finset.mul_sum]
        _ ≤ ∏ p ∈ s, L q p * (mertensFactor p).rpow (c q) :=
          Finset.prod_le_prod₀
            (fun p hp => (Real.exp_pos _).le)
            (fun p hp => (htailPoint q p
              (mem_strictPrimeRange.mp (mem_filter.mp hp).1).1
              (hTA.trans (mem_filter.mp hp).2)).1)
    · calc
        (∏ p ∈ s, L q p * (mertensFactor p).rpow (c q)) ≤
            ∏ p ∈ s, Real.exp (2 * eps p) :=
          Finset.prod_le_prod₀
            (fun p hp => (lt_of_lt_of_le ha0 (hnormalized q p
              (mem_strictPrimeRange.mp (mem_filter.mp hp).1).1).1).le)
            (fun p hp => (htailPoint q p
              (mem_strictPrimeRange.mp (mem_filter.mp hp).1).1
              (hTA.trans (mem_filter.mp hp).2)).2)
        _ = Real.exp (2 * ∑ p ∈ s, eps p) := by
          symm
          convert Real.exp_sum s (fun p => 2 * eps p) using 1
          simp [Finset.mul_sum]
        _ ≤ Real.exp (2 * S) := Real.exp_le_exp.mpr (by linarith)
  have hnormalizedAll : ∀ q A B, 2 ≤ A → A < B →
      gLower ≤ primeIntervalProduct
          (fun p => L q p * (mertensFactor p).rpow (c q)) A B ∧
        primeIntervalProduct
          (fun p => L q p * (mertensFactor p).rpow (c q)) A B ≤ gUpper := by
    intro q A B hA hAB
    let F := fun p => L q p * (mertensFactor p).rpow (c q)
    have hFpos : ∀ p : ℕ, p.Prime → 0 < F p := by
      intro p hp
      exact lt_of_lt_of_le ha0 (hnormalized q p hp).1
    have hlow : ∀ (X Y : ℝ), Y ≤ T →
        a ^ (strictPrimeRange T).card ≤ primeIntervalProduct F X Y ∧
          primeIntervalProduct F X Y ≤ b ^ (strictPrimeRange T).card := by
      intro X Y hYT
      exact low_interval_bounds (A := X) (B := Y) F ha0 ha1 hb1
        (fun p hp => hnormalized q p hp) hYT
    by_cases hBT : B ≤ T
    · have hbnd := hlow A B hBT
      constructor
      · dsimp [gLower, N]
        exact (mul_le_of_le_one_right (pow_nonneg ha0.le _)
          (Real.exp_le_one_iff.mpr (by linarith))).trans
          (by simpa [F] using hbnd.1)
      · calc
          primeIntervalProduct F A B ≤ b ^ N := by simpa [N] using hbnd.2
          _ ≤ b ^ N * Real.exp (2 * S) :=
            le_mul_of_one_le_right (pow_nonneg (by linarith [hb1]) _)
              (Real.one_le_exp (by positivity))
    · have hTB : T < B := lt_of_not_ge hBT
      by_cases hTA : T ≤ A
      · have hbnd := htail q A B hTA hAB
        constructor
        · dsimp [gLower]
          calc
            a ^ N * Real.exp (-2 * S) ≤ 1 * Real.exp (-2 * S) :=
              mul_le_mul_of_nonneg_right (pow_le_one₀ ha0.le ha1)
                (Real.exp_pos _).le
            _ = Real.exp (-2 * S) := one_mul _
            _ ≤ _ := hbnd.1
        · dsimp [gUpper]
          exact hbnd.2.trans (le_mul_of_one_le_left
            (Real.exp_pos _).le (one_le_pow₀ hb1))
      · have hAT : A < T := lt_of_not_ge hTA
        have hsplit := primeIntervalProduct_mul F hAT.le hTB.le
        have hpref := hlow A T le_rfl
        have hsuff := htail q T B le_rfl hTB
        rw [hsplit]
        constructor
        · dsimp [gLower, N]
          exact mul_le_mul hpref.1 hsuff.1 (Real.exp_pos _).le
            (primeIntervalProduct_pos F hFpos A T).le
        · dsimp [gUpper, N]
          exact mul_le_mul hpref.2 hsuff.2
            (primeIntervalProduct_pos F hFpos T B).le
            (pow_nonneg (by linarith [hb1]) _)
  have hcompLower : 0 < compLower := by
    dsimp [compLower, gLower]
    positivity
  have hcompUpper : 0 < compUpper := by
    dsimp [compUpper, gUpper]
    positivity
  refine ⟨{
    comparison := {
      lower := compLower
      upper := compUpper
      lower_pos := hcompLower
      upper_pos := hcompUpper
    }
    family_bounds := ?_
    empty_branch := ?_
  }⟩
  · intro q A B hA hAB
    have hB : 2 ≤ B := hA.trans hAB.le
    have hlogA := Real.log_pos (lt_of_lt_of_le (by norm_num) hA)
    have hlogB := Real.log_pos (lt_of_lt_of_le (by norm_num) hB)
    have hratio : 0 < Real.log A / Real.log B := div_pos hlogA hlogB
    have hmf := MB.bounds A B hA hAB
    have hmf0 := primeIntervalProduct_pos mertensFactor
      (fun p hp => mertensFactor_pos_prime hp) A B
    let z := primeIntervalProduct mertensFactor A B /
      (Real.log A / Real.log B)
    have hz0 : 0 < z := div_pos hmf0 hratio
    have hzLower : MB.lower ≤ z := by
      apply (le_div_iff₀ hratio).2
      simpa [mul_comm] using hmf.1
    have hzUpper : z ≤ MB.upper := by
      apply (div_le_iff₀ hratio).2
      simpa [mul_comm] using hmf.2
    have hzPow := bounded_rpow_of_interval MB.lower_pos MB.upper_pos hz0
      hzLower hzUpper hK (by simpa using hc q) (c := -(c q))
    change Real.exp (-(|Real.log MB.lower| + |Real.log MB.upper|) * K) ≤
        z ^ (-(c q)) ∧
      z ^ (-(c q)) ≤
        Real.exp ((|Real.log MB.lower| + |Real.log MB.upper|) * K) at hzPow
    have hnorm := hnormalizedAll q A B hA hAB
    have hnormId := normalized_product_identity (L q) (c q) A B
    have hfactor : primeIntervalProduct (L q) A B =
        primeIntervalProduct (fun p => L q p * (mertensFactor p).rpow (c q)) A B *
          z.rpow (-(c q)) * (Real.log B / Real.log A).rpow (c q) := by
      have hzEq : primeIntervalProduct mertensFactor A B =
          z * (Real.log A / Real.log B) := by
        dsimp [z]
        field_simp [ne_of_gt hratio]
      rw [hnormId, hzEq]
      change _ = _ * (z * (Real.log A / Real.log B)) ^ (c q) *
        z ^ (-(c q)) * (Real.log B / Real.log A) ^ (c q)
      rw [Real.mul_rpow hz0.le hratio.le]
      have hratioPow := rpow_log_ratio
        (lt_of_lt_of_le (by norm_num) hA)
        (lt_of_lt_of_le (by norm_num) hB) (c := c q)
      change (Real.log A / Real.log B) ^ (-(c q)) =
        (Real.log B / Real.log A) ^ (c q) at hratioPow
      rw [← hratioPow]
      have hzCancel := Real.rpow_add hz0 (c q) (-(c q))
      have hrCancel := Real.rpow_add hratio (c q) (-(c q))
      rw [add_neg_cancel, Real.rpow_zero] at hzCancel hrCancel
      symm
      calc
        primeIntervalProduct (L q) A B *
              (z ^ (c q) * (Real.log A / Real.log B) ^ (c q)) *
              z ^ (-(c q)) * (Real.log A / Real.log B) ^ (-(c q)) =
            primeIntervalProduct (L q) A B *
              (z ^ (c q) * z ^ (-(c q))) *
              ((Real.log A / Real.log B) ^ (c q) *
                (Real.log A / Real.log B) ^ (-(c q))) := by ring
        _ = primeIntervalProduct (L q) A B * 1 * 1 := by
          rw [← hzCancel, ← hrCancel]
        _ = primeIntervalProduct (L q) A B := by ring
    rw [hfactor]
    have hmain : 0 < (Real.log B / Real.log A).rpow (c q) :=
      Real.rpow_pos_of_pos (div_pos hlogB hlogA) _
    have hnormPos : 0 < primeIntervalProduct
        (fun p => L q p * (mertensFactor p).rpow (c q)) A B := by
      apply primeIntervalProduct_pos
      intro p hp
      exact lt_of_lt_of_le ha0 (hnormalized q p hp).1
    have hzRpowPos : 0 < z ^ (-(c q)) := Real.rpow_pos_of_pos hz0 _
    have hzLowerAligned : Real.exp (-H) ≤ z ^ (-(c q)) := by
      dsimp [H]
      simpa only [neg_mul] using hzPow.1
    have hzUpperAligned : z ^ (-(c q)) ≤ Real.exp H := by
      dsimp [H]
      exact hzPow.2
    constructor
    · dsimp [compLower, H]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hnorm.1 hzLowerAligned (Real.exp_pos _).le hnormPos.le)
        hmain.le
    · dsimp [compUpper, H]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hnorm.2 hzUpperAligned hzRpowPos.le
          (hnormPos.le.trans hnorm.2)) hmain.le
  · intro q A B hA hB hBA
    exact primeIntervalProduct_eq_one_of_le (L q) hBA

lemma p007_global_floor
    {c eta CErr : ℝ} (heta : 0 < eta) (hCErr : 0 < CErr)
    (L : ℕ → ℝ) (hLpos : ∀ p, p.Prime → 0 < L p)
    (herr : ∀ (p : ℕ), p.Prime → 2 ≤ p →
      |L p - (1 + c / p)| ≤ CErr * (p : ℝ).rpow (-1 - eta)) :
    ∃ m U : ℝ, 0 < m ∧ m ≤ U ∧
      ∀ p, p.Prime → m ≤ L p ∧ L p ≤ U := by
  let K := |c|
  let T := max 2 (max (4 * (K + 1)) (4 * CErr))
  let s := strictPrimeRange T
  let low := ∏ p ∈ s, min 1 (L p)
  let m := min (1 / 2) low
  let U := 1 + K / 2 + CErr
  have hlow0 : 0 < low := by
    dsimp [low]
    exact Finset.prod_pos fun p hp =>
      lt_min zero_lt_one (hLpos p (mem_strictPrimeRange.mp hp).1)
  have hm0 : 0 < m := lt_min (by norm_num) hlow0
  have hU : 0 < U := by dsimp [U]; dsimp [K]; positivity
  have hmU : m ≤ U := by
    dsimp [m, U, K]
    calc
      min (1 / 2) low ≤ 1 / 2 := min_le_left _ _
      _ ≤ 1 + |c| / 2 + CErr := by
        nlinarith [abs_nonneg c, hCErr]
  refine ⟨m, U, hm0, hmU, ?_⟩
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (by norm_num) hp2
  have hpow1 : (p : ℝ).rpow (-1 - eta) ≤ 1 := by
    calc
      (p : ℝ).rpow (-1 - eta) ≤ (p : ℝ).rpow 0 :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = 1 := by simp
  have hupper : L p ≤ U := by
    have he := herr p hp hp.two_le
    have hc : c ≤ K := le_abs_self c
    have hab := (abs_le.mp he).2
    dsimp [U]
    dsimp [K]
    have hcp : c / (p : ℝ) ≤ |c| / 2 := by
      apply (div_le_iff₀ hp0).2
      nlinarith [abs_nonneg c]
    nlinarith [mul_le_mul_of_nonneg_left hpow1 hCErr.le]
  constructor
  · by_cases hpT : (p : ℝ) < T
    · have hps : p ∈ s := by
        dsimp [s]
        exact mem_strictPrimeRange.mpr ⟨hp, hpT⟩
      have hrest : ∏ q ∈ s.erase p, min 1 (L q) ≤ 1 :=
        prod_nonnegative_le_one
          (fun q hq => (lt_min zero_lt_one (hLpos q
            (mem_strictPrimeRange.mp (mem_of_mem_erase hq)).1)).le)
          (fun q hq => min_le_left _ _)
      have hfac0 : 0 ≤ min 1 (L p) :=
        (lt_min zero_lt_one (hLpos p hp)).le
      have hlowp : low ≤ L p := by
        dsimp [low]
        rw [← Finset.prod_erase_mul (s := s)
          (f := fun q => min 1 (L q)) hps]
        exact (mul_le_mul_of_nonneg_right hrest hfac0).trans
          (by simpa using min_le_right (1 : ℝ) (L p))
      exact (min_le_right _ _).trans hlowp
    · have hpT' : T ≤ (p : ℝ) := le_of_not_gt hpT
      have hTK : 4 * (K + 1) ≤ T :=
        le_max_of_le_right (le_max_left _ _)
      have hTC : 4 * CErr ≤ T :=
        le_max_of_le_right (le_max_right _ _)
      have hKp : K / (p : ℝ) ≤ 1 / 4 := by
        apply (div_le_iff₀ hp0).2
        nlinarith [abs_nonneg c]
      have hCp : CErr * (p : ℝ).rpow (-1 - eta) ≤ 1 / 4 := by
        have hpow : (p : ℝ).rpow (-1 - eta) ≤ (p : ℝ).rpow (-1) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        change (p : ℝ) ^ ((-1 - eta : ℝ)) ≤
          (p : ℝ) ^ ((-1 : ℝ)) at hpow
        rw [Real.rpow_neg_one] at hpow
        calc
          CErr * (p : ℝ).rpow (-1 - eta) ≤ CErr * ((p : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_left hpow hCErr.le
          _ = CErr / (p : ℝ) := by ring
          _ ≤ 1 / 4 := by
            apply (div_le_iff₀ hp0).2
            nlinarith
      have he := herr p hp hp.two_le
      have hab := (abs_le.mp he).1
      have hc : -K ≤ c := neg_abs_le c
      have hhalf : (1 / 2 : ℝ) ≤ L p := by
        have hcp : -K / (p : ℝ) ≤ c / (p : ℝ) :=
          div_le_div_of_nonneg_right hc hp0.le
        have hneg : -(1 / 4 : ℝ) ≤ -K / (p : ℝ) := by
          simpa only [neg_div] using neg_le_neg hKp
        nlinarith
      exact (min_le_left _ _).trans hhalf
  · exact hupper

theorem p007 (hEXT002 : EXT002Statement) : P007Statement := by
  intro c eta CErr heta hCErr L hLpos herr
  obtain ⟨M⟩ := hEXT002
  obtain ⟨m, U, hm, hmU, hLU⟩ :=
    p007_global_floor heta hCErr L hLpos herr
  let Q := Unit
  let cq : Q → ℝ := fun _ => c
  let Lq : Q → ℕ → ℝ := fun _ => L
  obtain ⟨out⟩ := compactProductComparison M Q |c| eta CErr 2 m U
    (abs_nonneg c) heta hCErr (by norm_num) hm hmU cq
    (fun _ => by simp [cq]) Lq
    (fun _ p hp => hLU p hp)
    (fun _ p hp hp2 => herr p hp (by exact_mod_cast hp2))
  refine ⟨{
    P_err := 2
    comparison := out.comparison
    P_err_ge_two := le_rfl
    interval_bounds := ?_
    empty_branch := ?_
  }⟩
  · intro A B hA hAB
    simpa [cq, Lq] using out.family_bounds () A B hA hAB
  · intro A B hA hB hBA
    simpa [Lq] using out.empty_branch () A B hA hB hBA

theorem p008 (hEXT002 : EXT002Statement) : P008Statement.{0} := by
  intro Q hQ cMinus cPlus hcRange hcMinus eta CErr heta hCErr
    P0 mFin MFin hP0 hmFin hmM c hc L hfloor herr hprefix
  obtain ⟨M⟩ := hEXT002
  let K := max |cMinus| |cPlus|
  let U := max MFin (1 + K / 2 + CErr)
  have hK : 0 ≤ K := le_max_of_le_left (abs_nonneg cMinus)
  have hcK : ∀ q, |c q| ≤ K := by
    intro q
    rcases hc q with ⟨hl, hu⟩
    rw [abs_le]
    constructor
    · calc
        -K ≤ -|cMinus| := neg_le_neg (le_max_left _ _)
        _ ≤ cMinus := neg_abs_le cMinus
        _ ≤ c q := hl
    · calc
        c q ≤ cPlus := hu
        _ ≤ |cPlus| := le_abs_self cPlus
        _ ≤ K := le_max_right _ _
  have hglobal : ∀ q (p : ℕ), p.Prime → mFin ≤ L q p ∧ L q p ≤ U := by
    intro q p hp
    constructor
    · exact hfloor q p hp
    · by_cases hp0 : (p : ℝ) < P0
      · exact (hprefix q p hp hp.two_le hp0).2.trans (le_max_left _ _)
      · have hpP0 : P0 ≤ (p : ℝ) := le_of_not_gt hp0
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
        have hpR0 : (0 : ℝ) < p := by positivity
        have hpow1 : (p : ℝ).rpow (-1 - eta) ≤ 1 := by
          calc
            (p : ℝ).rpow (-1 - eta) ≤ (p : ℝ).rpow 0 :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
            _ = 1 := by simp
        have he := herr q p hp (by exact_mod_cast hpP0)
        have hcqp : c q / (p : ℝ) ≤ K / 2 := by
          apply (div_le_iff₀ hpR0).2
          have hcq : c q ≤ K := (le_abs_self (c q)).trans (hcK q)
          nlinarith
        have hab := (abs_le.mp he).2
        apply (show L q p ≤ 1 + K / 2 + CErr by
          nlinarith [mul_le_mul_of_nonneg_left hpow1 hCErr.le]).trans
        exact le_max_right _ _
  have hmU : mFin ≤ U := hmM.trans (le_max_left _ _)
  exact compactProductComparison M Q K eta CErr P0 mFin U hK heta hCErr
    hP0 hmFin hmU c hcK L hglobal
    (fun q p hp hpP => herr q p hp (by exact_mod_cast hpP))

end

end Erdos448.Stage7.ROOT01

namespace Erdos448.Stage7.ROOT01.Work

open Erdos448.Stage4.Contracts
open Erdos448.Stage6.TaskContracts

theorem result : ROOT01Target := by
  intro hEXT001 hEXT002
  exact {
    p001 := Erdos448.Stage7.ROOT01.p001
    p001A := Erdos448.Stage7.ROOT01.p001A
    p005A := Erdos448.Stage7.ROOT01.p005A hEXT001
    p005 := Erdos448.Stage7.ROOT01.p005 hEXT001
    p007 := Erdos448.Stage7.ROOT01.p007 hEXT002
    p008 := Erdos448.Stage7.ROOT01.p008 hEXT002
  }

end Erdos448.Stage7.ROOT01.Work
