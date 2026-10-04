module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-01».Reindex
public import Erdos448.stage7.tasks.«ROOT-01».LocalProducts
public import Mathlib.NumberTheory.EulerProduct.Basic

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT01

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Finset Nat
open scoped BigOperators

noncomputable section

@[expose] def coprimeMeanWeight
    (u v : ArithmeticWeight) (Ksh : PosNat) (n : ℕ) : ℝ :=
  if Nat.Coprime n Ksh.1 then u n * v n else 0

@[expose] def coprimeHarmonicWeight
    (u v : ArithmeticWeight) (Ksh : PosNat) (n : ℕ) : ℝ :=
  coprimeMeanWeight u v Ksh n / (n : ℝ)

lemma one_le_real_finset_prod
    {s : Finset ℕ} {F : ℕ → ℝ} (hF : ∀ i ∈ s, 1 ≤ F i) :
    1 ≤ ∏ i ∈ s, F i := by
  induction s using Finset.induction with
  | empty => simp
  | @insert i s his ih =>
      rw [Finset.prod_insert his]
      have hi := hF i (Finset.mem_insert_self i s)
      have hs := ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))
      nlinarith [mul_nonneg (by linarith : 0 ≤ F i) (by linarith : 0 ≤ ∏ j ∈ s, F j)]

lemma coprimeMeanWeight_nonnegative
    (u v : ArithmeticWeight) (hu : NonnegativeMultiplicativeWeight u)
    (hv : NonnegativeMultiplicativeWeight v) (Ksh : PosNat) :
    ∀ n : ℕ, 0 < n → 0 ≤ coprimeMeanWeight u v Ksh n := by
  intro n hn
  unfold coprimeMeanWeight
  split_ifs
  · exact mul_nonneg (hu.nonnegative n hn) (hv.nonnegative n hn)
  · exact le_rfl

lemma coprimeMeanWeight_one
    (u v : ArithmeticWeight) (hu : NonnegativeMultiplicativeWeight u)
    (hv : NonnegativeMultiplicativeWeight v) (Ksh : PosNat) :
    coprimeMeanWeight u v Ksh 1 = 1 := by
  simp [coprimeMeanWeight, hu.multiplicative.1, hv.multiplicative.1]

lemma coprimeMeanWeight_mul
    (u v : ArithmeticWeight) (hu : NonnegativeMultiplicativeWeight u)
    (hv : NonnegativeMultiplicativeWeight v) (Ksh : PosNat)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    coprimeMeanWeight u v Ksh (a * b) =
      coprimeMeanWeight u v Ksh a * coprimeMeanWeight u v Ksh b := by
  have hcop : Nat.Coprime (a * b) Ksh.1 ↔
      Nat.Coprime a Ksh.1 ∧ Nat.Coprime b Ksh.1 := Nat.coprime_mul_iff_left
  unfold coprimeMeanWeight
  by_cases haK : Nat.Coprime a Ksh.1
  · by_cases hbK : Nat.Coprime b Ksh.1
    · rw [if_pos (hcop.mpr ⟨haK, hbK⟩), if_pos haK, if_pos hbK,
        hu.multiplicative.2 a b ha hb hab,
        hv.multiplicative.2 a b ha hb hab]
      ring
    · rw [if_neg (fun h => hbK (hcop.mp h).2), if_pos haK, if_neg hbK]
      ring
  · rw [if_neg (fun h => haK (hcop.mp h).1), if_neg haK]
    ring

lemma coprimeMeanWeight_multiplicative
    (u v : ArithmeticWeight) (hu : NonnegativeMultiplicativeWeight u)
    (hv : NonnegativeMultiplicativeWeight v) (Ksh : PosNat) :
    NonnegativeMultiplicativeWeight (coprimeMeanWeight u v Ksh) :=
  ⟨coprimeMeanWeight_nonnegative u v hu hv Ksh,
    coprimeMeanWeight_one u v hu hv Ksh,
    fun a b ha hb hab => coprimeMeanWeight_mul u v hu hv Ksh ha hb hab⟩

lemma localEulerSeries_nonnegative
    (u v : ArithmeticWeight) (hu : NonnegativeMultiplicativeWeight u)
    (hv : NonnegativeMultiplicativeWeight v)
    (p : ℕ) (hp : p.Prime) : 0 ≤ localEulerSeries u v p := by
  unfold localEulerSeries
  exact tsum_nonneg fun j => div_nonneg
    (mul_nonneg (hu.nonnegative _ (pow_pos hp.pos j))
      (hv.nonnegative _ (pow_pos hp.pos j)))
    (pow_nonneg (Nat.cast_nonneg p) j)

lemma one_le_localEulerSeries_of_summable
    (u v : ArithmeticWeight) (hu : NonnegativeMultiplicativeWeight u)
    (hv : NonnegativeMultiplicativeWeight v)
    (p : ℕ) (hp : p.Prime)
    (hpSum : Summable (fun j : ℕ =>
      u (p ^ j) * v (p ^ j) / (p : ℝ) ^ j)) :
    1 ≤ localEulerSeries u v p := by
  let f : ℕ → ℝ := fun j => u (p ^ j) * v (p ^ j) / (p : ℝ) ^ j
  have hf := hpSum
  have hfNonneg : ∀ j, 0 ≤ f j := fun j => div_nonneg
    (mul_nonneg (hu.nonnegative _ (pow_pos hp.pos j))
      (hv.nonnegative _ (pow_pos hp.pos j)))
    (pow_nonneg (Nat.cast_nonneg p) j)
  have hsingle := hf.sum_le_tsum {0} (fun j _ => hfNonneg j)
  simpa [f, localEulerSeries, hu.multiplicative.1, hv.multiplicative.1] using hsingle

lemma meanEulerSeries_coprime
    (u v : ArithmeticWeight) (hu : NonnegativeMultiplicativeWeight u)
    (hv : NonnegativeMultiplicativeWeight v)
    (hsum : ∀ p : ℕ, p.Prime →
      Summable (fun j : ℕ => u (p ^ j) * v (p ^ j) / (p : ℝ) ^ j))
    (Ksh : PosNat) (p : ℕ) (hp : p.Prime) :
    meanEulerSeries (coprimeMeanWeight u v Ksh) p =
      if p ∣ Ksh.1 then 1 else localEulerSeries u v p := by
  by_cases hpK : p ∣ Ksh.1
  · rw [if_pos hpK]
    unfold meanEulerSeries
    rw [tsum_eq_single 0]
    · simp [coprimeMeanWeight, hu.multiplicative.1, hv.multiplicative.1]
    · intro j hj
      have hjPos : 0 < j := Nat.pos_of_ne_zero hj
      have hpPow : p ∣ p ^ j := dvd_pow_self p hj
      have hnot : ¬Nat.Coprime (p ^ j) Ksh.1 := by
        intro hcop
        have hpOne : p ∣ 1 := by
          rw [← hcop.gcd_eq_one]
          exact Nat.dvd_gcd (dvd_trans (dvd_pow_self p hj) dvd_rfl) hpK
        exact hp.not_dvd_one hpOne
      simp [coprimeMeanWeight, hnot]
  · rw [if_neg hpK]
    unfold meanEulerSeries localEulerSeries
    apply tsum_congr
    intro j
    have hcop : Nat.Coprime (p ^ j) Ksh.1 :=
      (hp.coprime_iff_not_dvd.mpr hpK).pow_left j
    simp only [coprimeMeanWeight, if_pos hcop]

lemma strictEulerProduct_coprime
    (u v : ArithmeticWeight) (hu : NonnegativeMultiplicativeWeight u)
    (hv : NonnegativeMultiplicativeWeight v)
    (hsum : ∀ p : ℕ, p.Prime →
      Summable (fun j : ℕ => u (p ^ j) * v (p ^ j) / (p : ℝ) ^ j))
    (Ksh : PosNat) (X : ℝ) :
    strictEulerProduct (coprimeMeanWeight u v Ksh) X =
      localEulerProductAway u v Ksh X := by
  unfold strictEulerProduct localEulerProductAway
  apply Finset.prod_congr rfl
  intro p hpX
  rw [meanEulerSeries_coprime u v hu hv hsum Ksh p
    (mem_strictPrimeRange.mp hpX).1]

lemma localEulerProductAway_mono
    (u v : ArithmeticWeight) (hu : NonnegativeMultiplicativeWeight u)
    (hv : NonnegativeMultiplicativeWeight v)
    (hsum : ∀ p : ℕ, p.Prime →
      Summable (fun j : ℕ => u (p ^ j) * v (p ^ j) / (p : ℝ) ^ j))
    (Ksh : PosNat) {X x : ℝ} (hXx : X ≤ x) :
    localEulerProductAway u v Ksh X ≤ localEulerProductAway u v Ksh x := by
  unfold localEulerProductAway
  have hsub : strictPrimeRange X ⊆ strictPrimeRange x := by
    intro p hp
    exact mem_strictPrimeRange.mpr
      ⟨(mem_strictPrimeRange.mp hp).1, (mem_strictPrimeRange.mp hp).2.trans_le hXx⟩
  let F : ℕ → ℝ := fun p => if p ∣ Ksh.1 then 1 else localEulerSeries u v p
  have hbase : 0 ≤ ∏ p ∈ strictPrimeRange X, F p :=
    Finset.prod_nonneg fun p hp => by
      dsimp [F]
      split_ifs
      · exact zero_le_one
      · exact localEulerSeries_nonnegative u v hu hv p
          (mem_strictPrimeRange.mp hp).1
  have hextra : 1 ≤ ∏ p ∈ strictPrimeRange x \ strictPrimeRange X, F p := by
    apply one_le_real_finset_prod
    intro p hp
    dsimp [F]
    split_ifs
    · exact le_rfl
    · exact one_le_localEulerSeries_of_summable u v hu hv p
        (mem_strictPrimeRange.mp (Finset.mem_sdiff.mp hp).1).1
        (hsum p (mem_strictPrimeRange.mp (Finset.mem_sdiff.mp hp).1).1)
  change (∏ p ∈ strictPrimeRange X, F p) ≤ ∏ p ∈ strictPrimeRange x, F p
  calc
    (∏ p ∈ strictPrimeRange X, F p) ≤
        (∏ p ∈ strictPrimeRange x \ strictPrimeRange X, F p) *
          ∏ p ∈ strictPrimeRange X, F p := le_mul_of_one_le_left hbase hextra
    _ = ∏ p ∈ strictPrimeRange x, F p := Finset.prod_sdiff hsub

lemma harmonicWeight_nonnegative
    (u v : ArithmeticWeight) (hu : NonnegativeMultiplicativeWeight u)
    (hv : NonnegativeMultiplicativeWeight v) (Ksh : PosNat) :
    ∀ n : ℕ, 0 < n → 0 ≤ coprimeHarmonicWeight u v Ksh n := by
  intro n hn
  exact div_nonneg (coprimeMeanWeight_nonnegative u v hu hv Ksh n hn)
    (Nat.cast_nonneg n)

lemma harmonicEulerDomination
    (u v : ArithmeticWeight) (hu : NonnegativeMultiplicativeWeight u)
    (hv : NonnegativeMultiplicativeWeight v)
    (hsum : ∀ p : ℕ, p.Prime →
      Summable (fun j : ℕ => u (p ^ j) * v (p ^ j) / (p : ℝ) ^ j))
    (Ksh : PosNat) {x : ℝ} (hx : 0 < x) :
    (∑ n ∈ positiveNatsBelow x, coprimeHarmonicWeight u v Ksh n) ≤
      localEulerProductAway u v Ksh x := by
  let f := coprimeHarmonicWeight u v Ksh
  have hfOne : f 1 = 1 := by
    simp [f, coprimeHarmonicWeight,
      coprimeMeanWeight_one u v hu hv Ksh]
  have hfMul : ∀ {a b : ℕ}, Nat.Coprime a b → f (a * b) = f a * f b := by
    intro a b hab
    rcases eq_or_ne a 0 with rfl | ha
    · simp [f, coprimeHarmonicWeight, coprimeMeanWeight]
    rcases eq_or_ne b 0 with rfl | hb
    · simp [f, coprimeHarmonicWeight, coprimeMeanWeight]
    unfold f coprimeHarmonicWeight
    rw [coprimeMeanWeight_mul u v hu hv Ksh (Nat.pos_of_ne_zero ha)
      (Nat.pos_of_ne_zero hb) hab]
    push_cast
    field_simp
  have hlocalNorm : ∀ {p : ℕ}, p.Prime →
      Summable (fun j : ℕ => ‖f (p ^ j)‖) := by
    intro p hp
    have hlocal : Summable (fun j : ℕ => f (p ^ j)) := by
      by_cases hpK : p ∣ Ksh.1
      · have hzero : ∀ j ≠ 0, f (p ^ j) = 0 := by
          intro j hj
          have hnot : ¬Nat.Coprime (p ^ j) Ksh.1 := by
            intro hcop
            have hpOne : p ∣ 1 := by
              rw [← hcop.gcd_eq_one]
              exact Nat.dvd_gcd (dvd_pow_self p hj) hpK
            exact hp.not_dvd_one hpOne
          simp [f, coprimeHarmonicWeight, coprimeMeanWeight, hnot]
        exact summable_of_ne_finset_zero (s := {0}) (fun j hj =>
          hzero j (by simpa using hj))
      · have hcop : ∀ j : ℕ, Nat.Coprime (p ^ j) Ksh.1 := fun j =>
          (hp.coprime_iff_not_dvd.mpr hpK).pow_left j
        convert hsum p hp using 1
        funext j
        simp only [f, coprimeHarmonicWeight, coprimeMeanWeight,
          if_pos (hcop j), Nat.cast_pow]
    apply hlocal.congr
    intro j
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact harmonicWeight_nonnegative u v hu hv Ksh _ (pow_pos hp.pos j)
  let S := strictPrimeRange x
  have hexpand :=
    EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
      hfOne hfMul hlocalNorm S
  have hproduct :
      (∏ p ∈ S with p.Prime, ∑' j : ℕ, f (p ^ j)) =
        localEulerProductAway u v Ksh x := by
    rw [← strictEulerProduct_coprime u v hu hv hsum Ksh x]
    unfold strictEulerProduct meanEulerSeries S f coprimeHarmonicWeight
    apply Finset.prod_congr
    · rw [Finset.filter_eq_self.2]
      intro p hpS
      exact (mem_strictPrimeRange.mp hpS).1
    · intro p hpS
      apply tsum_congr
      intro j
      simp [Nat.cast_pow]
  have hfinite :
      (∑ n ∈ positiveNatsBelow x, f n) ≤
        ∑' n : factoredNumbers S, f n := by
    let e : (positiveNatsBelow x : Set ℕ) ↪ factoredNumbers S :=
      { toFun := fun n => ⟨n.1, by
          have hn := mem_positiveNatsBelow.mp n.2
          apply mem_factoredNumbers_of_primeFactors_subset (Nat.ne_of_gt hn.1)
          intro p hpN
          apply mem_strictPrimeRange.mpr
          refine ⟨Nat.prime_of_mem_primeFactors hpN, ?_⟩
          have hpn : p ≤ n.1 := Nat.le_of_dvd hn.1
            (Nat.dvd_of_mem_primeFactors hpN)
          exact (Nat.cast_le.mpr hpn).trans_lt hn.2⟩
        inj' := fun a b h => by
          apply Subtype.ext
          exact congrArg (fun z : factoredNumbers S => z.1) h }
    calc
      (∑ n ∈ positiveNatsBelow x, f n) =
          ∑ n ∈ (positiveNatsBelow x).attach.map e, f n.1 := by
        rw [Finset.sum_map]
        simpa [e] using (Finset.sum_attach (positiveNatsBelow x) f).symm
      _ ≤ ∑' n : factoredNumbers S, f n := by
        exact hexpand.1.of_norm.sum_le_tsum _
          (fun n _ => harmonicWeight_nonnegative u v hu hv Ksh n.1
            (Nat.pos_of_ne_zero n.2.1))
  calc
    (∑ n ∈ positiveNatsBelow x, coprimeHarmonicWeight u v Ksh n) =
        ∑ n ∈ positiveNatsBelow x, f n := rfl
    _ ≤ ∑' n : factoredNumbers S, f n := hfinite
    _ = ∏ p ∈ S with p.Prime, ∑' j : ℕ, f (p ^ j) := hexpand.2.tsum_eq
    _ = localEulerProductAway u v Ksh x := hproduct

lemma one_add_sum_le_prod_one_add
    {s : Finset ℕ} (a : ℕ → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    1 + ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 + a i) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert i s his ih =>
      rw [Finset.sum_insert his, Finset.prod_insert his]
      have hi := ha i (Finset.mem_insert_self i s)
      have hs : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg fun j hj =>
        ha j (Finset.mem_insert_of_mem hj)
      have hih := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      nlinarith [mul_nonneg hi hs]

theorem p004 : P004Statement := by
  intro d
  have hlog : Real.log d.1 =
      ∑ p ∈ d.1.primeFactors, (d.1.factorization p : ℝ) * Real.log p := by
    rw [Real.log_nat_eq_sum_factorization]
    rfl
  rw [hlog, logarithmicPrimeFactorProduct]
  apply one_add_sum_le_prod_one_add
  intro p hp
  exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)

theorem p003 : P003Statement := by
  intro u v hu hv hsum Ksh d x hx hdSupport
  have hxPos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hdR : (0 : ℝ) < d.1 := by exact_mod_cast d.2
  have hfactor : 0 ≤ x / d.1 := (div_pos hxPos hdR).le
  have hinner : coprimeInnerSum u v Ksh (x / d.1) ≤
      (x / d.1) * ∑ m ∈ positiveNatsBelow x,
        coprimeHarmonicWeight u v Ksh m := by
    unfold coprimeInnerSum
    calc
      (∑ m ∈ positiveNatsBelow (x / d.1),
          if Nat.Coprime m Ksh.1 then u m * v m else 0) ≤
          ∑ m ∈ positiveNatsBelow (x / d.1),
            (x / d.1) * coprimeHarmonicWeight u v Ksh m := by
        apply Finset.sum_le_sum
        intro m hm
        have hm' := mem_positiveNatsBelow.mp hm
        by_cases hmK : Nat.Coprime m Ksh.1
        · rw [if_pos hmK]
          have huv : 0 ≤ u m * v m :=
            mul_nonneg (hu.nonnegative m hm'.1) (hv.nonnegative m hm'.1)
          unfold coprimeHarmonicWeight coprimeMeanWeight
          rw [if_pos hmK]
          have hmR : (0 : ℝ) < m := by exact_mod_cast hm'.1
          calc
            u m * v m = (m : ℝ) * (u m * v m / (m : ℝ)) := by
              field_simp [ne_of_gt hmR]
            _ ≤ (x / d.1) * (u m * v m / (m : ℝ)) :=
              mul_le_mul_of_nonneg_right hm'.2.le (div_nonneg huv hmR.le)
        · rw [if_neg hmK]
          exact mul_nonneg hfactor
            (harmonicWeight_nonnegative u v hu hv Ksh m hm'.1)
      _ = (x / d.1) * ∑ m ∈ positiveNatsBelow (x / d.1),
          coprimeHarmonicWeight u v Ksh m := by rw [Finset.mul_sum]
      _ ≤ (x / d.1) * ∑ m ∈ positiveNatsBelow x,
          coprimeHarmonicWeight u v Ksh m := by
        apply mul_le_mul_of_nonneg_left _ hfactor
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (fun m hm => inner_mem_global hxPos.le d.2 hm)
          (fun m hmX hmNot => harmonicWeight_nonnegative u v hu hv Ksh m
            (mem_positiveNatsBelow.mp hmX).1)
  have hEuler := harmonicEulerDomination u v hu hv hsum Ksh hxPos
  have hlogd : 0 ≤ Real.log d.1 := Real.log_natCast_nonneg d.1
  unfold secondLogComponent
  calc
    coprimeInnerSum u v Ksh (x / d.1) * Real.log d.1 ≤
        ((x / d.1) * ∑ m ∈ positiveNatsBelow x,
          coprimeHarmonicWeight u v Ksh m) * Real.log d.1 :=
      mul_le_mul_of_nonneg_right hinner hlogd
    _ ≤ ((x / d.1) * localEulerProductAway u v Ksh x) * Real.log d.1 := by
      gcongr
    _ = (x / d.1) * Real.log d.1 * localEulerProductAway u v Ksh x := by ring

theorem p002 (hEXT001 : EXT001Statement) : P002Statement := by
  intro lambda0 lambda hlambda0 hlambda hlt
  obtain ⟨provider⟩ := hEXT001 lambda0 lambda ⟨hlambda0, hlambda, hlt⟩
  let C := max provider.constant 1
  refine ⟨{
    constant := C
    constant_pos := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    local_series_summable := ?_
    bound := ?_
  }⟩
  · intro u v lambdaSeq hzero hbounds p hp
    let h : ArithmeticWeight := fun n => u n * v n
    have hgeom : PrimePowerGeometricBound h lambda0 lambda := by
      intro q hq j
      simpa [h, ← hzero, zero_add] using hbounds q hq 0 j
    simpa [h] using provider.local_series_summable h hgeom p hp
  · intro u v hu hv lambdaSeq hlambdaSeq hzero hbounds Ksh d x hx hdSupport
    have hsum : ∀ p : ℕ, p.Prime →
        Summable (fun j : ℕ => u (p ^ j) * v (p ^ j) / (p : ℝ) ^ j) := by
      intro p hp
      exact provider.local_series_summable (fun n => u n * v n) (by
        intro q hq j
        simpa [← hzero, zero_add] using hbounds q hq 0 j) p hp
    let h := coprimeMeanWeight u v Ksh
    have hgeom : PrimePowerGeometricBound h lambda0 lambda := by
      intro p hp j
      have hb := hbounds p hp 0 j
      unfold h coprimeMeanWeight
      split_ifs
      · simpa [← hzero, zero_add] using hb
      · exact ⟨le_rfl, mul_nonneg hlambda0 (pow_nonneg hlambda j)⟩
    have hnonneg := coprimeMeanWeight_multiplicative u v hu hv Ksh
    let Y : ℝ := x / d.1
    have hYPos : 0 < Y := div_pos (lt_of_lt_of_le (by norm_num) hx)
      (by exact_mod_cast d.2)
    by_cases hY : 2 ≤ Y
    · have hbound := provider.bound h hnonneg hgeom Y hY
      have hlog : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
      have hmean : strictMean h Y * Real.log Y ≤
          provider.constant * Y * strictEulerProduct h Y := by
        have := mul_le_mul_of_nonneg_right hbound hlog
        have hlogPos : 0 < Real.log Y :=
          Real.log_pos (lt_of_lt_of_le (by norm_num) hY)
        calc
          strictMean h Y * Real.log Y ≤
              (provider.constant * (Y / Real.log Y) * strictEulerProduct h Y) *
                Real.log Y := this
          _ = provider.constant * Y * strictEulerProduct h Y := by
            field_simp [ne_of_gt hlogPos]
      have hEulerMono := localEulerProductAway_mono u v hu hv hsum Ksh
        (show Y ≤ x by
          dsimp [Y]
          exact div_le_self (le_trans (by norm_num) hx) (by exact_mod_cast d.2))
      unfold firstLogComponent coprimeInnerSum
      change strictMean h Y * Real.log Y ≤ C * Y * localEulerProductAway u v Ksh x
      rw [strictEulerProduct_coprime u v hu hv hsum Ksh Y] at hmean
      calc
        strictMean h Y * Real.log Y ≤
            provider.constant * Y * localEulerProductAway u v Ksh Y := hmean
        _ ≤ C * Y * localEulerProductAway u v Ksh x := by
          have hC : provider.constant ≤ C := le_max_left _ _
          have hY0 : 0 ≤ Y := hYPos.le
          have hProd0 : 0 ≤ localEulerProductAway u v Ksh Y := by
            unfold localEulerProductAway
            exact Finset.prod_nonneg fun p hpS => by
              split_ifs
              · exact zero_le_one
              · exact localEulerSeries_nonnegative u v hu hv p
                  (mem_strictPrimeRange.mp hpS).1
          have hProdX0 : 0 ≤ localEulerProductAway u v Ksh x := by
            exact hProd0.trans hEulerMono
          nlinarith [mul_le_mul_of_nonneg_left hEulerMono
            (mul_nonneg (provider.constant_pos.le) hY0),
            mul_le_mul_of_nonneg_right hC (mul_nonneg hY0 hProdX0)]
    · have hYlt : Y < 2 := lt_of_not_ge hY
      have hsmall : firstLogComponent u v Ksh d x ≤
          Y * localEulerProductAway u v Ksh x := by
        have h001B : P001BStatement := by
          intro u' v' hu' hv' K' d' x' Y' hx' hYeq hYpos hYlt' hs'
          unfold firstLogComponent coprimeInnerSum
          rw [← hYeq]
          by_cases hY1 : Y' ≤ 1
          · rw [positiveNatsBelow_eq_empty_of_le_one hY1]
            simp only [Finset.sum_empty, zero_mul]
            have hProd0 : 0 ≤ localEulerProductAway u' v' K' x' := by
              unfold localEulerProductAway
              exact Finset.prod_nonneg fun p hpP => by
                split_ifs
                · exact zero_le_one
                · exact localEulerSeries_nonnegative u' v' hu' hv' p
                    (mem_strictPrimeRange.mp hpP).1
            exact mul_nonneg hYpos.le hProd0
          · have h1Y : 1 < Y' := lt_of_not_ge hY1
            rw [positiveNatsBelow_eq_singleton_one h1Y hYlt']
            simp [hu'.multiplicative.1, hv'.multiplicative.1]
            have hlogY : Real.log Y' ≤ Y' :=
              (Real.log_le_sub_one_of_pos hYpos).trans (by linarith)
            have hprod : 1 ≤ localEulerProductAway u' v' K' x' := by
              unfold localEulerProductAway
              exact one_le_real_finset_prod (fun p hpP => by
                split_ifs
                · exact le_rfl
                · exact one_le_localEulerSeries_of_summable u' v' hu' hv' p
                    (mem_strictPrimeRange.mp hpP).1
                    (hs' p (mem_strictPrimeRange.mp hpP).1
                      (mem_strictPrimeRange.mp hpP).2))
            nlinarith [mul_le_mul_of_nonneg_left hprod hYpos.le]
        exact h001B u v hu hv Ksh d x Y hx rfl hYPos hYlt
          (fun p hp hpx => hsum p hp)
      have hC : 1 ≤ C := le_max_right _ _
      have hE0 : 0 ≤ localEulerProductAway u v Ksh x := by
        unfold localEulerProductAway
        exact Finset.prod_nonneg fun p hpS => by
          split_ifs
          · exact zero_le_one
          · exact localEulerSeries_nonnegative u v hu hv p
              (mem_strictPrimeRange.mp hpS).1
      calc
        firstLogComponent u v Ksh d x ≤ Y * localEulerProductAway u v Ksh x := hsmall
        _ ≤ C * (Y * localEulerProductAway u v Ksh x) :=
          le_mul_of_one_le_left (mul_nonneg hYPos.le hE0) hC
        _ = C * (x / d.1) * localEulerProductAway u v Ksh x := by
          dsimp [Y]
          ring

end

end Erdos448.Stage7.ROOT01
