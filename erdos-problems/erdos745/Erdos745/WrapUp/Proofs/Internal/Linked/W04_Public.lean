module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W04_Envelope
public import Erdos745.WrapUp.Proofs.Internal.Linked.W04_Near

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


/-! Consumer-shaped global, compact, and separated-tail conclusions. -/
namespace Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_Public

noncomputable section
open scoped BigOperators

open W04_TUPLES_IndependentEnvelope
open W04_TUPLES_IndependentEntropy
open W04_TUPLES_GlobalSmall
open W04_TUPLES_Compact
open W04_TUPLES_Tails

private theorem rpow_neg_five_halves_le_one {k : ℕ} (hk : 0 < k) :
    Real.rpow (k : ℝ) (-5 / 2) ≤ 1 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  exact Real.rpow_le_one_of_one_le_of_nonpos hk1 (by norm_num)

private theorem entropy_to_separated_exp
    {n K : ℕ} {lam H delta : ℝ}
    (hn : 0 < n) (hKn : K ≤ n)
    (hlam : 0 < lam) (hH : 1 ≤ H) (hlamH : lam ≤ H)
    (hdelta : 0 < delta) (hsep : delta ≤ |lam - 1|) :
    Real.exp ((n : ℝ) * independentEntropy lam ((K : ℝ) / n)) ≤
      Real.exp (-(min (delta ^ 2 / (32 * H)) (1 / 4)) * K) := by
  have hc1 : 0 < delta ^ 2 / (32 * H) := by positivity
  have hc : 0 < min (delta ^ 2 / (32 * H)) (1 / 4) := lt_min hc1 (by norm_num)
  by_cases hK : K = n
  · subst K
    have h := independentEntropy_one_upper hlam
    apply Real.exp_le_exp.mpr
    have hmin : min (delta ^ 2 / (32 * H)) (1 / 4) ≤ 1 / 4 := min_le_right _ _
    have hnR : 0 ≤ (n : ℝ) := by positivity
    have hnR0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    rw [div_self hnR0]
    nlinarith [mul_nonneg (sub_nonneg.mpr hmin) hnR]
  · have hKlt : K < n := lt_of_le_of_ne hKn hK
    have ht0 : 0 ≤ (K : ℝ) / n := by positivity
    have ht : (K : ℝ) / n < 1 := by
      exact (div_lt_one (by positivity)).2 (by exact_mod_cast hKlt)
    have h := independentEntropy_separated hlam hH hlamH hdelta hsep ht0 ht
    apply Real.exp_le_exp.mpr
    have hmin : min (delta ^ 2 / (32 * H)) (1 / 4) ≤
        delta ^ 2 / (32 * H) := min_le_left _ _
    have hnR : 0 < (n : ℝ) := by positivity
    have hK0 : 0 ≤ (K : ℝ) := by positivity
    have hmain : (n : ℝ) * independentEntropy lam ((K : ℝ) / n) ≤
        -(delta ^ 2 / (32 * H)) * K := by
      calc
        _ ≤ (n : ℝ) * (-(delta ^ 2 / (32 * H)) * ((K : ℝ) / n)) :=
          mul_le_mul_of_nonneg_left h hnR.le
        _ = _ := by field_simp
    nlinarith [mul_nonneg (sub_nonneg.mpr hmin) hK0]

theorem separatedExpEnvelopeEventually
    (hF : FiniteEnumerationStatement)
    (lo hi delta : ℝ) (q : ℕ)
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hdelta : 0 < delta) (hq : 0 < q) :
    ∃ D : ℝ, 0 < D ∧ ∃ c : ℝ, 0 < c ∧ ∃ n0 : ℕ,
      ∀ (n M : ℕ), n0 ≤ n → M ≤ capacity n →
        lo ≤ degreeAt n M → degreeAt n M ≤ hi →
        delta ≤ |degreeAt n M - 1| →
        ∀ ks : Fin q → ℕ, (∀ i, 0 < ks i) →
          tupleMoment n M q ks ≤
            D * (n : ℝ) ^ (q + 3) *
              Real.exp (-c * ∑ i, (ks i : ℝ)) := by
  obtain ⟨D, hD, n0, henv⟩ :=
    compactIndependentEntropyEnvelope hF lo hi q hlo hlohi hq
  let H : ℝ := max 1 hi
  let c : ℝ := min (delta ^ 2 / (32 * H)) (1 / 4)
  have hH : 1 ≤ H := le_max_left _ _
  have hhiH : hi ≤ H := le_max_right _ _
  have hc : 0 < c := by
    dsimp [c, H]
    exact lt_min (by positivity) (by norm_num)
  refine ⟨D, hD, c, hc, max 1 n0, ?_⟩
  intro n M hn hM hdeglo hdeghi hsep ks hpos
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) (le_trans (le_max_left _ _) hn)
  have hnenv : n0 ≤ n := le_trans (le_max_right _ _) hn
  let K : ℕ := ∑ i, ks i
  by_cases hKn : K ≤ n
  · have he := henv n M ks hnenv hM hdeglo hdeghi hpos
    have hentropy := entropy_to_separated_exp
      (n := n) (K := K) (lam := degreeAt n M) (H := H) (delta := delta)
      hnpos hKn (lt_of_lt_of_le hlo hdeglo) hH (hdeghi.trans hhiH)
      hdelta hsep
    have hprod : (∏ i, Real.rpow (ks i : ℝ) (-5 / 2)) ≤ 1 := by
      calc
        _ ≤ ∏ _i : Fin q, (1 : ℝ) := by
          apply Finset.prod_le_prod₀
          · intro i hi
            exact (Real.rpow_pos_of_pos (by exact_mod_cast hpos i) _).le
          · intro i hi
            exact rpow_neg_five_halves_le_one (hpos i)
        _ = 1 := by simp
    have hprod0 : 0 ≤ (∏ i, Real.rpow (ks i : ℝ) (-5 / 2)) := by
      apply Finset.prod_nonneg
      intro i hi
      exact (Real.rpow_pos_of_pos (by exact_mod_cast hpos i) _).le
    calc
      tupleMoment n M q ks ≤ D * (n : ℝ) ^ (q + 3) *
          (∏ i, Real.rpow (ks i : ℝ) (-5 / 2)) *
          Real.exp ((n : ℝ) * independentEntropy (degreeAt n M)
            ((∑ i, (ks i : ℝ)) / n)) := he
      _ ≤ D * (n : ℝ) ^ (q + 3) *
          (∏ i, Real.rpow (ks i : ℝ) (-5 / 2)) *
          Real.exp (-c * (K : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (by simpa [c, K] using! hentropy)
          (mul_nonneg (mul_nonneg hD.le (by positivity)) hprod0)
      _ ≤ D * (n : ℝ) ^ (q + 3) * 1 *
          Real.exp (-c * (K : ℝ)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hprod (by positivity)) (Real.exp_nonneg _)
      _ = D * (n : ℝ) ^ (q + 3) *
          Real.exp (-c * ∑ i, (ks i : ℝ)) := by simp [K]
  · have hbad : ¬ ((∀ i, 0 < ks i) ∧ (∑ i, ks i) ≤ n ∧
        (∑ i, ks i) ≤ M + q) := by
      intro hg
      exact hKn (by simpa [K] using! hg.2.1)
    rw [W04_TUPLES_Foundation.tupleMoment_eq_zero_of_guard_failure
      hF n M q ks hM hbad]
    positivity

theorem separatedTailEventually (hF : FiniteEnumerationStatement) :
    ∀ (lo hi delta A : ℝ) (q power : ℕ), 0 < lo → lo ≤ hi → 0 < delta →
      0 < A → 0 < q → ∃ B : ℝ, 0 < B ∧ ∃ n0 : ℕ, ∀ n M : ℕ,
        n0 ≤ n → M ≤ capacity n → lo ≤ degreeAt n M → degreeAt n M ≤ hi →
        delta ≤ |degreeAt n M - 1| →
        tupleTail n M q power B ≤ Real.rpow (n : ℝ) (-A) := by
  intro lo hi delta A q power hlo hlohi hdelta hA hq
  obtain ⟨D, hD, c, hc, n1, henv⟩ :=
    separatedExpEnvelopeEventually hF lo hi delta q hlo hlohi hdelta hq
  let P : ℕ → ℕ → Prop := fun n M =>
    n1 ≤ n ∧ M ≤ capacity n ∧ lo ≤ degreeAt n M ∧
      degreeAt n M ≤ hi ∧ delta ≤ |degreeAt n M - 1|
  obtain ⟨B, hB, n2, htail⟩ := tupleTail_eventually_of_expEnvelope
    q power (q + 3) D c A hD.le hc hA P (by
      intro n M hP ks hpos
      exact henv n M hP.1 hP.2.1 hP.2.2.1 hP.2.2.2.1 hP.2.2.2.2 ks hpos)
  refine ⟨B, hB, max n1 n2, ?_⟩
  intro n M hn hM hdeglo hdeghi hsep
  apply htail n M (le_trans (le_max_right _ _) hn)
  exact ⟨le_trans (le_max_left _ _) hn, hM, hdeglo, hdeghi, hsep⟩

private theorem near_entropy_large
    {n K : ℕ} {lam : ℝ}
    (hn : 0 < n) (hKn : K ≤ n)
    (hlo : (1 : ℝ) / 2 ≤ lam) (hhi : lam ≤ (3 : ℝ) / 2)
    (hlarge : (n : ℝ) / 16 ≤ K) :
    Real.exp ((n : ℝ) * independentEntropy lam ((K : ℝ) / n)) ≤
      Real.exp (-(1 / 393216 : ℝ) * K) := by
  by_cases hK : K = n
  · subst K
    have h := independentEntropy_one_upper (lt_of_lt_of_le (by norm_num) hlo)
    apply Real.exp_le_exp.mpr
    have hnR : 0 ≤ (n : ℝ) := by positivity
    have hnR0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    rw [div_self hnR0]
    nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4 - 1 / 393216) hnR]
  · have hKlt : K < n := lt_of_le_of_ne hKn hK
    have hnR : 0 < (n : ℝ) := by positivity
    have ht : (K : ℝ) / n < 1 :=
      (div_lt_one hnR).2 (by exact_mod_cast hKlt)
    have htLarge : (1 : ℝ) / 16 ≤ (K : ℝ) / n :=
      (le_div_iff₀ hnR).2 (by nlinarith only [hlarge])
    have h := independentEntropy_near_large
      (lam := lam) (t := (K : ℝ) / n) hlo hhi (by positivity) ht htLarge
    apply Real.exp_le_exp.mpr
    calc
      (n : ℝ) * independentEntropy lam ((K : ℝ) / n) ≤
          (n : ℝ) * (-((K : ℝ) / n) / 393216) :=
        mul_le_mul_of_nonneg_left h hnR.le
      _ = -(1 / 393216 : ℝ) * K := by field_simp

set_option maxHeartbeats 1200000 in
theorem globalLargeEventually
    (hF : FiniteEnumerationStatement) (q : ℕ) (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, ∀ (n M : ℕ) (ks : Fin q → ℕ),
      n0 ≤ n → M ≤ capacity n →
      1 / 2 ≤ degreeAt n M → degreeAt n M ≤ 3 / 2 →
      (∀ i, 0 < ks i) → (n : ℝ) / 16 ≤ ∑ i, (ks i : ℝ) →
      tupleGlobalBound n M q ks C (1 / 1572864) := by
  obtain ⟨D, hD, n1, henv⟩ := compactIndependentEntropyEnvelope hF
    (1 / 2) (3 / 2) q (by norm_num) (by norm_num) hq
  let a : ℝ := 1 / 12582912
  obtain ⟨B, hB, n2, habs⟩ := polynomialExp_absorb 3 D a 1 (by dsimp [a]; norm_num)
    (by norm_num)
  let T : ℝ := max 4 (2 * B)
  obtain ⟨n3, hn3⟩ := exists_nat_ge (T ^ 2)
  refine ⟨1, by norm_num, max n1 (max n2 n3), ?_⟩
  intro n M ks hn hM hlo hhi hpos hlarge
  let K : ℕ := ∑ i, ks i
  have hn1 : n1 ≤ n := le_trans (le_max_left _ _) hn
  have hn23 : max n2 n3 ≤ n := le_trans (le_max_right _ _) hn
  have hn2 : n2 ≤ n := le_trans (le_max_left _ _) hn23
  have hn3' : n3 ≤ n := le_trans (le_max_right _ _) hn23
  have hn4 : 4 ≤ n := by
    have hT : 4 ≤ T := le_max_left _ _
    have hTsq : T ^ 2 ≤ (n : ℝ) := le_trans hn3 (by exact_mod_cast hn3')
    have h16 : (16 : ℝ) ≤ T ^ 2 := by nlinarith only [hT]
    have : (4 : ℝ) ≤ n := by linarith only [h16, hTsq]
    exact_mod_cast this
  have hprod0 : 0 ≤ (∏ i, Real.rpow (ks i : ℝ) (-5 / 2)) := by
    apply Finset.prod_nonneg
    intro i hi
    exact (Real.rpow_pos_of_pos (by exact_mod_cast hpos i) _).le
  unfold tupleGlobalBound
  by_cases hKn : K ≤ n
  swap
  · have hnot : ¬ K ≤ n := hKn
    have hbad : ¬ ((∀ i, 0 < ks i) ∧ (∑ i, ks i) ≤ n ∧
        (∑ i, ks i) ≤ M + q) := by
      intro hg
      exact hnot (by simpa [K] using! hg.2.1)
    rw [W04_TUPLES_Foundation.tupleMoment_eq_zero_of_guard_failure hF n M q ks hM hbad]
    positivity
  have he := henv n M ks hn1 hM hlo hhi hpos
  have hent := near_entropy_large (n := n) (K := K) (lam := degreeAt n M)
    (by omega) hKn hlo hhi (by simpa [K] using! hlarge)
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hTsqrt : T ≤ Real.sqrt n := (Real.le_sqrt hT0 (by positivity)).2
    (le_trans hn3 (by exact_mod_cast hn3'))
  have hlog := Real.log_natCast_le_rpow_div n (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [show (n : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt n by rw [Real.sqrt_eq_rpow]] at hlog
  have hBlog : B * Real.log n ≤ n := by
    have h2B : 2 * B ≤ T := le_max_right _ _
    have hsqrt := Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)
    nlinarith [mul_nonneg hB.le (sub_nonneg.mpr hlog),
      mul_nonneg (Real.sqrt_nonneg n) (sub_nonneg.mpr (le_trans h2B hTsqrt))]
  have habs' : D * (n : ℝ) ^ 3 * Real.exp (-a * n) ≤ 1 := by
    calc
      _ ≤ D * (n : ℝ) ^ 3 * Real.exp (-a * (B * Real.log n)) := by
        have ha : 0 ≤ a := by dsimp [a]; norm_num
        have hexp : Real.exp (-a * (n : ℝ)) ≤
            Real.exp (-a * (B * Real.log n)) :=
          Real.exp_le_exp.mpr (by nlinarith [mul_nonneg ha (sub_nonneg.mpr hBlog)])
        exact mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ Real.rpow (n : ℝ) (-(1 : ℝ)) := habs n hn2
      _ ≤ 1 := by
        change (n : ℝ) ^ (-(1 : ℝ)) ≤ 1
        rw [Real.rpow_neg_one]
        exact (inv_le_one₀ (by positivity : (0 : ℝ) < n)).2
          (by exact_mod_cast (show 1 ≤ n by omega))
  have hQ : (degreeAt n M - 1) ^ 2 * (K : ℝ) + (K : ℝ) ^ 3 / (n : ℝ) ^ 2 ≤
      (5 / 4 : ℝ) * K := by
    have hlam : |degreeAt n M - 1| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
    have hsq : (degreeAt n M - 1) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith
    have hKnR : (K : ℝ) ≤ n := by exact_mod_cast hKn
    have hnR : 0 < (n : ℝ) := by positivity
    have hcubic : (K : ℝ) ^ 3 / (n : ℝ) ^ 2 ≤ K := by
      field_simp
      nlinarith [mul_nonneg (show 0 ≤ (K : ℝ) by positivity) (sub_nonneg.mpr hKnR)]
    nlinarith
  have hgap : -(1 / 393216 : ℝ) * K ≤
      -a * n - (1 / 1572864 : ℝ) *
        ((degreeAt n M - 1) ^ 2 * (K : ℝ) + (K : ℝ) ^ 3 / (n : ℝ) ^ 2) := by
    have hlarge' : (n : ℝ) / 16 ≤ K := by simpa [K] using! hlarge
    dsimp [a]
    nlinarith
  have hexpGap : Real.exp (-(1 / 393216 : ℝ) * K) ≤
      Real.exp (-a * n) * Real.exp (-(1 / 1572864 : ℝ) *
        ((degreeAt n M - 1) ^ 2 * (K : ℝ) + (K : ℝ) ^ 3 / (n : ℝ) ^ 2)) := by
    rw [← Real.exp_add]
    convert Real.exp_le_exp.mpr hgap using 1 <;> ring
  calc
    tupleMoment n M q ks ≤ D * (n : ℝ) ^ (q + 3) *
        (∏ i, Real.rpow (ks i : ℝ) (-5 / 2)) *
        Real.exp ((n : ℝ) * independentEntropy (degreeAt n M) ((K : ℝ) / n)) := by
          simpa [K] using! he
    _ ≤ D * (n : ℝ) ^ (q + 3) *
        (∏ i, Real.rpow (ks i : ℝ) (-5 / 2)) *
        Real.exp (-(1 / 393216 : ℝ) * K) := by
          exact mul_le_mul_of_nonneg_left (by simpa [K] using! hent)
            (mul_nonneg (mul_nonneg hD.le (by positivity)) hprod0)
    _ ≤ (n : ℝ) ^ q * (∏ i, Real.rpow (ks i : ℝ) (-5 / 2)) *
        Real.exp (-(1 / 1572864 : ℝ) *
          ((degreeAt n M - 1) ^ 2 * (K : ℝ) + (K : ℝ) ^ 3 / (n : ℝ) ^ 2)) := by
      rw [show (n : ℝ) ^ (q + 3) = (n : ℝ) ^ q * (n : ℝ) ^ 3 by rw [pow_add]]
      let P : ℝ := ∏ i, Real.rpow (ks i : ℝ) (-5 / 2)
      have hprod0 : 0 ≤ P := by
        dsimp [P]
        apply Finset.prod_nonneg
        intro i hi
        exact (Real.rpow_pos_of_pos (by exact_mod_cast hpos i) _).le
      calc
        _ = ((n : ℝ) ^ q * P) *
            (D * (n : ℝ) ^ 3 * Real.exp (-(1 / 393216 : ℝ) * K)) := by ring
        _ ≤ ((n : ℝ) ^ q * P) *
            ((D * (n : ℝ) ^ 3 * Real.exp (-a * n)) *
              Real.exp (-(1 / 1572864 : ℝ) *
                ((degreeAt n M - 1) ^ 2 * (K : ℝ) + (K : ℝ) ^ 3 / (n : ℝ) ^ 2))) := by
          have hbase : 0 ≤ (n : ℝ) ^ q * P := mul_nonneg (by positivity) hprod0
          have hstep := mul_le_mul_of_nonneg_left hexpGap
            (by positivity : 0 ≤ D * (n : ℝ) ^ 3)
          convert mul_le_mul_of_nonneg_left hstep hbase using 1 <;> ring
        _ ≤ ((n : ℝ) ^ q * P) *
            (1 * Real.exp (-(1 / 1572864 : ℝ) *
              ((degreeAt n M - 1) ^ 2 * (K : ℝ) + (K : ℝ) ^ 3 / (n : ℝ) ^ 2))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right habs' (Real.exp_nonneg _))
            (mul_nonneg (by positivity) hprod0)
        _ = _ := by ring
    _ = 1 * (n : ℝ) ^ q * (∏ i, Real.rpow (ks i : ℝ) (-5 / 2)) *
        Real.exp (-(1 / 1572864 : ℝ) *
          ((degreeAt n M - 1) ^ 2 * (∑ i, (ks i : ℝ)) +
            (∑ i, (ks i : ℝ)) ^ 3 / (n : ℝ) ^ 2)) := by simp [K]

theorem globalEventually (hF : FiniteEnumerationStatement) :
    ∀ q : ℕ, 0 < q → ∃ C kappa : ℝ, 0 < C ∧ 0 < kappa ∧
      ∃ n0 : ℕ, ∀ (n M : ℕ) (ks : Fin q → ℕ), n0 ≤ n → M ≤ capacity n →
        1 / 2 ≤ degreeAt n M → degreeAt n M ≤ 3 / 2 → (∀ i, 0 < ks i) →
        tupleGlobalBound n M q ks C kappa ∧
        (((∑ i, (ks i : ℝ)) ≤ (n : ℝ) / 16) → tupleLocalBound n M q ks C) := by
  intro q hq
  obtain ⟨Cs, hCs, ns, hsmall⟩ := globalSmallEventually hF q hq
  obtain ⟨Cl, hCl, nl, hlarge⟩ := globalLargeEventually hF q hq
  obtain ⟨Cnear, hCnear, nn, hnear⟩ := W04_TUPLES_PublicNear.nearLocalEventually hF q hq
  let C : ℝ := max Cs (max Cl Cnear)
  have hC : 0 < C := lt_of_lt_of_le hCs (le_max_left _ _)
  refine ⟨C, (1 / 1572864 : ℝ), hC, by norm_num,
    max ns (max nl nn), ?_⟩
  intro n M ks hn hM hlo hhi hpos
  have hns : ns ≤ n := le_trans (le_max_left _ _) hn
  have hrest : max nl nn ≤ n := le_trans (le_max_right _ _) hn
  have hnl : nl ≤ n := le_trans (le_max_left _ _) hrest
  have hnn : nn ≤ n := le_trans (le_max_right _ _) hrest
  have hP0 : 0 ≤ (∏ i, Real.rpow (ks i : ℝ) (-5 / 2)) := by
    apply Finset.prod_nonneg
    intro i hi
    exact (Real.rpow_pos_of_pos (by exact_mod_cast hpos i) _).le
  have hbase : 0 ≤ (n : ℝ) ^ q *
      (∏ i, Real.rpow (ks i : ℝ) (-5 / 2)) :=
    mul_nonneg (by positivity) hP0
  constructor
  · by_cases hK : (∑ i, (ks i : ℝ)) ≤ (n : ℝ) / 16
    · have hs := hsmall n M ks hns hM hlo hhi hpos hK
      unfold tupleGlobalBound at hs ⊢
      have hCsC : Cs ≤ C := le_max_left _ _
      have hk : (1 / 1572864 : ℝ) ≤ 1 / 64 := by norm_num
      have hE0 : 0 ≤ (degreeAt n M - 1) ^ 2 * (∑ i, (ks i : ℝ)) +
          (∑ i, (ks i : ℝ)) ^ 3 / (n : ℝ) ^ 2 := by positivity
      have hExp : Real.exp (-(1 / 64 : ℝ) *
          ((degreeAt n M - 1) ^ 2 * (∑ i, (ks i : ℝ)) +
            (∑ i, (ks i : ℝ)) ^ 3 / (n : ℝ) ^ 2)) ≤
          Real.exp (-(1 / 1572864 : ℝ) *
          ((degreeAt n M - 1) ^ 2 * (∑ i, (ks i : ℝ)) +
            (∑ i, (ks i : ℝ)) ^ 3 / (n : ℝ) ^ 2)) :=
        Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hk) hE0])
      have hcoef : Cs * (n : ℝ) ^ q *
          (∏ i, Real.rpow (ks i : ℝ) (-5 / 2)) ≤
          C * (n : ℝ) ^ q *
          (∏ i, Real.rpow (ks i : ℝ) (-5 / 2)) := by
        convert mul_le_mul_of_nonneg_right hCsC hbase using 1 <;> ring
      calc
        tupleMoment n M q ks ≤ _ := hs
        _ ≤ C * (n : ℝ) ^ q * (∏ i, Real.rpow (ks i : ℝ) (-5 / 2)) *
            Real.exp (-(1 / 64 : ℝ) *
              ((degreeAt n M - 1) ^ 2 * (∑ i, (ks i : ℝ)) +
                (∑ i, (ks i : ℝ)) ^ 3 / (n : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
        _ ≤ C * (n : ℝ) ^ q * (∏ i, Real.rpow (ks i : ℝ) (-5 / 2)) *
            Real.exp (-(1 / 1572864 : ℝ) *
              ((degreeAt n M - 1) ^ 2 * (∑ i, (ks i : ℝ)) +
                (∑ i, (ks i : ℝ)) ^ 3 / (n : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hExp
            (mul_nonneg (mul_nonneg hC.le (by positivity)) hP0)
    · have hl := hlarge n M ks hnl hM hlo hhi hpos (le_of_not_ge hK)
      unfold tupleGlobalBound at hl ⊢
      have hClC : Cl ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
      have hcoef : Cl * (n : ℝ) ^ q *
          (∏ i, Real.rpow (ks i : ℝ) (-5 / 2)) ≤
          C * (n : ℝ) ^ q *
          (∏ i, Real.rpow (ks i : ℝ) (-5 / 2)) := by
        convert mul_le_mul_of_nonneg_right hClC hbase using 1 <;> ring
      exact le_trans hl (mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _))
  · intro hK
    have hnloc := hnear n M ks hnn hM hlo hhi hpos hK
    unfold tupleLocalBound at hnloc ⊢
    exact ⟨hnloc.1, le_trans hnloc.2 (by
      gcongr
      exact le_trans (le_max_right _ _) (le_max_right _ _))⟩

end

end Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_Public
