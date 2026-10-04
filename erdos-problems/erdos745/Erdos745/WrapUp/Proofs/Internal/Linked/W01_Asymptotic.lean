module

public import Erdos745.WrapUp.Contracts
public import Mathlib

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


namespace Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Asymptotic

open Filter Topology

/-! The last four conjuncts of `FiniteEnumerationStatement`.  The exact
unicyclic enumeration is supplied by the sibling tree/enumeration development;
this file proves the canonical rank endpoint and owns the analytic consequences
of that exact formula. -/

def UnicyclicFormula : Prop :=
  ∀ k : ℕ, 3 ≤ k → (connectedCount k k : ℝ) =
    ((k - 1).factorial : ℝ) / 2 *
      (Finset.range (k - 2)).sum (fun m =>
        (k : ℝ) ^ m / (m.factorial : ℝ))

def RankEquivalence : Prop :=
  ∀ (n : ℕ) (G : Graph n) (i h : ℕ), 0 < i → 0 < h →
    (rankSize G i < h ↔ countGE G h ≤ i - 1)

def UniformUnicyclicBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 3 ≤ k →
    (connectedCount k k : ℝ) ≤
      C * Real.rpow (k : ℝ) ((k : ℝ) - 1 / 2)

def UnicyclicLimit : Prop :=
  Tendsto (fun k : ℕ => (connectedCount k k : ℝ) /
    Real.rpow (k : ℝ) ((k : ℝ) - 1 / 2)) atTop
      (𝓝 (Real.sqrt (Real.pi / 8)))

/- The purely analytic finite-Poisson/Stirling statement left after the exact
cycle/forest bijection has removed all graph structure. -/
def AnalyticUnicyclicLimit : Prop :=
  Tendsto (fun k : ℕ =>
    ((((k - 1).factorial : ℝ) / 2 *
      (Finset.range (k - 2)).sum (fun m =>
        (k : ℝ) ^ m / (m.factorial : ℝ))) /
      Real.rpow (k : ℝ) ((k : ℝ) - 1 / 2))) atTop
        (𝓝 (Real.sqrt (Real.pi / 8)))

noncomputable def poissonPrefix (k : ℕ) : ℝ :=
  Real.exp (-(k : ℝ)) *
    (Finset.range (k - 2)).sum (fun m =>
      (k : ℝ) ^ m / (m.factorial : ℝ))

private noncomputable def stirlingPrefactor (k : ℕ) : ℝ :=
  ((k - 1).factorial : ℝ) * Real.exp (k : ℝ) /
    Real.rpow (k : ℝ) ((k : ℝ) - 1 / 2)

private noncomputable def stirlingCorrection (k : ℕ) : ℝ :=
  Real.exp 1 * Real.sqrt (2 * ((k - 1 : ℕ) : ℝ) / k) *
    ((((k - 1 : ℕ) : ℝ) / k) ^ (k - 1))

def PoissonMidpointLimit : Prop :=
  Tendsto poissonPrefix atTop (𝓝 (1 / 2 : ℝ))

def StirlingPrefactorLimit : Prop :=
  Tendsto stirlingPrefactor atTop (𝓝 (Real.sqrt (2 * Real.pi)))

def AsymptoticCoreStatement : Prop :=
  PoissonMidpointLimit → UnicyclicFormula →
    UnicyclicFormula ∧ RankEquivalence ∧ UniformUnicyclicBound ∧ UnicyclicLimit

private lemma countGE_antitone {n : ℕ} (G : Graph n) :
    Antitone (countGE G) := by
  intro a b hab
  unfold countGE
  apply Finset.card_le_card
  intro S hS
  simp only [Finset.mem_filter] at hS ⊢
  exact ⟨hS.1, le_trans hab hS.2⟩

private lemma countGE_eq_zero_of_lt {n : ℕ} (G : Graph n) {h : ℕ}
    (hhn : n < h) : countGE G h = 0 := by
  apply Nat.eq_zero_of_le_zero
  unfold countGE
  rw [Nat.le_zero, Finset.card_eq_zero]
  rw [Finset.filter_eq_empty_iff]
  intro S hS hcard
  exact (not_le_of_gt hhn) (le_trans hcard (by simpa using! Finset.card_le_univ S))

private lemma rank_threshold {n : ℕ} (G : Graph n) {i h : ℕ}
    (hi : 0 < i) (hh : 0 < h) :
    h ≤ rankSize G i ↔ i ≤ countGE G h := by
  unfold rankSize
  simp only [if_neg (ne_of_gt hi)]
  constructor
  · intro hle
    obtain ⟨u, hu, hlu⟩ := (Finset.le_sup_iff hh).mp hle
    simp only [Finset.mem_range] at hu
    by_cases hui : i ≤ countGE G u
    · simp only [if_pos hui] at hlu
      exact le_trans hui (countGE_antitone G hlu)
    · simp only [if_neg hui] at hlu
      omega
  · intro hic
    have hhn : h ≤ n := by
      by_contra hn
      have hzero := countGE_eq_zero_of_lt G (Nat.lt_of_not_ge hn)
      rw [hzero] at hic
      omega
    have hmem : h ∈ Finset.range (n + 1) := by
      simp only [Finset.mem_range]
      omega
    have hle := Finset.le_sup (f := fun u => if i ≤ countGE G u then u else 0) hmem
    simpa only [if_pos hic] using! hle

theorem rank_equivalence : RankEquivalence := by
  intro n G i h hi hh
  rw [show rankSize G i < h ↔ ¬ h ≤ rankSize G i by omega]
  rw [rank_threshold G hi hh]
  omega

private noncomputable def normalizedUnicyclic (k : ℕ) : ℝ :=
  (connectedCount k k : ℝ) /
    Real.rpow (k : ℝ) ((k : ℝ) - 1 / 2)

theorem uniform_bound_of_limit (hlim : UnicyclicLimit) :
    UniformUnicyclicBound := by
  change Tendsto normalizedUnicyclic atTop
      (𝓝 (Real.sqrt (Real.pi / 8))) at hlim
  obtain ⟨B, hB⟩ := hlim.bddAbove_range
  refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro k hk
  have hkpos : (0 : ℝ) < k := by positivity
  have hdpos : 0 < Real.rpow (k : ℝ) ((k : ℝ) - 1 / 2) :=
    Real.rpow_pos_of_pos hkpos _
  have hratio : normalizedUnicyclic k ≤ max 1 B :=
    le_trans (hB ⟨k, rfl⟩) (le_max_right _ _)
  exact (div_le_iff₀ hdpos).mp hratio

theorem limit_of_formula (hformula : UnicyclicFormula)
    (hanalytic : AnalyticUnicyclicLimit) : UnicyclicLimit := by
  change Tendsto normalizedUnicyclic atTop
      (𝓝 (Real.sqrt (Real.pi / 8)))
  apply hanalytic.congr'
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with k hk
  rw [normalizedUnicyclic, hformula k hk]

private lemma sqrt_two_pi_div_four :
    Real.sqrt (2 * Real.pi) / 4 = Real.sqrt (Real.pi / 8) := by
  have hp : 0 ≤ Real.pi := le_of_lt Real.pi_pos
  have h2p : 0 ≤ 2 * Real.pi := mul_nonneg (by norm_num) hp
  have hp8 : 0 ≤ Real.pi / 8 := div_nonneg hp (by norm_num)
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [div_pow]
  rw [Real.sq_sqrt h2p, Real.sq_sqrt hp8]
  ring

theorem analytic_limit_of_factors (hpois : PoissonMidpointLimit)
    (hstir : StirlingPrefactorLimit) : AnalyticUnicyclicLimit := by
  have hprod : Tendsto (fun k => stirlingPrefactor k * poissonPrefix k / 2)
      atTop (𝓝 (Real.sqrt (2 * Real.pi) / 4)) := by
    convert (hstir.mul hpois).div_const 2 using 1 <;> norm_num <;> ring_nf
  rw [sqrt_two_pi_div_four] at hprod
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  have hkpos : (0 : ℝ) < k := by positivity
  have hd : Real.rpow (k : ℝ) ((k : ℝ) - 1 / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hkpos _)
  rw [stirlingPrefactor, poissonPrefix]
  have hexp : Real.exp (k : ℝ) * Real.exp (-(k : ℝ)) = 1 := by
    rw [← Real.exp_add]
    simp
  field_simp
  rw [hexp, one_mul]

private lemma tendsto_stirlingCorrection :
    Tendsto stirlingCorrection atTop (𝓝 (Real.sqrt 2)) := by
  have hbase : Tendsto (fun k : ℕ => (1 : ℝ) - 1 / k) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
      (tendsto_one_div_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0))
    simpa using! h
  have hpowFull : Tendsto (fun k : ℕ => ((1 : ℝ) - 1 / k) ^ k)
      atTop (𝓝 (Real.exp (-1))) := by
    convert Real.tendsto_one_add_div_pow_exp (-1) using 1
    funext k
    ring
  have hpowDiv := hpowFull.div hbase (by norm_num)
  have hpow : Tendsto (fun k : ℕ => ((1 : ℝ) - 1 / k) ^ (k - 1))
      atTop (𝓝 (Real.exp (-1))) := by
    have hpowDiv' : Tendsto (fun k : ℕ =>
        ((1 : ℝ) - 1 / k) ^ k / ((1 : ℝ) - 1 / k))
        atTop (𝓝 (Real.exp (-1))) := by simpa using! hpowDiv
    apply hpowDiv'.congr'
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with k hk
    have hb : (1 : ℝ) - 1 / k ≠ 0 := by
      have hkreal : (1 : ℝ) < k := by exact_mod_cast hk
      have hdiv : (1 : ℝ) / k < 1 := (div_lt_one (by positivity)).2 hkreal
      linarith
    symm
    rw [pow_sub₀ _ hb (by omega : 1 ≤ k)]
    simp [div_eq_mul_inv]
  have hargAux := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).mul hbase
  have hargAux' : Tendsto (fun k : ℕ => (2 : ℝ) * (1 - 1 / k))
      atTop (𝓝 2) := by simpa using! hargAux
  have hsqrt : Tendsto
      (fun k : ℕ => Real.sqrt (2 * ((k - 1 : ℕ) : ℝ) / k))
      atTop (𝓝 (Real.sqrt 2)) := by
    have harg : Tendsto (fun k : ℕ =>
        (2 : ℝ) * ((k - 1 : ℕ) : ℝ) / k) atTop (𝓝 2) := by
      apply hargAux'.congr'
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
      symm
      rw [Nat.cast_sub hk]
      field_simp
      ring
    exact harg.sqrt
  have hpowCast : Tendsto (fun k : ℕ =>
      (((k - 1 : ℕ) : ℝ) / k) ^ (k - 1))
      atTop (𝓝 (Real.exp (-1))) := by
    apply hpow.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
    rw [Nat.cast_sub hk]
    congr 1
    field_simp
    ring
  have h := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.exp 1)
      atTop (𝓝 (Real.exp 1))).mul hsqrt).mul hpowCast
  have hexp : Real.exp 1 * Real.sqrt 2 * Real.exp (-1) = Real.sqrt 2 := by
    calc
      Real.exp 1 * Real.sqrt 2 * Real.exp (-1) =
          (Real.exp 1 * Real.exp (-1)) * Real.sqrt 2 := by ring
      _ = Real.sqrt 2 := by rw [← Real.exp_add]; norm_num
  rw [← hexp]
  exact h

private lemma rpow_nat_sub_half (k : ℕ) (hk : 0 < k) :
    Real.rpow (k : ℝ) ((k : ℝ) - 1 / 2) =
      (k : ℝ) ^ k / Real.sqrt k := by
  calc
    Real.rpow (k : ℝ) ((k : ℝ) - 1 / 2) =
        Real.rpow (k : ℝ) (k : ℝ) / Real.rpow (k : ℝ) (1 / 2) :=
      Real.rpow_sub (by positivity) _ _
    _ = (k : ℝ) ^ k / Real.rpow (k : ℝ) (1 / 2) := by
      congr 1
      exact Real.rpow_natCast _ _
    _ = (k : ℝ) ^ k / Real.sqrt k := by
      congr 1
      exact (Real.sqrt_eq_rpow _).symm

private lemma stirlingPrefactor_eq (k : ℕ) (hk : 2 ≤ k) :
    stirlingPrefactor k =
      Stirling.stirlingSeq (k - 1) * stirlingCorrection k := by
  have hk0 : 0 < k := by omega
  have hk1 : 1 ≤ k := by omega
  have hkr : (0 : ℝ) < k := by positivity
  have hk2r : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hn : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt (by omega : 1 < k))
  have hsqrtk : Real.sqrt (k : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos_of_pos hkr)
  have hsqrtn : Real.sqrt (2 * ((k - 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hn0 : (((k - 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt hn
  have hkR0 : (k : ℝ) ≠ 0 := ne_of_gt hkr
  have hexp1 : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
  have hexpk : Real.exp (k : ℝ) =
      Real.exp 1 ^ (k - 1) * Real.exp 1 := by
    rw [← Real.exp_one_pow]
    nth_rewrite 1 [show k = (k - 1) + 1 by omega]
    rw [pow_succ]
  have hpowk : (k : ℝ) ^ k = (k : ℝ) ^ (k - 1) * k := by
    calc
      (k : ℝ) ^ k = (k : ℝ) ^ ((k - 1) + 1) := by congr 1 <;> omega
      _ = (k : ℝ) ^ (k - 1) * k := by rw [pow_succ]
  rw [stirlingPrefactor, stirlingCorrection, Stirling.stirlingSeq,
    rpow_nat_sub_half k hk0]
  rw [Real.sqrt_div (by positivity)]
  simp only [Nat.cast_sub hk1, Nat.cast_one]
  rw [div_pow, div_pow, hexpk, hpowk]
  field_simp [hsqrtk, hsqrtn, hn0, hkR0, hexp1]
  rw [Real.sq_sqrt (le_of_lt hkr)]
  have hD : Real.sqrt (2 * ((k : ℝ) - 1)) *
      ((k : ℝ) - 1) ^ (k - 1) ≠ 0 := by
    apply mul_ne_zero
    · apply ne_of_gt
      apply Real.sqrt_pos_of_pos
      nlinarith
    · apply pow_ne_zero
      nlinarith
  rw [mul_assoc, mul_div_assoc, div_self hD, mul_one]

theorem stirling_prefactor_limit : StirlingPrefactorLimit := by
  have hsub : Tendsto (fun k : ℕ => k - 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b + 1)] with k hk
    omega
  have hstir : Tendsto (fun k : ℕ => Stirling.stirlingSeq (k - 1))
      atTop (𝓝 (Real.sqrt Real.pi)) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.comp hsub
  have hmul := hstir.mul tendsto_stirlingCorrection
  have hsqrt : Real.sqrt Real.pi * Real.sqrt 2 =
      Real.sqrt (2 * Real.pi) := by
    rw [← Real.sqrt_mul (le_of_lt Real.pi_pos)]
    congr 1
    ring
  rw [hsqrt] at hmul
  apply hmul.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with k hk
  exact (stirlingPrefactor_eq k hk).symm

theorem result : AsymptoticCoreStatement := by
  intro hpoisson hformula
  have hanalytic := analytic_limit_of_factors hpoisson stirling_prefactor_limit
  have hlim := limit_of_formula hformula hanalytic
  exact ⟨hformula, rank_equivalence, uniform_bound_of_limit hlim, hlim⟩

end Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Asymptotic


namespace Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Midpoint

open Filter Topology
open scoped NNReal

noncomputable def p (k m : ℕ) : ℝ :=
  Real.exp (-(k : ℝ)) * (k : ℝ) ^ m / (m.factorial : ℝ)

lemma p_nonneg (k m : ℕ) : 0 ≤ p k m := by
  exact div_nonneg
    (mul_nonneg (Real.exp_pos _).le (pow_nonneg (Nat.cast_nonneg _) _))
    (Nat.cast_nonneg _)

lemma p_sum (k : ℕ) : HasSum (p k) 1 := by
  simpa [p, ProbabilityTheory.poissonPMFReal] using!
    ProbabilityTheory.poissonPMFRealSum (k : ℝ≥0)

lemma p_succ (k m : ℕ) :
    (m + 1 : ℝ) * p k (m + 1) = (k : ℝ) * p k m := by
  simp only [p, Nat.cast_add, Nat.cast_one, pow_succ, Nat.factorial_succ, Nat.cast_mul]
  field_simp

lemma first_moment (k : ℕ) :
    HasSum (fun m : ℕ => (m : ℝ) * p k m) k := by
  apply (hasSum_nat_add_iff' 1).mp
  convert (p_sum k).mul_left (k : ℝ) using 1
  · funext m
    simpa [Nat.cast_add, Nat.cast_one] using! p_succ k m
  · simp [p]

lemma factorial_second_moment (k : ℕ) :
    HasSum (fun m : ℕ => (m : ℝ) * (m - 1) * p k m) ((k : ℝ) ^ 2) := by
  apply (hasSum_nat_add_iff' 2).mp
  convert (p_sum k).mul_left ((k : ℝ) ^ 2) using 1
  · funext m
    have h1 := p_succ k (m + 1)
    norm_num [Nat.cast_add, Nat.add_assoc] at h1
    have h1' : (↑m + 2) * p k (m + 2) = ↑k * p k (m + 1) := by
      nlinarith [h1]
    have h0 := p_succ k m
    norm_num [Nat.cast_add] at h0 ⊢
    calc
      (↑m + 2) * (↑m + 2 - 1) * p k (m + 2) =
          (↑m + 1) * ((↑m + 2) * p k (m + 2)) := by ring
      _ = (↑m + 1) * (↑k * p k (m + 1)) := by rw [h1']
      _ = ↑k * ((↑m + 1) * p k (m + 1)) := by ring
      _ = ↑k * (↑k * p k m) := by rw [h0]
      _ = ↑k ^ 2 * p k m := by ring
  · simp [Finset.sum_range_succ, p]

lemma second_moment (k : ℕ) :
    HasSum (fun m : ℕ => (m : ℝ) ^ 2 * p k m) ((k : ℝ) ^ 2 + k) := by
  convert (factorial_second_moment k).add (first_moment k) using 1
  · funext m
    ring

lemma centered_second_moment (k : ℕ) :
    HasSum (fun m : ℕ => ((m : ℝ) - k) ^ 2 * p k m) k := by
  have h := ((second_moment k).add ((first_moment k).mul_left (-2 * (k : ℝ)))).add
    ((p_sum k).mul_left ((k : ℝ) ^ 2))
  convert h using 1
  · funext m
    ring
  · ring

noncomputable def tailMass (k : ℕ) (w : ℝ) : ℝ :=
  ∑' m : ℕ, if w ≤ |(m : ℝ) - k| then p k m else 0

lemma tail_summable (k : ℕ) (w : ℝ) :
    Summable (fun m : ℕ => if w ≤ |(m : ℝ) - k| then p k m else 0) := by
  apply Summable.of_nonneg_of_le
  · intro m
    split_ifs
    · exact p_nonneg _ _
    · exact le_rfl
  · intro m
    split_ifs
    · exact le_rfl
    · exact p_nonneg _ _
  · exact (p_sum k).summable

lemma tail_mass_le (k : ℕ) {w : ℝ} (hw : 0 < w) :
    tailMass k w ≤ (k : ℝ) / w ^ 2 := by
  have hterm : ∀ m : ℕ,
      w ^ 2 * (if w ≤ |(m : ℝ) - k| then p k m else 0) ≤
        ((m : ℝ) - k) ^ 2 * p k m := by
    intro m
    split_ifs with hm
    · apply mul_le_mul_of_nonneg_right _ (p_nonneg _ _)
      simpa only [sq_abs] using!
        (sq_le_sq₀ (le_of_lt hw) (abs_nonneg ((m : ℝ) - k))).2 hm
    · simp only [mul_zero]
      exact mul_nonneg (sq_nonneg _) (p_nonneg _ _)
  have hsum := Summable.tsum_le_tsum hterm
    ((tail_summable k w).mul_left (w ^ 2))
    (centered_second_moment k).summable
  have hleft :
      (∑' i : ℕ, w ^ 2 * if w ≤ |(i : ℝ) - k| then p k i else 0) =
        w ^ 2 * tailMass k w := by
    rw [tailMass, ← tsum_mul_left]
  have hsum' : w ^ 2 * tailMass k w ≤ (k : ℝ) := by
    rw [hleft, (centered_second_moment k).tsum_eq] at hsum
    exact hsum
  exact (le_div_iff₀ (sq_pos_of_pos hw)).2 (by simpa [mul_comm] using! hsum')

noncomputable def pairProd (k j : ℕ) : ℝ :=
  (Finset.range j).prod (fun r => 1 - (((r + 1 : ℕ) : ℝ) / k) ^ 2)

lemma pair_identity (k j : ℕ) (hj : j < k) :
    p k (k - 1 - j) = p k (k + j) * pairProd k j := by
  induction j with
  | zero =>
      simp only [pairProd, Finset.range_zero, Finset.prod_empty, mul_one, Nat.sub_zero,
        Nat.add_zero]
      have hk : 1 ≤ k := by omega
      have h := p_succ k (k - 1)
      rw [Nat.sub_add_cancel hk] at h
      have hkpos : (0 : ℝ) < k := by positivity
      have h' : (k : ℝ) * p k k = (k : ℝ) * p k (k - 1) := by
        simpa [Nat.cast_sub hk] using! h
      nlinarith
  | succ j ih =>
      have hj' : j < k := by omega
      have hleftIndex : k - 1 - (j + 1) + 1 = k - 1 - j := by omega
      have hl := p_succ k (k - 1 - (j + 1))
      rw [hleftIndex] at hl
      have hrightIndex : k + j + 1 = k + (j + 1) := by omega
      have hr := p_succ k (k + j)
      rw [hrightIndex] at hr
      have hk0 : (k : ℝ) ≠ 0 := by
        exact_mod_cast (show k ≠ 0 by omega)
      have hkp : ((k + j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have hb : p k (k - 1 - (j + 1)) =
          ((k - 1 - (j + 1) + 1 : ℕ) : ℝ) * p k (k - 1 - j) / k := by
        apply (eq_div_iff hk0).2
        have hc : ((k - 1 - (j + 1) : ℕ) : ℝ) + 1 =
            ((k - 1 - (j + 1) + 1 : ℕ) : ℝ) := by norm_cast
        rw [← hc]
        nlinarith [hl]
      have ha : p k (k + (j + 1)) =
          (k : ℝ) * p k (k + j) / (k + j + 1 : ℕ) := by
        apply (eq_div_iff hkp).2
        have hc : (((k + j : ℕ) : ℝ) + 1) = ((k + j + 1 : ℕ) : ℝ) := by norm_cast
        rw [← hc]
        nlinarith [hr]
      rw [hb, ha, ih hj']
      simp only [pairProd, Finset.prod_range_succ]
      have hnat : k - 1 - (j + 1) + 1 = k - (j + 1) := by omega
      rw [hnat, Nat.cast_sub (by omega : j + 1 ≤ k)]
      push_cast
      field_simp
      ring

lemma pairProd_nonneg (k j : ℕ) (hj : j ≤ k) : 0 ≤ pairProd k j := by
  apply Finset.prod_nonneg
  intro r hr
  simp only [Finset.mem_range] at hr
  have hk : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hle : (((r + 1 : ℕ) : ℝ) / k) ≤ 1 := by
    rw [div_le_one hk]
    exact_mod_cast (show r + 1 ≤ k by omega)
  nlinarith [sq_nonneg ((((r + 1 : ℕ) : ℝ) / k)),
    mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) / k) hle]

lemma one_sub_prod_le_sum {s : Finset ℕ} {x : ℕ → ℝ}
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hx1 : ∀ i ∈ s, x i ≤ 1) :
    1 - ∏ i ∈ s, (1 - x i) ≤ ∑ i ∈ s, x i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have hxa0 := hx0 a (Finset.mem_insert_self _ _)
      have hs0 : 0 ≤ ∏ i ∈ s, (1 - x i) := by
        apply Finset.prod_nonneg
        intro i hi
        exact sub_nonneg.mpr (hx1 i (Finset.mem_insert_of_mem hi))
      have ih' := ih (fun i hi => hx0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => hx1 i (Finset.mem_insert_of_mem hi))
      have hs1 : (∏ i ∈ s, (1 - x i)) ≤ 1 := by
        apply Finset.prod_le_one₀
        · intro i hi
          exact sub_nonneg.mpr (hx1 i (Finset.mem_insert_of_mem hi))
        · intro i hi
          exact sub_le_self _ (hx0 i (Finset.mem_insert_of_mem hi))
      calc
        1 - (1 - x a) * ∏ i ∈ s, (1 - x i) =
            x a + (1 - x a) * (1 - ∏ i ∈ s, (1 - x i)) := by ring
        _ ≤ x a + 1 * (1 - ∏ i ∈ s, (1 - x i)) := by
          have hm := mul_le_mul_of_nonneg_right
            (sub_le_self 1 hxa0) (sub_nonneg.mpr hs1)
          linarith
        _ ≤ x a + ∑ i ∈ s, x i := by linarith

lemma pair_difference_bound (k j : ℕ) (hj : j < k) :
    0 ≤ p k (k + j) - p k (k - 1 - j) ∧
    p k (k + j) - p k (k - 1 - j) ≤
      ((j : ℝ) ^ 3 / (k : ℝ) ^ 2) * p k (k + j) := by
  rw [pair_identity k j hj]
  have hprod0 : 0 ≤ pairProd k j := pairProd_nonneg k j (Nat.le_of_lt hj)
  have hprod1 : pairProd k j ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro r hr
      simp only [Finset.mem_range] at hr
      have hk : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hle : (((r + 1 : ℕ) : ℝ) / k) ≤ 1 := by
        rw [div_le_one hk]
        exact_mod_cast (show r + 1 ≤ k by omega)
      nlinarith [sq_nonneg ((((r + 1 : ℕ) : ℝ) / k)),
        mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) / k) hle]
    · intro r hr
      exact sub_le_self 1 (sq_nonneg _)
  constructor
  · exact sub_nonneg.mpr (mul_le_of_le_one_right (p_nonneg _ _) hprod1)
  · calc
      p k (k + j) - p k (k + j) * pairProd k j =
          (1 - pairProd k j) * p k (k + j) := by ring
      _ ≤ ((Finset.range j).sum fun r => (((r + 1 : ℕ) : ℝ) / k) ^ 2) *
          p k (k + j) := by
        apply mul_le_mul_of_nonneg_right _ (p_nonneg _ _)
        exact one_sub_prod_le_sum
          (fun r hr => sq_nonneg _)
          (fun r hr => by
            simp only [Finset.mem_range] at hr
            have hk : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
            have hle : (((r + 1 : ℕ) : ℝ) / k) ≤ 1 := by
              rw [div_le_one hk]
              exact_mod_cast (show r + 1 ≤ k by omega)
            simpa using! (sq_le_sq₀
              (by positivity : (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) / k)
              (by norm_num : (0 : ℝ) ≤ 1)).2 hle)
      _ ≤ ((j : ℝ) ^ 3 / (k : ℝ) ^ 2) * p k (k + j) := by
        apply mul_le_mul_of_nonneg_right _ (p_nonneg _ _)
        simp_rw [div_pow]
        rw [← Finset.sum_div]
        have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by
          exact sq_pos_of_pos (by exact_mod_cast (show 0 < k by omega))
        apply (div_le_div_iff_of_pos_right hk2).2
        calc
          (Finset.range j).sum (fun r => ((r + 1 : ℕ) : ℝ) ^ 2) ≤
              (Finset.range j).sum (fun _ => (j : ℝ) ^ 2) := by
            apply Finset.sum_le_sum
            intro r hr
            simp only [Finset.mem_range] at hr
            gcongr
            exact_mod_cast (show r + 1 ≤ j by omega)
          _ = (j : ℝ) ^ 3 := by simp; ring

noncomputable def lowerMass (k : ℕ) : ℝ :=
  (Finset.range k).sum (p k)

noncomputable def upperMass (k : ℕ) : ℝ :=
  ∑' j : ℕ, p k (k + j)

noncomputable def imbalance (k : ℕ) : ℝ := upperMass k - lowerMass k

lemma upper_summable (k : ℕ) : Summable (fun j : ℕ => p k (k + j)) := by
  simpa [add_comm] using! (summable_nat_add_iff k).2 (p_sum k).summable

lemma total_mass (k : ℕ) : lowerMass k + upperMass k = 1 := by
  rw [lowerMass, upperMass]
  calc
    (Finset.range k).sum (p k) + ∑' j : ℕ, p k (k + j) = ∑' m : ℕ, p k m := by
      simpa [add_comm] using! (p_sum k).summable.sum_add_tsum_nat_add k
    _ = 1 := (p_sum k).tsum_eq

lemma lower_nonneg (k : ℕ) : 0 ≤ lowerMass k := by
  exact Finset.sum_nonneg fun _ _ => p_nonneg _ _

lemma lower_eq_reflected (k : ℕ) :
    lowerMass k = (Finset.range k).sum (fun j => p k (k - 1 - j)) := by
  rw [lowerMass, Finset.sum_range_reflect]

lemma lower_le_upper (k : ℕ) : lowerMass k ≤ upperMass k := by
  rw [lower_eq_reflected, upperMass]
  calc
    (Finset.range k).sum (fun j => p k (k - 1 - j)) ≤
        (Finset.range k).sum (fun j => p k (k + j)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact sub_nonneg.mp (pair_difference_bound k j (Finset.mem_range.mp hj)).1
    _ ≤ ∑' j : ℕ, p k (k + j) := by
      apply Summable.sum_le_tsum (Finset.range k)
      · intro j hj
        exact p_nonneg _ _
      · exact upper_summable k

lemma imbalance_nonneg (k : ℕ) : 0 ≤ imbalance k :=
  sub_nonneg.mpr (lower_le_upper k)

lemma shifted_tail_le (k w : ℕ) :
    (∑' j : ℕ, p k (k + (j + w))) ≤ tailMass k w := by
  let e : ℕ → ℕ := fun j => k + (j + w)
  have he : Function.Injective e := by
    intro a b hab
    dsimp [e] at hab
    omega
  apply Summable.tsum_le_tsum_of_inj e he
  · intro m hm
    split_ifs <;> simp [p_nonneg]
  · intro j
    dsimp [e]
    rw [if_pos (by
      have hdiff : ((k + (j + w) : ℕ) : ℝ) - (k : ℝ) = ((j + w : ℕ) : ℝ) := by
        push_cast
        ring
      rw [hdiff, abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast (show w ≤ j + w by omega))]
  · simpa [add_assoc, add_left_comm, add_comm] using!
      (summable_nat_add_iff (k + w)).2 (p_sum k).summable
  · exact tail_summable k w

lemma central_difference_le (k w : ℕ) (hwk : w ≤ k) :
    (Finset.range w).sum (fun j => p k (k + j) - p k (k - 1 - j)) ≤
      ((w : ℝ) ^ 3 / (k : ℝ) ^ 2) := by
  by_cases hk0 : k = 0
  · subst k
    have hw0 : w = 0 := Nat.eq_zero_of_le_zero hwk
    subst w
    simp
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  calc
    (Finset.range w).sum (fun j => p k (k + j) - p k (k - 1 - j)) ≤
      (Finset.range w).sum
        (fun j => ((w : ℝ) ^ 3 / (k : ℝ) ^ 2) * p k (k + j)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjw : j < w := Finset.mem_range.mp hj
      calc
        p k (k + j) - p k (k - 1 - j) ≤
            ((j : ℝ) ^ 3 / (k : ℝ) ^ 2) * p k (k + j) :=
          (pair_difference_bound k j (lt_of_lt_of_le hjw hwk)).2
        _ ≤ ((w : ℝ) ^ 3 / (k : ℝ) ^ 2) * p k (k + j) := by
          apply mul_le_mul_of_nonneg_right _ (p_nonneg _ _)
          apply div_le_div_of_nonneg_right _ (sq_nonneg _)
          gcongr
    _ = ((w : ℝ) ^ 3 / (k : ℝ) ^ 2) *
        (Finset.range w).sum (fun j => p k (k + j)) := by rw [Finset.mul_sum]
    _ ≤ ((w : ℝ) ^ 3 / (k : ℝ) ^ 2) * 1 := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (by positivity) (sq_nonneg _))
      have hsum : (Finset.range w).sum (fun j => p k (k + j)) ≤ upperMass k := by
        rw [upperMass]
        apply Summable.sum_le_tsum (Finset.range w)
        · intro j hj
          exact p_nonneg _ _
        · exact upper_summable k
      have hu : upperMass k ≤ 1 := by
        rw [← total_mass k]
        linarith [lower_nonneg k]
      exact hsum.trans hu
    _ = (w : ℝ) ^ 3 / (k : ℝ) ^ 2 := by ring

lemma imbalance_le_window (k w : ℕ) (hw : 0 < w) (hwk : w ≤ k) :
    imbalance k ≤ (w : ℝ) ^ 3 / (k : ℝ) ^ 2 + (k : ℝ) / (w : ℝ) ^ 2 := by
  have hupper := (upper_summable k).sum_add_tsum_nat_add w
  have hupper' : upperMass k =
      (Finset.range w).sum (fun j => p k (k + j)) +
        ∑' j : ℕ, p k (k + (j + w)) := by
    rw [upperMass]
    symm
    simpa [add_assoc, add_left_comm, add_comm] using! hupper
  have hlower :
      (Finset.range w).sum (fun j => p k (k - 1 - j)) ≤ lowerMass k := by
    rw [lower_eq_reflected]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      simp only [Finset.mem_range] at hj ⊢
      exact lt_of_lt_of_le hj hwk
    · intro j hjk hjw
      exact p_nonneg _ _
  calc
    imbalance k = upperMass k - lowerMass k := rfl
    _ ≤ upperMass k - (Finset.range w).sum (fun j => p k (k - 1 - j)) :=
      sub_le_sub_left hlower _
    _ = (Finset.range w).sum (fun j => p k (k + j) - p k (k - 1 - j)) +
        (∑' j : ℕ, p k (k + (j + w))) := by
      rw [hupper', Finset.sum_sub_distrib]
      ring
    _ ≤ (w : ℝ) ^ 3 / (k : ℝ) ^ 2 + tailMass k w :=
      add_le_add (central_difference_le k w hwk) (shifted_tail_le k w)
    _ ≤ (w : ℝ) ^ 3 / (k : ℝ) ^ 2 + (k : ℝ) / (w : ℝ) ^ 2 := by
      gcongr
      exact tail_mass_le k (by exact_mod_cast hw)

noncomputable def window (A k : ℕ) : ℕ :=
  ⌈(A : ℝ) * Real.sqrt (k : ℝ)⌉₊

lemma window_ratio_tendsto (A : ℕ) :
    Tendsto (fun k : ℕ => (window A k : ℝ) / Real.sqrt (k : ℝ))
      atTop (𝓝 (A : ℝ)) := by
  exact (tendsto_nat_ceil_mul_div_atTop (show (0 : ℝ) ≤ A by positivity)).comp
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

lemma window_first_term_tendsto (A : ℕ) :
    Tendsto (fun k : ℕ => (window A k : ℝ) ^ 3 / (k : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have hs : Tendsto (fun k : ℕ => Real.sqrt (k : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hlim := ((window_ratio_tendsto A).pow 3).mul (tendsto_inv_atTop_zero.comp hs)
  rw [show (0 : ℝ) = (A : ℝ) ^ 3 * 0 by ring]
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hs0 : Real.sqrt (k : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hk0)
  have hsk : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt hk0.le
  have hk2 : (k : ℝ) ^ 2 = Real.sqrt (k : ℝ) ^ 4 := by
    calc
      (k : ℝ) ^ 2 = (Real.sqrt (k : ℝ) ^ 2) ^ 2 :=
        congrArg (fun x : ℝ => x ^ 2) hsk.symm
      _ = Real.sqrt (k : ℝ) ^ 4 := by ring
  simp only [Function.comp_apply]
  rw [div_pow]
  field_simp
  exact congrArg (fun x : ℝ => (window A k : ℝ) ^ 3 * x) hk2

lemma window_second_term_tendsto (A : ℕ) (hA : 0 < A) :
    Tendsto (fun k : ℕ => (k : ℝ) / (window A k : ℝ) ^ 2)
      atTop (𝓝 (1 / (A : ℝ) ^ 2)) := by
  letI : ContinuousInv₀ ℝ := NormedDivisionRing.to_continuousInv₀
  have hq := (window_ratio_tendsto A).pow 2
  have hA0 : (A : ℝ) ^ 2 ≠ 0 := by positivity
  have hinv := Filter.Tendsto.inv₀ hq hA0
  rw [show (1 / (A : ℝ) ^ 2) = ((A : ℝ) ^ 2)⁻¹ by simp]
  refine hinv.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hw0 : (window A k : ℝ) ≠ 0 := by
    norm_cast
    unfold window
    exact (Nat.ceil_pos.mpr (mul_pos (by exact_mod_cast hA) (Real.sqrt_pos.2 hk0))).ne'
  have hsk : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt hk0.le
  rw [div_pow]
  field_simp
  exact hsk

lemma window_fraction_tendsto (A : ℕ) :
    Tendsto (fun k : ℕ => (window A k : ℝ) / (k : ℝ)) atTop (𝓝 0) := by
  have hs : Tendsto (fun k : ℕ => Real.sqrt (k : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hlim := (window_ratio_tendsto A).mul (tendsto_inv_atTop_zero.comp hs)
  rw [show (0 : ℝ) = (A : ℝ) * 0 by ring]
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hs0 : Real.sqrt (k : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hk0)
  have hsk : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt hk0.le
  simp only [Function.comp_apply]
  field_simp
  exact congrArg (fun x : ℝ => (window A k : ℝ) * x) hsk.symm

lemma window_le_eventually (A : ℕ) : ∀ᶠ k : ℕ in atTop, window A k ≤ k := by
  filter_upwards [(window_fraction_tendsto A).eventually_lt_const
      (by norm_num : (0 : ℝ) < 1), eventually_gt_atTop (0 : ℕ)] with k hk hk0
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hh : (window A k : ℝ) < k := (div_lt_one hkR).mp hk
  exact Nat.le_of_lt (by exact_mod_cast hh)

lemma imbalance_tendsto_zero : Tendsto imbalance atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨A, hApos, hsmall⟩ : ∃ A : ℕ, 0 < A ∧ 1 / (A : ℝ) ^ 2 < ε / 2 := by
    obtain ⟨A, hA⟩ := exists_nat_gt (max 1 (2 / ε))
    have hA1 : (1 : ℝ) < A := lt_of_le_of_lt (le_max_left _ _) hA
    have hA1nat : 1 < A := by exact_mod_cast hA1
    refine ⟨A, by omega, ?_⟩
    have hAeps : 2 / ε < (A : ℝ) := lt_of_le_of_lt (le_max_right _ _) hA
    have hAsq : (A : ℝ) < (A : ℝ) ^ 2 := by nlinarith
    have hden : 2 / ε < (A : ℝ) ^ 2 := hAeps.trans hAsq
    rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < (A : ℝ) ^ 2)
      (by positivity : (0 : ℝ) < 2)]
    have := (div_lt_iff₀ hε).mp hden
    nlinarith
  have hboundlim :
      Tendsto (fun k : ℕ => (window A k : ℝ) ^ 3 / (k : ℝ) ^ 2 +
        (k : ℝ) / (window A k : ℝ) ^ 2)
        atTop (𝓝 (1 / (A : ℝ) ^ 2)) := by
    simpa using! (window_first_term_tendsto A).add (window_second_term_tendsto A hApos)
  have hlt : ∀ᶠ k : ℕ in atTop,
      (window A k : ℝ) ^ 3 / (k : ℝ) ^ 2 +
        (k : ℝ) / (window A k : ℝ) ^ 2 < ε :=
    hboundlim.eventually_lt_const (by linarith)
  apply eventually_atTop.1
  filter_upwards [hlt, window_le_eventually A, eventually_gt_atTop (0 : ℕ)] with k hk hwk hk0
  have hwpos : 0 < window A k := by
    unfold window
    rw [Nat.ceil_pos]
    exact mul_pos (by exact_mod_cast hApos) (Real.sqrt_pos.2 (by exact_mod_cast hk0))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (imbalance_nonneg k)]
  exact (imbalance_le_window k (window A k) hwpos hwk).trans_lt hk

lemma lowerMass_tendsto_half : Tendsto lowerMass atTop (𝓝 (1 / 2 : ℝ)) := by
  have hform : ∀ k : ℕ, lowerMass k = (1 - imbalance k) / 2 := by
    intro k
    rw [imbalance]
    have htotal := total_mass k
    linarith
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hlim := (hone.sub imbalance_tendsto_zero).div_const (2 : ℝ)
  convert hlim using 1
  · exact funext hform
  · norm_num

lemma center_bound (n : ℕ) (hn : 0 < n) :
    p (n + 1) n ≤ 1 / Real.sqrt (2 * Real.pi * n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbase : 1 + 1 / (n : ℝ) ≤ Real.exp (1 / (n : ℝ)) := by
    simpa [add_comm] using! Real.add_one_le_exp (1 / (n : ℝ))
  have hpow : (1 + 1 / (n : ℝ)) ^ n ≤ Real.exp (1 / (n : ℝ)) ^ n :=
    pow_le_pow_left₀ (by positivity) hbase n
  have hexp : Real.exp (1 / (n : ℝ)) ^ n = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [hexp] at hpow
  have hst := Stirling.le_factorial_stirling n
  have hsqrt : 0 < Real.sqrt (2 * Real.pi * n) := Real.sqrt_pos.2 (by positivity)
  have hfac : 0 < (n.factorial : ℝ) := by positivity
  have hnform : ((n : ℝ) + 1) ^ n =
      (n : ℝ) ^ n * (1 + 1 / (n : ℝ)) ^ n := by
    have hb : (n : ℝ) + 1 = (n : ℝ) * (1 + 1 / (n : ℝ)) := by field_simp
    rw [hb, mul_pow]
  have hen : Real.exp (-(n : ℝ)) = (Real.exp 1)⁻¹ ^ n := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    ring
  have htarget : Real.exp (-((n + 1 : ℕ) : ℝ)) * ((n + 1 : ℕ) : ℝ) ^ n *
        Real.sqrt (2 * Real.pi * n) ≤ (n.factorial : ℝ) := by
    apply le_trans ?_ hst
    push_cast
    rw [hnform]
    calc
      Real.exp (-(↑n + 1)) * (↑n ^ n * (1 + 1 / ↑n) ^ n) *
          √(2 * Real.pi * ↑n) ≤
        Real.exp (-(↑n + 1)) * (↑n ^ n * Real.exp 1) *
          √(2 * Real.pi * ↑n) := by gcongr
      _ = √(2 * Real.pi * ↑n) * (↑n / Real.exp 1) ^ n := by
        rw [div_pow, div_eq_mul_inv, ← inv_pow, ← hen]
        have heq : Real.exp (-(↑n + 1)) * (↑n ^ n * Real.exp 1) =
            ↑n ^ n * Real.exp (-↑n) := by
          calc
            _ = ↑n ^ n * (Real.exp (-(↑n + 1)) * Real.exp 1) := by ring
            _ = ↑n ^ n * Real.exp (-↑n) := by
              rw [← Real.exp_add]
              congr 2
              ring
        rw [heq]
        ring
  rw [p, Nat.cast_add, Nat.cast_one, div_le_iff₀ hfac]
  have hdiv := (le_div_iff₀ hsqrt).2 htarget
  simpa [div_eq_mul_inv, mul_comm] using! hdiv

lemma shifted_center_tendsto_zero :
    Tendsto (fun n : ℕ => p (n + 1) n) atTop (𝓝 0) := by
  have hlin : Tendsto (fun n : ℕ => (2 * Real.pi) * (n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).const_mul_atTop
      (by positivity)
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt ((2 * Real.pi) * (n : ℝ)))
      atTop atTop := Real.tendsto_sqrt_atTop.comp hlin
  have hinv0 := tendsto_inv_atTop_zero.comp hsqrt
  have hinv : Tendsto (fun n : ℕ => 1 / Real.sqrt ((2 * Real.pi) * (n : ℝ)))
      atTop (𝓝 0) := by
    refine hinv0.congr' ?_
    exact Eventually.of_forall fun n => by simp only [Function.comp_apply, one_div]
  apply squeeze_zero' (Eventually.of_forall fun n => p_nonneg _ _) _ hinv
  filter_upwards [eventually_ge_atTop 1] with n hn
  simpa [mul_assoc] using! center_bound n (by omega)

lemma center_tendsto_zero :
    Tendsto (fun k : ℕ => p k (k - 1)) atTop (𝓝 0) := by
  have h := shifted_center_tendsto_zero.comp (Filter.tendsto_sub_atTop_nat 1)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  simp [Nat.sub_add_cancel hk]

lemma penultimate_le_center (k : ℕ) (hk : 2 ≤ k) :
    p k (k - 2) ≤ p k (k - 1) := by
  have h := p_succ k (k - 2)
  have hi : k - 2 + 1 = k - 1 := by omega
  rw [hi] at h
  have hcast : ((k - 2 : ℕ) : ℝ) + 1 = ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast hi
  rw [hcast] at h
  have hkR : (0 : ℝ) < k := by positivity
  have hkm1 : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.sub_le k 1)
  nlinarith [p_nonneg k (k - 1), p_nonneg k (k - 2)]

lemma penultimate_tendsto_zero :
    Tendsto (fun k : ℕ => p k (k - 2)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun k => p_nonneg _ _) _ center_tendsto_zero
  filter_upwards [eventually_ge_atTop 2] with k hk
  exact penultimate_le_center k hk

noncomputable def prefixMass (k : ℕ) : ℝ :=
  (Finset.range (k - 2)).sum (p k)

lemma lowerMass_eq_prefix (k : ℕ) (hk : 2 ≤ k) :
    lowerMass k = prefixMass k + p k (k - 2) + p k (k - 1) := by
  rw [lowerMass, prefixMass, show k = (k - 2) + 2 by omega,
    Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Nat.sub_add_cancel hk, Nat.add_sub_cancel, show k - 2 + 1 = k - 1 by omega]

lemma prefixMass_tendsto_half : Tendsto prefixMass atTop (𝓝 (1 / 2 : ℝ)) := by
  have hcorr := penultimate_tendsto_zero.add center_tendsto_zero
  have hlim := lowerMass_tendsto_half.sub hcorr
  have hlim' : Tendsto
      (fun k => lowerMass k - (p k (k - 2) + p k (k - 1)))
      atTop (𝓝 (1 / 2 : ℝ)) := by simpa using! hlim
  refine hlim'.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with k hk
  rw [lowerMass_eq_prefix k hk]
  ring

theorem result :
    W01_ENUM_Asymptotic.PoissonMidpointLimit := by
  change Tendsto
    (fun k : ℕ => Real.exp (-(k : ℝ)) *
      (Finset.range (k - 2)).sum (fun m => (k : ℝ) ^ m / (m.factorial : ℝ)))
    atTop (𝓝 (1 / 2 : ℝ))
  refine prefixMass_tendsto_half.congr' ?_
  exact Eventually.of_forall fun k => by
    change (Finset.range (k - 2)).sum (p k) =
      Real.exp (-(k : ℝ)) *
        (Finset.range (k - 2)).sum (fun m => (k : ℝ) ^ m / (m.factorial : ℝ))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [p]
    ring

end Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Midpoint
