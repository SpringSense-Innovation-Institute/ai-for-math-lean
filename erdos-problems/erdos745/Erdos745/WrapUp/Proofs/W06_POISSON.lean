module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W06_P03

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section
namespace Erdos745.WrapUp.Proofs.W06_POISSON

noncomputable section

open Erdos745.WrapUp
open Filter
open scoped BigOperators
open scoped Topology

lemma falling_eq_descFactorial (n q : ℕ) :
    falling n q = n.descFactorial q := by
  simpa [falling] using! (Nat.descFactorial_eq_prod_range n q).symm

lemma falling_add_eq (x j l : ℕ) :
    falling x (j + l) =
      j.factorial * l.factorial * (x.choose j * (x - j).choose l) := by
  rw [falling_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  rw [← Nat.add_choose_mul_factorial_mul_factorial j l, ← Nat.choose_symm_add]
  have hc := Nat.choose_mul (n := x) (k := j + l) (s := j) (Nat.le_add_right j l)
  rw [show j + l - j = l by omega] at hc
  calc
    (j + l).choose j * j.factorial * l.factorial * x.choose (j + l) =
        j.factorial * l.factorial *
          (x.choose (j + l) * (j + l).choose j) := by ring
    _ = j.factorial * l.factorial *
          (x.choose j * (x - j).choose l) := by rw [hc]

lemma falling_div_factorials (x j l : ℕ) :
    (falling x (j + l) : ℝ) / ((j.factorial : ℝ) * (l.factorial : ℝ)) =
      (x.choose j : ℝ) * ((x - j).choose l : ℝ) := by
  rw [falling_add_eq]
  push_cast
  field_simp

lemma real_alternating_sum_range_choose_eq_choose (n r : ℕ) :
    (∑ l ∈ Finset.range (r + 1),
      (-1 : ℝ) ^ l * (Nat.choose (n + 1) l : ℝ)) =
      (-1 : ℝ) ^ r * (Nat.choose n r : ℝ) := by
  exact_mod_cast (Int.alternating_sum_range_choose_eq_choose (n := n) (m := r))

def bonferroniTerm (x j r : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (r + 1),
    (-1 : ℝ) ^ l *
      ((falling x (j + l) : ℝ) / ((j.factorial : ℝ) * (l.factorial : ℝ)))

lemma sum_choose_zero (r : ℕ) :
    (∑ l ∈ Finset.range (r + 1), (-1 : ℝ) ^ l * (Nat.choose 0 l : ℝ)) = 1 := by
  rw [Finset.sum_eq_single 0]
  · norm_num
  · intro b _ hb0
    simp [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hb0)]
  · simp

lemma bonferroniTerm_of_lt (x j r : ℕ) (h : x < j) :
    bonferroniTerm x j r = 0 := by
  simp_rw [bonferroniTerm, falling_div_factorials]
  simp [Nat.choose_eq_zero_of_lt h]

lemma bonferroniTerm_of_eq (x j r : ℕ) (h : x = j) :
    bonferroniTerm x j r = 1 := by
  subst x
  simp_rw [bonferroniTerm, falling_div_factorials]
  simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self]
  exact sum_choose_zero r

lemma bonferroniTerm_of_gt (x j r : ℕ) (h : j < x) :
    bonferroniTerm x j r =
      (x.choose j : ℝ) * ((-1 : ℝ) ^ r * ((x - j - 1).choose r : ℝ)) := by
  simp_rw [bonferroniTerm, falling_div_factorials]
  calc
    (∑ l ∈ Finset.range (r + 1),
      (-1 : ℝ) ^ l * ((x.choose j : ℝ) * ((x - j).choose l : ℝ))) =
        (x.choose j : ℝ) *
          ∑ l ∈ Finset.range (r + 1),
            (-1 : ℝ) ^ l * ((x - j).choose l : ℝ) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro l _
              ring
    _ = (x.choose j : ℝ) *
        ((-1 : ℝ) ^ r * ((x - j - 1).choose r : ℝ)) := by
      have hx : x - j = (x - j - 1) + 1 := by omega
      rw [hx, real_alternating_sum_range_choose_eq_choose]
      congr 3

lemma bonferroni_odd_le_indicator (x j m : ℕ) :
    bonferroniTerm x j (2 * m + 1) ≤ if x = j then 1 else 0 := by
  rcases lt_trichotomy x j with h | h | h
  · rw [bonferroniTerm_of_lt _ _ _ h]
    simp [ne_of_lt h]
  · rw [bonferroniTerm_of_eq _ _ _ h]
    simp [h]
  · rw [bonferroniTerm_of_gt _ _ _ h, if_neg (ne_of_gt h)]
    norm_num [pow_succ, pow_mul]
    positivity

lemma indicator_le_bonferroni_even (x j m : ℕ) :
    (if x = j then 1 else 0 : ℝ) ≤ bonferroniTerm x j (2 * m) := by
  rcases lt_trichotomy x j with h | h | h
  · rw [bonferroniTerm_of_lt _ _ _ h]
    simp [ne_of_lt h]
  · rw [bonferroniTerm_of_eq _ _ _ h]
    simp [h]
  · rw [bonferroniTerm_of_gt _ _ _ h, if_neg (ne_of_gt h)]
    norm_num [pow_mul]
    positivity

section Weighted

variable {Ω : ℕ → Type*} [∀ i, Fintype (Ω i)]
variable (p : ∀ i, Ω i → ℝ) (X : ∀ i, Ω i → ℕ)

def weightedMoment (i q : ℕ) : ℝ :=
  ∑ ω : Ω i, p i ω * (falling (X i ω) q : ℝ)

def weightedMass (i j : ℕ) : ℝ :=
  ∑ ω : Ω i, p i ω * if X i ω = j then 1 else 0

def weightedBonferroni (i j r : ℕ) : ℝ :=
  ∑ ω : Ω i, p i ω * bonferroniTerm (X i ω) j r

lemma weightedBonferroni_odd_le_mass (i j m : ℕ)
    (hp : ∀ ω, 0 ≤ p i ω) :
    weightedBonferroni p X i j (2 * m + 1) ≤ weightedMass p X i j := by
  apply Finset.sum_le_sum
  intro ω _
  exact mul_le_mul_of_nonneg_left (bonferroni_odd_le_indicator _ _ _) (hp _)

lemma weightedMass_le_bonferroni_even (i j m : ℕ)
    (hp : ∀ ω, 0 ≤ p i ω) :
    weightedMass p X i j ≤ weightedBonferroni p X i j (2 * m) := by
  apply Finset.sum_le_sum
  intro ω _
  exact mul_le_mul_of_nonneg_left (indicator_le_bonferroni_even _ _ _) (hp _)

lemma weightedBonferroni_eq (i j r : ℕ) :
    weightedBonferroni p X i j r =
      ∑ l ∈ Finset.range (r + 1),
        ((-1 : ℝ) ^ l / ((j.factorial : ℝ) * (l.factorial : ℝ))) *
          weightedMoment p X i (j + l) := by
  simp_rw [weightedBonferroni, bonferroniTerm, weightedMoment, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro ω _
  ring

lemma tendsto_weightedBonferroni (j r : ℕ) (nu : ℝ)
    (hMom : ∀ q, Tendsto (fun i => weightedMoment p X i q) atTop (𝓝 (nu ^ q))) :
    Tendsto (fun i => weightedBonferroni p X i j r) atTop
      (𝓝 (∑ l ∈ Finset.range (r + 1),
        ((-1 : ℝ) ^ l / ((j.factorial : ℝ) * (l.factorial : ℝ))) *
          nu ^ (j + l))) := by
  simp_rw [weightedBonferroni_eq]
  apply tendsto_finset_sum
  intro l _
  exact tendsto_const_nhds.mul (hMom (j + l))

lemma hasSum_poissonMassSeries (j : ℕ) (nu : ℝ) :
    HasSum (fun l : ℕ =>
      ((-1 : ℝ) ^ l / ((j.factorial : ℝ) * (l.factorial : ℝ))) *
        nu ^ (j + l))
      (Real.exp (-nu) * (nu ^ j / (j.factorial : ℝ))) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (-nu : ℝ))
  have h' := h.mul_left (nu ^ j / (j.factorial : ℝ))
  rw [← Real.exp_eq_exp_ℝ] at h'
  convert h' using 1
  · funext l
    rw [pow_add, neg_pow]
    ring
  · ring

lemma tendsto_weightedMass (j : ℕ) (nu : ℝ)
    (hp : ∀ᶠ i in atTop, ∀ ω, 0 ≤ p i ω)
    (hNorm : ∀ᶠ i in atTop, ∑ ω : Ω i, p i ω = 1)
    (hMom : ∀ q, 0 < q →
      Tendsto (fun i => weightedMoment p X i q) atTop (𝓝 (nu ^ q))) :
    Tendsto (fun i => weightedMass p X i j) atTop
      (𝓝 (Real.exp (-nu) * (nu ^ j / (j.factorial : ℝ)))) := by
  have hMomAll : ∀ q,
      Tendsto (fun i => weightedMoment p X i q) atTop (𝓝 (nu ^ q)) := by
    intro q
    by_cases hq : q = 0
    · subst q
      apply tendsto_const_nhds.congr'
      filter_upwards [hNorm] with i hi
      simpa [weightedMoment, falling] using! hi.symm
    · exact hMom q (Nat.pos_of_ne_zero hq)
  have hSeries := hasSum_poissonMassSeries j nu
  have hOddIndex : StrictMono (fun m : ℕ => (2 * m + 1) + 1) := by
    intro a b hab
    change 2 * a + 2 < 2 * b + 2
    exact Nat.add_lt_add_right
      ((Nat.mul_lt_mul_left (by omega : 0 < 2)).2 hab) 2
  have hEvenIndex : StrictMono (fun m : ℕ => 2 * m + 1) := by
    intro a b hab
    change 2 * a + 1 < 2 * b + 1
    exact Nat.add_lt_add_right
      ((Nat.mul_lt_mul_left (by omega : 0 < 2)).2 hab) 1
  have hOddPartial : Tendsto
      (fun m => ∑ l ∈ Finset.range ((2 * m + 1) + 1),
        ((-1 : ℝ) ^ l / ((j.factorial : ℝ) * (l.factorial : ℝ))) *
          nu ^ (j + l)) atTop
      (𝓝 (Real.exp (-nu) * (nu ^ j / (j.factorial : ℝ)))) :=
    hSeries.tendsto_sum_nat.comp hOddIndex.tendsto_atTop
  have hEvenPartial : Tendsto
      (fun m => ∑ l ∈ Finset.range (2 * m + 1),
        ((-1 : ℝ) ^ l / ((j.factorial : ℝ) * (l.factorial : ℝ))) *
          nu ^ (j + l)) atTop
      (𝓝 (Real.exp (-nu) * (nu ^ j / (j.factorial : ℝ)))) :=
    hSeries.tendsto_sum_nat.comp hEvenIndex.tendsto_atTop
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨m, hm⟩ := ((tendsto_order.1 hOddPartial).1 a ha).exists
    have hBonf := tendsto_weightedBonferroni p X j (2 * m + 1) nu hMomAll
    have hEventually := (tendsto_order.1 hBonf).1 a hm
    filter_upwards [hEventually, hp] with i hi hpi
    exact lt_of_lt_of_le hi (weightedBonferroni_odd_le_mass p X i j m hpi)
  · intro b hb
    obtain ⟨m, hm⟩ := ((tendsto_order.1 hEvenPartial).2 b hb).exists
    have hBonf := tendsto_weightedBonferroni p X j (2 * m) nu hMomAll
    have hEventually := (tendsto_order.1 hBonf).2 b hm
    filter_upwards [hEventually, hp] with i hi hpi
    exact lt_of_le_of_lt (weightedMass_le_bonferroni_even p X i j m hpi) hi

def weightedCDF (i j : ℕ) : ℝ :=
  ∑ ω : Ω i, p i ω * if X i ω ≤ j then 1 else 0

lemma weightedCDF_eq_sum_mass (i j : ℕ) :
    weightedCDF p X i j =
      ∑ k ∈ Finset.range (j + 1), weightedMass p X i k := by
  simp_rw [weightedCDF, weightedMass]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : X i ω ≤ j
  · rw [if_pos h, Finset.sum_eq_single (X i ω)]
    · simp
    · intro b hb hne
      simp [hne.symm]
    · simp [h]
  · rw [if_neg h]
    simp only [mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro b hb
    have hne : X i ω ≠ b := by
      intro heq
      apply h
      simpa [heq] using! (Finset.mem_range.1 hb)
    simp [hne]

lemma factorialMoments_to_poissonCDF_varying (nu : ℝ) (hnu : 0 ≤ nu)
    (hp : ∀ᶠ i in atTop, ∀ ω, 0 ≤ p i ω)
    (hNorm : ∀ᶠ i in atTop, ∑ ω : Ω i, p i ω = 1)
    (hMom : ∀ q, 0 < q →
      Tendsto (fun i => weightedMoment p X i q) atTop (𝓝 (nu ^ q)))
    (j : ℕ) :
    Tendsto (fun i => weightedCDF p X i j) atTop (𝓝 (poissonCDF nu j)) := by
  have hnu_abs : |nu| = nu := abs_of_nonneg hnu
  have hMomAbs : ∀ q, 0 < q →
      Tendsto (fun i => weightedMoment p X i q) atTop (𝓝 (|nu| ^ q)) := by
    intro q hq
    simpa [hnu_abs] using! hMom q hq
  have hMass : ∀ k, Tendsto (fun i => weightedMass p X i k) atTop
      (𝓝 (Real.exp (-nu) * (nu ^ k / (k.factorial : ℝ)))) := by
    intro k
    simpa [hnu_abs] using! tendsto_weightedMass p X k |nu| hp hNorm hMomAbs
  have hSum : Tendsto
      (fun i => ∑ k ∈ Finset.range (j + 1), weightedMass p X i k) atTop
      (𝓝 (∑ k ∈ Finset.range (j + 1),
        Real.exp (-nu) * (nu ^ k / (k.factorial : ℝ)))) := by
    apply tendsto_finset_sum
    intro k _
    exact hMass k
  convert hSum using 1
  · funext i
    exact weightedCDF_eq_sum_mass p X i j
  · simp [poissonCDF, Finset.mul_sum]

end Weighted

def graphWeight (M : NatSeq) (n : ℕ) (G : Graph n) : ℝ :=
  if G ∈ fixedGraphs n (M n) then
    1 / ((fixedGraphs n (M n)).card : ℝ)
  else 0

lemma weightedMoment_graphWeight
    (M : NatSeq) (X : (n : ℕ) → Graph n → ℕ) (n q : ℕ) :
    weightedMoment (graphWeight M) X n q =
      expectM n (M n) (fun G ↦ (falling (X n G) q : ℝ)) := by
  simp only [weightedMoment, expectM, graphWeight, ite_mul, zero_mul, Finset.sum_ite]
  rw [show (Finset.univ.filter fun x ↦ x ∈ fixedGraphs n (M n)) =
      fixedGraphs n (M n) by ext; simp]
  simp only [Finset.sum_const_zero, add_zero]
  rw [← Finset.mul_sum, div_eq_mul_inv]
  ring

lemma weightedCDF_graphWeight
    (M : NatSeq) (X : (n : ℕ) → Graph n → ℕ) (n j : ℕ) :
    weightedCDF (graphWeight M) X n j =
      probM n (M n) (fun G ↦ X n G ≤ j) := by
  simp only [weightedCDF, probM, graphWeight, ite_mul, zero_mul, Finset.sum_ite]
  rw [show (Finset.univ.filter fun x ↦ x ∈ fixedGraphs n (M n)) =
      fixedGraphs n (M n) by ext; simp]
  simp only [Finset.sum_const_zero, add_zero, mul_ite, mul_one, mul_zero,
    Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul]
  simp only [one_mul, div_eq_mul_inv]
  congr 4

lemma graphWeight_nonneg (M : NatSeq) (n : ℕ) (G : Graph n) :
    0 ≤ graphWeight M n G := by
  simp only [graphWeight]
  split <;> positivity

lemma graphWeight_sum_eq_one
    (hEnum : FiniteEnumerationStatement) (M : NatSeq) {n : ℕ}
    (hn : M n ≤ capacity n) :
    ∑ G : Graph n, graphWeight M n G = 1 := by
  calc
    ∑ G : Graph n, graphWeight M n G =
        weightedMoment (graphWeight M) (fun _ _ ↦ 0) n 0 := by
          simp [weightedMoment, falling]
    _ = expectM n (M n) (fun G ↦ (falling (0 : ℕ) 0 : ℝ)) :=
      weightedMoment_graphWeight M (fun _ _ ↦ 0) n 0
    _ = 1 := by
      simpa [falling] using! hEnum.1 n (M n) hn

lemma poissonStatement_factorial_moment_part
    (hEnum : FiniteEnumerationStatement) :
    ∀ (M : NatSeq) (X : (n : ℕ) → Graph n → ℕ) (nu : ℝ),
      admissible M → 0 ≤ nu →
      (∀ q : ℕ, 0 < q → Tendsto
        (fun n ↦ expectM n (M n) (fun G ↦ (falling (X n G) q : ℝ)))
        atTop (𝓝 (nu ^ q))) →
      ∀ j : ℕ, Tendsto (fun n ↦ probM n (M n) (fun G ↦ X n G ≤ j))
        atTop (𝓝 (poissonCDF nu j)) := by
  intro M X nu hM hnu hMom j
  have hp : ∀ᶠ n in atTop, ∀ G, 0 ≤ graphWeight M n G :=
    Filter.Eventually.of_forall fun n G ↦ graphWeight_nonneg M n G
  have hNorm : ∀ᶠ n in atTop, ∑ G : Graph n, graphWeight M n G = 1 := by
    filter_upwards [hM] with n hn
    exact graphWeight_sum_eq_one hEnum M hn
  have hMom' : ∀ q, 0 < q →
      Tendsto (fun n ↦ weightedMoment (graphWeight M) X n q)
        atTop (𝓝 (nu ^ q)) := by
    intro q hq
    exact (hMom q hq).congr'
      (Filter.Eventually.of_forall fun n ↦ (weightedMoment_graphWeight M X n q).symm)
  exact
    (factorialMoments_to_poissonCDF_varying
      (graphWeight M) X nu hnu hp hNorm hMom' j).congr'
      (Filter.Eventually.of_forall fun n ↦ weightedCDF_graphWeight M X n j)

section SubsequenceAdapter

variable (M ns : NatSeq)
variable (X : (i : ℕ) → Graph (ns i) → ℕ)

lemma weightedMoment_graphWeight_subsequence (i q : ℕ) :
    weightedMoment (fun i G ↦ graphWeight M (ns i) G) X i q =
      expectM (ns i) (M (ns i)) (fun G ↦ (falling (X i G) q : ℝ)) := by
  simp only [weightedMoment, expectM, graphWeight, ite_mul, zero_mul, Finset.sum_ite]
  rw [show (Finset.univ.filter fun G ↦ G ∈ fixedGraphs (ns i) (M (ns i))) =
      fixedGraphs (ns i) (M (ns i)) by ext; simp]
  simp only [Finset.sum_const_zero, add_zero]
  rw [← Finset.mul_sum, div_eq_mul_inv]
  ring

lemma weightedCDF_graphWeight_subsequence (i j : ℕ) :
    weightedCDF (fun i G ↦ graphWeight M (ns i) G) X i j =
      probM (ns i) (M (ns i)) (fun G ↦ X i G ≤ j) := by
  simp only [weightedCDF, probM, graphWeight, ite_mul, zero_mul, Finset.sum_ite]
  rw [show (Finset.univ.filter fun G ↦ G ∈ fixedGraphs (ns i) (M (ns i))) =
      fixedGraphs (ns i) (M (ns i)) by ext; simp]
  simp only [Finset.sum_const_zero, add_zero, mul_ite, mul_one, mul_zero,
    Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, one_mul, div_eq_mul_inv]
  congr 4

lemma factorialMoments_to_poissonCDF_subsequence
    (hEnum : FiniteEnumerationStatement)
    (hM : admissible M) (hns : Tendsto ns atTop atTop)
    (nu : ℝ) (hnu : 0 ≤ nu)
    (hMom : ∀ q : ℕ, 0 < q → Tendsto
      (fun i ↦ expectM (ns i) (M (ns i))
        (fun G ↦ (falling (X i G) q : ℝ))) atTop (nhds (nu ^ q)))
    (j : ℕ) :
    Tendsto (fun i ↦ probM (ns i) (M (ns i)) (fun G ↦ X i G ≤ j))
      atTop (nhds (poissonCDF nu j)) := by
  let p : (i : ℕ) → Graph (ns i) → ℝ :=
    fun i G ↦ graphWeight M (ns i) G
  have hp : ∀ᶠ i in atTop, ∀ G, 0 ≤ p i G :=
    Filter.Eventually.of_forall fun i G ↦ graphWeight_nonneg M (ns i) G
  have hcap : ∀ᶠ i in atTop, M (ns i) ≤ capacity (ns i) :=
    hns.eventually hM
  have hNorm : ∀ᶠ i in atTop, ∑ G : Graph (ns i), p i G = 1 := by
    filter_upwards [hcap] with i hi
    exact graphWeight_sum_eq_one hEnum M hi
  have hMom' : ∀ q, 0 < q →
      Tendsto (fun i ↦ weightedMoment p X i q) atTop (nhds (nu ^ q)) := by
    intro q hq
    exact (hMom q hq).congr'
      (Filter.Eventually.of_forall fun i ↦
        (weightedMoment_graphWeight_subsequence M ns X i q).symm)
  exact (factorialMoments_to_poissonCDF_varying p X nu hnu hp hNorm hMom' j).congr'
    (Filter.Eventually.of_forall fun i ↦ weightedCDF_graphWeight_subsequence M ns X i j)

end SubsequenceAdapter

lemma poissonStatement_fixedDensity_part
    (hEnum : FiniteEnumerationStatement) (hRate : RateStatement)
    (hTuple : TupleEstimatesStatement) :
    ∀ (M : NatSeq) (lam : ℝ), admissible M → 0 < lam → lam ≠ 1 →
      Tendsto (degree M) atTop (nhds lam) → ∀ (ns h : NatSeq) (ell : ℝ),
      StrictMono ns →
      Tendsto (fun j ↦ (h j : ℝ) - center M (ns j)) atTop (nhds ell) →
      ∀ q : ℕ, Tendsto (fun j ↦ countCDF (ns j) (M (ns j)) (h j) q)
        atTop (nhds (poissonCDF (latticeRate lam ell) q)) := by
  intro M lam hM hlam hlam1 hdegree ns h ell hns hoffset q
  let X : (j : ℕ) → Graph (ns j) → ℕ := fun j G ↦ treeCountGE G (h j)
  have hMom := fixedDensity_factorialMoments hEnum hRate hTuple M ns h lam ell
    hM hlam hlam1 hdegree hns hoffset
  have hCDF := factorialMoments_to_poissonCDF_subsequence M ns X hEnum hM
    hns.tendsto_atTop (latticeRate lam ell)
    (latticeRate_pos hRate lam ell hlam hlam1).le hMom q
  simpa [X, countCDF] using! hCDF

lemma poissonStatement_barelyCritical_part
    (hEnum : FiniteEnumerationStatement) (hRate : RateStatement)
    (hTuple : TupleEstimatesStatement) (hSums : AnalyticSumsStatement) :
    ∀ M : NatSeq, bareSub M ∨ bareSuper M → ∀ (r : ℝ) (q : ℕ),
      Tendsto (fun n ↦ countCDF n (M n) ⌈nearThreshold M n r⌉₊ q)
        atTop (nhds (poissonCDF (nearRate r) q)) := by
  intro M hbare r q
  let X : (n : ℕ) → Graph n → ℕ :=
    fun n G ↦ treeCountGE G (nearHeight M r n)
  have hMom := barelyCritical_factorialMoments hEnum hRate hTuple hSums M hbare r
  have hCDF := poissonStatement_factorial_moment_part hEnum M X (nearRate r)
    (bare_admissible hbare) (nearRate_pos r).le hMom q
  simpa [X, countCDF, nearHeight] using! hCDF

theorem result : FiniteEnumerationStatement →
    RateStatement →
    TupleEstimatesStatement →
    AnalyticSumsStatement →
    PoissonStatement := by
  intro hEnum hRate hTuple hSums
  exact ⟨
    poissonStatement_factorial_moment_part hEnum,
    poissonStatement_fixedDensity_part hEnum hRate hTuple,
    poissonStatement_barelyCritical_part hEnum hRate hTuple hSums
  ⟩

end

end Erdos745.WrapUp.Proofs.W06_POISSON
