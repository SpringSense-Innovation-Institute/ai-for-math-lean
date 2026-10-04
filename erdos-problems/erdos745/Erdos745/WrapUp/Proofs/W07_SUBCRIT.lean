module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W07_Subcritical

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section
namespace Erdos745.WrapUp.Proofs.W07_SUBCRIT

open scoped BigOperators Sym2
open Finset
open Erdos745.WrapUp.Proofs.Internal.W07_SUBCRIT_Finite
open Erdos745.WrapUp.Proofs.Internal.W07_SUBCRIT_Cover

noncomputable section
attribute [local instance] Classical.propDecidable

private lemma edge_card_le_capacity (n : ℕ) :
    Fintype.card (Edge n) ≤ capacity n := by
  let f : Edge n → {a : Sym2 (Fin n) // ¬ a.IsDiag} := fun e =>
    ⟨s(e.1.1, e.1.2), by simpa [Sym2.mk_isDiag_iff] using! ne_of_lt e.2⟩
  have hf : Function.Injective f := by
    intro e e' h
    apply Subtype.ext
    simp only [f, Subtype.mk.injEq] at h
    rw [Sym2.eq_iff] at h
    rcases h with h | h
    · exact Prod.ext h.1 h.2
    · have hback : e.1.2 < e.1.1 := by
        rw [h.2, h.1]
        exact e'.2
      exact (lt_asymm e.2 hback).elim
  calc
    Fintype.card (Edge n) ≤ Fintype.card {a : Sym2 (Fin n) // ¬ a.IsDiag} :=
      Fintype.card_le_of_injective f hf
    _ = capacity n := by
      simpa only [capacity, Fintype.card_fin] using!
        (Sym2.card_subtype_not_diag (α := Fin n))

private lemma graph_card_le_capacity {n : ℕ} (F : Graph n) :
    F.card ≤ capacity n := by
  calc
    F.card ≤ (univ : Finset (Edge n)).card := card_le_card (by simp)
    _ = Fintype.card (Edge n) := card_univ
    _ ≤ capacity n := edge_card_le_capacity n

private lemma card_inter_eq_right_iff {n : ℕ} (G F : Graph n) :
    (G ∩ F).card = F.card ↔ F ⊆ G := by
  constructor
  · intro h
    have heq : G ∩ F = F :=
      eq_of_subset_of_card_le inter_subset_right (by simp [h])
    exact inter_eq_right.mp heq
  · intro h
    exact congrArg card (inter_eq_right.mpr h)

private lemma empty_pattern_prob
    (hEnum : FiniteEnumerationStatement) {n M : ℕ}
    (hM : M ≤ capacity n) :
    probM n M (patternEvent ∅ ∅) = 1 := by
  have h := hEnum.1 n M hM
  unfold probM
  rw [show (fixedGraphs n M).filter (patternEvent ∅ ∅) = fixedGraphs n M by
    ext G
    simp [patternEvent]]
  simpa [expectM] using! h

lemma prescribed_probability
    (hEnum : FiniteEnumerationStatement) {n M : ℕ}
    (hM : M ≤ capacity n) (F : Graph n) :
    probM n M (fun G => F ⊆ G) =
      (M.choose F.card : ℝ) / (capacity n).choose F.card := by
  have hbase : 0 < probM n M (patternEvent ∅ ∅) := by
    rw [empty_pattern_prob hEnum hM]
    norm_num
  have h := hEnum.2.1 n M ∅ ∅ F hM (by simp) (by simp) hbase F.card
  have hF : F.card ≤ capacity n := graph_card_le_capacity F
  rw [show conditionalProbM n M (patternEvent ∅ ∅)
      (fun G => (G ∩ F).card = F.card) =
      probM n M (fun G => F ⊆ G) by
    simp only [conditionalProbM, empty_pattern_prob hEnum hM, div_one]
    apply congrArg (probM n M)
    funext G
    apply propext
    simp only [patternEvent, empty_subset, disjoint_empty_left, true_and, and_self,
      card_inter_eq_right_iff]] at h
  simpa [hypergeomMass, hM, hF] using! h

private lemma rpow_quarter_neg_three (e : ℝ) (he : 0 < e) :
    Real.rpow (e / 4) (- (3 : ℝ)) = 64 / e ^ 3 := by
  have hp : 0 ≤ e / 4 := le_of_lt (div_pos he (by norm_num))
  have hpow : Real.rpow (e / 4) (3 : ℝ) = (e / 4) ^ (3 : ℕ) := by
    exact Real.rpow_natCast (e / 4) 3
  calc
    Real.rpow (e / 4) (- (3 : ℝ)) =
        (Real.rpow (e / 4) (3 : ℝ))⁻¹ := Real.rpow_neg hp (3 : ℝ)
    _ = ((e / 4) ^ (3 : ℕ))⁻¹ := congrArg Inv.inv hpow
    _ = 64 / e ^ 3 := by
      field_simp
      ring

lemma analytic_quadratic_sum
    (hSums : AnalyticSumsStatement) :
    ∃ C : ℝ, 0 < C ∧ ∀ e : ℝ, 0 < e → e ≤ 1 →
      Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ 2) *
        Real.exp (-(e / 4) * (k + 1))) ∧
      (∑' k : ℕ, (((k + 1 : ℕ) : ℝ) ^ 2) *
        Real.exp (-(e / 4) * (k + 1))) ≤ C / e ^ 3 := by
  obtain ⟨C, hC, hbound⟩ := hSums.2.1 (2 : ℝ) (by norm_num)
  refine ⟨64 * C, mul_pos (by norm_num) hC, ?_⟩
  intro e he he_one
  have hu : 0 < e / 4 := div_pos he (by norm_num)
  have hu_one : e / 4 ≤ 1 := by linarith
  obtain ⟨hsum, hle⟩ := hbound (e / 4) hu hu_one
  have hfun :
      (fun k : ℕ => Real.rpow ((k + 1 : ℕ) : ℝ) (2 : ℝ) *
        Real.exp (-(e / 4) * (k + 1))) =
      (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ 2) *
        Real.exp (-(e / 4) * (k + 1))) := by
    funext k
    have hk : Real.rpow ((k + 1 : ℕ) : ℝ) (2 : ℝ) =
        (((k + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
      exact Real.rpow_natCast ((k + 1 : ℕ) : ℝ) 2
    rw [hk]
  rw [hfun] at hsum hle
  refine ⟨hsum, ?_⟩
  calc
    (∑' k : ℕ, (((k + 1 : ℕ) : ℝ) ^ 2) *
        Real.exp (-(e / 4) * (k + 1))) ≤
        C * Real.rpow (e / 4) (-(2 : ℝ) - 1) := hle
    _ = C * (64 / e ^ 3) := by
      rw [show -(2 : ℝ) - 1 = -(3 : ℝ) by ring,
        rpow_quarter_neg_three e he]
    _ = (64 * C) / e ^ 3 := by ring

private lemma contraction_real (x m e : ℝ) (hx : 4 ≤ x)
    (heps : 4 / x ≤ e) (hdeg : 2 * m / x ≤ 1 - e) :
    x * (m / (x * (x - 1) / 2)) ≤ 1 - e / 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hxm1 : 0 < x - 1 := by linarith
  have hD : 0 < x * (x - 1) / 2 := by positivity
  have hd : 2 * m ≤ x * (1 - e) := by
    simpa [mul_comm] using! (div_le_iff₀ hx0).mp hdeg
  have hdx := mul_le_mul_of_nonneg_left hd hx0.le
  have he4 : 4 ≤ e * x := (div_le_iff₀ hx0).mp heps
  rw [show x * (m / (x * (x - 1) / 2)) =
      (x * m) / (x * (x - 1) / 2) by ring]
  apply (div_le_iff₀ hD).2
  nlinarith

lemma endpoint_contraction (n M : ℕ) (e : ℝ) (hn : 2 ≤ n)
    (heps : 4 / (n : ℝ) ≤ e) (hdeg : degreeAt n M ≤ 1 - e) :
    e ≤ 1 ∧ 4 ≤ n ∧
      (n : ℝ) * ((M : ℝ) / (capacity n : ℝ)) ≤ 1 - e / 2 := by
  have hn0 : 0 < (n : ℝ) := by positivity
  have hd0 : 0 ≤ degreeAt n M := by
    unfold degreeAt
    positivity
  have he_one : e ≤ 1 := by linarith
  have h4r : (4 : ℝ) ≤ n := (div_le_one hn0).mp (heps.trans he_one)
  have h4n : 4 ≤ n := by exact_mod_cast h4r
  refine ⟨he_one, h4n, ?_⟩
  simpa [capacity, Nat.cast_choose_two, degreeAt] using!
    (contraction_real (n : ℝ) (M : ℝ) e (by exact_mod_cast h4n)
      heps hdeg)

lemma finite_geometric_le_quadratic_sum (n : ℕ) (e : ℝ)
    (he : 0 < e) (he_one : e ≤ 1) :
    (∑ v ∈ Icc 4 n, (v : ℝ) ^ 2 * (1 - e / 4) ^ v) ≤
      ∑' k : ℕ, (((k + 1 : ℕ) : ℝ) ^ 2) *
        Real.exp (-(e / 4) * (k + 1)) := by
  let f : ℕ → ℝ := fun v => (v : ℝ) ^ 2 * Real.exp (-(e / 4) * v)
  have hu : 0 < e / 4 := div_pos he (by norm_num)
  have hr : 0 ≤ 1 - e / 4 := by linarith
  have hbase : 1 - e / 4 ≤ Real.exp (-(e / 4)) :=
    Real.one_sub_le_exp_neg (e / 4)
  have hterm : ∀ v : ℕ,
      (v : ℝ) ^ 2 * (1 - e / 4) ^ v ≤ f v := by
    intro v
    have hp := pow_le_pow_left₀ hr hbase v
    have hexp : Real.exp (-(e / 4)) ^ v = Real.exp (-(e / 4) * v) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hexp] at hp
    exact mul_le_mul_of_nonneg_left hp (sq_nonneg (v : ℝ))
  have hfull : Summable f := by
    simpa [f, neg_mul] using!
      (Real.summable_pow_mul_exp_neg_nat_mul (2 : ℕ) hu)
  have hfinite : (∑ v ∈ Icc 4 n, f v) ≤ ∑' v : ℕ, f v :=
    hfull.sum_le_tsum (Icc 4 n) (by
      intro v hv
      exact mul_nonneg (sq_nonneg (v : ℝ)) (Real.exp_pos _).le)
  have htsum : (∑' v : ℕ, f v) =
      ∑' k : ℕ, (((k + 1 : ℕ) : ℝ) ^ 2) *
        Real.exp (-(e / 4) * (k + 1)) := by
    have h := hfull.sum_add_tsum_nat_add 1
    simpa [f, Nat.add_comm, add_comm] using! h.symm
  calc
    (∑ v ∈ Icc 4 n, (v : ℝ) ^ 2 * (1 - e / 4) ^ v) ≤
        ∑ v ∈ Icc 4 n, f v := by
      exact sum_le_sum fun v _ => hterm v
    _ ≤ ∑' v : ℕ, f v := hfinite
    _ = _ := htsum

abbrev BicyclicWitnessBound :=
  Erdos745.WrapUp.Proofs.Internal.W07_SUBCRIT_Finite.BicyclicWitnessBound

theorem close_from_bicyclic_witness_bound
    (hBound : BicyclicWitnessBound)
    (hSums : AnalyticSumsStatement) : SubcriticalExclusionStatement := by
  obtain ⟨C, hC, hsum⟩ := analytic_quadratic_sum hSums
  refine ⟨8 * C, mul_pos (by norm_num) hC, ?_⟩
  intro n M e hn hM he heps hdeg
  obtain ⟨he_one, _, _⟩ :=
    endpoint_contraction n M e hn heps hdeg
  have hfinite := finite_geometric_le_quadratic_sum n e he he_one
  have hraw := hBound n M e hn hM he heps hdeg
  have hn0 : 0 < (n : ℝ) := by positivity
  have he3 : 0 < e ^ 3 := pow_pos he 3
  calc
    probM n M (fun G => ¬ noComplex G) ≤
        8 / (n : ℝ) *
          ∑ v ∈ Icc 4 n, (v : ℝ) ^ 2 * (1 - e / 4) ^ v := hraw
    _ ≤ 8 / (n : ℝ) *
        (∑' k : ℕ, (((k + 1 : ℕ) : ℝ) ^ 2) *
          Real.exp (-(e / 4) * (k + 1))) := by
      exact mul_le_mul_of_nonneg_left hfinite (by positivity)
    _ ≤ 8 / (n : ℝ) * (C / e ^ 3) := by
      exact mul_le_mul_of_nonneg_left (hsum e he he_one).2 (by positivity)
    _ = (8 * C) / ((n : ℝ) * e ^ 3) := by
      field_simp

/-- Exact public W07 producer; the finite core cover is discharged internally. -/
theorem result :
    FiniteEnumerationStatement → AnalyticSumsStatement →
    SubcriticalExclusionStatement := by
  intro hEnum hSums
  exact close_from_bicyclic_witness_bound
    (bicyclicWitnessBound_of_cover hEnum coreFamily coreFamily_isCover) hSums

end
end Erdos745.WrapUp.Proofs.W07_SUBCRIT
