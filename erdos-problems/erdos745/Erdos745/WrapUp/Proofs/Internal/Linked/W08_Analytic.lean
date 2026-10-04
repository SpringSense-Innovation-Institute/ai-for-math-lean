module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W04_Foundation
public import Erdos745.WrapUp.Proofs.Internal.Linked.W04_Envelope
public import Erdos745.WrapUp.Proofs.Internal.Linked.W06_P03

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


namespace Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Finite

noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

def treeMomentOne (n M k : ℕ) : ℝ :=
  tupleMoment n M 1 (fun _ => k)

def cyclicFormula (n M k : ℕ) : ℝ := componentFormula n M k k

def excessFormula (n M k r : ℕ) : ℝ := componentFormula n M k (k + r)

def treeTailOne (n M power : ℕ) (B : ℝ) : ℝ :=
  ∑ k : Fin (n + 1),
    if 0 < k.val ∧ B * Real.log n < (k.val : ℝ) then
      (k.val : ℝ) ^ power * treeMomentOne n M k.val else 0

lemma tupleTail_one_eq (n M power : ℕ) (B : ℝ) :
    tupleTail n M 1 power B = treeTailOne n M power B := by
  unfold tupleTail treeTailOne treeMomentOne
  let e : (Fin 1 → Fin (n + 1)) ≃ Fin (n + 1) :=
    Equiv.funUnique (Fin 1) (Fin (n + 1))
  refine Fintype.sum_equiv e _ _ ?_
  intro k
  have hk : (fun i : Fin 1 => (k i).val) = fun _ => (k 0).val := by
    funext i
    fin_cases i
    rfl
  have hp : (∀ i : Fin 1, 0 < (k i).val) ↔ 0 < (k 0).val := by
    constructor
    · intro h; exact h 0
    · intro h i; fin_cases i; exact h
  have he : (∃ i : Fin 1, B * Real.log n < ((k i).val : ℝ)) ↔
      B * Real.log n < ((k 0).val : ℝ) := by
    constructor
    · rintro ⟨i, hi⟩; fin_cases i; exact hi
    · intro h; exact ⟨0, h⟩
  have hdef : (default : Fin 1) = 0 := Subsingleton.elim _ _
  simp only [e, Equiv.funUnique_apply, Fin.prod_univ_one, hk, hp, he, hdef]

lemma enum_normalization (hF : FiniteEnumerationStatement) :
    ∀ n M : ℕ, M ≤ capacity n → expectM n M (fun _ => 1) = 1 := by
  rcases hF with ⟨h, _⟩
  exact h

lemma enum_component (hF : FiniteEnumerationStatement) :
    ∀ n M k e : ℕ, M ≤ capacity n →
      expectM n M (fun G => (componentCount G k e : ℝ)) =
        componentFormula n M k e := by
  rcases hF with ⟨_, _, _, _, h, _⟩
  exact h

lemma enum_tuple (hF : FiniteEnumerationStatement) :
    ∀ (n M q : ℕ) (ks : Fin q → ℕ), M ≤ capacity n →
      tupleMoment n M q ks = tupleFormula n M q ks := by
  rcases hF with ⟨_, _, _, _, _, h, _⟩
  exact h

lemma enum_cayley (hF : FiniteEnumerationStatement) :
    ∀ k : ℕ, 0 < k → connectedCount k (k - 1) = cayley k := by
  rcases hF with ⟨_, _, _, _, _, _, _, _, h, _⟩
  exact h

lemma enum_unicyclic_exact (hF : FiniteEnumerationStatement) :
    ∀ k : ℕ, 3 ≤ k → (connectedCount k k : ℝ) =
      ((k - 1).factorial : ℝ) / 2 *
        (Finset.range (k - 2)).sum (fun m =>
          (k : ℝ) ^ m / (m.factorial : ℝ)) := by
  rcases hF with ⟨_, _, _, _, _, _, _, _, _, h, _⟩
  exact h

lemma enum_unicyclic_bound (hF : FiniteEnumerationStatement) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 3 ≤ k →
      (connectedCount k k : ℝ) ≤
        C * Real.rpow (k : ℝ) ((k : ℝ) - 1 / 2) := by
  rcases hF with ⟨_, _, _, _, _, _, _, _, _, _, _, h, _⟩
  exact h

lemma expectM_nonneg {n M : ℕ} {f : Graph n → ℝ}
    (hf : ∀ G, 0 ≤ f G) : 0 ≤ expectM n M f := by
  unfold expectM
  exact div_nonneg (Finset.sum_nonneg fun G _ => hf G) (by positivity)

lemma expectM_sum {ι : Type*} [Fintype ι] {n M : ℕ}
    (f : ι → Graph n → ℝ) :
    expectM n M (fun G => ∑ i, f i G) =
      ∑ i, expectM n M (f i) := by
  unfold expectM
  rw [Finset.sum_comm]
  simp only [Finset.sum_div]

lemma expectM_finset_sum {ι : Type*} {s : Finset ι} {n M : ℕ}
    (f : ι → Graph n → ℝ) :
    expectM n M (fun G => ∑ i ∈ s, f i G) =
      ∑ i ∈ s, expectM n M (f i) := by
  unfold expectM
  rw [Finset.sum_comm]
  simp only [Finset.sum_div]

private lemma component_card_le {n : ℕ} (G : Graph n)
    {S : Finset (Fin n)} (hS : S ∈ components G) : S.card ≤ n := by
  exact (Finset.card_le_univ S).trans_eq (Fintype.card_fin n)

lemma unicyclicMass_eq_componentCount {n : ℕ} (G : Graph n) :
    unicyclicMass G =
      ∑ k ∈ Finset.range (n + 1),
        (k : ℝ) * (componentCount G k k : ℝ) := by
  unfold unicyclicMass componentCount isUnicyclic
  simp only [and_assoc, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  have hk : S.card ∈ Finset.range (n + 1) := by
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using! component_card_le G hS
  by_cases hcycle : edgesInside G S = S.card
  · simp only [hcycle, and_true]
    rw [Finset.sum_eq_single S.card]
    · simp [hS]
    · intro b hb hne
      simp [Ne.symm hne]
    · exact fun hnot => (hnot hk).elim
  · simp [hcycle]
    symm
    apply Finset.sum_eq_zero
    intro k hk'
    by_cases hcard : S.card = k
    · subst k
      simp [hcycle]
    · simp [hcard]

lemma expect_unicyclicMass_eq (hF : FiniteEnumerationStatement)
    {n M : ℕ} (hM : M ≤ capacity n) :
    expectM n M unicyclicMass =
      ∑ k ∈ Finset.range (n + 1), (k : ℝ) * cyclicFormula n M k := by
  rw [show expectM n M unicyclicMass = expectM n M
      (fun G => ∑ k ∈ Finset.range (n + 1),
        (k : ℝ) * (componentCount G k k : ℝ)) by
    apply congrArg (expectM n M)
    funext G
    exact unicyclicMass_eq_componentCount G]
  rw [expectM_finset_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show expectM n M (fun G => (k : ℝ) * (componentCount G k k : ℝ)) =
      (k : ℝ) * expectM n M (fun G => (componentCount G k k : ℝ)) by
    unfold expectM
    rw [← Finset.mul_sum]
    ring]
  rw [enum_component hF n M k k hM]
  rfl

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
    · have hback : e.1.2 < e.1.1 := by rw [h.2, h.1]; exact e'.2
      exact (lt_asymm e.2 hback).elim
  calc
    Fintype.card (Edge n) ≤ Fintype.card {a : Sym2 (Fin n) // ¬ a.IsDiag} :=
      Fintype.card_le_of_injective f hf
    _ = capacity n := by
      simpa only [capacity, Fintype.card_fin] using!
        (Sym2.card_subtype_not_diag (α := Fin n))

private lemma graph_card_le_capacity {n : ℕ} (G : Graph n) :
    G.card ≤ capacity n := by
  calc
    G.card ≤ (Finset.univ : Finset (Edge n)).card := Finset.card_le_card (by simp)
    _ = Fintype.card (Edge n) := Finset.card_univ
    _ ≤ capacity n := edge_card_le_capacity n

lemma smallComplexCount_eq_componentCount {n : ℕ} (G : Graph n) (h : ℕ) :
    (smallComplexCount G h : ℝ) =
      ∑ k ∈ Finset.range (n + 1),
        ∑ r ∈ Finset.Icc 1 (capacity n),
          if k < h then (componentCount G k (k + r) : ℝ) else 0 := by
  unfold smallComplexCount componentCount
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]
  symm
  calc
    (∑ k ∈ Finset.range (n + 1),
      ∑ r ∈ Finset.Icc 1 (capacity n),
        if k < h then
          ∑ S ∈ components G, if S.card = k ∧ edgesInside G S = k + r then (1 : ℝ) else 0
        else 0) =
        ∑ k ∈ Finset.range (n + 1),
          ∑ r ∈ Finset.Icc 1 (capacity n),
            ∑ S ∈ components G,
              if k < h ∧ S.card = k ∧ edgesInside G S = k + r then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hkh : k < h <;> simp [hkh]
    _ = ∑ r ∈ Finset.Icc 1 (capacity n), ∑ S ∈ components G,
        ∑ k ∈ Finset.range (n + 1),
          if k < h ∧ S.card = k ∧ edgesInside G S = k + r then (1 : ℝ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_comm]
    _ = ∑ S ∈ components G, ∑ r ∈ Finset.Icc 1 (capacity n),
        ∑ k ∈ Finset.range (n + 1),
          if k < h ∧ S.card = k ∧ edgesInside G S = k + r then (1 : ℝ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ S ∈ components G, ∑ k ∈ Finset.range (n + 1),
        ∑ r ∈ Finset.Icc 1 (capacity n),
          if k < h ∧ S.card = k ∧ edgesInside G S = k + r then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [Finset.sum_comm]
    _ = ∑ S ∈ components G, if S.card < h ∧ S.card < edgesInside G S then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      have hk : S.card ∈ Finset.range (n + 1) := by
        simpa only [Finset.mem_range, Nat.lt_succ_iff] using! component_card_le G hS
      by_cases hc : S.card < h ∧ S.card < edgesInside G S
      · let r := edgesInside G S - S.card
        have hr : 1 ≤ r := by dsimp [r]; omega
        have hedge : edgesInside G S ≤ capacity n := by
          exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
            (graph_card_le_capacity G)
        have hrCap : r ≤ capacity n := by dsimp [r]; omega
        have hrmem : r ∈ Finset.Icc 1 (capacity n) :=
          Finset.mem_Icc.mpr ⟨hr, hrCap⟩
        rw [Finset.sum_eq_single S.card]
        · rw [Finset.sum_eq_single r]
          · simp [hc, r, Nat.add_sub_of_le (Nat.le_of_lt hc.2)]
          · intro b hb hne
            by_cases heq : edgesInside G S = S.card + b
            · have : b = r := by dsimp [r]; omega
              exact (hne this).elim
            · simp [heq]
          · exact fun hnot => (hnot hrmem).elim
        · intro b hb hne
          simp [Ne.symm hne]
        · exact fun hnot => (hnot hk).elim
      · simp only [if_neg hc]
        apply Finset.sum_eq_zero
        intro k hk'
        by_cases hSk : S.card = k
        · subst k
          by_cases hlt : S.card < h
          · apply Finset.sum_eq_zero
            intro r hr
            have hnedge : ¬ edgesInside G S = S.card + r := by
              intro he
              apply hc
              exact ⟨hlt, by have := (Finset.mem_Icc.mp hr).1; omega⟩
            simp [hlt, hnedge]
          · simp [hlt]
        · simp [hSk]

lemma expect_smallComplexCount_eq (hF : FiniteEnumerationStatement)
    {n M h : ℕ} (hM : M ≤ capacity n) :
    expectM n M (fun G => (smallComplexCount G h : ℝ)) =
      ∑ k ∈ Finset.range (n + 1),
        ∑ r ∈ Finset.Icc 1 (capacity n),
          if k < h then excessFormula n M k r else 0 := by
  rw [show expectM n M (fun G => (smallComplexCount G h : ℝ)) =
      expectM n M (fun G => ∑ k ∈ Finset.range (n + 1),
        ∑ r ∈ Finset.Icc 1 (capacity n),
          if k < h then (componentCount G k (k + r) : ℝ) else 0) by
    apply congrArg (expectM n M)
    funext G
    exact smallComplexCount_eq_componentCount G h]
  rw [expectM_finset_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [expectM_finset_sum]
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs with hkh
  · exact enum_component hF n M k (k + r) hM
  · simp [expectM]

lemma componentFormula_nonneg (n M k e : ℕ) :
    0 ≤ componentFormula n M k e := by
  unfold componentFormula
  split_ifs <;> positivity

lemma cyclicFormula_nonneg (n M k : ℕ) : 0 ≤ cyclicFormula n M k :=
  componentFormula_nonneg _ _ _ _

lemma expect_unicyclicMass_nonneg (n M : ℕ) :
    0 ≤ expectM n M unicyclicMass := by
  apply expectM_nonneg
  intro G
  unfold unicyclicMass
  exact Finset.sum_nonneg fun S _ => by split_ifs <;> positivity

lemma expect_smallComplexCount_nonneg (n M h : ℕ) :
    0 ≤ expectM n M (fun G => (smallComplexCount G h : ℝ)) := by
  apply expectM_nonneg
  intro G
  positivity

lemma probM_le_expectM_of_indicator
    (hF : FiniteEnumerationStatement) {n M : ℕ} (hM : M ≤ capacity n)
    (A : Graph n → Prop) (f : Graph n → ℝ)
    (hf : ∀ G, 0 ≤ f G) (hA : ∀ G, A G → 1 ≤ f G) :
    probM n M A ≤ expectM n M f := by
  have hnorm := enum_normalization hF n M hM
  unfold probM expectM at hnorm ⊢
  have hcardpos : 0 < ((fixedGraphs n M).card : ℝ) := by
    by_contra hz
    have hz' : ((fixedGraphs n M).card : ℝ) = 0 := le_antisymm (le_of_not_gt hz) (by positivity)
    simp [hz'] at hnorm
  have hnum : (((fixedGraphs n M).filter A).card : ℝ) ≤
      ∑ G ∈ fixedGraphs n M, f G := by
    calc
    (((fixedGraphs n M).filter A).card : ℝ) =
        ∑ G ∈ fixedGraphs n M, if A G then 1 else 0 := by
      norm_cast
      simp
    _ ≤ ∑ G ∈ fixedGraphs n M, f G := by
      apply Finset.sum_le_sum
      intro G hG
      split_ifs with h
      · exact hA G h
      · exact hf G
  exact div_le_div_of_nonneg_right hnum hcardpos.le

lemma cyclicAbove_le_unicyclicMass {n : ℕ} (G : Graph n) {h : ℝ}
    (hh : 0 < h) (hcyc : cyclicAbove G h) : h ≤ unicyclicMass G := by
  rcases hcyc with ⟨S, hS, hU, hcard⟩
  unfold unicyclicMass
  calc
    h ≤ (S.card : ℝ) := hcard
    _ = if isUnicyclic G S then (S.card : ℝ) else 0 := by simp [hU]
    _ ≤ ∑ T ∈ components G, if isUnicyclic G T then (T.card : ℝ) else 0 := by
      exact Finset.single_le_sum (s := components G)
        (f := fun T => if isUnicyclic G T then (T.card : ℝ) else 0)
        (fun T _ => by by_cases hT : isUnicyclic G T <;> simp [hT]) hS

lemma prob_cyclicAbove_le_mass_div
    (hF : FiniteEnumerationStatement) {n M : ℕ} (hM : M ≤ capacity n)
    {h : ℝ} (hh : 0 < h) :
    probM n M (fun G => cyclicAbove G h) ≤ expectM n M unicyclicMass / h := by
  have hbound := probM_le_expectM_of_indicator hF hM
    (fun G => cyclicAbove G h) (fun G => unicyclicMass G / h)
    (fun G => div_nonneg (by
      unfold unicyclicMass
      exact Finset.sum_nonneg fun S _ => by split_ifs <;> positivity) hh.le)
    (fun G hG => (le_div_iff₀ hh).2 (by
      simpa using! cyclicAbove_le_unicyclicMass G hh hG))
  simpa [expectM, Finset.sum_div, div_div, mul_comm] using! hbound

end
end Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Finite


namespace Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Analytic

noncomputable section
open Filter
open scoped BigOperators Topology

def excessKernel (D : ℝ) (r : ℕ) : ℝ :=
  D ^ r * Real.rpow (r : ℝ) (-(r : ℝ) / 2)

lemma excessKernel_nonneg {D : ℝ} (hD : 0 ≤ D) (r : ℕ) :
    0 ≤ excessKernel D r := by
  unfold excessKernel
  exact mul_nonneg (pow_nonneg hD r) (Real.rpow_nonneg (by positivity) _)

private lemma rpow_succ_kernel_le (D : ℝ) (hD : 0 ≤ D) (r : ℕ)
    (hr : 1 ≤ r) :
    excessKernel D (r + 1) ≤
      (D / Real.sqrt (((r + 1 : ℕ) : ℝ))) * excessKernel D r := by
  have hr0 : 0 < (r : ℝ) := by positivity
  have hrs0 : 0 < ((r + 1 : ℕ) : ℝ) := by positivity
  have hbase : (r : ℝ) ≤ (r + 1 : ℕ) := by norm_num
  have hexp : -(r : ℝ) / 2 ≤ 0 := by linarith
  have hmono := Real.rpow_le_rpow_of_nonpos
    (by exact_mod_cast hr) hbase hexp
  have hsplit :
      Real.rpow ((r + 1 : ℕ) : ℝ) (-((r + 1 : ℕ) : ℝ) / 2) =
        Real.rpow ((r + 1 : ℕ) : ℝ) (-(r : ℝ) / 2) /
          Real.sqrt ((r + 1 : ℕ) : ℝ) := by
    rw [show -((r + 1 : ℕ) : ℝ) / 2 = -(r : ℝ) / 2 + (-(1 : ℝ) / 2) by
      push_cast; ring]
    change (((r + 1 : ℕ) : ℝ) ^ (-(r : ℝ) / 2 + (-(1 : ℝ) / 2))) = _
    rw [Real.rpow_add hrs0 (-(r : ℝ) / 2) (-(1 : ℝ) / 2)]
    rw [Real.sqrt_eq_rpow]
    have hneg : (((r + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) =
        ((((r + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)))⁻¹ :=
      Real.rpow_neg (le_of_lt hrs0) (1 / 2 : ℝ)
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, hneg]
    simp [div_eq_mul_inv]
  unfold excessKernel
  rw [pow_succ, hsplit]
  have hsqrt : 0 < Real.sqrt ((r + 1 : ℕ) : ℝ) := by positivity
  have hp : 0 ≤ D ^ r := pow_nonneg hD r
  have hmul : D ^ r * D * Real.rpow ((r + 1 : ℕ) : ℝ) (-(r : ℝ) / 2) ≤
      D * (D ^ r * Real.rpow (r : ℝ) (-(r : ℝ) / 2)) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using!
      mul_le_mul_of_nonneg_left hmono (mul_nonneg hp hD)
  calc
    D ^ r * D * (Real.rpow ((r + 1 : ℕ) : ℝ) (-(r : ℝ) / 2) /
        Real.sqrt ((r + 1 : ℕ) : ℝ)) =
      (D ^ r * D * Real.rpow ((r + 1 : ℕ) : ℝ) (-(r : ℝ) / 2)) /
        Real.sqrt ((r + 1 : ℕ) : ℝ) := by ring
    _ ≤ (D * (D ^ r * Real.rpow (r : ℝ) (-(r : ℝ) / 2))) /
        Real.sqrt ((r + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hmul hsqrt.le
    _ = D / Real.sqrt ((r + 1 : ℕ) : ℝ) *
        (D ^ r * Real.rpow (r : ℝ) (-(r : ℝ) / 2)) := by ring

lemma summable_excessKernel (D : ℝ) (hD : 0 ≤ D) :
    Summable (excessKernel D) := by
  apply summable_of_ratio_norm_eventually_le (r := (1 / 2 : ℝ)) (by norm_num)
  obtain ⟨N, hN⟩ := exists_nat_ge (max 1 (4 * D ^ 2))
  filter_upwards [eventually_ge_atTop N] with r hr
  have hN1 : 1 ≤ N := by
    exact_mod_cast (le_trans (le_max_left (1 : ℝ) (4 * D ^ 2)) hN)
  have hr1 : 1 ≤ r := hN1.trans hr
  have hlarge : 4 * D ^ 2 ≤ (r : ℝ) :=
    le_trans (le_max_right _ _) (hN.trans (by exact_mod_cast hr))
  have hsqrt : 0 < Real.sqrt ((r + 1 : ℕ) : ℝ) := by positivity
  have hcoef : D / Real.sqrt ((r + 1 : ℕ) : ℝ) ≤ 1 / 2 := by
    by_cases hDp : D = 0
    · simp [hDp]
    · have hDpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hDp)
      apply (div_le_iff₀ hsqrt).2
      have hs : 2 * D ≤ Real.sqrt ((r + 1 : ℕ) : ℝ) := by
        have hs0 : 0 ≤ Real.sqrt (((r + 1 : ℕ) : ℝ)) := Real.sqrt_nonneg _
        have hsquare := Real.sq_sqrt (show 0 ≤ (((r + 1 : ℕ) : ℝ)) by positivity)
        have hleft : 0 ≤ 2 * D := mul_nonneg (by norm_num) hD
        have hsqleft : (2 * D) ^ 2 = 4 * D ^ 2 := by ring
        by_contra hnot
        have hlt : Real.sqrt (((r + 1 : ℕ) : ℝ)) < 2 * D := lt_of_not_ge hnot
        have hsumpos : 0 < Real.sqrt (((r + 1 : ℕ) : ℝ)) + 2 * D :=
          add_pos_of_nonneg_of_pos hs0 (mul_pos (by norm_num) hDpos)
        have hp := mul_pos (sub_pos.mpr hlt) hsumpos
        norm_num only [Nat.cast_add, Nat.cast_one] at hsquare hp
        nlinarith
      nlinarith
  have hk := rpow_succ_kernel_le D hD r hr1
  rw [Real.norm_eq_abs, abs_of_nonneg (excessKernel_nonneg hD _),
    Real.norm_eq_abs, abs_of_nonneg (excessKernel_nonneg hD _)]
  exact hk.trans (mul_le_mul_of_nonneg_right hcoef (excessKernel_nonneg hD r))

def excessKernelConstant (D : ℝ) : ℝ :=
  ∑' r : ℕ, excessKernel (max 0 (2 * D)) r

lemma excessKernelConstant_pos (D : ℝ) : 0 < excessKernelConstant D := by
  have hsum := summable_excessKernel (max 0 (2 * D)) (le_max_left _ _)
  have hzero : excessKernel (max 0 (2 * D)) 0 = 1 := by
    simp [excessKernel]
  have hle : excessKernel (max 0 (2 * D)) 0 ≤ excessKernelConstant D := by
    exact hsum.le_tsum 0 (fun r _ => excessKernel_nonneg (le_max_left _ _) r)
  linarith

lemma excess_series_le (D y : ℝ) (hD : 0 ≤ D) (hy0 : 0 ≤ y) (hy2 : y ≤ 2) :
    Summable (fun r : ℕ => (D * y) ^ r *
      Real.rpow (r : ℝ) (-(r : ℝ) / 2)) ∧
    (∑' r : ℕ, (D * y) ^ (r + 1) *
      Real.rpow ((r + 1 : ℕ) : ℝ) (-((r + 1 : ℕ) : ℝ) / 2)) ≤
        y * D * excessKernelConstant D := by
  let E := max 0 (2 * D)
  have hE : 0 ≤ E := le_max_left _ _
  have hbase : 0 ≤ D * y := mul_nonneg hD hy0
  have hDE : D * y ≤ E := by
    calc
      D * y ≤ D * 2 := mul_le_mul_of_nonneg_left hy2 hD
      _ ≤ max 0 (2 * D) := by simpa [mul_comm] using! le_max_right (0 : ℝ) (2 * D)
  have hdom : ∀ r : ℕ,
      (D * y) ^ r * Real.rpow (r : ℝ) (-(r : ℝ) / 2) ≤ excessKernel E r := by
    intro r
    unfold excessKernel
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hbase hDE r)
      (Real.rpow_nonneg (by positivity) _)
  have hsumE := summable_excessKernel E hE
  have hsum : Summable (fun r : ℕ => (D * y) ^ r *
      Real.rpow (r : ℝ) (-(r : ℝ) / 2)) := by
    apply Summable.of_nonneg_of_le
    · intro r
      exact mul_nonneg (pow_nonneg hbase r) (Real.rpow_nonneg (by positivity) _)
    · exact hdom
    · exact hsumE
  refine ⟨hsum, ?_⟩
  have htail :
      (∑' r : ℕ, (D * y) ^ (r + 1) *
        Real.rpow ((r + 1 : ℕ) : ℝ) (-((r + 1 : ℕ) : ℝ) / 2)) ≤
      y * D * (∑' r : ℕ, excessKernel E r) := by
    calc
      (∑' r : ℕ, (D * y) ^ (r + 1) *
          Real.rpow ((r + 1 : ℕ) : ℝ) (-((r + 1 : ℕ) : ℝ) / 2)) ≤
          ∑' r : ℕ, (y * D) * excessKernel E r := by
        apply Summable.tsum_le_tsum
        · intro r
          have hfac : (D * y) ^ (r + 1) = D * y * (D ^ r * y ^ r) := by
            rw [mul_pow, pow_succ, pow_succ]
            ring
          have hpow : D ^ r * y ^ r ≤ (2 * D) ^ r := by
            rw [mul_pow]
            simpa [mul_comm] using! mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ hy0 hy2 r) (pow_nonneg hD r)
          have hpowE : (2 * D) ^ r ≤ E ^ r := by
            exact pow_le_pow_left₀ (mul_nonneg (by norm_num) hD)
              (le_max_right _ _) r
          have hrpow : 0 ≤ Real.rpow ((r + 1 : ℕ) : ℝ)
              (-((r + 1 : ℕ) : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
          have hshift : Real.rpow ((r + 1 : ℕ) : ℝ)
              (-((r + 1 : ℕ) : ℝ) / 2) ≤
              Real.rpow (r : ℝ) (-(r : ℝ) / 2) := by
            by_cases hr0 : r = 0
            · subst r; simp
            · have hr : (1 : ℝ) ≤ r := by
                exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr0
              have hbase' : (r : ℝ) ≤ (r + 1 : ℕ) := by norm_num
              have hstep1 := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (r : ℝ)) hbase'
                (by linarith : -(r : ℝ) / 2 ≤ 0)
              have hstep2 := Real.rpow_le_rpow_of_exponent_le
                (by norm_num : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ)) (by push_cast; linarith :
                  -((r + 1 : ℕ) : ℝ) / 2 ≤ -(r : ℝ) / 2)
              exact hstep2.trans hstep1
          calc
            (D * y) ^ (r + 1) * Real.rpow ((r + 1 : ℕ) : ℝ)
                (-((r + 1 : ℕ) : ℝ) / 2) =
                (D * y) * (D ^ r * y ^ r) * Real.rpow ((r + 1 : ℕ) : ℝ)
                  (-((r + 1 : ℕ) : ℝ) / 2) := by rw [hfac]
            _ ≤ (D * y) * E ^ r * Real.rpow ((r + 1 : ℕ) : ℝ)
                (-((r + 1 : ℕ) : ℝ) / 2) := by
              gcongr
              exact hpow.trans hpowE
            _ ≤ (D * y) * E ^ r * Real.rpow (r : ℝ) (-(r : ℝ) / 2) :=
              mul_le_mul_of_nonneg_left hshift
                (mul_nonneg hbase (pow_nonneg hE r))
            _ = y * D * excessKernel E r := by unfold excessKernel; ring
        · exact (summable_nat_add_iff 1).2 hsum
        · exact (hsumE.mul_left (y * D))
      _ = y * D * (∑' r : ℕ, excessKernel E r) :=
        hsumE.tsum_mul_left (y * D)
  simpa [E, excessKernelConstant] using! htail

lemma analytic_power_bound (hA : AnalyticSumsStatement) (beta : ℝ)
    (hbeta : -1 < beta) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 0 < u → u ≤ 1 →
      Summable (fun k : ℕ => Real.rpow ((k + 1 : ℕ) : ℝ) beta *
        Real.exp (-u * (k + 1))) ∧
      (∑' k : ℕ, Real.rpow ((k + 1 : ℕ) : ℝ) beta *
        Real.exp (-u * (k + 1))) ≤ C * Real.rpow u (-beta - 1) := by
  rcases hA with ⟨_, h, _⟩
  exact h beta hbeta

end
end Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Analytic


namespace Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Bounds

noncomputable section
open Filter
open scoped BigOperators Topology
open Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_Foundation
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Finite
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Analytic

lemma treeMomentOne_eq_componentFormula
    (hF : FiniteEnumerationStatement) {n M k : ℕ}
    (hM : M ≤ capacity n) (hk : 0 < k) :
    treeMomentOne n M k = componentFormula n M k (k - 1) := by
  rw [treeMomentOne, enum_tuple hF n M 1 (fun _ => k) hM]
  unfold tupleFormula componentFormula
  simp only [Fin.sum_univ_one, Fin.prod_univ_one]
  by_cases hkn : k ≤ n
  · by_cases hkM : k ≤ M + 1
    · have heM : k - 1 ≤ M := by omega
      simp only [hk, hkn, hkM, heM, and_self, if_true]
      rw [enum_cayley hF k hk]
      have hfall : (falling n k : ℝ) =
          (k.factorial : ℝ) * (n.choose k : ℝ) := by
        rw [falling, ← Nat.descFactorial_eq_prod_range,
          Nat.descFactorial_eq_factorial_mul_choose]
        push_cast
        ring
      rw [hfall]
      have hfac : (k.factorial : ℝ) ≠ 0 := by positivity
      field_simp [hfac]
      simpa [show M + 1 - k = M - (k - 1) by omega]
    · have heM : M < k - 1 := by omega
      simp [hkn, hkM, heM]
  · have : n < k := Nat.lt_of_not_ge hkn
    simp [hkn, this]

lemma choose_down_one_identity {Q s : ℕ} (hs : 0 < s) (hsQ : s ≤ Q) :
    (Q.choose (s - 1) : ℝ) * ((Q - s + 1 : ℕ) : ℝ) =
      (Q.choose s : ℝ) * s := by
  have hpred : s = (s - 1) + 1 := by omega
  have h := Nat.choose_succ_right_eq Q (s - 1)
  rw [← hpred] at h
  have hsub : Q - (s - 1) = Q - s + 1 := by omega
  rw [hsub] at h
  exact_mod_cast h.symm

lemma choose_down_one_le {Q s : ℕ} (hs : 0 < s) (hsQ : s ≤ Q) :
    (Q.choose (s - 1) : ℝ) ≤
      (Q.choose s : ℝ) * ((s : ℝ) / (Q - s + 1 : ℕ)) := by
  have hden : 0 < ((Q - s + 1 : ℕ) : ℝ) := by positivity
  apply le_of_eq
  calc
    (Q.choose (s - 1) : ℝ) =
        ((Q.choose s : ℝ) * s) / (Q - s + 1 : ℕ) := by
      apply (eq_div_iff hden.ne').2
      exact choose_down_one_identity hs hsQ
    _ = (Q.choose s : ℝ) * ((s : ℝ) / (Q - s + 1 : ℕ)) := by ring

lemma choose_down_le {Q s d : ℕ} (hd : d ≤ s) (hsQ : s ≤ Q) :
    (Q.choose (s - d) : ℝ) ≤
      (Q.choose s : ℝ) *
        ((s : ℝ) / (Q - s + 1 : ℕ)) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hds : d ≤ s := Nat.le_trans (Nat.le_succ d) hd
      have hsd : 0 < s - d := by omega
      have hsdQ : s - d ≤ Q := (Nat.sub_le s d).trans hsQ
      have hone := choose_down_one_le (Q := Q) (s := s - d) hsd hsdQ
      have hnum : ((s - d : ℕ) : ℝ) ≤ s := by exact_mod_cast Nat.sub_le s d
      have hden : ((Q - s + 1 : ℕ) : ℝ) ≤ (Q - (s - d) + 1 : ℕ) := by
        exact_mod_cast (by omega : Q - s + 1 ≤ Q - (s - d) + 1)
      have hratio : ((s - d : ℕ) : ℝ) / (Q - (s - d) + 1 : ℕ) ≤
          (s : ℝ) / (Q - s + 1 : ℕ) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        exact mul_le_mul hnum hden (by positivity) (by positivity)
      have hbase : 0 ≤ (s : ℝ) / (Q - s + 1 : ℕ) := by positivity
      have ih' := ih hds
      rw [show s - (d + 1) = (s - d) - 1 by omega]
      calc
        (Q.choose ((s - d) - 1) : ℝ) ≤
            (Q.choose (s - d) : ℝ) *
              (((s - d : ℕ) : ℝ) / (Q - (s - d) + 1 : ℕ)) := hone
        _ ≤ ((Q.choose s : ℝ) *
              ((s : ℝ) / (Q - s + 1 : ℕ)) ^ d) *
              ((s : ℝ) / (Q - s + 1 : ℕ)) := by
          exact mul_le_mul ih' hratio (by positivity) (by positivity)
        _ = (Q.choose s : ℝ) *
              ((s : ℝ) / (Q - s + 1 : ℕ)) ^ (d + 1) := by rw [pow_succ]; ring

lemma cayley_cast {k : ℕ} (hk : 2 ≤ k) :
    (cayley k : ℝ) = (k : ℝ) ^ (k - 2) := by
  simp [cayley, show k ≠ 0 by omega, show k ≠ 1 by omega]

lemma unicyclic_over_cayley
    (hF : FiniteEnumerationStatement) (CU : ℝ)
    (hCU : ∀ k : ℕ, 3 ≤ k → (connectedCount k k : ℝ) ≤
      CU * Real.rpow (k : ℝ) ((k : ℝ) - 1 / 2))
    {k : ℕ} (hk : 3 ≤ k) :
    (connectedCount k k : ℝ) ≤
      (cayley k : ℝ) * (CU * Real.rpow (k : ℝ) (3 / 2 : ℝ)) := by
  have hkpos : 0 < (k : ℝ) := by positivity
  rw [cayley_cast (by omega), ← Real.rpow_natCast]
  calc
    (connectedCount k k : ℝ) ≤
        CU * Real.rpow (k : ℝ) ((k : ℝ) - 1 / 2) := hCU k hk
    _ = Real.rpow (k : ℝ) ((k - 2 : ℕ) : ℝ) *
        (CU * Real.rpow (k : ℝ) (3 / 2 : ℝ)) := by
      have hexp : ((k : ℝ) - 1 / 2) = ((k - 2 : ℕ) : ℝ) + 3 / 2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ k)]
        ring
      rw [hexp]
      simp only [Real.rpow_eq_pow, Real.rpow_add hkpos]
      ring

lemma kernel_over_cayley_of_bound
    (A : ℝ) (hbound : ∀ k r : ℕ, 0 < k → 0 < r →
      (connectedCount k (k + r) : ℝ) ≤ A ^ r *
        Real.rpow (r : ℝ) (-(r : ℝ) / 2) *
        Real.rpow (k : ℝ) ((k : ℝ) + (3 * (r : ℝ) - 1) / 2))
    {k r : ℕ} (hk : 3 ≤ k) (hr : 0 < r) :
    (connectedCount k (k + r) : ℝ) ≤
        (cayley k : ℝ) *
          (A ^ r * Real.rpow (r : ℝ) (-(r : ℝ) / 2) *
            Real.rpow (k : ℝ) ((3 * (r : ℝ) + 3) / 2)) := by
  have hkpos : 0 < (k : ℝ) := by positivity
  rw [cayley_cast (by omega), ← Real.rpow_natCast]
  calc
    (connectedCount k (k + r) : ℝ) ≤
        A ^ r * Real.rpow (r : ℝ) (-(r : ℝ) / 2) *
          Real.rpow (k : ℝ) ((k : ℝ) + (3 * (r : ℝ) - 1) / 2) :=
      hbound k r (by omega) hr
    _ = Real.rpow (k : ℝ) ((k - 2 : ℕ) : ℝ) *
        (A ^ r * Real.rpow (r : ℝ) (-(r : ℝ) / 2) *
          Real.rpow (k : ℝ) ((3 * (r : ℝ) + 3) / 2)) := by
      have hexp : (k : ℝ) + (3 * (r : ℝ) - 1) / 2 =
          ((k - 2 : ℕ) : ℝ) + (3 * (r : ℝ) + 3) / 2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ k)]
        ring
      rw [hexp]
      simp only [Real.rpow_eq_pow, Real.rpow_add hkpos]
      ring

lemma component_ratio_unicyclic_eq
    (hF : FiniteEnumerationStatement)
    {n M k : ℕ} (hM : M ≤ capacity n) (hk : 3 ≤ k)
    (hkn : k ≤ n) (hkM : k ≤ M)
    (hsQ : M - k + 1 ≤ (n - k).choose 2) :
    cyclicFormula n M k =
      treeMomentOne n M k *
        ((connectedCount k k : ℝ) / (cayley k : ℝ)) *
        (((M - k + 1 : ℕ) : ℝ) /
          (((n - k).choose 2 - (M - k + 1) + 1 : ℕ) : ℝ)) := by
  let Q := (n - k).choose 2
  let s := M - k + 1
  have hs : 0 < s := by dsimp [s]; omega
  have heM : k - 1 ≤ M := by omega
  have htree := treeMomentOne_eq_componentFormula hF hM (by omega : 0 < k)
  rw [htree]
  unfold cyclicFormula componentFormula
  simp only [hkn, hkM, heM, and_self, if_true]
  have hchoose := choose_down_one_identity (Q := Q) (s := s) hs hsQ
  have hindex : M - k = s - 1 := by omega
  have htreeIndex : M - (k - 1) = s := by dsimp [s]; omega
  have hcayley : (cayley k : ℝ) ≠ 0 := by
    rw [cayley_cast (by omega)]
    positivity
  have hden : (((capacity n).choose M : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hM))
  have hratden : (((Q - s + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hchooseEq : (Q.choose (s - 1) : ℝ) =
      (Q.choose s : ℝ) * s / (Q - s + 1 : ℕ) := by
    apply (eq_div_iff hratden).2
    exact hchoose
  rw [hindex, htreeIndex]
  rw [enum_cayley hF k (by omega)]
  dsimp [Q, s] at hchooseEq ⊢
  rw [hchooseEq]
  field_simp [hcayley, hden, hratden]

lemma component_ratio_unicyclic
    (hF : FiniteEnumerationStatement) (CU : ℝ)
    (hCU : ∀ k : ℕ, 3 ≤ k → (connectedCount k k : ℝ) ≤
      CU * Real.rpow (k : ℝ) ((k : ℝ) - 1 / 2))
    {n M k : ℕ} (hM : M ≤ capacity n) (hk : 3 ≤ k)
    (hkn : k ≤ n) (hkM : k ≤ M) (hsQ : M - k + 1 ≤ (n - k).choose 2) :
    cyclicFormula n M k ≤
      treeMomentOne n M k *
        (CU * Real.rpow (k : ℝ) (3 / 2 : ℝ)) *
        ((M - k + 1 : ℕ) : ℝ) /
          (((n - k).choose 2 - (M - k + 1) + 1 : ℕ) : ℝ) := by
  have hconn := unicyclic_over_cayley hF CU hCU hk
  have hcayley : (0 : ℝ) < cayley k := by
    rw [cayley_cast (by omega)]
    positivity
  have hcoef : (connectedCount k k : ℝ) / (cayley k : ℝ) ≤
      CU * Real.rpow (k : ℝ) (3 / 2 : ℝ) := by
    apply (div_le_iff₀ hcayley).2
    simpa [mul_comm] using! hconn
  have htree : 0 ≤ treeMomentOne n M k := by
    rw [treeMomentOne_eq_componentFormula hF hM (by omega)]
    exact componentFormula_nonneg n M k (k - 1)
  have hratio : 0 ≤ ((M - k + 1 : ℕ) : ℝ) /
      (((n - k).choose 2 - (M - k + 1) + 1 : ℕ) : ℝ) := by positivity
  calc
    cyclicFormula n M k =
        treeMomentOne n M k *
          ((connectedCount k k : ℝ) / (cayley k : ℝ)) *
          (((M - k + 1 : ℕ) : ℝ) /
            (((n - k).choose 2 - (M - k + 1) + 1 : ℕ) : ℝ)) :=
      component_ratio_unicyclic_eq hF hM hk hkn hkM hsQ
    _ ≤ treeMomentOne n M k *
          (CU * Real.rpow (k : ℝ) (3 / 2 : ℝ)) *
          (((M - k + 1 : ℕ) : ℝ) /
            (((n - k).choose 2 - (M - k + 1) + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef htree) hratio
    _ = _ := by ring

lemma component_ratio_excess_of_bound
    (hF : FiniteEnumerationStatement) (A : ℝ) (hA : 1 < A)
    (hbound : ∀ k r : ℕ, 0 < k → 0 < r →
      (connectedCount k (k + r) : ℝ) ≤ A ^ r *
        Real.rpow (r : ℝ) (-(r : ℝ) / 2) *
        Real.rpow (k : ℝ) ((k : ℝ) + (3 * (r : ℝ) - 1) / 2))
    {n M k r : ℕ} (hM : M ≤ capacity n) (hk : 3 ≤ k) (hr : 0 < r)
    (hkn : k ≤ n) (hkeM : k + r ≤ M)
    (hsQ : M - k + 1 ≤ (n - k).choose 2) :
    excessFormula n M k r ≤
      treeMomentOne n M k *
        (A ^ r * Real.rpow (r : ℝ) (-(r : ℝ) / 2) *
          Real.rpow (k : ℝ) ((3 * (r : ℝ) + 3) / 2)) *
        (((M - k + 1 : ℕ) : ℝ) /
          (((n - k).choose 2 - (M - k + 1) + 1 : ℕ) : ℝ)) ^ (r + 1) := by
  have hconn := kernel_over_cayley_of_bound A hbound hk hr
  let Q := (n - k).choose 2
  let s := M - k + 1
  have hs : 0 < s := by dsimp [s]; omega
  have hd : r + 1 ≤ s := by dsimp [s]; omega
  have heM : k - 1 ≤ M := by omega
  have htree := treeMomentOne_eq_componentFormula hF hM (by omega : 0 < k)
  rw [htree]
  unfold excessFormula componentFormula
  simp only [hkn, hkeM, heM, and_self, if_true]
  have hchoose := choose_down_le (Q := Q) (s := s) (d := r + 1) hd hsQ
  have hindex : M - (k + r) = s - (r + 1) := by dsimp [s]; omega
  have htreeIndex : M - (k - 1) = s := by dsimp [s]; omega
  rw [hindex, htreeIndex, enum_cayley hF k (by omega)]
  dsimp [Q, s] at hchoose ⊢
  have hden : 0 ≤ (((capacity n).choose M : ℕ) : ℝ) := by positivity
  have hcoef0 : 0 ≤ (cayley k : ℝ) *
      (A ^ r * Real.rpow (r : ℝ) (-(r : ℝ) / 2) *
        Real.rpow (k : ℝ) ((3 * (r : ℝ) + 3) / 2)) := by
    exact mul_nonneg (by rw [cayley_cast (by omega)]; positivity)
      (by simp only [Real.rpow_eq_pow]; positivity)
  calc
    (n.choose k : ℝ) * (connectedCount k (k + r) : ℝ) *
        (((n - k).choose 2).choose (M - k + 1 - (r + 1)) : ℝ) /
        ((capacity n).choose M : ℝ) ≤
      (n.choose k : ℝ) *
        ((cayley k : ℝ) * (A ^ r * Real.rpow (r : ℝ) (-(r : ℝ) / 2) *
          Real.rpow (k : ℝ) ((3 * (r : ℝ) + 3) / 2))) *
        (((n - k).choose 2).choose (M - k + 1 - (r + 1)) : ℝ) /
        ((capacity n).choose M : ℝ) := by gcongr
    _ ≤ (n.choose k : ℝ) *
        ((cayley k : ℝ) * (A ^ r * Real.rpow (r : ℝ) (-(r : ℝ) / 2) *
          Real.rpow (k : ℝ) ((3 * (r : ℝ) + 3) / 2))) *
        ((((n - k).choose 2).choose (M - k + 1) : ℝ) *
          (((M - k + 1 : ℕ) : ℝ) /
            (((n - k).choose 2 - (M - k + 1) + 1 : ℕ) : ℝ)) ^ (r + 1)) /
        ((capacity n).choose M : ℝ) := by
          gcongr
    _ = _ := by simp only [Real.rpow_eq_pow]; ring

private lemma complement_ratio_of_cross_bound
    {n t s : ℕ} (hn : 0 < n) (hsQ : s ≤ t.choose 2)
    (hcross : ((n : ℝ) + 8) * s ≤ 8 * ((t.choose 2 : ℝ) + 1)) :
    (s : ℝ) / ((t.choose 2 - s + 1 : ℕ) : ℝ) ≤ 8 / n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hdenNat : 0 < t.choose 2 - s + 1 := by omega
  have hden : (0 : ℝ) < (t.choose 2 - s + 1 : ℕ) := by exact_mod_cast hdenNat
  have hcast : ((t.choose 2 - s + 1 : ℕ) : ℝ) =
      (t.choose 2 : ℝ) - s + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hsQ]
    norm_num
  apply (div_le_div_iff₀ hden hnpos).2
  rw [hcast]
  nlinarith

lemma near_complement_ratio
    {n M k : ℕ} (hn : 16 ≤ n)
    (hdegLo : 1 / 2 ≤ degreeAt n M) (hdegHi : degreeAt n M ≤ 3 / 2)
    (hkM : k ≤ M) :
    M - k + 1 ≤ (n - k).choose 2 ∧
    (((M - k + 1 : ℕ) : ℝ) /
      (((n - k).choose 2 - (M - k + 1) + 1 : ℕ) : ℝ)) ≤ 8 / n := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hMreal : 4 * (M : ℝ) ≤ 3 * n := by
    unfold degreeAt at hdegHi
    have h := (div_le_iff₀ hnpos).1 hdegHi
    nlinarith
  have hMnat : 4 * M ≤ 3 * n := by exact_mod_cast hMreal
  let t := n - k
  let s := M - k + 1
  have ht : 4 ≤ t := by dsimp [t]; omega
  have hnt : n ≤ 4 * t := by dsimp [t]; omega
  have hst : s + 3 ≤ t := by dsimp [s, t]; omega
  have htR : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have hntR : (n : ℝ) ≤ 4 * t := by exact_mod_cast hnt
  have hstR : (s : ℝ) + 3 ≤ t := by exact_mod_cast hst
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have hs0 : (0 : ℝ) ≤ s := by positivity
  have hQ : ((t.choose 2 : ℕ) : ℝ) = t * (t - 1) / 2 := by
    rw [Nat.cast_choose_two]
  have hQlower : (s : ℝ) ≤ (t.choose 2 : ℝ) := by
    rw [hQ]
    nlinarith [sq_nonneg ((t : ℝ) - 2)]
  have hsQ : s ≤ t.choose 2 := by exact_mod_cast hQlower
  have hmul1 : ((n : ℝ) + 8) * s ≤ (4 * (t : ℝ) + 8) * s := by
    gcongr
  have hmul2 : (4 * (t : ℝ) + 8) * s ≤
      (4 * (t : ℝ) + 8) * (t - 3) := by
    exact mul_le_mul_of_nonneg_left (by linarith : (s : ℝ) ≤ t - 3) (by positivity)
  have hcross : ((n : ℝ) + 8) * s ≤ 8 * ((t.choose 2 : ℝ) + 1) := by
    rw [hQ]
    calc
      ((n : ℝ) + 8) * s ≤ (4 * (t : ℝ) + 8) * s := hmul1
      _ ≤ (4 * (t : ℝ) + 8) * (t - 3) := hmul2
      _ ≤ 8 * ((t : ℝ) * (t - 1) / 2 + 1) := by nlinarith
  dsimp [s, t] at hsQ ⊢
  exact ⟨hsQ, complement_ratio_of_cross_bound (by omega) hsQ hcross⟩

end
end Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Bounds


namespace Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Bounds

noncomputable section
open Filter
open scoped BigOperators Topology
open Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_Foundation
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Finite
open Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Analytic

private lemma sum_Icc_le_tsum_shift (f : ℕ → ℝ) (N : ℕ)
    (hf : ∀ r, 0 ≤ f r) (hs : Summable f) :
    (∑ r ∈ Finset.Icc 1 N, f r) ≤ ∑' j : ℕ, f (j + 1) := by
  have hset : (Finset.range N).image (fun j => j + 1) = Finset.Icc 1 N := by
    ext r
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨j, hj, rfl⟩
      omega
    · intro hr
      exact ⟨r - 1, by omega, by omega⟩
  rw [← hset, Finset.sum_image (by intro a _ b _ hab; exact Nat.add_right_cancel hab)]
  exact ((summable_nat_add_iff 1).2 hs).sum_le_tsum _ (fun j _ => hf (j + 1))

lemma excess_sum_le_tree
    (hF : FiniteEnumerationStatement) (A K : ℝ) (hA : 1 < A)
    (hKpos : 0 < K)
    (hbound : ∀ k r : ℕ, 0 < k → 0 < r →
      (connectedCount k (k + r) : ℝ) ≤ A ^ r *
        Real.rpow (r : ℝ) (-(r : ℝ) / 2) *
        Real.rpow (k : ℝ) ((k : ℝ) + (3 * (r : ℝ) - 1) / 2))
    {n M k : ℕ} (hM : M ≤ capacity n) (hn : 0 < n) (hk : 3 ≤ k)
    (hkn : k ≤ n) (hkhalf : k ≤ n / 2)
    (hratio : (((M - k + 1 : ℕ) : ℝ) /
      (((n - k).choose 2 - (M - k + 1) + 1 : ℕ) : ℝ)) ≤ 8 / n)
    (hsQ : M - k + 1 ≤ (n - k).choose 2)
    (hy : Real.rpow (k : ℝ) (3 / 2 : ℝ) / n ≤ 2) :
    (∑ r ∈ Finset.Icc 1 (capacity k), excessFormula n M k r) ≤
      treeMomentOne n M k *
        (64 * A * excessKernelConstant (8 * A)) *
        (Real.rpow (k : ℝ) (3 : ℝ) / (n : ℝ) ^ 2) := by
  let y : ℝ := Real.rpow (k : ℝ) (3 / 2 : ℝ) / n
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hD : 0 ≤ 8 * A := by positivity
  have hseries := excess_series_le (8 * A) y hD hy0 hy
  have htree0 : 0 ≤ treeMomentOne n M k := by
    exact Erdos745.WrapUp.Proofs.W06_POISSON.tupleMoment_nonneg n M 1 (fun _ => k)
  have hterm : ∀ r ∈ Finset.Icc 1 (capacity k),
      excessFormula n M k r ≤
        treeMomentOne n M k * (8 * y) *
          ((8 * A * y) ^ r *
            Real.rpow (r : ℝ) (-(r : ℝ) / 2)) := by
    intro r hr
    have hrpos : 0 < r := (Finset.mem_Icc.mp hr).1
    by_cases hfeas : k + r ≤ M
    · have hc := component_ratio_excess_of_bound hF A hA hbound hM hk hrpos
        hkn hfeas hsQ
      have hkpos : 0 < (k : ℝ) := by positivity
      have hnpos : 0 < (n : ℝ) := by positivity
      have hkrpow : Real.rpow (k : ℝ) ((3 * (r : ℝ) + 3) / 2) =
          Real.rpow (k : ℝ) (3 / 2 : ℝ) ^ (r + 1) := by
        have hp := Real.rpow_mul_natCast hkpos.le (3 / 2 : ℝ) (r + 1)
        calc
          Real.rpow (k : ℝ) ((3 * (r : ℝ) + 3) / 2) =
              Real.rpow (k : ℝ) ((3 / 2 : ℝ) * (r + 1)) := by
                congr 1
                push_cast
                ring
          _ = Real.rpow (k : ℝ) (3 / 2 : ℝ) ^ (r + 1) := by
                simpa only [Real.rpow_eq_pow, Nat.cast_add, Nat.cast_one] using! hp
      calc
        excessFormula n M k r ≤ treeMomentOne n M k *
            (A ^ r * Real.rpow (r : ℝ) (-(r : ℝ) / 2) *
              Real.rpow (k : ℝ) ((3 * (r : ℝ) + 3) / 2)) *
            (((M - k + 1 : ℕ) : ℝ) /
              (((n - k).choose 2 - (M - k + 1) + 1 : ℕ) : ℝ)) ^ (r + 1) := hc
        _ ≤ treeMomentOne n M k *
            (A ^ r * Real.rpow (r : ℝ) (-(r : ℝ) / 2) *
              Real.rpow (k : ℝ) ((3 * (r : ℝ) + 3) / 2)) *
            (8 / n) ^ (r + 1) := by
          gcongr
          exact mul_nonneg htree0 (mul_nonneg (mul_nonneg (pow_nonneg (by linarith : 0 ≤ A) r)
            (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg hkpos.le _))
        _ = treeMomentOne n M k * (8 * y) *
            ((8 * A * y) ^ r * Real.rpow (r : ℝ) (-(r : ℝ) / 2)) := by
          rw [hkrpow]
          dsimp [y]
          rw [pow_succ, pow_succ, mul_pow, mul_pow]
          field_simp [ne_of_gt hnpos]
          ring
    · have hz : excessFormula n M k r = 0 := by
        unfold excessFormula componentFormula
        simp [Nat.lt_of_not_ge hfeas]
      rw [hz]
      exact mul_nonneg (mul_nonneg htree0 (mul_nonneg (by norm_num) hy0))
        (mul_nonneg (pow_nonneg (mul_nonneg hD hy0) r)
          (Real.rpow_nonneg (by positivity) _))
  calc
    (∑ r ∈ Finset.Icc 1 (capacity k), excessFormula n M k r) ≤
        ∑ r ∈ Finset.Icc 1 (capacity k),
          treeMomentOne n M k * (8 * y) *
            ((8 * A * y) ^ r * Real.rpow (r : ℝ) (-(r : ℝ) / 2)) :=
      Finset.sum_le_sum hterm
    _ ≤ treeMomentOne n M k * (8 * y) *
        (∑' j : ℕ, (8 * A * y) ^ (j + 1) *
          Real.rpow ((j + 1 : ℕ) : ℝ) (-((j + 1 : ℕ) : ℝ) / 2)) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (sum_Icc_le_tsum_shift _ _ (fun r =>
          mul_nonneg (pow_nonneg (mul_nonneg hD hy0) r)
            (Real.rpow_nonneg (by positivity) _)) hseries.1)
        (mul_nonneg htree0 (mul_nonneg (by norm_num) hy0))
    _ ≤ treeMomentOne n M k * (8 * y) *
        (y * (8 * A) * excessKernelConstant (8 * A)) :=
      mul_le_mul_of_nonneg_left hseries.2
        (mul_nonneg htree0 (mul_nonneg (by norm_num) hy0))
    _ = treeMomentOne n M k *
        (64 * A * excessKernelConstant (8 * A)) *
        (Real.rpow (k : ℝ) 3 / (n : ℝ) ^ 2) := by
      dsimp [y]
      have hk0 : 0 ≤ (k : ℝ) := by positivity
      have hp : (k : ℝ) ^ (3 : ℝ) = ((k : ℝ) ^ (3 / 2 : ℝ)) ^ (2 : ℕ) := by
        have ht := Real.rpow_mul_natCast hk0 (3 / 2 : ℝ) 2
        norm_num at ht
        simpa only [Real.rpow_ofNat] using ht
      simp only [Real.rpow_ofNat] at hp ⊢
      rw [hp]
      ring

private lemma choose_shift_four_le (n k : ℕ) (hk : 4 ≤ k) :
    (n.choose k : ℝ) ≤ (n : ℝ) ^ 4 * (n.choose (k - 4) : ℝ) := by
  have hstep (j : ℕ) : (n.choose (j + 1) : ℝ) ≤
      (n : ℝ) * (n.choose j : ℝ) := by
    have h := Nat.choose_succ_right_eq n j
    have hj : 1 ≤ j + 1 := by omega
    have hcast := congrArg (fun z : ℕ => (z : ℝ)) h
    push_cast at hcast
    nlinarith [show 0 ≤ (n.choose (j + 1) : ℝ) by positivity,
      show ((n - j : ℕ) : ℝ) ≤ n by exact_mod_cast Nat.sub_le n j]
  have hk0 : k = (k - 4) + 4 := by omega
  rw [hk0]
  calc
    (n.choose ((k - 4) + 4) : ℝ) ≤ n * (n.choose ((k - 4) + 3) : ℝ) := by
      simpa [Nat.add_assoc] using! hstep ((k - 4) + 3)
    _ ≤ n * (n * (n.choose ((k - 4) + 2) : ℝ)) := by gcongr; simpa using! hstep ((k - 4) + 2)
    _ ≤ n * (n * (n * (n.choose ((k - 4) + 1) : ℝ))) := by gcongr; simpa using! hstep ((k - 4) + 1)
    _ ≤ n * (n * (n * (n * (n.choose (k - 4) : ℝ)))) := by gcongr; simpa using! hstep (k - 4)
    _ = (n : ℝ) ^ 4 * (n.choose (k - 4) : ℝ) := by ring

private lemma rpow_shift_four_le {k : ℕ} (hk : 8 ≤ k) :
    Real.rpow (k : ℝ) ((k : ℝ) - 1 / 2) ≤
      Real.exp 8 * (k : ℝ) ^ 6 * ((k - 4 : ℕ) : ℝ) ^ (k - 6) := by
  have hkpos : 0 < (k : ℝ) := by positivity
  have hjpos : 0 < ((k - 4 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k - 4)
  have hbase : (k : ℝ) / (k - 4 : ℕ) = 1 + 4 / (k - 4 : ℕ) := by
    rw [Nat.cast_sub (by omega : 4 ≤ k)]
    have hne : (k : ℝ) - 4 ≠ 0 := by
      have hk8 : (8 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    field_simp [hne]
    ring
  have hpowexp : ((k : ℝ) / (k - 4 : ℕ)) ^ (k - 6) ≤ Real.exp 8 := by
    rw [hbase]
    calc
      (1 + 4 / ((k - 4 : ℕ) : ℝ)) ^ (k - 6) ≤
          (Real.exp (4 / ((k - 4 : ℕ) : ℝ))) ^ (k - 6) := by
        gcongr
        simpa only [add_comm] using! Real.add_one_le_exp (4 / ((k - 4 : ℕ) : ℝ))
      _ = Real.exp ((4 / ((k - 4 : ℕ) : ℝ)) * (k - 6)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        rw [Nat.cast_sub (by omega : 6 ≤ k)]
        ring
      _ ≤ Real.exp 8 := by
        apply Real.exp_le_exp.mpr
        have : ((k - 6 : ℕ) : ℝ) ≤ 2 * (k - 4 : ℕ) := by exact_mod_cast (by omega : k - 6 ≤ 2 * (k - 4))
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ hjpos).2
        have hcast4 : ((k - 4 : ℕ) : ℝ) = (k : ℝ) - 4 := by
          exact_mod_cast Nat.cast_sub (by omega : 4 ≤ k)
        have hcast6 : ((k - 6 : ℕ) : ℝ) = (k : ℝ) - 6 := by
          exact_mod_cast Nat.cast_sub (by omega : 6 ≤ k)
        simp only [hcast4, hcast6] at this ⊢
        nlinarith
  have hrewrite : Real.rpow (k : ℝ) ((k : ℝ) - 1 / 2) =
      (k : ℝ) ^ (k - 6) * Real.rpow (k : ℝ) (11 / 2 : ℝ) := by
    calc
      Real.rpow (k : ℝ) ((k : ℝ) - 1 / 2) =
          Real.rpow (k : ℝ) (((k - 6 : ℕ) : ℝ) + 11 / 2) := by
            congr 1
            rw [Nat.cast_sub (by omega : 6 ≤ k)]
            ring
      _ = (k : ℝ) ^ (k - 6) * Real.rpow (k : ℝ) (11 / 2 : ℝ) := by
        have hp := Real.rpow_add hkpos (((k - 6 : ℕ) : ℝ)) (11 / 2 : ℝ)
        simpa only [Real.rpow_eq_pow, Real.rpow_natCast] using! hp
  rw [hrewrite]
  have hratio : (k : ℝ) ^ (k - 6) ≤
      Real.exp 8 * ((k - 4 : ℕ) : ℝ) ^ (k - 6) := by
    have heq : (k : ℝ) ^ (k - 6) =
        ((k : ℝ) / (k - 4 : ℕ)) ^ (k - 6) *
          ((k - 4 : ℕ) : ℝ) ^ (k - 6) := by
      rw [div_pow]
      field_simp
    rw [heq]
    gcongr
  have hrpow6 : Real.rpow (k : ℝ) (11 / 2 : ℝ) ≤ (k : ℝ) ^ 6 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ k))
      (by norm_num)
  calc
    (k : ℝ) ^ (k - 6) * Real.rpow (k : ℝ) (11 / 2 : ℝ) ≤
        (Real.exp 8 * ((k - 4 : ℕ) : ℝ) ^ (k - 6)) * (k : ℝ) ^ 6 := by
      exact mul_le_mul hratio hrpow6 (Real.rpow_nonneg hkpos.le _)
        (mul_nonneg (Real.exp_nonneg _) (pow_nonneg hjpos.le _))
    _ = Real.exp 8 * (k : ℝ) ^ 6 * ((k - 4 : ℕ) : ℝ) ^ (k - 6) := by ring

lemma bad_unicyclic_shift_le
    (hF : FiniteEnumerationStatement) (CU : ℝ) (hCU : 0 < CU)
    (hCUb : ∀ k : ℕ, 3 ≤ k → (connectedCount k k : ℝ) ≤
      CU * Real.rpow (k : ℝ) ((k : ℝ) - 1 / 2))
    {n M k : ℕ} (hM : M ≤ capacity n) (hk : 8 ≤ k) (hkn : k ≤ n)
    (hbad : (n - k).choose 2 = M - k) :
    (k : ℝ) * cyclicFormula n M k ≤
      (CU * Real.exp 8) * (n : ℝ) ^ 11 * treeMomentOne n M (k - 4) := by
  by_cases hkM : k ≤ M
  swap
  · have hz : cyclicFormula n M k = 0 := by
      unfold cyclicFormula componentFormula
      simp [show ¬k ≤ M by omega]
    rw [hz, mul_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCU.le (Real.exp_nonneg _)) (by positivity))
      (by unfold treeMomentOne
          exact Erdos745.WrapUp.Proofs.W06_POISSON.tupleMoment_nonneg n M 1
            (fun _ => k - 4))
  have hj : 0 < k - 4 := by omega
  have hjn : k - 4 ≤ n := by omega
  have hjeM : k - 4 - 1 ≤ M := by omega
  have hcay : (cayley (k - 4) : ℝ) = ((k - 4 : ℕ) : ℝ) ^ (k - 6) := by
    rw [cayley_cast (by omega)]
    simp only [show (k - 4) - 2 = k - 6 by omega]
  have hchoosePos : 1 ≤ (((n - (k - 4)).choose 2).choose
      (M + 1 - (k - 4)) : ℕ) := by
    apply Nat.choose_pos
    rw [show n - (k - 4) = n - k + 4 by omega]
    rw [show M + 1 - (k - 4) = M - k + 5 by omega, ← hbad]
    let s := n - k
    have hstep (u : ℕ) : (u + 1).choose 2 = u.choose 2 + u := by
      simpa only [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm] using!
        Nat.choose_succ_succ u 1
    have h4 : (s + 4).choose 2 = s.choose 2 + 4 * s + 6 := by
      calc
        (s + 4).choose 2 = (s + 3).choose 2 + (s + 3) := by
          simpa [Nat.add_assoc] using! hstep (s + 3)
        _ = (s + 2).choose 2 + (s + 2) + (s + 3) := by
          rw [show s + 3 = (s + 2) + 1 by omega, hstep]
        _ = (s + 1).choose 2 + (s + 1) + (s + 2) + (s + 3) := by
          rw [show s + 2 = (s + 1) + 1 by omega, hstep]
        _ = s.choose 2 + 4 * s + 6 := by rw [hstep s]; omega
    dsimp [s] at h4
    omega
  have hden : 0 < (((capacity n).choose M : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos hM
  have hconn : (connectedCount k k : ℝ) ≤
      CU * Real.exp 8 * (k : ℝ) ^ 6 * ((k - 4 : ℕ) : ℝ) ^ (k - 6) := by
    calc
      (connectedCount k k : ℝ) ≤ CU * Real.rpow (k : ℝ) ((k : ℝ) - 1 / 2) :=
        hCUb k (by omega)
      _ ≤ CU * (Real.exp 8 * (k : ℝ) ^ 6 * ((k - 4 : ℕ) : ℝ) ^ (k - 6)) :=
        mul_le_mul_of_nonneg_left (rpow_shift_four_le hk) hCU.le
      _ = _ := by ring
  have hshift := choose_shift_four_le n k (by omega)
  have htreeChoose : (1 : ℝ) ≤
      (((n - (k - 4)).choose 2).choose (M + 1 - (k - 4)) : ℝ) := by
    exact_mod_cast hchoosePos
  have hnPow : (k : ℝ) ^ 7 ≤ (n : ℝ) ^ 7 := by gcongr
  rw [treeMomentOne_eq_componentFormula hF hM hj]
  unfold cyclicFormula componentFormula
  simp only [hkn, hkM, hjn, hjeM, and_self, if_true, hbad, Nat.choose_self,
    Nat.cast_one, mul_one]
  rw [enum_cayley hF (k - 4) hj, hcay]
  rw [show M - (k - 4 - 1) = M + 1 - (k - 4) by omega]
  calc
    (k : ℝ) * ((n.choose k : ℝ) * (connectedCount k k : ℝ) / ((capacity n).choose M : ℝ)) ≤
        k * ((n : ℝ) ^ 4 * (n.choose (k - 4) : ℝ) *
          (CU * Real.exp 8 * (k : ℝ) ^ 6 * ((k - 4 : ℕ) : ℝ) ^ (k - 6)) /
          ((capacity n).choose M : ℝ)) := by
      gcongr
    _ = (CU * Real.exp 8) * (n : ℝ) ^ 4 * (k : ℝ) ^ 7 *
        ((n.choose (k - 4) : ℝ) * ((k - 4 : ℕ) : ℝ) ^ (k - 6)) /
        ((capacity n).choose M : ℝ) := by ring
    _ ≤ (CU * Real.exp 8) * (n : ℝ) ^ 4 * (n : ℝ) ^ 7 *
        ((n.choose (k - 4) : ℝ) * ((k - 4 : ℕ) : ℝ) ^ (k - 6)) /
        ((capacity n).choose M : ℝ) := by
      gcongr
    _ = (CU * Real.exp 8) * (n : ℝ) ^ 11 *
        ((n.choose (k - 4) : ℝ) * ((k - 4 : ℕ) : ℝ) ^ (k - 6) /
        ((capacity n).choose M : ℝ)) := by ring
    _ ≤ (CU * Real.exp 8) * (n : ℝ) ^ 11 *
        ((n.choose (k - 4) : ℝ) * ((k - 4 : ℕ) : ℝ) ^ (k - 6) *
        (((n - (k - 4)).choose 2).choose (M + 1 - (k - 4)) : ℝ) /
        ((capacity n).choose M : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply div_le_div_of_nonneg_right _ hden.le
      exact le_mul_of_one_le_right (by positivity) htreeChoose

end
end Erdos745.WrapUp.Proofs.Internal.W08_CYCLIC_Bounds
