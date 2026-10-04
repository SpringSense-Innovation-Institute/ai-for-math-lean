module

public import Erdos745.WrapUp.Contracts

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


namespace Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Trees

attribute [local instance] Classical.propDecidable
open scoped Sym2

def RootedForestFormula : Prop :=
  ∀ (k : ℕ) (roots : Finset (Fin k)), rootedForestCount k roots =
    if roots.card = k then 1 else roots.card * k ^ (k - roots.card - 1)

def CayleyBridge : Prop :=
  ∀ k : ℕ, 0 < k → connectedCount k (k - 1) = cayley k

def TreeCoreStatement : Prop := RootedForestFormula ∧ CayleyBridge

lemma adj_symm {n : ℕ} {G : Graph n} {u v : Fin n} (h : adj G u v) : adj G v u := by
  rcases h with ⟨e, he, huv | hvu⟩
  · exact ⟨e, he, Or.inr ⟨huv.1, huv.2⟩⟩
  · exact ⟨e, he, Or.inl ⟨hvu.1, hvu.2⟩⟩

lemma adj_irrefl {n : ℕ} (G : Graph n) (u : Fin n) : ¬ adj G u u := by
  rintro ⟨e, -, h | h⟩
  · have heq : e.val.1 = e.val.2 := h.1.trans h.2.symm
    exact (ne_of_lt e.property) heq
  · have heq : e.val.1 = e.val.2 := h.1.trans h.2.symm
    exact (ne_of_lt e.property) heq

def simpleGraph {n : ℕ} (G : Graph n) : SimpleGraph (Fin n) where
  Adj := adj G
  symm := ⟨fun _ _ h => adj_symm h⟩
  loopless := ⟨adj_irrefl G⟩

@[simp] theorem simpleGraph_adj {n : ℕ} (G : Graph n) (u v : Fin n) :
    (simpleGraph G).Adj u v ↔ adj G u v := Iff.rfl

lemma reach_refl {n : ℕ} {G : Graph n} (u : Fin n) : reach G u u :=
  Relation.ReflTransGen.refl

lemma reach_of_adj {n : ℕ} {G : Graph n} {u v : Fin n} (h : adj G u v) : reach G u v :=
  Relation.ReflTransGen.single h

lemma reach_symm {n : ℕ} {G : Graph n} {u v : Fin n} (h : reach G u v) : reach G v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h huv ih => exact (reach_of_adj (adj_symm huv)).trans ih

lemma reach_trans {n : ℕ} {G : Graph n} {u v w : Fin n}
    (huv : reach G u v) (hvw : reach G v w) : reach G u w :=
  huv.trans hvw

theorem simpleGraph_reachable_iff {n : ℕ} {G : Graph n} {u v : Fin n} :
    (simpleGraph G).Reachable u v ↔ reach G u v := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  rfl

lemma mem_componentOf_iff {n : ℕ} {G : Graph n} {u v : Fin n} :
    v ∈ componentOf G u ↔ reach G u v := by
  simp [componentOf]

lemma componentOf_self {n : ℕ} (G : Graph n) (u : Fin n) : u ∈ componentOf G u :=
  mem_componentOf_iff.mpr (reach_refl u)

lemma componentOf_eq_of_reach {n : ℕ} {G : Graph n} {u v : Fin n} (h : reach G u v) :
    componentOf G u = componentOf G v := by
  ext w
  simp only [mem_componentOf_iff]
  constructor
  · intro huw
    exact (reach_symm h).trans huw
  · intro hvw
    exact h.trans hvw

lemma componentOf_mem_components {n : ℕ} (G : Graph n) (u : Fin n) :
    componentOf G u ∈ components G := by
  simp [components]

lemma reach_empty_iff_eq {n : ℕ} {u v : Fin n} : reach (∅ : Graph n) u v ↔ u = v := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail h huv ih => simp [adj] at huv
  · rintro rfl
    exact reach_refl u

lemma componentOf_empty (n : ℕ) (u : Fin n) : componentOf (∅ : Graph n) u = {u} := by
  ext v
  simp only [mem_componentOf_iff, reach_empty_iff_eq, Finset.mem_singleton]
  exact eq_comm

lemma empty_rooted_full (k : ℕ) :
    ∀ S ∈ components (∅ : Graph k),
      isTree (∅ : Graph k) S ∧ (S ∩ (Finset.univ : Finset (Fin k))).card = 1 := by
  intro S hS
  simp only [components, Finset.mem_image] at hS
  rcases hS with ⟨v, -, rfl⟩
  constructor
  · constructor
    · exact componentOf_mem_components (∅ : Graph k) v
    · simp [edgesInside, componentOf_empty]
  · simp [componentOf_empty]

lemma full_roots_force_empty {k : ℕ} {G : Graph k}
    (hG : ∀ S ∈ components G,
      isTree G S ∧ (S ∩ (Finset.univ : Finset (Fin k))).card = 1) :
    G = ∅ := by
  ext e
  simp only [Finset.notMem_empty, iff_false]
  intro he
  let u : Fin k := e.val.1
  let v : Fin k := e.val.2
  have huv : adj G u v := ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
  have hu : u ∈ componentOf G u := componentOf_self G u
  have hv : v ∈ componentOf G u := mem_componentOf_iff.mpr (reach_of_adj huv)
  have hne : u ≠ v := by
    intro huv'
    have : e.val.1 < e.val.1 := by simpa [u, v, huv'] using! e.property
    exact (lt_irrefl _ this)
  have hcardgt : 1 < (componentOf G u).card :=
    Finset.one_lt_card.mpr ⟨u, hu, v, hv, hne⟩
  have hcard := (hG (componentOf G u) (componentOf_mem_components G u)).2
  simp only [Finset.inter_univ] at hcard
  omega

theorem rootedForestCount_full (k : ℕ) (roots : Finset (Fin k))
    (hroots : roots.card = k) : rootedForestCount k roots = 1 := by
  have hru : roots = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa using! hroots
  subst roots
  unfold rootedForestCount allGraphs
  have hfilter :
      (Finset.univ.powerset.filter (fun G : Graph k =>
        ∀ S ∈ components G, isTree G S ∧
          (S ∩ (Finset.univ : Finset (Fin k))).card = 1)) = {∅} := by
    ext G
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ,
      true_and, Finset.mem_singleton]
    constructor
    · exact full_roots_force_empty
    · rintro rfl
      exact empty_rooted_full k
  rw [hfilter, Finset.card_singleton]

theorem rootedForestCount_empty {k : ℕ} (hk : 0 < k) :
    rootedForestCount k (∅ : Finset (Fin k)) = 0 := by
  unfold rootedForestCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro G hG hroot
  let u : Fin k := ⟨0, hk⟩
  have h := (hroot (componentOf G u) (componentOf_mem_components G u)).2
  simpa using! h

lemma componentOf_eq_univ_of_connected {k : ℕ} {G : Graph k}
    (hconn : ∀ u v : Fin k, reach G u v) (u : Fin k) : componentOf G u = Finset.univ := by
  ext v
  simp [mem_componentOf_iff, hconn]

lemma edgesInside_univ {k : ℕ} (G : Graph k) :
    edgesInside G (Finset.univ : Finset (Fin k)) = G.card := by
  simp [edgesInside]

lemma connected_fixed_iff_rooted_singleton {k : ℕ} (hk : 0 < k) (r : Fin k) (G : Graph k) :
    (G ∈ fixedGraphs k (k - 1) ∧ ∀ u v : Fin k, reach G u v) ↔
      (G ∈ allGraphs k ∧ ∀ S ∈ components G,
        isTree G S ∧ (S ∩ {r}).card = 1) := by
  constructor
  · rintro ⟨hG, hconn⟩
    have hcard : G.card = k - 1 := (Finset.mem_filter.mp hG).2
    refine ⟨(Finset.mem_filter.mp hG).1, ?_⟩
    intro S hS
    simp only [components, Finset.mem_image] at hS
    rcases hS with ⟨u, -, rfl⟩
    have hcu := componentOf_eq_univ_of_connected hconn u
    constructor
    · constructor
      · exact componentOf_mem_components G u
      · rw [hcu, edgesInside_univ, hcard]
        have hfin : (Finset.univ : Finset (Fin k)).card = k := by simp
        rw [hfin]
        omega
    · rw [hcu]
      simp
  · rintro ⟨hG, hroot⟩
    have hconn : ∀ u v : Fin k, reach G u v := by
      intro u v
      have hru : r ∈ componentOf G u := by
        have hc := (hroot (componentOf G u) (componentOf_mem_components G u)).2
        rw [Finset.inter_singleton] at hc
        split at hc <;> simp_all
      have hrv : r ∈ componentOf G v := by
        have hc := (hroot (componentOf G v) (componentOf_mem_components G v)).2
        rw [Finset.inter_singleton] at hc
        split at hc <;> simp_all
      exact (mem_componentOf_iff.mp hru).trans (reach_symm (mem_componentOf_iff.mp hrv))
    have hcr : componentOf G r = Finset.univ := componentOf_eq_univ_of_connected hconn r
    have htree := (hroot (componentOf G r) (componentOf_mem_components G r)).1.2
    rw [hcr, edgesInside_univ] at htree
    have htree' : G.card + 1 = k := by simpa using! htree
    have hcard : G.card = k - 1 := by omega
    refine ⟨?_, hconn⟩
    exact Finset.mem_filter.mpr ⟨hG, hcard⟩

lemma connectedCount_eq_rootedForestCount_singleton (k : ℕ) (hk : 0 < k) (r : Fin k) :
    connectedCount k (k - 1) = rootedForestCount k {r} := by
  unfold connectedCount fixedGraphs rootedForestCount
  rw [Finset.filter_filter]
  apply congrArg Finset.card
  ext G
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hG, hcard, -, hconn⟩
    exact (connected_fixed_iff_rooted_singleton hk r G).mp
      ⟨Finset.mem_filter.mpr ⟨hG, hcard⟩, hconn⟩
  · intro h
    have hc := (connected_fixed_iff_rooted_singleton hk r G).mpr h
    exact ⟨(Finset.mem_filter.mp hc.1).1, (Finset.mem_filter.mp hc.1).2, hk, hc.2⟩

lemma cayley_of_rootedForest_formula
    (hforest : RootedForestFormula) : CayleyBridge := by
  intro k hk
  let r : Fin k := ⟨0, hk⟩
  rw [connectedCount_eq_rootedForestCount_singleton k hk r, hforest k {r}]
  simp only [Finset.card_singleton]
  rcases Nat.eq_or_lt_of_le hk with rfl | hk2
  · simp [cayley]
  · rw [if_neg hk2.ne'.symm]
    simp only [one_mul]
    unfold cayley
    rw [if_neg hk.ne', if_neg hk2.ne']
    rw [Nat.sub_sub]

theorem treeCore_of_rootedForest_formula (hforest : RootedForestFormula) :
    TreeCoreStatement :=
  ⟨hforest, cayley_of_rootedForest_formula hforest⟩

/-- Exact telescope boundary for the generalized Pruefer worker. -/
theorem result (hforest : RootedForestFormula) : TreeCoreStatement :=
  treeCore_of_rootedForest_formula hforest

end Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Trees


/-!
The exact finite-law portion of `FiniteEnumerationStatement`.  The Cayley
enumeration is supplied by the sibling tree module; it is an explicit telescope
input because the ordered-tree-tuple count genuinely uses it.
-/
namespace Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Finite

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Trees

def CayleyBridge : Prop :=
  ∀ k : ℕ, 0 < k → connectedCount k (k - 1) = cayley k

def FiniteCoreStatement : Prop :=
  (∀ n M : ℕ, M ≤ capacity n → expectM n M (fun _ => 1) = 1) ∧
  (∀ (n M : ℕ) (yes no query : Graph n), M ≤ capacity n →
    Disjoint yes no → Disjoint query (yes ∪ no) →
    0 < probM n M (patternEvent yes no) → ∀ y : ℕ,
    conditionalProbM n M (patternEvent yes no) (fun G => (G ∩ query).card = y) =
      hypergeomMass (capacity n - yes.card - no.card) (M - yes.card) query.card y) ∧
  (∀ (n M t : ℕ) (A : Graph n → Prop), M + t ≤ capacity n →
    expectM n M (fun G => growProb G t A) = probM n (M + t) A) ∧
  (∀ (n : ℕ) (G query : Graph n) (t : ℕ), G.card + t ≤ capacity n →
    Disjoint G query →
    growProb G t (fun H => Disjoint H query) =
      ((capacity n - G.card - query.card).choose t : ℝ) /
        ((capacity n - G.card).choose t : ℝ) ∧
    growProb G t (fun H => Disjoint H query) ≤
      Real.exp (-(t : ℝ) * query.card / (capacity n : ℝ))) ∧
  (∀ n M k e : ℕ, M ≤ capacity n →
    expectM n M (fun G => (componentCount G k e : ℝ)) = componentFormula n M k e) ∧
  (∀ (n M q : ℕ) (ks : Fin q → ℕ), M ≤ capacity n →
    tupleMoment n M q ks = tupleFormula n M q ks) ∧
  (∀ n M q h : ℕ, M ≤ capacity n → 0 < h →
    expectM n M (fun G => (falling (treeCountGE G h) q : ℝ)) =
      ∑ ks : Fin q → Fin (n + 1),
        if ∀ i, h ≤ (ks i).val then tupleFormula n M q (fun i => (ks i).val) else 0)

private def edgeSigmaEquiv (n : ℕ) : Edge n ≃ Σ j : Fin n, Fin j.val where
  toFun e := ⟨e.1.2, ⟨e.1.1, e.2⟩⟩
  invFun e :=
    ⟨(⟨e.2.val, e.2.isLt.trans e.1.isLt⟩, e.1), e.2.isLt⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e with | mk j i => cases i; rfl

theorem card_edge (n : ℕ) : Fintype.card (Edge n) = capacity n := by
  rw [Fintype.card_congr (edgeSigmaEquiv n), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [show (∑ x : Fin n, x.val) = ∑ i ∈ Finset.range n, i from
    Fin.sum_univ_eq_sum_range id n, Finset.sum_range_id]
  exact (Nat.choose_two_right n).symm

theorem card_fixedGraphs (n M : ℕ) :
    (fixedGraphs n M).card = (capacity n).choose M := by
  rw [fixedGraphs, allGraphs, ← Finset.powersetCard_eq_filter,
    Finset.card_powersetCard]
  simp [card_edge]

theorem fixedGraphs_nonempty {n M : ℕ} (hM : M ≤ capacity n) :
    (fixedGraphs n M).Nonempty := by
  rw [← Finset.card_pos, card_fixedGraphs]
  exact Nat.choose_pos hM

theorem normalization (n M : ℕ) (hM : M ≤ capacity n) :
    expectM n M (fun _ => 1) = 1 := by
  unfold expectM
  rw [Finset.sum_const, nsmul_eq_mul]
  simp only [mul_one]
  have hne : ((fixedGraphs n M).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr (fixedGraphs_nonempty hM))
  exact div_self hne

variable {α : Type*} [Fintype α] [DecidableEq α]

private lemma inter_mem_left (U Q : Finset α) (R y : ℕ)
    (S : ↑((U.powersetCard R).filter (fun T => (T ∩ Q).card = y))) :
    S.1 ∩ Q ∈ Q.powersetCard y := by
  rcases Finset.mem_filter.mp S.2 with ⟨hSp, hSc⟩
  exact Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hSc⟩

private lemma sdiff_mem_right (U Q : Finset α) (R y : ℕ)
    (S : ↑((U.powersetCard R).filter (fun T => (T ∩ Q).card = y))) :
    S.1 \ Q ∈ (U \ Q).powersetCard (R - y) := by
  rcases Finset.mem_filter.mp S.2 with ⟨hSp, hSc⟩
  rcases Finset.mem_powersetCard.mp hSp with ⟨hSU, hSR⟩
  apply Finset.mem_powersetCard.mpr
  refine ⟨Finset.sdiff_subset_sdiff hSU (fun _ h => h), ?_⟩
  rw [Finset.card_sdiff, Finset.inter_comm, hSR, hSc]

private lemma union_mem_source (U Q : Finset α) (R y : ℕ) (hyR : y ≤ R)
    (hQU : Q ⊆ U) (P : ↑(Q.powersetCard y) × ↑((U \ Q).powersetCard (R - y))) :
    P.1.1 ∪ P.2.1 ∈ (U.powersetCard R).filter (fun T => (T ∩ Q).card = y) := by
  have hA := Finset.mem_powersetCard.mp P.1.2
  have hB := Finset.mem_powersetCard.mp P.2.2
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · apply Finset.mem_powersetCard.mpr
    constructor
    · apply Finset.union_subset (hA.1.trans hQU)
      exact hB.1.trans Finset.sdiff_subset
    · rw [Finset.card_union_of_disjoint]
      · omega
      · exact Finset.disjoint_left.mpr (by
          intro a ha hb
          have haQ := hA.1 ha
          exact (Finset.mem_sdiff.mp (hB.1 hb)).2 haQ)
  · have hdis : Disjoint P.2.1 Q := Finset.disjoint_left.mpr (by
      intro a ha hq
      exact (Finset.mem_sdiff.mp (hB.1 ha)).2 hq)
    rw [Finset.union_inter_distrib_right]
    rw [Finset.inter_eq_left.mpr hA.1]
    rw [Finset.disjoint_iff_inter_eq_empty.mp hdis]
    simp [hA.2]

private def splitEquiv (U Q : Finset α) (R y : ℕ) (hyR : y ≤ R) (hQU : Q ⊆ U) :
    ↑((U.powersetCard R).filter (fun T => (T ∩ Q).card = y)) ≃
      ↑(Q.powersetCard y) × ↑((U \ Q).powersetCard (R - y)) where
  toFun S := (⟨S.1 ∩ Q, inter_mem_left U Q R y S⟩,
    ⟨S.1 \ Q, sdiff_mem_right U Q R y S⟩)
  invFun P := ⟨P.1.1 ∪ P.2.1, union_mem_source U Q R y hyR hQU P⟩
  left_inv S := by
    dsimp
    apply Subtype.ext
    ext a
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro (⟨ha, -⟩ | ⟨ha, -⟩) <;> exact ha
    · intro ha
      by_cases hq : a ∈ Q
      · exact Or.inl ⟨ha, hq⟩
      · exact Or.inr ⟨ha, hq⟩
  right_inv P := by
    rcases P with ⟨A, B⟩
    dsimp
    have hA := Finset.mem_powersetCard.mp A.2
    have hB := Finset.mem_powersetCard.mp B.2
    apply Prod.ext
    · apply Subtype.ext
      ext a
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨ha | hb, hq⟩
        · exact ha
        · exact False.elim ((Finset.mem_sdiff.mp (hB.1 hb)).2 hq)
      · intro ha
        exact ⟨Or.inl ha, hA.1 ha⟩
    · apply Subtype.ext
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨ha | hb, hnq⟩
        · exact False.elim (hnq (hA.1 ha))
        · exact hb
      · intro hb
        exact ⟨Or.inr hb, (Finset.mem_sdiff.mp (hB.1 hb)).2⟩

theorem card_uniform_inter (U Q : Finset α) (R y : ℕ) (hyR : y ≤ R) (hQU : Q ⊆ U) :
    ((U.powersetCard R).filter (fun S => (S ∩ Q).card = y)).card =
      Q.card.choose y * (U.card - Q.card).choose (R - y) := by
  calc
    _ = Fintype.card
        (↑((U.powersetCard R).filter (fun T => (T ∩ Q).card = y))) :=
          (Fintype.card_coe _).symm
    _ = Fintype.card
        (↑(Q.powersetCard y) × ↑((U \ Q).powersetCard (R - y))) :=
          Fintype.card_congr (splitEquiv U Q R y hyR hQU)
    _ = _ := by
      rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe,
        Finset.card_powersetCard, Finset.card_powersetCard,
        Finset.card_sdiff_of_subset hQU]


def completions (U G : Finset α) (t : ℕ) : Finset (Finset α) :=
  U.powerset.filter (fun H => G ⊆ H ∧ H.card = G.card + t)

private lemma add_mem_completion (U G : Finset α) (t : ℕ) (hGU : G ⊆ U)
    (F : ↑((U \ G).powersetCard t)) : G ∪ F.1 ∈ completions U G t := by
  rw [completions, Finset.mem_filter, Finset.mem_powerset]
  have hF := Finset.mem_powersetCard.mp F.2
  constructor
  · exact Finset.union_subset hGU (hF.1.trans Finset.sdiff_subset)
  constructor
  · exact Finset.subset_union_left
  · rw [Finset.card_union_of_disjoint]
    · rw [hF.2]
    · exact Finset.disjoint_left.mpr (by
        intro a haG haF
        exact (Finset.mem_sdiff.mp (hF.1 haF)).2 haG)

private lemma remove_mem_additions (U G : Finset α) (t : ℕ)
    (H : ↑(completions U G t)) : H.1 \ G ∈ (U \ G).powersetCard t := by
  have hmem := H.2
  change H.1 ∈ U.powerset.filter (fun H => G ⊆ H ∧ H.card = G.card + t) at hmem
  rcases Finset.mem_filter.mp hmem with ⟨hpow, hGH, hcard⟩
  have hHU := Finset.mem_powerset.mp hpow
  apply Finset.mem_powersetCard.mpr
  constructor
  · exact Finset.sdiff_subset_sdiff hHU (fun _ h => h)
  · rw [Finset.card_sdiff_of_subset hGH, hcard]
    omega

def completionEquiv (U G : Finset α) (t : ℕ) (hGU : G ⊆ U) :
    ↑(completions U G t) ≃ ↑((U \ G).powersetCard t) where
  toFun H := ⟨H.1 \ G, remove_mem_additions U G t H⟩
  invFun F := ⟨G ∪ F.1, add_mem_completion U G t hGU F⟩
  left_inv H := by
    dsimp
    apply Subtype.ext
    change G ∪ (H.1 \ G) = H.1
    apply Finset.union_sdiff_of_subset
    exact (Finset.mem_filter.mp H.2).2.1
  right_inv F := by
    dsimp
    apply Subtype.ext
    ext a
    have hF := Finset.mem_powersetCard.mp F.2
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨ha | ha, hnG⟩
      · exact False.elim (hnG ha)
      · exact ha
    · intro ha
      exact ⟨Or.inr ha, (Finset.mem_sdiff.mp (hF.1 ha)).2⟩

theorem card_completions (U G : Finset α) (t : ℕ) (hGU : G ⊆ U) :
    (completions U G t).card = (U.card - G.card).choose t := by
  calc
    _ = Fintype.card ↑(completions U G t) := (Fintype.card_coe _).symm
    _ = Fintype.card ↑((U \ G).powersetCard t) :=
      Fintype.card_congr (completionEquiv U G t hGU)
    _ = _ := by
      rw [Fintype.card_coe, Finset.card_powersetCard,
        Finset.card_sdiff_of_subset hGU]


def avoidCompletions (U G Q : Finset α) (t : ℕ) : Finset (Finset α) :=
  (completions U G t).filter (fun H => Disjoint H Q)

private def avoidAdditions (U G Q : Finset α) (t : ℕ) : Finset (Finset α) :=
  ((U \ G).powersetCard t).filter (fun F => Disjoint F Q)

private lemma completion_disjoint_iff (G Q F : Finset α) (hGQ : Disjoint G Q) :
    Disjoint (G ∪ F) Q ↔ Disjoint F Q := by
  simp only [Finset.disjoint_union_left]
  exact and_iff_right hGQ

private def avoidEquiv (U G Q : Finset α) (t : ℕ) (hGU : G ⊆ U)
    (hGQ : Disjoint G Q) : ↑(avoidCompletions U G Q t) ≃ ↑(avoidAdditions U G Q t) where
  toFun H := by
    have hbase : H.1 ∈ completions U G t := (Finset.mem_filter.mp H.2).1
    let H0 : ↑(completions U G t) := ⟨H.1, hbase⟩
    let F := completionEquiv U G t hGU H0
    refine ⟨F.1, Finset.mem_filter.mpr ⟨F.2, ?_⟩⟩
    have hHQ : Disjoint H.1 Q := (Finset.mem_filter.mp H.2).2
    exact hHQ.mono_left Finset.sdiff_subset
  invFun F := by
    have hbase : F.1 ∈ (U \ G).powersetCard t := (Finset.mem_filter.mp F.2).1
    let F0 : ↑((U \ G).powersetCard t) := ⟨F.1, hbase⟩
    let H := (completionEquiv U G t hGU).symm F0
    refine ⟨H.1, Finset.mem_filter.mpr ⟨H.2, ?_⟩⟩
    change Disjoint (G ∪ F.1) Q
    exact (completion_disjoint_iff G Q F.1 hGQ).mpr (Finset.mem_filter.mp F.2).2
  left_inv H := by
    apply Subtype.ext
    simpa only using! congrArg Subtype.val ((completionEquiv U G t hGU).symm_apply_apply
      ⟨H.1, (Finset.mem_filter.mp H.2).1⟩)
  right_inv F := by
    apply Subtype.ext
    simpa only using! congrArg Subtype.val ((completionEquiv U G t hGU).apply_symm_apply
      ⟨F.1, (Finset.mem_filter.mp F.2).1⟩)

theorem card_avoiding_completions (U G Q : Finset α) (t : ℕ)
    (hGU : G ⊆ U) (hQU : Q ⊆ U) (hGQ : Disjoint G Q) :
    (avoidCompletions U G Q t).card =
      (U.card - G.card - Q.card).choose t := by
  have hQU' : Q ⊆ U \ G := by
    intro a haQ
    exact Finset.mem_sdiff.mpr ⟨hQU haQ, fun haG =>
      Finset.disjoint_left.mp hGQ haG haQ⟩
  have hfilter : avoidAdditions U G Q t =
      ((U \ G).powersetCard t).filter (fun F => (F ∩ Q).card = 0) := by
    ext F
    simp only [avoidAdditions, Finset.mem_filter]
    congr 1
    rw [Finset.disjoint_iff_inter_eq_empty, Finset.card_eq_zero]
  calc
    _ = Fintype.card ↑(avoidCompletions U G Q t) := (Fintype.card_coe _).symm
    _ = Fintype.card ↑(avoidAdditions U G Q t) :=
      Fintype.card_congr (avoidEquiv U G Q t hGU hGQ)
    _ = (avoidAdditions U G Q t).card := Fintype.card_coe _
    _ = _ := by
      rw [hfilter, card_uniform_inter (U \ G) Q t 0 (Nat.zero_le _) hQU']
      rw [Finset.card_sdiff_of_subset hGU]
      simp

theorem grow_avoid_exact (n : ℕ) (G query : Graph n) (t : ℕ)
    (_hGt : G.card + t ≤ capacity n) (hGQ : Disjoint G query) :
    growProb G t (fun H => Disjoint H query) =
      ((capacity n - G.card - query.card).choose t : ℝ) /
        ((capacity n - G.card).choose t : ℝ) := by
  have hGU : G ⊆ (Finset.univ : Finset (Edge n)) := Finset.subset_univ G
  have hQU : query ⊆ (Finset.univ : Finset (Edge n)) := Finset.subset_univ query
  have hcardU : (Finset.univ : Finset (Edge n)).card = capacity n := by
    rw [Finset.card_univ, card_edge]
  unfold growProb
  simp only [allGraphs]
  have hcomp : (Finset.univ : Finset (Edge n)).powerset.filter
      (fun H => G ⊆ H ∧ H.card = G.card + t) =
      completions (Finset.univ : Finset (Edge n)) G t := rfl
  rw [hcomp]
  congr 1
  · norm_cast
    calc
      _ = (avoidCompletions (Finset.univ : Finset (Edge n)) G query t).card := by
        congr 1
        ext H
        simp [avoidCompletions]
      _ = _ := by
        simpa only [hcardU] using!
          card_avoiding_completions (Finset.univ : Finset (Edge n)) G query t hGU hQU hGQ
  · norm_cast
    simpa only [hcardU] using!
      card_completions (Finset.univ : Finset (Edge n)) G t hGU


private lemma choose_ratio_step (A E t : ℕ) (htA : t + 1 ≤ A) (htE : t + 1 ≤ E) :
    (A.choose (t + 1) : ℝ) / (E.choose (t + 1) : ℝ) =
      ((A.choose t : ℝ) / (E.choose t : ℝ)) * ((A - t : ℕ) : ℝ) / (E - t : ℕ) := by
  have hAt : 0 < A.choose t := Nat.choose_pos (by omega)
  have hEt : 0 < E.choose t := Nat.choose_pos (by omega)
  have hAs : 0 < A.choose (t + 1) := Nat.choose_pos htA
  have hEs : 0 < E.choose (t + 1) := Nat.choose_pos htE
  have hA := Nat.choose_succ_right_eq A t
  have hE := Nat.choose_succ_right_eq E t
  have hAr0 := congrArg (fun z : ℕ => (z : ℝ)) hA
  have hEr0 := congrArg (fun z : ℕ => (z : ℝ)) hE
  have hAr : (A.choose (t + 1) : ℝ) * (t + 1) =
      (A.choose t : ℝ) * ((A - t : ℕ) : ℝ) := by
    norm_num at hAr0 ⊢
    exact hAr0
  have hEr : (E.choose (t + 1) : ℝ) * (t + 1) =
      (E.choose t : ℝ) * ((E - t : ℕ) : ℝ) := by
    norm_num at hEr0 ⊢
    exact hEr0
  have hEt' : ((E.choose t : ℝ) ≠ 0) := by exact_mod_cast hEt.ne'
  have hEs' : ((E.choose (t + 1) : ℝ) ≠ 0) := by exact_mod_cast hEs.ne'
  have hdiff : (((E - t : ℕ) : ℝ) ≠ 0) := by
    exact_mod_cast (show E - t ≠ 0 by omega)
  field_simp [hEt', hEs', hdiff]
  nlinarith [hAr, hEr]

theorem choose_ratio_exp (N E d t : ℕ) (hEN : E ≤ N) (hdE : d ≤ E) (htE : t ≤ E) :
    ((E - d).choose t : ℝ) / (E.choose t : ℝ) ≤
      Real.exp (-(t : ℝ) * d / (N : ℝ)) := by
  by_cases hN : N = 0
  · subst N
    have : E = 0 := by omega
    subst E
    have : d = 0 := by omega
    subst d
    have : t = 0 := by omega
    subst t
    simp
  induction t with
  | zero => simp
  | succ t ih =>
      have htE' : t ≤ E := by omega
      have hi := ih htE'
      by_cases htA : t + 1 ≤ E - d
      · rw [choose_ratio_step (E - d) E t htA htE]
        have hEt : 0 < (E - t : ℕ) := by omega
        have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
        have hEtpos : (0 : ℝ) < ((E - t : ℕ) : ℝ) := by exact_mod_cast hEt
        have hNt : (((E - t : ℕ) : ℝ)) ≤ N := by
          exact_mod_cast (Nat.sub_le E t |>.trans hEN)
        have hdEt : (d : ℝ) / N ≤ (d : ℝ) / (E - t : ℕ) := by
          exact div_le_div_of_nonneg_left (Nat.cast_nonneg d) hEtpos hNt
        have hfactor : ((E - d - t : ℕ) : ℝ) / (E - t : ℕ) ≤
            Real.exp (-(d : ℝ) / N) := by
          have hsub : ((E - d - t : ℕ) : ℝ) = (E - t : ℕ) - d := by
            have hn : E - d - t = E - t - d := by omega
            rw [hn, Nat.cast_sub (by omega)]
          rw [hsub]
          calc
            ((E - t : ℕ) - d : ℝ) / (E - t : ℕ) =
                1 - (d : ℝ) / (E - t : ℕ) := by field_simp
            _ ≤ Real.exp (-((d : ℝ) / (E - t : ℕ))) := Real.one_sub_le_exp_neg _
            _ ≤ Real.exp (-(d : ℝ) / N) := by
              apply Real.exp_le_exp.mpr
              calc
                -((d : ℝ) / (E - t : ℕ)) ≤ -((d : ℝ) / N) := neg_le_neg hdEt
                _ = -(d : ℝ) / N := by ring
        rw [mul_div_assoc]
        calc
          ((E - d).choose t : ℝ) / E.choose t *
                (((E - d - t : ℕ) : ℝ) / (E - t : ℕ)) ≤
              Real.exp (-(t : ℝ) * d / N) * Real.exp (-(d : ℝ) / N) := by
            exact mul_le_mul hi hfactor
              (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
              (Real.exp_pos _).le
          _ = Real.exp (-((t + 1 : ℕ) : ℝ) * d / N) := by
            rw [← Real.exp_add]
            congr 1
            push_cast
            field_simp
            ring
      · have hzero : (E - d).choose (t + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        simp only [hzero, Nat.cast_zero, zero_div]
        exact (Real.exp_pos _).le

theorem grow_avoid_bound (n : ℕ) (G query : Graph n) (t : ℕ)
    (hGt : G.card + t ≤ capacity n) (hGQ : Disjoint G query) :
    growProb G t (fun H => Disjoint H query) ≤
      Real.exp (-(t : ℝ) * query.card / (capacity n : ℝ)) := by
  rw [grow_avoid_exact n G query t hGt hGQ]
  have hsum : G.card + query.card ≤ capacity n := by
    have hu : G ∪ query ⊆ (Finset.univ : Finset (Edge n)) := Finset.subset_univ _
    have hc := Finset.card_le_card hu
    rw [Finset.card_union_of_disjoint hGQ, Finset.card_univ, card_edge] at hc
    exact hc
  apply choose_ratio_exp (capacity n) (capacity n - G.card) query.card t
  · omega
  · omega
  · omega

private def goodTargets (U : Finset α) (L : ℕ) (A : Finset α → Prop) :
    Finset (Finset α) := (U.powersetCard L).filter A

private lemma completion_target_mem (U : Finset α) (M t : ℕ) (A : Finset α → Prop)
    (P : Σ G : ↑(U.powersetCard M),
      ↑((completions U G.1 t).filter A)) :
    P.2.1 ∈ goodTargets U (M + t) A := by
  rcases Finset.mem_filter.mp P.2.2 with ⟨hcomp, hA⟩
  have hc := Finset.mem_filter.mp hcomp
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hc.1, by
      rw [hc.2.2, (Finset.mem_powersetCard.mp P.1.2).2]⟩
  · exact hA

private lemma predecessor_mem (U : Finset α) (M t : ℕ) (A : Finset α → Prop)
    (P : Σ H : ↑(goodTargets U (M + t) A), ↑(H.1.powersetCard M)) :
    P.2.1 ∈ U.powersetCard M := by
  have hH := Finset.mem_filter.mp P.1.2
  have hG := Finset.mem_powersetCard.mp P.2.2
  exact Finset.mem_powersetCard.mpr ⟨hG.1.trans (Finset.mem_powersetCard.mp hH.1).1, hG.2⟩

private lemma target_completion_mem (U : Finset α) (M t : ℕ) (A : Finset α → Prop)
    (P : Σ H : ↑(goodTargets U (M + t) A), ↑(H.1.powersetCard M)) :
    P.1.1 ∈ (completions U P.2.1 t).filter A := by
  have hH := Finset.mem_filter.mp P.1.2
  have hG := Finset.mem_powersetCard.mp P.2.2
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hH.1).1,
      hG.1, by rw [(Finset.mem_powersetCard.mp hH.1).2, hG.2]⟩
  · exact hH.2

private def completionSwap (U : Finset α) (M t : ℕ) (A : Finset α → Prop) :
    (Σ G : ↑(U.powersetCard M), ↑((completions U G.1 t).filter A)) ≃
      (Σ H : ↑(goodTargets U (M + t) A), ↑(H.1.powersetCard M)) where
  toFun P := ⟨⟨P.2.1, completion_target_mem U M t A P⟩,
    ⟨P.1.1, Finset.mem_powersetCard.mpr ⟨(Finset.mem_filter.mp
      (Finset.mem_filter.mp P.2.2).1).2.1, (Finset.mem_powersetCard.mp P.1.2).2⟩⟩⟩
  invFun P := ⟨⟨P.2.1, predecessor_mem U M t A P⟩,
    ⟨P.1.1, target_completion_mem U M t A P⟩⟩
  left_inv P := by cases P; rfl
  right_inv P := by cases P; rfl

theorem sum_completion_counts (U : Finset α) (M t : ℕ) (A : Finset α → Prop) :
    ∑ G ∈ U.powersetCard M, ((completions U G t).filter A).card =
      (goodTargets U (M + t) A).card * (M + t).choose M := by
  have hcard := Fintype.card_congr (completionSwap U M t A)
  rw [Fintype.card_sigma, Fintype.card_sigma] at hcard
  simp only [Fintype.card_coe] at hcard
  have hleft : (∑ x : ↑(U.powersetCard M),
      ((completions U x.1 t).filter A).card) =
      ∑ G ∈ U.powersetCard M, ((completions U G t).filter A).card := by
    calc
      _ = ∑ x ∈ (U.powersetCard M).attach,
          ((completions U x.1 t).filter A).card :=
        Finset.sum_coe_sort_eq_attach _ _
      _ = _ := by
        simpa only using! Finset.sum_attach (U.powersetCard M)
          (fun G => ((completions U G t).filter A).card)
  have hright : (∑ x : ↑(goodTargets U (M + t) A),
      (x.1.powersetCard M).card) =
      ∑ H ∈ goodTargets U (M + t) A, (H.powersetCard M).card := by
    calc
      _ = ∑ x ∈ (goodTargets U (M + t) A).attach,
          (x.1.powersetCard M).card := Finset.sum_coe_sort_eq_attach _ _
      _ = _ := by
        simpa only using! Finset.sum_attach (goodTargets U (M + t) A)
          (fun H => (H.powersetCard M).card)
  rw [hleft, hright] at hcard
  calc
    _ = ∑ H ∈ goodTargets U (M + t) A, (H.powersetCard M).card := hcard
    _ = _ := by
      apply Finset.sum_const_nat
      intro H hH
      rw [Finset.card_powersetCard]
      exact congrArg (fun z => z.choose M) (Finset.mem_powersetCard.mp
        (Finset.mem_filter.mp hH).1).2

theorem average_completion (U : Finset α) (M t : ℕ) (A : Finset α → Prop)
    (hMt : M + t ≤ U.card) :
    (∑ G ∈ U.powersetCard M,
      (((completions U G t).filter A).card : ℝ) / ((completions U G t).card : ℝ)) /
        (U.card.choose M : ℝ) =
      ((goodTargets U (M + t) A).card : ℝ) / (U.card.choose (M + t) : ℝ) := by
  have hM : M ≤ U.card := by omega
  have hchooseM : (U.card.choose M : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hM).ne'
  have hchooseT : ((U.card - M).choose t : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hchooseMt : (U.card.choose (M + t) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hMt).ne'
  have hden : ∀ G ∈ U.powersetCard M,
      ((completions U G t).card : ℝ) = ((U.card - M).choose t : ℝ) := by
    intro G hG
    have hc := card_completions U G t (Finset.mem_powersetCard.mp hG).1
    rw [(Finset.mem_powersetCard.mp hG).2] at hc
    exact_mod_cast hc
  have hsum : (∑ G ∈ U.powersetCard M,
      (((completions U G t).filter A).card : ℝ) / ((completions U G t).card : ℝ)) =
      ((∑ G ∈ U.powersetCard M, ((completions U G t).filter A).card : ℕ) : ℝ) /
        ((U.card - M).choose t : ℝ) := by
    calc
      _ = ∑ G ∈ U.powersetCard M,
          (((completions U G t).filter A).card : ℝ) /
            ((U.card - M).choose t : ℝ) := by
        apply Finset.sum_congr rfl
        intro G hG
        rw [hden G hG]
      _ = (∑ G ∈ U.powersetCard M,
          (((completions U G t).filter A).card : ℝ)) /
            ((U.card - M).choose t : ℝ) := by
        rw [← Finset.sum_div]
      _ = _ := by
        congr 1
        norm_cast
  rw [hsum]
  have hcount := sum_completion_counts U M t A
  have hchoose := Nat.choose_mul (n := U.card) (k := M + t) (s := M) (by omega)
  have hchoose' : U.card.choose M * (U.card - M).choose t =
      U.card.choose (M + t) * (M + t).choose M := by
    have hsub : M + t - M = t := by omega
    rw [hsub] at hchoose
    exact hchoose.symm
  have hcountR := congrArg (fun z : ℕ => (z : ℝ)) hcount
  have hchooseR := congrArg (fun z : ℕ => (z : ℝ)) hchoose'
  norm_num at hcountR hchooseR
  push_cast
  field_simp [hchooseM, hchooseT, hchooseMt]
  nlinarith [hcountR, hchooseR]

theorem growth_averaging (n M t : ℕ) (A : Graph n → Prop)
    (hMt : M + t ≤ capacity n) :
    expectM n M (fun G => growProb G t A) = probM n (M + t) A := by
  let U : Finset (Edge n) := Finset.univ
  have hcardU : U.card = capacity n := by
    dsimp [U]
    exact card_edge n
  have hfixM : fixedGraphs n M = U.powersetCard M := by
    ext G
    simp only [fixedGraphs, allGraphs, Finset.mem_filter, Finset.mem_powerset,
      Finset.mem_powersetCard]
    tauto
  have hfixMt : fixedGraphs n (M + t) = U.powersetCard (M + t) := by
    ext G
    simp only [fixedGraphs, allGraphs, Finset.mem_filter, Finset.mem_powerset,
      Finset.mem_powersetCard]
    tauto
  unfold expectM probM
  rw [hfixM, hfixMt]
  have havg := average_completion U M t A (by simpa only [hcardU] using! hMt)
  have hleft :
      (∑ G ∈ U.powersetCard M, growProb G t A) /
          ((U.powersetCard M).card : ℝ) =
      (∑ G ∈ U.powersetCard M,
        (((completions U G t).filter A).card : ℝ) /
          ((completions U G t).card : ℝ)) /
            (U.card.choose M : ℝ) := by
    have hs : (∑ G ∈ U.powersetCard M, growProb G t A) =
        ∑ G ∈ U.powersetCard M,
          (((completions U G t).filter A).card : ℝ) /
            ((completions U G t).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro G hG
      unfold growProb
      simp only [allGraphs]
      congr 2 <;> congr 1 <;> ext H <;> simp [completions, U]
    have hd : ((U.powersetCard M).card : ℝ) = (U.card.choose M : ℝ) := by
      norm_cast
      exact Finset.card_powersetCard M U
    rw [hs, hd]
  have hright : (((U.powersetCard (M + t)).filter A).card : ℝ) /
        ((U.powersetCard (M + t)).card : ℝ) =
      ((goodTargets U (M + t) A).card : ℝ) /
        (U.card.choose (M + t) : ℝ) := by
    have hn : (((U.powersetCard (M + t)).filter A).card : ℝ) =
        (goodTargets U (M + t) A).card := by
      norm_cast
    have hd : ((U.powersetCard (M + t)).card : ℝ) =
        (U.card.choose (M + t) : ℝ) := by
      norm_cast
      exact Finset.card_powersetCard (M + t) U
    rw [hn, hd]
  rw [hleft, hright]
  exact havg

theorem hypergeom_symmetry (E R d y : ℕ) (hRE : R ≤ E) (hdE : d ≤ E)
    (hyR : y ≤ R) :
    (d.choose y : ℝ) * ((E - d).choose (R - y) : ℝ) / (E.choose R : ℝ) =
      hypergeomMass E R d y := by
  by_cases hyd : y ≤ d
  · rw [hypergeomMass, if_pos ⟨hRE, hdE, hyd⟩]
    by_cases hfeas : R + d - y ≤ E
    · have hER : (E.choose R : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos hRE).ne'
      have hEd : (E.choose d : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos hdE).ne'
      have h1 := Nat.choose_mul (n := E) (k := R) (s := y) hyR
      have h2 := Nat.choose_mul (n := E) (k := d) (s := y) hyd
      have hremR : E - y - (R - y) = E - R := by omega
      have hremd : E - y - (d - y) = E - d := by omega
      have htotR : (R - y) + (d - y) - (R - y) = d - y := by omega
      have htotd : (R - y) + (d - y) - (d - y) = R - y := by omega
      have h3 := Nat.choose_mul (n := E - y) (k := (R - y) + (d - y))
        (s := R - y) (by omega)
      have h4 := Nat.choose_mul (n := E - y) (k := (R - y) + (d - y))
        (s := d - y) (by omega)
      rw [hremR, htotR] at h3
      rw [hremd, htotd] at h4
      have hcross : E.choose R * R.choose y * (E - R).choose (d - y) =
          E.choose d * d.choose y * (E - d).choose (R - y) := by
        calc
          _ = (E.choose R * R.choose y) * (E - R).choose (d - y) := by ring
          _ = (E.choose y * (E - y).choose (R - y)) *
              (E - R).choose (d - y) := by rw [h1]
          _ = E.choose y * ((E - y).choose ((R - y) + (d - y)) *
              ((R - y) + (d - y)).choose (R - y)) := by rw [h3]; ring
          _ = E.choose y * ((E - y).choose ((R - y) + (d - y)) *
              ((R - y) + (d - y)).choose (d - y)) := by
            rw [Nat.choose_symm_add]
          _ = (E.choose y * (E - y).choose (d - y)) *
              (E - d).choose (R - y) := by rw [h4]; ring
          _ = (E.choose d * d.choose y) * (E - d).choose (R - y) := by rw [h2]
          _ = _ := by ring
      have hcrossR := congrArg (fun z : ℕ => (z : ℝ)) hcross
      norm_num at hcrossR
      field_simp [hER, hEd]
      nlinarith
    · have hleft0 : (E - d).choose (R - y) = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      have hright0 : (E - R).choose (d - y) = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      simp [hleft0, hright0]
  · have hdy0 : d.choose y = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [hypergeomMass, hyd, hdy0]

private lemma sdiff_inter_eq_of_disjoint (H G Q : Finset α) (hGQ : Disjoint G Q) :
    (H \ G) ∩ Q = H ∩ Q := by
  ext a
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨haH, -⟩, haQ⟩
    exact ⟨haH, haQ⟩
  · rintro ⟨haH, haQ⟩
    exact ⟨⟨haH, fun haG => Finset.disjoint_left.mp hGQ haG haQ⟩, haQ⟩

private lemma union_inter_eq_of_disjoint (G F Q : Finset α) (hGQ : Disjoint G Q) :
    (G ∪ F) ∩ Q = F ∩ Q := by
  ext a
  simp only [Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨haG | haF, haQ⟩
    · exact False.elim (Finset.disjoint_left.mp hGQ haG haQ)
    · exact ⟨haF, haQ⟩
  · rintro ⟨haF, haQ⟩
    exact ⟨Or.inr haF, haQ⟩

private def completionInterEquiv (U G Q : Finset α) (t y : ℕ)
    (hGU : G ⊆ U) (hGQ : Disjoint G Q) :
    ↑((completions U G t).filter (fun H => (H ∩ Q).card = y)) ≃
      ↑(((U \ G).powersetCard t).filter (fun F => (F ∩ Q).card = y)) where
  toFun H := by
    let H0 : ↑(completions U G t) :=
      ⟨H.1, (Finset.mem_filter.mp H.2).1⟩
    let F := completionEquiv U G t hGU H0
    refine ⟨F.1, Finset.mem_filter.mpr ⟨F.2, ?_⟩⟩
    change ((H.1 \ G) ∩ Q).card = y
    rw [sdiff_inter_eq_of_disjoint H.1 G Q hGQ]
    exact (Finset.mem_filter.mp H.2).2
  invFun F := by
    let F0 : ↑((U \ G).powersetCard t) :=
      ⟨F.1, (Finset.mem_filter.mp F.2).1⟩
    let H := (completionEquiv U G t hGU).symm F0
    refine ⟨H.1, Finset.mem_filter.mpr ⟨H.2, ?_⟩⟩
    change ((G ∪ F.1) ∩ Q).card = y
    rw [union_inter_eq_of_disjoint G F.1 Q hGQ]
    exact (Finset.mem_filter.mp F.2).2
  left_inv H := by
    apply Subtype.ext
    simpa only using! congrArg Subtype.val ((completionEquiv U G t hGU).symm_apply_apply
      ⟨H.1, (Finset.mem_filter.mp H.2).1⟩)
  right_inv F := by
    apply Subtype.ext
    simpa only using! congrArg Subtype.val ((completionEquiv U G t hGU).apply_symm_apply
      ⟨F.1, (Finset.mem_filter.mp F.2).1⟩)

private theorem card_completion_inter (U G Q : Finset α) (t y : ℕ)
    (hGU : G ⊆ U) (hQU : Q ⊆ U) (hGQ : Disjoint G Q) (hyt : y ≤ t) :
    ((completions U G t).filter (fun H => (H ∩ Q).card = y)).card =
      Q.card.choose y * (U.card - G.card - Q.card).choose (t - y) := by
  have hQrem : Q ⊆ U \ G := by
    intro a haQ
    exact Finset.mem_sdiff.mpr ⟨hQU haQ, fun haG =>
      Finset.disjoint_left.mp hGQ haG haQ⟩
  calc
    _ = Fintype.card ↑((completions U G t).filter
        (fun H => (H ∩ Q).card = y)) := (Fintype.card_coe _).symm
    _ = Fintype.card ↑(((U \ G).powersetCard t).filter
        (fun F => (F ∩ Q).card = y)) :=
      Fintype.card_congr (completionInterEquiv U G Q t y hGU hGQ)
    _ = _ := by
      rw [Fintype.card_coe, card_uniform_inter (U \ G) Q t y hyt hQrem,
        Finset.card_sdiff_of_subset hGU]

private theorem card_completion_inter_eq_zero_of_lt (U G Q : Finset α) (t y : ℕ)
    (hGQ : Disjoint G Q) (hty : t < y) :
    ((completions U G t).filter (fun H => (H ∩ Q).card = y)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro H hH heq
  have hbase := Finset.mem_filter.mp hH
  have hdiff : (H \ G).card = t := by
    rw [Finset.card_sdiff_of_subset hbase.2.1, hbase.2.2]
    omega
  have hsub : H ∩ Q ⊆ H \ G := by
    intro a ha
    have haH := (Finset.mem_inter.mp ha).1
    have haQ := (Finset.mem_inter.mp ha).2
    exact Finset.mem_sdiff.mpr ⟨haH, fun haG =>
      Finset.disjoint_left.mp hGQ haG haQ⟩
  have := Finset.card_le_card hsub
  rw [heq, hdiff] at this
  omega

private theorem pattern_family_eq_completions (U yes no : Finset α) (M : ℕ)
    (hYM : yes.card ≤ M) :
    (U.powersetCard M).filter (fun G => yes ⊆ G ∧ Disjoint no G) =
      completions (U \ no) yes (M - yes.card) := by
  ext G
  simp only [Finset.mem_filter, Finset.mem_powersetCard, completions,
    Finset.mem_powerset]
  constructor
  · rintro ⟨⟨hGU, hGM⟩, hyesG, hnoG⟩
    refine ⟨?_, hyesG, ?_⟩
    · intro a ha
      exact Finset.mem_sdiff.mpr ⟨hGU ha, fun hno =>
        Finset.disjoint_left.mp hnoG hno ha⟩
    · omega
  · rintro ⟨hGUno, hyesG, hcard⟩
    refine ⟨⟨fun a ha => (Finset.mem_sdiff.mp (hGUno ha)).1, ?_⟩, hyesG, ?_⟩
    · omega
    · exact Finset.disjoint_left.mpr (fun a hno ha =>
        (Finset.mem_sdiff.mp (hGUno ha)).2 hno)

theorem conditional_hypergeom (n M : ℕ) (yes no query : Graph n)
    (hM : M ≤ capacity n) (hyn : Disjoint yes no)
    (hq : Disjoint query (yes ∪ no))
    (hpos : 0 < probM n M (patternEvent yes no)) (y : ℕ) :
    conditionalProbM n M (patternEvent yes no)
        (fun G => (G ∩ query).card = y) =
      hypergeomMass (capacity n - yes.card - no.card)
        (M - yes.card) query.card y := by
  let U : Finset (Edge n) := Finset.univ
  have hcardU : U.card = capacity n := by
    dsimp [U]
    exact card_edge n
  have hyesU : yes ⊆ U := Finset.subset_univ _
  have hnoU : no ⊆ U := Finset.subset_univ _
  have hqueryU : query ⊆ U := Finset.subset_univ _
  have hfixed : fixedGraphs n M = U.powersetCard M := by
    ext G
    simp only [fixedGraphs, allGraphs, Finset.mem_filter, Finset.mem_powerset,
      Finset.mem_powersetCard, U]
  have hpatternpos : 0 < (((fixedGraphs n M).filter
      (patternEvent yes no)).card : ℝ) := by
    unfold probM at hpos
    rcases (div_pos_iff.mp hpos) with h | h
    · exact h.1
    · exact False.elim ((not_lt_of_ge (Nat.cast_nonneg _)) h.1)
  obtain ⟨G, hG⟩ := Finset.card_pos.mp (by exact_mod_cast hpatternpos)
  have hGfixed := (Finset.mem_filter.mp hG).1
  have hGpattern := (Finset.mem_filter.mp hG).2
  have hyesG : yes ⊆ G := hGpattern.1
  have hGM : G.card = M := (Finset.mem_filter.mp hGfixed).2
  have hYM : yes.card ≤ M := by
    rw [← hGM]
    exact Finset.card_le_card hyesG
  have hGno : Disjoint G no := hGpattern.2.symm
  have hMno : M + no.card ≤ capacity n := by
    have hu : G ∪ no ⊆ U := Finset.union_subset
      (by simpa [U] using! Finset.subset_univ G)
      (by simpa [U] using! Finset.subset_univ no)
    have hc := Finset.card_le_card hu
    rw [Finset.card_union_of_disjoint hGno, hGM, hcardU] at hc
    exact hc
  have hqyes : Disjoint query yes := hq.mono_right Finset.subset_union_left
  have hqno : Disjoint query no := hq.mono_right Finset.subset_union_right
  have hyesQ : Disjoint yes query := hqyes.symm
  have hyesUno : yes ⊆ U \ no := by
    intro a ha
    exact Finset.mem_sdiff.mpr ⟨hyesU ha, fun hna =>
      Finset.disjoint_left.mp hyn ha hna⟩
  have hqueryUno : query ⊆ U \ no := by
    intro a ha
    exact Finset.mem_sdiff.mpr ⟨hqueryU ha, fun hna =>
      Finset.disjoint_left.mp hqno ha hna⟩
  have hsum : yes.card + no.card + query.card ≤ capacity n := by
    have hdis : Disjoint (yes ∪ no) query := hq.symm
    have hu : (yes ∪ no) ∪ query ⊆ U := Finset.subset_univ _
    have hc := Finset.card_le_card hu
    rw [Finset.card_union_of_disjoint hdis,
      Finset.card_union_of_disjoint hyn, hcardU] at hc
    exact hc
  have hRE : M - yes.card ≤ capacity n - yes.card - no.card := by omega
  have hdE : query.card ≤ capacity n - yes.card - no.card := by omega
  have hfamily : (fixedGraphs n M).filter (patternEvent yes no) =
      completions (U \ no) yes (M - yes.card) := by
    rw [hfixed]
    unfold patternEvent
    exact Finset.filter_congr_decidable _ _ _ |>.trans
      (pattern_family_eq_completions U yes no M hYM)
  have hremcard : (U \ no).card - yes.card =
      capacity n - yes.card - no.card := by
    rw [Finset.card_sdiff_of_subset hnoU, hcardU]
    omega
  have hqueryremcard : (U \ no).card - yes.card - query.card =
      capacity n - yes.card - no.card - query.card := by
    rw [Finset.card_sdiff_of_subset hnoU, hcardU]
    omega
  have hPcard : ((fixedGraphs n M).filter (patternEvent yes no)).card =
      (capacity n - yes.card - no.card).choose (M - yes.card) := by
    rw [hfamily, card_completions (U \ no) yes (M - yes.card) hyesUno,
      hremcard]
  have hPne : ((((fixedGraphs n M).filter
      (patternEvent yes no)).card : ℝ)) ≠ 0 := ne_of_gt hpatternpos
  have hBne : (((fixedGraphs n M).card : ℝ)) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr (fixedGraphs_nonempty hM))
  have hjoint : (fixedGraphs n M).filter
      (fun G => patternEvent yes no G ∧ (G ∩ query).card = y) =
      (completions (U \ no) yes (M - yes.card)).filter
        (fun G => (G ∩ query).card = y) := by
    calc
      _ = ((fixedGraphs n M).filter (patternEvent yes no)).filter
          (fun G => (G ∩ query).card = y) := by
        ext H
        simp only [Finset.mem_filter]
        tauto
      _ = _ := by rw [hfamily]
  by_cases hyR : y ≤ M - yes.card
  · have hJcard : ((fixedGraphs n M).filter
        (fun G => patternEvent yes no G ∧ (G ∩ query).card = y)).card =
        query.card.choose y *
          (capacity n - yes.card - no.card - query.card).choose
            (M - yes.card - y) := by
      rw [hjoint, card_completion_inter (U \ no) yes query
        (M - yes.card) y hyesUno hqueryUno hyesQ hyR, hqueryremcard]
    have hJcardR : (((fixedGraphs n M).filter
        (fun G => patternEvent yes no G ∧ (G ∩ query).card = y)).card : ℝ) =
        (query.card.choose y *
          (capacity n - yes.card - no.card - query.card).choose
            (M - yes.card - y) : ℕ) := by
      exact_mod_cast hJcard
    have hPcardR : (((fixedGraphs n M).filter
        (patternEvent yes no)).card : ℝ) =
        ((capacity n - yes.card - no.card).choose (M - yes.card) : ℕ) := by
      exact_mod_cast hPcard
    push_cast at hJcardR hPcardR
    unfold conditionalProbM probM
    simp only
    rw [hJcardR, hPcardR, div_div_div_cancel_right₀ hBne]
    exact hypergeom_symmetry _ _ _ _ hRE hdE hyR
  · have hyR' : M - yes.card < y := Nat.lt_of_not_ge hyR
    have hJzero : ((fixedGraphs n M).filter
        (fun G => patternEvent yes no G ∧ (G ∩ query).card = y)).card = 0 := by
      rw [hjoint]
      exact card_completion_inter_eq_zero_of_lt (U \ no) yes query
        (M - yes.card) y hyesQ hyR'
    have hJzeroR : (((fixedGraphs n M).filter
        (fun G => patternEvent yes no G ∧ (G ∩ query).card = y)).card : ℝ) = 0 := by
      exact_mod_cast hJzero
    unfold conditionalProbM probM
    simp only
    rw [hJzeroR]
    simp only [zero_div, zero_div]
    have hchoose : (M - yes.card).choose y = 0 :=
      Nat.choose_eq_zero_of_lt hyR'
    simp [hypergeomMass, hchoose]

private def componentEdgeMap {a b : ℕ} (f : Fin a ↪o Fin b) : Edge a ↪ Edge b where
  toFun e := ⟨(f e.1.1, f e.1.2), f.lt_iff_lt.mpr e.2⟩
  inj' e e' h := by
    apply Subtype.ext
    apply Prod.ext <;> apply f.injective
    · exact congrArg (fun z => z.1.1) h
    · exact congrArg (fun z => z.1.2) h

private def componentGraphMap {a b : ℕ} (f : Fin a ↪o Fin b)
    (G : Graph a) : Graph b := G.map (componentEdgeMap f)

private lemma componentAdj_map_iff {a b : ℕ} (f : Fin a ↪o Fin b)
    (G : Graph a) (u v : Fin a) :
    adj (componentGraphMap f G) (f u) (f v) ↔ adj G u v := by
  constructor
  · rintro ⟨e, he, hends⟩
    rw [componentGraphMap, Finset.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    refine ⟨e0, he0, ?_⟩
    rcases hends with h | h
    · exact Or.inl ⟨f.injective h.1, f.injective h.2⟩
    · exact Or.inr ⟨f.injective h.1, f.injective h.2⟩
  · rintro ⟨e, he, hends⟩
    refine ⟨componentEdgeMap f e, Finset.mem_map.mpr ⟨e, he, rfl⟩, ?_⟩
    rcases hends with h | h
    · exact Or.inl ⟨congrArg f h.1, congrArg f h.2⟩
    · exact Or.inr ⟨congrArg f h.1, congrArg f h.2⟩

private lemma componentAdj_map_iff_exists {a b : ℕ} (f : Fin a ↪o Fin b)
    (G : Graph a) (u : Fin a) (z : Fin b) :
    adj (componentGraphMap f G) (f u) z ↔
      ∃ v : Fin a, z = f v ∧ adj G u v := by
  constructor
  · rintro ⟨e, he, hends⟩
    rw [componentGraphMap, Finset.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    rcases hends with h | h
    · refine ⟨e0.1.2, h.2.symm, ?_⟩
      exact ⟨e0, he0, Or.inl ⟨f.injective h.1, rfl⟩⟩
    · refine ⟨e0.1.1, h.1.symm, ?_⟩
      exact ⟨e0, he0, Or.inr ⟨rfl, f.injective h.2⟩⟩
  · rintro ⟨v, rfl, huv⟩
    exact (componentAdj_map_iff f G u v).mpr huv

private lemma componentReach_map_iff {a b : ℕ} (f : Fin a ↪o Fin b)
    (G : Graph a) (u v : Fin a) :
    reach (componentGraphMap f G) (f u) (f v) ↔ reach G u v := by
  constructor
  · intro h
    have lift : ∀ z : Fin b, reach (componentGraphMap f G) (f u) z →
        ∃ w : Fin a, z = f w ∧ reach G u w := by
      intro z huz
      induction huz with
      | refl => exact ⟨u, rfl, Relation.ReflTransGen.refl⟩
      | tail hxy hyz ih =>
          obtain ⟨w, rfl, huw⟩ := ih
          obtain ⟨w', rfl, hww'⟩ :=
            (componentAdj_map_iff_exists f G w _).mp hyz
          exact ⟨w', rfl, huw.tail hww'⟩
    obtain ⟨w, hw, huw⟩ := lift (f v) h
    exact (f.injective hw).symm ▸ huw
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail hxy hyz ih => exact ih.tail ((componentAdj_map_iff f G _ _).mpr hyz)

private def componentEdgeInside {n : ℕ} (S : Finset (Fin n))
    (e : Edge n) : Prop := e.1.1 ∈ S ∧ e.1.2 ∈ S

private def componentEdgeIso {n k : ℕ} (S : Finset (Fin n))
    (hS : S.card = k) : Edge k ≃ {e : Edge n // componentEdgeInside S e} where
  toFun e :=
    ⟨⟨(S.orderIsoOfFin hS e.1.1, S.orderIsoOfFin hS e.1.2),
      (S.orderIsoOfFin hS).lt_iff_lt.mpr e.2⟩,
      ⟨(S.orderIsoOfFin hS e.1.1).2, (S.orderIsoOfFin hS e.1.2).2⟩⟩
  invFun e :=
    ⟨((S.orderIsoOfFin hS).symm ⟨e.1.1.1, e.2.1⟩,
      (S.orderIsoOfFin hS).symm ⟨e.1.1.2, e.2.2⟩),
      (S.orderIsoOfFin hS).symm.lt_iff_lt.mpr e.1.2⟩
  left_inv e := by
    apply Subtype.ext
    apply Prod.ext
    · exact (S.orderIsoOfFin hS).symm_apply_apply e.1.1
    · exact (S.orderIsoOfFin hS).symm_apply_apply e.1.2
  right_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val ((S.orderIsoOfFin hS).apply_symm_apply
        ⟨e.1.1.1, e.2.1⟩)
    · exact congrArg Subtype.val ((S.orderIsoOfFin hS).apply_symm_apply
        ⟨e.1.1.2, e.2.2⟩)

private def componentPlace {n k : ℕ} (S : Finset (Fin n))
    (hS : S.card = k) (G : Graph k) : Graph n :=
  ((Equiv.finsetCongr (componentEdgeIso S hS)) G).map
    (Function.Embedding.subtype _)

private def componentTake {n k : ℕ} (S : Finset (Fin n))
    (hS : S.card = k) (G : Graph n) : Graph k :=
  (Equiv.finsetCongr (componentEdgeIso S hS)).symm
    (G.subtype (componentEdgeInside S))

private lemma componentTake_place {n k : ℕ} (S : Finset (Fin n))
    (hS : S.card = k) (G : Graph k) :
    componentTake S hS (componentPlace S hS G) = G := by
  apply (Equiv.finsetCongr (componentEdgeIso S hS)).injective
  unfold componentTake componentPlace
  rw [(Equiv.finsetCongr (componentEdgeIso S hS)).apply_symm_apply]
  ext e
  have he : e.1.1.1 ∈ S ∧ e.1.1.2 ∈ S := e.2
  simp [componentEdgeInside, he]
  rfl

private lemma componentPlace_take {n k : ℕ} (S : Finset (Fin n))
    (hS : S.card = k) (G : Graph n) :
    componentPlace S hS (componentTake S hS G) =
      G.filter (componentEdgeInside S) := by
  unfold componentPlace componentTake
  rw [(Equiv.finsetCongr (componentEdgeIso S hS)).apply_symm_apply]
  exact Finset.subtype_map (componentEdgeInside S)

private lemma componentPlace_card {n k : ℕ} (S : Finset (Fin n))
    (hS : S.card = k) (G : Graph k) :
    (componentPlace S hS G).card = G.card := by
  simp [componentPlace]

private lemma componentPlace_eq_map {n k : ℕ} (S : Finset (Fin n))
    (hS : S.card = k) (G : Graph k) :
    componentPlace S hS G = componentGraphMap (S.orderEmbOfFin hS) G := by
  ext e
  constructor
  · intro he
    rw [componentPlace, Finset.mem_map] at he
    obtain ⟨q, hq, hqe⟩ := he
    rw [Equiv.finsetCongr_apply, Finset.mem_map] at hq
    obtain ⟨a, ha, haq⟩ := hq
    rw [componentGraphMap, Finset.mem_map]
    refine ⟨a, ha, ?_⟩
    subst q
    subst e
    rfl
  · intro he
    rw [componentGraphMap, Finset.mem_map] at he
    obtain ⟨a, ha, rfl⟩ := he
    rw [componentPlace, Finset.mem_map]
    refine ⟨componentEdgeIso S hS a, ?_, rfl⟩
    rw [Equiv.finsetCongr_apply, Finset.mem_map]
    exact ⟨a, ha, rfl⟩

private lemma componentPlace_reach_iff {n k : ℕ} (S : Finset (Fin n))
    (hS : S.card = k) (G : Graph k) (u v : Fin k) :
    reach (componentPlace S hS G) (S.orderEmbOfFin hS u)
        (S.orderEmbOfFin hS v) ↔ reach G u v := by
  rw [componentPlace_eq_map]
  exact componentReach_map_iff _ _ _ _

private lemma componentPlace_mem {n k : ℕ} (S : Finset (Fin n))
    (hS : S.card = k) (G : Graph k) {e : Edge n}
    (he : e ∈ componentPlace S hS G) : componentEdgeInside S e := by
  unfold componentPlace at he
  rw [Finset.mem_map] at he
  obtain ⟨q, -, rfl⟩ := he
  exact q.2

private lemma componentPlace_injective {n k : ℕ} (S : Finset (Fin n))
    (hS : S.card = k) : Function.Injective (componentPlace S hS) := by
  intro G H h
  rw [← componentTake_place S hS G, ← componentTake_place S hS H, h]

private def componentSeparated {n : ℕ} (S : Finset (Fin n))
    (G : Graph n) : Prop :=
  ∀ e ∈ G, componentEdgeInside S e ∨
    componentEdgeInside ((Finset.univ : Finset (Fin n)) \ S) e

private lemma componentComplement_card {n k : ℕ} (S : Finset (Fin n))
    (hS : S.card = k) :
    ((Finset.univ : Finset (Fin n)) \ S).card = n - k := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, hS]
  simp

private def componentCombine {n k : ℕ} (S : Finset (Fin n))
    (hS : S.card = k) (I : Graph k) (O : Graph (n - k)) : Graph n :=
  componentPlace S hS I ∪
    componentPlace ((Finset.univ : Finset (Fin n)) \ S)
      (componentComplement_card S hS) O

private lemma componentCombine_separated {n k : ℕ} (S : Finset (Fin n))
    (hS : S.card = k) (I : Graph k) (O : Graph (n - k)) :
    componentSeparated S (componentCombine S hS I O) := by
  intro e he
  rw [componentCombine, Finset.mem_union] at he
  rcases he with he | he
  · exact Or.inl (componentPlace_mem S hS I he)
  · exact Or.inr (componentPlace_mem _ (componentComplement_card S hS) O he)

private lemma componentPlace_disjoint {n k : ℕ} (S : Finset (Fin n))
    (hS : S.card = k) (I : Graph k) (O : Graph (n - k)) :
    Disjoint (componentPlace S hS I)
      (componentPlace ((Finset.univ : Finset (Fin n)) \ S)
        (componentComplement_card S hS) O) := by
  apply Finset.disjoint_left.mpr
  intro e heI heO
  have hi := componentPlace_mem S hS I heI
  have ho := componentPlace_mem _ (componentComplement_card S hS) O heO
  exact (Finset.mem_sdiff.mp ho.1).2 hi.1

private lemma componentCombine_card {n k : ℕ} (S : Finset (Fin n))
    (hS : S.card = k) (I : Graph k) (O : Graph (n - k)) :
    (componentCombine S hS I O).card = I.card + O.card := by
  rw [componentCombine, Finset.card_union_of_disjoint
    (componentPlace_disjoint S hS I O), componentPlace_card, componentPlace_card]

private lemma componentCombine_inside {n k : ℕ} (S : Finset (Fin n))
    (hS : S.card = k) (I : Graph k) (O : Graph (n - k)) :
    (componentCombine S hS I O).filter (componentEdgeInside S) =
      componentPlace S hS I := by
  ext e
  simp only [Finset.mem_filter, Finset.mem_union, componentCombine]
  constructor
  · rintro ⟨heI | heO, hin⟩
    · exact heI
    · have hi := componentPlace_mem _ (componentComplement_card S hS) O heO
      exact False.elim ((Finset.mem_sdiff.mp hi.1).2 hin.1)
  · intro heI
    exact ⟨Or.inl heI, componentPlace_mem S hS I heI⟩

private lemma componentEdgesInside_combine {n k : ℕ} (S : Finset (Fin n))
    (hS : S.card = k) (I : Graph k) (O : Graph (n - k)) :
    edgesInside (componentCombine S hS I O) S = I.card := by
  unfold edgesInside
  calc
    ((componentCombine S hS I O).filter
      (fun e => e.1.1 ∈ S ∧ e.1.2 ∈ S)).card =
        ((componentCombine S hS I O).filter (componentEdgeInside S)).card := by
          congr 1
          ext e
          simp [componentEdgeInside]
    _ = (componentPlace S hS I).card :=
      congrArg Finset.card (componentCombine_inside S hS I O)
    _ = I.card := componentPlace_card S hS I

private lemma componentSeparated_adj {n : ℕ} {S : Finset (Fin n)}
    {G : Graph n} (hsep : componentSeparated S G) {u v : Fin n}
    (h : adj G u v) : (u ∈ S ↔ v ∈ S) := by
  rcases h with ⟨e, heG, hends⟩
  rcases hsep e heG with hi | ho
  · rcases hends with h | h
    · rw [← h.1, ← h.2]
      exact ⟨fun _ => hi.2, fun _ => hi.1⟩
    · rw [← h.2, ← h.1]
      exact ⟨fun _ => hi.1, fun _ => hi.2⟩
  · have hno1 : e.1.1 ∉ S := (Finset.mem_sdiff.mp ho.1).2
    have hno2 : e.1.2 ∉ S := (Finset.mem_sdiff.mp ho.2).2
    rcases hends with h | h
    · rw [← h.1, ← h.2]
      exact ⟨fun hu => False.elim (hno1 hu), fun hv => False.elim (hno2 hv)⟩
    · rw [← h.2, ← h.1]
      exact ⟨fun hu => False.elim (hno2 hu), fun hv => False.elim (hno1 hv)⟩

private lemma componentSeparated_reach_mem {n : ℕ} {S : Finset (Fin n)}
    {G : Graph n} (hsep : componentSeparated S G) {u v : Fin n}
    (hu : u ∈ S) (h : reach G u v) : v ∈ S := by
  induction h with
  | refl => exact hu
  | tail hxy hyz ih => exact (componentSeparated_adj hsep hyz).mp ih

private lemma componentReach_mono {n : ℕ} {G H : Graph n} (hGH : G ⊆ H)
    {u v : Fin n} (h : reach G u v) : reach H u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      apply ih.tail
      rcases hyz with ⟨e, he, hends⟩
      exact ⟨e, hGH he, hends⟩

private lemma componentMem_of_combine_connected {n k : ℕ}
    (S : Finset (Fin n)) (hS : S.card = k) (hk : 0 < k)
    (I : Graph k) (O : Graph (n - k))
    (hconn : ∀ u v : Fin k, reach I u v) :
    S ∈ components (componentCombine S hS I O) := by
  let r : Fin k := ⟨0, hk⟩
  have hrS : S.orderEmbOfFin hS r ∈ S := Finset.orderEmbOfFin_mem S hS r
  have hcomp : componentOf (componentCombine S hS I O)
      (S.orderEmbOfFin hS r) = S := by
    ext x
    rw [mem_componentOf_iff]
    constructor
    · intro hrx
      exact componentSeparated_reach_mem
        (componentCombine_separated S hS I O) hrS hrx
    · intro hxS
      let xs : S := ⟨x, hxS⟩
      let u : Fin k := (S.orderIsoOfFin hS).symm xs
      have hxu : S.orderEmbOfFin hS u = x := by
        exact congrArg Subtype.val ((S.orderIsoOfFin hS).apply_symm_apply xs)
      rw [← hxu]
      apply componentReach_mono Finset.subset_union_left
      exact (componentPlace_reach_iff S hS I r u).mpr (hconn r u)
  simpa only [hcomp] using!
    componentOf_mem_components (componentCombine S hS I O) (S.orderEmbOfFin hS r)

private lemma componentMember_nonempty {n : ℕ} {G : Graph n}
    {S : Finset (Fin n)} (hS : S ∈ components G) : S.Nonempty := by
  rw [components, Finset.mem_image] at hS
  obtain ⟨u, -, rfl⟩ := hS
  exact ⟨u, componentOf_self G u⟩

private lemma componentMember_reach {n : ℕ} {G : Graph n}
    {S : Finset (Fin n)} (hS : S ∈ components G) {u v : Fin n}
    (hu : u ∈ S) (hv : v ∈ S) : reach G u v := by
  rw [components, Finset.mem_image] at hS
  obtain ⟨r, -, hr⟩ := hS
  rw [← hr, mem_componentOf_iff] at hu hv
  exact (reach_symm hu).trans hv

private lemma componentMember_separated {n : ℕ} {G : Graph n}
    {S : Finset (Fin n)} (hS : S ∈ components G) :
    componentSeparated S G := by
  intro e he
  by_cases h1 : e.1.1 ∈ S
  · have hadj : adj G e.1.1 e.1.2 := ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
    have h2 : e.1.2 ∈ S := by
      rw [components, Finset.mem_image] at hS
      obtain ⟨r, -, rfl⟩ := hS
      exact mem_componentOf_iff.mpr ((mem_componentOf_iff.mp h1).tail hadj)
    exact Or.inl ⟨h1, h2⟩
  · by_cases h2 : e.1.2 ∈ S
    · have hadj : adj G e.1.2 e.1.1 := ⟨e, he, Or.inr ⟨rfl, rfl⟩⟩
      have h1' : e.1.1 ∈ S := by
        rw [components, Finset.mem_image] at hS
        obtain ⟨r, -, rfl⟩ := hS
        exact mem_componentOf_iff.mpr ((mem_componentOf_iff.mp h2).tail hadj)
      exact False.elim (h1 h1')
    · exact Or.inr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h1⟩,
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h2⟩⟩

private lemma componentCombine_outside {n k : ℕ} (S : Finset (Fin n))
    (hS : S.card = k) (I : Graph k) (O : Graph (n - k)) :
    (componentCombine S hS I O).filter
        (componentEdgeInside ((Finset.univ : Finset (Fin n)) \ S)) =
      componentPlace ((Finset.univ : Finset (Fin n)) \ S)
        (componentComplement_card S hS) O := by
  ext e
  simp only [Finset.mem_filter, Finset.mem_union, componentCombine]
  constructor
  · rintro ⟨heI | heO, hout⟩
    · have hi := componentPlace_mem S hS I heI
      exact False.elim ((Finset.mem_sdiff.mp hout.1).2 hi.1)
    · exact heO
  · intro heO
    exact ⟨Or.inr heO,
      componentPlace_mem _ (componentComplement_card S hS) O heO⟩

private lemma componentTake_combine_left {n k : ℕ} (S : Finset (Fin n))
    (hS : S.card = k) (I : Graph k) (O : Graph (n - k)) :
    componentTake S hS (componentCombine S hS I O) = I := by
  apply componentPlace_injective S hS
  rw [componentPlace_take, componentCombine_inside]

private lemma componentTake_combine_right {n k : ℕ} (S : Finset (Fin n))
    (hS : S.card = k) (I : Graph k) (O : Graph (n - k)) :
    componentTake ((Finset.univ : Finset (Fin n)) \ S)
        (componentComplement_card S hS) (componentCombine S hS I O) = O := by
  apply componentPlace_injective _ (componentComplement_card S hS)
  rw [componentPlace_take, componentCombine_outside]

private lemma componentCombine_take {n k : ℕ} (S : Finset (Fin n))
    (hS : S.card = k) (G : Graph n) (hsep : componentSeparated S G) :
    componentCombine S hS (componentTake S hS G)
        (componentTake ((Finset.univ : Finset (Fin n)) \ S)
          (componentComplement_card S hS) G) = G := by
  rw [componentCombine, componentPlace_take, componentPlace_take]
  ext e
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨he, -⟩ | ⟨he, -⟩) <;> exact he
  · intro he
    rcases hsep e he with hi | ho
    · exact Or.inl ⟨he, hi⟩
    · exact Or.inr ⟨he, ho⟩

private lemma componentAdj_filter_inside {n : ℕ} {S : Finset (Fin n)}
    {G : Graph n} {u v : Fin n} (hu : u ∈ S) (hv : v ∈ S)
    (h : adj G u v) : adj (G.filter (componentEdgeInside S)) u v := by
  rcases h with ⟨e, he, hends⟩
  refine ⟨e, Finset.mem_filter.mpr ⟨he, ?_⟩, hends⟩
  rcases hends with h | h
  · exact ⟨h.1.symm ▸ hu, h.2.symm ▸ hv⟩
  · exact ⟨h.1.symm ▸ hv, h.2.symm ▸ hu⟩

private lemma componentReach_filter_inside {n : ℕ} {S : Finset (Fin n)}
    {G : Graph n} (hsep : componentSeparated S G) {u v : Fin n}
    (hu : u ∈ S) (h : reach G u v) :
    reach (G.filter (componentEdgeInside S)) u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      have hx : _ ∈ S := componentSeparated_reach_mem hsep hu hxy
      have hy : _ ∈ S := (componentSeparated_adj hsep hyz).mp hx
      exact ih.tail (componentAdj_filter_inside hx hy hyz)

private lemma componentTake_connected_of_member {n k : ℕ}
    (S : Finset (Fin n)) (hS : S.card = k) (G : Graph n)
    (hmem : S ∈ components G) :
    ∀ u v : Fin k, reach (componentTake S hS G) u v := by
  intro u v
  have hu : S.orderEmbOfFin hS u ∈ S := Finset.orderEmbOfFin_mem S hS u
  have hv : S.orderEmbOfFin hS v ∈ S := Finset.orderEmbOfFin_mem S hS v
  have hreach := componentMember_reach hmem hu hv
  have hfiltered := componentReach_filter_inside
    (componentMember_separated hmem) hu hreach
  rw [← componentPlace_take S hS G] at hfiltered
  exact (componentPlace_reach_iff S hS (componentTake S hS G) u v).mp hfiltered

private lemma componentTake_card_edgesInside {n k : ℕ}
    (S : Finset (Fin n)) (hS : S.card = k) (G : Graph n) :
    (componentTake S hS G).card = edgesInside G S := by
  rw [← componentPlace_card S hS (componentTake S hS G),
    componentPlace_take]
  unfold edgesInside
  congr 1
  ext e
  simp [componentEdgeInside]

private lemma componentTake_complement_card {n k M e : ℕ}
    (S : Finset (Fin n)) (hS : S.card = k) (G : Graph n)
    (hGM : G.card = M) (hmem : S ∈ components G)
    (hedge : edgesInside G S = e) (heM : e ≤ M) :
    (componentTake ((Finset.univ : Finset (Fin n)) \ S)
      (componentComplement_card S hS) G).card = M - e := by
  have hsep := componentMember_separated hmem
  have hdecomp := congrArg Finset.card (componentCombine_take S hS G hsep)
  rw [componentCombine_card, componentTake_card_edgesInside, hedge, hGM] at hdecomp
  omega

private def componentConnectedFamily (k e : ℕ) : Finset (Graph k) :=
  (fixedGraphs k e).filter (fun G => 0 < k ∧ ∀ u v : Fin k, reach G u v)

private def componentMarkedFamily (n M k e : ℕ) : Type :=
  Σ G : ↑(fixedGraphs n M),
    ↑((components G.1).filter
      (fun S => S.card = k ∧ edgesInside G.1 S = e))

private def componentDataFamily (n M k e : ℕ) : Type :=
  Σ S : ↑((Finset.univ : Finset (Fin n)).powersetCard k),
    ↑(componentConnectedFamily k e) × ↑(fixedGraphs (n - k) (M - e))

private noncomputable instance componentMarkedFintype (n M k e : ℕ) :
    Fintype (componentMarkedFamily n M k e) := by
  unfold componentMarkedFamily
  infer_instance

private noncomputable instance componentDataFintype (n M k e : ℕ) :
    Fintype (componentDataFamily n M k e) := by
  unfold componentDataFamily
  infer_instance

private def componentAssemble {n M k e : ℕ} (hk : 0 < k)
    (_hkN : k ≤ n) (_heM : e ≤ M) :
    componentDataFamily n M k e → componentMarkedFamily n M k e := fun P => by
  let S : Finset (Fin n) := P.1.1
  have hS : S.card = k := (Finset.mem_powersetCard.mp P.1.2).2
  let I : Graph k := P.2.1.1
  let O : Graph (n - k) := P.2.2.1
  have hIfixed := (Finset.mem_filter.mp P.2.1.2).1
  have hIconn := (Finset.mem_filter.mp P.2.1.2).2.2
  have hOfixed := P.2.2.2
  have hIcard : I.card = e := (Finset.mem_filter.mp hIfixed).2
  have hOcard : O.card = M - e := (Finset.mem_filter.mp hOfixed).2
  let G := componentCombine S hS I O
  have hGcard : G.card = M := by
    dsimp [G]
    rw [componentCombine_card, hIcard, hOcard]
    omega
  have hGall : G ∈ allGraphs n := by
    unfold allGraphs
    exact Finset.mem_powerset.mpr (Finset.subset_univ G)
  have hGfixed : G ∈ fixedGraphs n M := Finset.mem_filter.mpr ⟨hGall, hGcard⟩
  have hSmem : S ∈ components G := by
    dsimp [G]
    exact componentMem_of_combine_connected S hS hk I O hIconn
  have hEdges : edgesInside G S = e := by
    dsimp [G]
    rw [componentEdgesInside_combine, hIcard]
  exact ⟨⟨G, hGfixed⟩,
    ⟨S, Finset.mem_filter.mpr ⟨hSmem, hS, hEdges⟩⟩⟩

private def componentDisassemble {n M k e : ℕ} (_hk : 0 < k)
    (_hkN : k ≤ n) (heM : e ≤ M) :
    componentMarkedFamily n M k e → componentDataFamily n M k e := fun P => by
  let G : Graph n := P.1.1
  let S : Finset (Fin n) := P.2.1
  have hGfixed := P.1.2
  have hSmem := (Finset.mem_filter.mp P.2.2).1
  have hS : S.card = k := (Finset.mem_filter.mp P.2.2).2.1
  have hEdges : edgesInside G S = e := (Finset.mem_filter.mp P.2.2).2.2
  have hGM : G.card = M := (Finset.mem_filter.mp hGfixed).2
  have hSU : S ⊆ (Finset.univ : Finset (Fin n)) := Finset.subset_univ _
  let I : Graph k := componentTake S hS G
  let O : Graph (n - k) := componentTake
    ((Finset.univ : Finset (Fin n)) \ S) (componentComplement_card S hS) G
  have hIcard : I.card = e := by
    dsimp [I]
    rw [componentTake_card_edgesInside, hEdges]
  have hOcard : O.card = M - e := by
    dsimp [O]
    exact componentTake_complement_card S hS G hGM hSmem hEdges heM
  have hIfixed : I ∈ fixedGraphs k e := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ I), hIcard⟩
  have hOfixed : O ∈ fixedGraphs (n - k) (M - e) := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ O), hOcard⟩
  have hIconn : ∀ u v : Fin k, reach I u v := by
    dsimp [I]
    exact componentTake_connected_of_member S hS G hSmem
  exact ⟨⟨S, Finset.mem_powersetCard.mpr ⟨hSU, hS⟩⟩,
    ⟨⟨I, Finset.mem_filter.mpr ⟨hIfixed, _hk, hIconn⟩⟩, ⟨O, hOfixed⟩⟩⟩

private def componentAssemblyEquiv {n M k e : ℕ} (hk : 0 < k)
    (hkN : k ≤ n) (heM : e ≤ M) :
    componentDataFamily n M k e ≃ componentMarkedFamily n M k e where
  toFun := componentAssemble hk hkN heM
  invFun := componentDisassemble hk hkN heM
  left_inv P := by
    rcases P with ⟨S, I, O⟩
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Prod.ext <;> apply Subtype.ext
      · exact componentTake_combine_left S.1
          (Finset.mem_powersetCard.mp S.2).2 I.1 O.1
      · exact componentTake_combine_right S.1
          (Finset.mem_powersetCard.mp S.2).2 I.1 O.1
  right_inv P := by
    rcases P with ⟨G, S⟩
    have hG : componentCombine S.1 (Finset.mem_filter.mp S.2).2.1
        (componentTake S.1 (Finset.mem_filter.mp S.2).2.1 G.1)
        (componentTake ((Finset.univ : Finset (Fin n)) \ S.1)
          (componentComplement_card S.1 (Finset.mem_filter.mp S.2).2.1) G.1) = G.1 :=
      componentCombine_take S.1 (Finset.mem_filter.mp S.2).2.1 G.1
        (componentMember_separated (Finset.mem_filter.mp S.2).1)
    have hfst :
        (componentAssemble hk hkN heM
          (componentDisassemble hk hkN heM ⟨G, S⟩)).1 = G := Subtype.ext hG
    apply Sigma.ext
    · exact hfst
    · apply (Subtype.heq_iff_coe_eq (fun T => by simpa only [hfst])).2
      rfl

private lemma componentMarked_card {n M k e : ℕ} (hk : 0 < k)
    (hkN : k ≤ n) (heM : e ≤ M) :
    Fintype.card (componentMarkedFamily n M k e) =
      n.choose k * connectedCount k e *
        ((n - k).choose 2).choose (M - e) := by
  rw [Fintype.card_eq_nat_card, ← Nat.card_congr (componentAssemblyEquiv hk hkN heM)]
  unfold componentDataFamily
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_coe]
  have hconn : (componentConnectedFamily k e).card = connectedCount k e := rfl
  simp_rw [hconn, card_fixedGraphs]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  unfold capacity
  simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

private lemma componentSum_eq_marked_card (n M k e : ℕ) :
    ∑ G ∈ fixedGraphs n M, componentCount G k e =
      Fintype.card (componentMarkedFamily n M k e) := by
  unfold componentMarkedFamily componentCount
  rw [Fintype.card_eq_nat_card, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Fintype.card_coe]
  symm
  calc
    _ = ∑ x ∈ (fixedGraphs n M).attach,
        ((components x.1).filter
          (fun S => S.card = k ∧ edgesInside x.1 S = e)).card :=
      Finset.sum_coe_sort_eq_attach _ _
    _ = _ := by
      simpa only using! Finset.sum_attach (fixedGraphs n M)
        (fun G => ((components G).filter
          (fun S => S.card = k ∧ edgesInside G S = e)).card)

private lemma componentCount_zero_of_k_zero {n e : ℕ} (G : Graph n) :
    componentCount G 0 e = 0 := by
  rw [componentCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro S hSmem h
  exact (componentMember_nonempty hSmem).card_pos.ne' h.1

private lemma componentCount_zero_of_k_gt_n {n k e : ℕ} (G : Graph n)
    (hnk : n < k) : componentCount G k e = 0 := by
  rw [componentCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro S hSmem h
  have hSU : S ⊆ (Finset.univ : Finset (Fin n)) := by
    rw [components, Finset.mem_image] at hSmem
    obtain ⟨v, -, rfl⟩ := hSmem
    exact Finset.filter_subset _ _
  have hc := Finset.card_le_card hSU
  rw [h.1, Finset.card_univ, Fintype.card_fin] at hc
  omega

private lemma componentCount_zero_of_e_gt_M {n M k e : ℕ} (G : Graph n)
    (hGM : G.card = M) (hMe : M < e) : componentCount G k e = 0 := by
  rw [componentCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro S hSmem h
  have hc : edgesInside G S ≤ G.card := Finset.card_le_card (Finset.filter_subset _ _)
  rw [h.2, hGM] at hc
  omega

theorem component_identity (n M k e : ℕ) (hM : M ≤ capacity n) :
    expectM n M (fun G => (componentCount G k e : ℝ)) =
      componentFormula n M k e := by
  by_cases hkN : k ≤ n
  · by_cases heM : e ≤ M
    · by_cases hk : k = 0
      · subst k
        unfold expectM componentFormula
        rw [if_pos ⟨Nat.zero_le _, heM⟩]
        have hz : (fixedGraphs n M).sum
            (fun G => (componentCount G 0 e : ℝ)) = 0 := by
          apply Finset.sum_eq_zero
          intro G hG
          rw [componentCount_zero_of_k_zero G]
          norm_num
        rw [hz]
        simp [connectedCount]
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        have hsum := componentSum_eq_marked_card n M k e
        rw [componentMarked_card hkpos hkN heM] at hsum
        unfold expectM componentFormula
        rw [if_pos ⟨hkN, heM⟩, card_fixedGraphs]
        have hsumR : (∑ G ∈ fixedGraphs n M,
            (componentCount G k e : ℝ)) =
            (n.choose k : ℝ) * connectedCount k e *
              (((n - k).choose 2).choose (M - e) : ℝ) := by
          exact_mod_cast hsum
        rw [hsumR]
    · have hMe : M < e := Nat.lt_of_not_ge heM
      unfold expectM componentFormula
      rw [if_neg (fun h => heM h.2)]
      have hz : (fixedGraphs n M).sum
          (fun G => (componentCount G k e : ℝ)) = 0 := by
        apply Finset.sum_eq_zero
        intro G hG
        rw [componentCount_zero_of_e_gt_M G (Finset.mem_filter.mp hG).2 hMe]
        norm_num
      rw [hz]
      norm_num
  · have hnk : n < k := Nat.lt_of_not_ge hkN
    unfold expectM componentFormula
    rw [if_neg (fun h => hkN h.1)]
    have hz : (fixedGraphs n M).sum
        (fun G => (componentCount G k e : ℝ)) = 0 := by
      apply Finset.sum_eq_zero
      intro G hG
      rw [componentCount_zero_of_k_gt_n G hnk]
      norm_num
    rw [hz]
    norm_num

private def eligibleTrees {n : ℕ} (G : Graph n) (h : ℕ) :
    Finset (Finset (Fin n)) :=
  (components G).filter (fun S => isTree G S ∧ h ≤ S.card)

private def eligibleTuples {n : ℕ} (G : Graph n) (q h : ℕ) :
    Finset (Fin q → Finset (Fin n)) :=
  (Finset.univ : Finset (Fin q → Finset (Fin n))).filter
    (fun C => Function.Injective C ∧ ∀ i, C i ∈ eligibleTrees G h)

private def eligibleTupleEquiv {n q h : ℕ} (G : Graph n) :
    {C // C ∈ eligibleTuples G q h} ≃
      (Fin q ↪ (↥(eligibleTrees G h))) where
  toFun C :=
    { toFun := fun i => ⟨C.1 i, by
        have hC := (Finset.mem_filter.mp C.2).2
        exact hC.2 i⟩
      inj' := fun _ _ hij =>
        (Finset.mem_filter.mp C.2).2.1 (congrArg Subtype.val hij) }
  invFun f :=
    ⟨fun i => (f i).1, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨fun _ _ hij => f.injective (Subtype.ext hij), fun i => (f i).2⟩⟩⟩
  left_inv C := by
    apply Subtype.ext
    funext i
    rfl
  right_inv f := by
    ext i
    rfl

private lemma card_eligibleTuples {n : ℕ} (G : Graph n) (q h : ℕ) :
    (eligibleTuples G q h).card = falling (treeCountGE G h) q := by
  have he : Fintype.card {C // C ∈ eligibleTuples G q h} =
      Fintype.card (Fin q ↪ (↥(eligibleTrees G h))) :=
    Fintype.card_congr (eligibleTupleEquiv G)
  rw [Fintype.card_embedding_eq] at he
  have htrees : (eligibleTrees G h).card = treeCountGE G h := rfl
  simp only [Fintype.card_coe, Fintype.card_fin, htrees] at he
  have hfall : falling (treeCountGE G h) q =
      (treeCountGE G h).descFactorial q := by
    rw [falling, Nat.descFactorial_eq_prod_range]
  simpa [hfall] using! he

private lemma component_card_le {n : ℕ} {G : Graph n} {S : Finset (Fin n)}
    (_hS : S ∈ components G) : S.card ≤ n := by
  have hsub : S ⊆ (Finset.univ : Finset (Fin n)) := fun _ _ => Finset.mem_univ _
  simpa only [Finset.card_univ, Fintype.card_fin] using! Finset.card_le_card hsub

private def tupleSizes {n q : ℕ} (h : ℕ) (G : Graph n)
    (C : Fin q → Finset (Fin n)) : Fin q → Fin (n + 1) :=
  fun i =>
    if hC : C ∈ eligibleTuples G q h then
      ⟨(C i).card, by
        have hi := (Finset.mem_filter.mp hC).2.2 i
        have hmem := (Finset.mem_filter.mp hi).1
        exact Nat.lt_succ_of_le (component_card_le hmem)⟩
    else ⟨0, Nat.zero_lt_succ n⟩

private lemma eligibleTuple_fiber_card {n : ℕ} (G : Graph n) (q h : ℕ)
    (ks : Fin q → Fin (n + 1)) :
    ((eligibleTuples G q h).filter (fun C => tupleSizes h G C = ks)).card =
      if ∀ i, h ≤ (ks i).val then
        treeTupleCount G q (fun i => (ks i).val)
      else 0 := by
  classical
  by_cases hks : ∀ i, h ≤ (ks i).val
  · rw [if_pos hks]
    unfold treeTupleCount
    apply congrArg Finset.card
    ext C
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hC, hsizes⟩
      have helig := (Finset.mem_filter.mp hC).2
      refine ⟨helig.1, fun i => ?_⟩
      have hitree := (Finset.mem_filter.mp (helig.2 i)).2.1
      refine ⟨hitree, ?_⟩
      have hv := congrFun hsizes i
      simp only [tupleSizes, dif_pos hC] at hv
      exact Fin.ext_iff.mp hv
    · rintro ⟨hinj, htree⟩
      have hC : C ∈ eligibleTuples G q h := by
        rw [eligibleTuples, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, hinj, fun i => ?_⟩
        rw [eligibleTrees, Finset.mem_filter]
        exact ⟨(htree i).1.1, (htree i).1, by simpa [(htree i).2] using! hks i⟩
      refine ⟨hC, ?_⟩
      funext i
      apply Fin.ext
      simpa [tupleSizes, hC] using! (htree i).2
  · rw [if_neg hks, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro C hC hsizes
    apply hks
    intro i
    have helig := (Finset.mem_filter.mp hC).2.2 i
    have hh := (Finset.mem_filter.mp helig).2.2
    have hv := congrFun hsizes i
    simp only [tupleSizes, dif_pos hC] at hv
    rw [← Fin.ext_iff.mp hv]
    exact hh

private lemma falling_treeCount_eq_tuple_sum {n : ℕ} (G : Graph n) (q h : ℕ) :
    falling (treeCountGE G h) q =
      ∑ ks : Fin q → Fin (n + 1),
        if ∀ i, h ≤ (ks i).val then
          treeTupleCount G q (fun i => (ks i).val)
        else 0 := by
  rw [← card_eligibleTuples G q h]
  have hmap : Set.MapsTo (tupleSizes h G)
      (↑(eligibleTuples G q h))
      (↑(Finset.univ : Finset (Fin q → Fin (n + 1)))) :=
    fun C _ =>
      (show tupleSizes h G C ∈
        (Finset.univ : Finset (Fin q → Fin (n + 1))) from Finset.mem_univ _)
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro ks _
  exact eligibleTuple_fiber_card G q h ks

private lemma expectM_sum {ι : Type*} [Fintype ι] {n M : ℕ}
    (f : ι → Graph n → ℝ) :
    expectM n M (fun G => ∑ i, f i G) =
      ∑ i, expectM n M (f i) := by
  unfold expectM
  rw [Finset.sum_comm]
  rw [Finset.sum_div]

theorem factorial_moment_of_tuple_formula
    (htuple : ∀ (n M q : ℕ) (ks : Fin q → ℕ), M ≤ capacity n →
      tupleMoment n M q ks = tupleFormula n M q ks) :
    ∀ n M q h : ℕ, M ≤ capacity n → 0 < h →
      expectM n M (fun G => (falling (treeCountGE G h) q : ℝ)) =
        ∑ ks : Fin q → Fin (n + 1),
          if ∀ i, h ≤ (ks i).val then
            tupleFormula n M q (fun i => (ks i).val)
          else 0 := by
  intro n M q h hM _hh
  calc
    expectM n M (fun G => (falling (treeCountGE G h) q : ℝ)) =
        expectM n M (fun G =>
          ∑ ks : Fin q → Fin (n + 1),
            if ∀ i, h ≤ (ks i).val then
              (treeTupleCount G q (fun i => (ks i).val) : ℝ)
            else 0) := by
      congr 1
      funext G
      exact_mod_cast falling_treeCount_eq_tuple_sum G q h
    _ = ∑ ks : Fin q → Fin (n + 1),
          expectM n M (fun G =>
            if ∀ i, h ≤ (ks i).val then
              (treeTupleCount G q (fun i => (ks i).val) : ℝ)
            else 0) := expectM_sum _
    _ = ∑ ks : Fin q → Fin (n + 1),
          if ∀ i, h ≤ (ks i).val then
            tupleFormula n M q (fun i => (ks i).val)
          else 0 := by
      apply Finset.sum_congr rfl
      intro ks _
      split_ifs with hks
      · change tupleMoment n M q (fun i => (ks i).val) = _
        exact htuple n M q (fun i => (ks i).val) hM
      · simp [expectM]

private lemma componentMember_disjoint {n : ℕ} {G : Graph n}
    {S T : Finset (Fin n)} (hS : S ∈ components G)
    (hT : T ∈ components G) (hne : S ≠ T) : Disjoint S T := by
  apply Finset.disjoint_left.mpr
  intro x hxS hxT
  simp only [components, Finset.mem_image] at hS hT
  rcases hS with ⟨u, -, rfl⟩
  rcases hT with ⟨v, -, rfl⟩
  apply hne
  apply componentOf_eq_of_reach
  exact (mem_componentOf_iff.mp hxS).trans
    (reach_symm (mem_componentOf_iff.mp hxT))

private lemma selected_tree_vertex_bound {n q : ℕ} {G : Graph n}
    {ks : Fin q → ℕ} {C : Fin q → Finset (Fin n)}
    (hinj : Function.Injective C)
    (htree : ∀ i, isTree G (C i) ∧ (C i).card = ks i) :
    (∑ i, ks i) ≤ n := by
  have hpair :
      ((Finset.univ : Finset (Fin q)) : Set (Fin q)).PairwiseDisjoint C := by
    intro i _ j _ hij
    exact componentMember_disjoint (htree i).1.1 (htree j).1.1
      (hinj.ne hij)
  have hcard :
      ((Finset.univ : Finset (Fin q)).biUnion C).card =
        ∑ i, (C i).card := by
    simpa using! Finset.card_biUnion hpair
  calc
    (∑ i, ks i) = ∑ i, (C i).card := by
      apply Finset.sum_congr rfl
      intro i _
      exact (htree i).2.symm
    _ = ((Finset.univ : Finset (Fin q)).biUnion C).card := hcard.symm
    _ ≤ n := by
      simpa only [Finset.card_univ, Fintype.card_fin] using!
        Finset.card_le_univ ((Finset.univ : Finset (Fin q)).biUnion C)

private lemma selected_tree_edge_bound {n M q : ℕ} {G : Graph n}
    {ks : Fin q → ℕ} {C : Fin q → Finset (Fin n)}
    (hGM : G.card = M) (hinj : Function.Injective C)
    (htree : ∀ i, isTree G (C i) ∧ (C i).card = ks i) :
    (∑ i, ks i) ≤ M + q := by
  let E : Fin q → Finset (Edge n) := fun i =>
    G.filter (fun e => e.val.1 ∈ C i ∧ e.val.2 ∈ C i)
  have hpair :
      ((Finset.univ : Finset (Fin q)) : Set (Fin q)).PairwiseDisjoint E := by
    intro i _ j _ hij
    have hdis := componentMember_disjoint (htree i).1.1 (htree j).1.1
      (hinj.ne hij)
    apply Finset.disjoint_left.mpr
    intro e hei hej
    have hei' := (Finset.mem_filter.mp hei).2
    have hej' := (Finset.mem_filter.mp hej).2
    exact Finset.disjoint_left.mp hdis hei'.1 hej'.1
  have hunion :
      ((Finset.univ : Finset (Fin q)).biUnion E).card =
        ∑ i, (E i).card := by
    simpa using! Finset.card_biUnion hpair
  have hsub : (Finset.univ : Finset (Fin q)).biUnion E ⊆ G := by
    intro e he
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at he
    rcases he with ⟨i, hei⟩
    exact (Finset.mem_filter.mp hei).1
  have hedge :
      (∑ i, (ks i - 1)) ≤ M := by
    calc
      (∑ i, (ks i - 1)) = ∑ i, (E i).card := by
        apply Finset.sum_congr rfl
        intro i _
        have ht := (htree i).1.2
        rw [(htree i).2] at ht
        change ks i - 1 = edgesInside G (C i)
        omega
      _ = ((Finset.univ : Finset (Fin q)).biUnion E).card := hunion.symm
      _ ≤ G.card := Finset.card_le_card hsub
      _ = M := hGM
  have hpositive (i : Fin q) : 0 < ks i := by
    have hn := componentMember_nonempty (htree i).1.1
    calc
      0 < (C i).card := hn.card_pos
      _ = ks i := (htree i).2
  have hsplit :
      (∑ i, ks i) = (∑ i, (ks i - 1)) + q := by
    calc
      (∑ i, ks i) = ∑ i, ((ks i - 1) + 1) := by
        apply Finset.sum_congr rfl
        intro i _
        have hi := hpositive i
        omega
      _ = (∑ i, (ks i - 1)) + ∑ _i : Fin q, 1 := by
        rw [Finset.sum_add_distrib]
      _ = (∑ i, (ks i - 1)) + q := by simp
  omega

private lemma treeTupleCount_zero_of_guard_failure {n M q : ℕ}
    (G : Graph n) (ks : Fin q → ℕ) (hGM : G.card = M)
    (hbad : ¬ ((∀ i, 0 < ks i) ∧
      (∑ i, ks i) ≤ n ∧ (∑ i, ks i) ≤ M + q)) :
    treeTupleCount G q ks = 0 := by
  rw [treeTupleCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro C _ hC
  rcases hC with ⟨hinj, htree⟩
  apply hbad
  refine ⟨?_, selected_tree_vertex_bound hinj htree,
    selected_tree_edge_bound hGM hinj htree⟩
  intro i
  have hn := componentMember_nonempty (htree i).1.1
  calc
    0 < (C i).card := hn.card_pos
    _ = ks i := (htree i).2

theorem tuple_identity_of_guard_failure (n M q : ℕ) (ks : Fin q → ℕ)
    (hbad : ¬ ((∀ i, 0 < ks i) ∧
      (∑ i, ks i) ≤ n ∧ (∑ i, ks i) ≤ M + q)) :
    tupleMoment n M q ks = tupleFormula n M q ks := by
  unfold tupleMoment expectM
  have hzero :
      (fixedGraphs n M).sum (fun G => (treeTupleCount G q ks : ℝ)) = 0 := by
    apply Finset.sum_eq_zero
    intro G hG
    rw [treeTupleCount_zero_of_guard_failure G ks
      (Finset.mem_filter.mp hG).2 hbad]
    norm_num
  rw [hzero]
  simp [tupleFormula, hbad]

theorem tuple_identity_zero (n M : ℕ) (ks : Fin 0 → ℕ)
    (hM : M ≤ capacity n) :
    tupleMoment n M 0 ks = tupleFormula n M 0 ks := by
  have hcount (G : Graph n) : treeTupleCount G 0 ks = 1 := by
    unfold treeTupleCount
    rw [Finset.filter_eq_self.mpr]
    · simp
    · intro C _
      constructor
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  have hden : ((capacity n).choose M : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hM))
  calc
    tupleMoment n M 0 ks =
        expectM n M (fun _ => 1) := by
      unfold tupleMoment
      congr 1
      funext G
      rw [hcount G]
      norm_num
    _ = 1 := normalization n M hM
    _ = tupleFormula n M 0 ks := by
      simp [tupleFormula, falling, capacity]
      change 1 = ((capacity n).choose M : ℝ) /
        ((capacity n).choose M : ℝ)
      exact (div_self hden).symm

private lemma treeTupleCount_one {n k : ℕ} (G : Graph n) (hk : 0 < k)
    (ks : Fin 1 → ℕ) (hks : ks 0 = k) :
    treeTupleCount G 1 ks = componentCount G k (k - 1) := by
  unfold treeTupleCount componentCount
  apply Finset.card_bij (fun C _ => C 0)
  · intro C hC
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC ⊢
    have htree := hC.2 0
    refine ⟨htree.1.1, ?_, ?_⟩
    · exact htree.2.trans hks
    · have hedge := htree.1.2
      rw [htree.2, hks] at hedge
      omega
  · intro C₁ hC₁ C₂ hC₂ hzero
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact hzero
  · intro S hS
    simp only [Finset.mem_filter] at hS
    let C : Fin 1 → Finset (Fin n) := fun _ => S
    refine ⟨C, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro i j _
      exact Subsingleton.elim i j
    · intro i
      have hcard : S.card = ks i := by
        rw [Subsingleton.elim i 0, hks]
        exact hS.2.1
      refine ⟨⟨hS.1, ?_⟩, hcard⟩
      rw [hS.2.2, hS.2.1]
      omega

theorem tuple_identity_one (hCayley : CayleyBridge)
    (n M : ℕ) (ks : Fin 1 → ℕ) (hM : M ≤ capacity n)
    (hpos : 0 < ks 0) (hkn : ks 0 ≤ n) (hkm : ks 0 ≤ M + 1) :
    tupleMoment n M 1 ks = tupleFormula n M 1 ks := by
  let k := ks 0
  have hk : 0 < k := hpos
  have heM : k - 1 ≤ M := by omega
  have htree :
      tupleMoment n M 1 ks =
        expectM n M (fun G => (componentCount G k (k - 1) : ℝ)) := by
    unfold tupleMoment
    congr 1
    funext G
    rw [treeTupleCount_one G hk ks rfl]
  rw [htree, component_identity n M k (k - 1) hM]
  unfold componentFormula tupleFormula
  rw [if_pos ⟨hkn, heM⟩]
  have hguard :
      (∀ i : Fin 1, 0 < ks i) ∧
        (∑ i, ks i) ≤ n ∧ (∑ i, ks i) ≤ M + 1 := by
    simp only [Fin.sum_univ_one]
    refine ⟨?_, hkn, hkm⟩
    intro i
    simpa [Subsingleton.elim i 0] using! hpos
  rw [if_pos hguard]
  simp only [Fin.sum_univ_one, Fin.prod_univ_one]
  rw [hCayley k hk]
  have hsub : M + 1 - k = M - (k - 1) := by omega
  rw [hsub]
  have hfallNat : falling n k = k.factorial * n.choose k := by
    rw [falling, ← Nat.descFactorial_eq_prod_range,
      Nat.descFactorial_eq_factorial_mul_choose]
  have hfall :
      (falling n k : ℝ) = (k.factorial : ℝ) * (n.choose k : ℝ) := by
    exact_mod_cast hfallNat
  rw [hfall]
  have hfact : (k.factorial : ℝ) ≠ 0 := by positivity
  have hden : ((capacity n).choose M : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hM))
  field_simp [hfact, hden]
  ring

def tupleMarkedFamily (n M q : ℕ) (ks : Fin q → ℕ) : Type :=
  Σ G : ↑(fixedGraphs n M),
    ↑((Finset.univ : Finset (Fin q → Finset (Fin n))).filter
      (fun C => Function.Injective C ∧
        ∀ i, isTree G.1 (C i) ∧ (C i).card = ks i))

noncomputable instance tupleMarkedFamilyFintype
    (n M q : ℕ) (ks : Fin q → ℕ) :
    Fintype (tupleMarkedFamily n M q ks) := by
  unfold tupleMarkedFamily
  infer_instance

theorem tupleMarkedFamily_card (n M q : ℕ) (ks : Fin q → ℕ) :
    Fintype.card (tupleMarkedFamily n M q ks) =
      ∑ G ∈ fixedGraphs n M, treeTupleCount G q ks := by
  unfold tupleMarkedFamily treeTupleCount
  rw [Fintype.card_eq_nat_card, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Fintype.card_coe]
  calc
    _ = ∑ G ∈ (fixedGraphs n M).attach,
        ((Finset.univ : Finset (Fin q → Finset (Fin n))).filter
          (fun C => Function.Injective C ∧
            ∀ i, isTree G.1 (C i) ∧ (C i).card = ks i)).card :=
      Finset.sum_coe_sort_eq_attach _ _
    _ = _ := by
      simpa only using! Finset.sum_attach (fixedGraphs n M)
        (fun G => ((Finset.univ :
          Finset (Fin q → Finset (Fin n))).filter
            (fun C => Function.Injective C ∧
              ∀ i, isTree G (C i) ∧ (C i).card = ks i)).card)

theorem tupleMoment_eq_marked_card (n M q : ℕ) (ks : Fin q → ℕ) :
    tupleMoment n M q ks =
      (Fintype.card (tupleMarkedFamily n M q ks) : ℝ) /
        ((capacity n).choose M : ℝ) := by
  unfold tupleMoment expectM
  rw [card_fixedGraphs]
  congr 1
  exact_mod_cast (tupleMarkedFamily_card n M q ks).symm

abbrev TupleSlot {q : ℕ} (ks : Fin q → ℕ) :=
  Σ i : Fin q, Fin (ks i)

def TupleLayout (n q : ℕ) (ks : Fin q → ℕ) :=
  {C : Fin q → Finset (Fin n) //
    Function.Injective C ∧
    (∀ i, (C i).card = ks i) ∧
    ((Finset.univ : Finset (Fin q)) : Set (Fin q)).PairwiseDisjoint C}

noncomputable instance tupleLayoutFintype (n q : ℕ) (ks : Fin q → ℕ) :
    Fintype (TupleLayout n q ks) := by
  unfold TupleLayout
  infer_instance

private def tupleFiberEmbedding {n q : ℕ} {ks : Fin q → ℕ}
    (f : TupleSlot ks ↪ Fin n) (i : Fin q) : Fin (ks i) ↪ Fin n where
  toFun x := f ⟨i, x⟩
  inj' x y h := by
    have hs : (⟨i, x⟩ : TupleSlot ks) = ⟨i, y⟩ := f.injective h
    cases hs
    rfl

private def tupleBlock {n q : ℕ} {ks : Fin q → ℕ}
    (f : TupleSlot ks ↪ Fin n) (i : Fin q) : Finset (Fin n) :=
  Finset.univ.map (tupleFiberEmbedding f i)

private lemma tupleBlock_card {n q : ℕ} {ks : Fin q → ℕ}
    (f : TupleSlot ks ↪ Fin n) (i : Fin q) :
    (tupleBlock f i).card = ks i := by
  simp [tupleBlock]

private lemma tupleBlock_pairwise {n q : ℕ} {ks : Fin q → ℕ}
    (f : TupleSlot ks ↪ Fin n) :
    ((Finset.univ : Finset (Fin q)) : Set (Fin q)).PairwiseDisjoint
      (tupleBlock f) := by
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  rw [tupleBlock, Finset.mem_map] at hxi hxj
  rcases hxi with ⟨a, -, ha⟩
  rcases hxj with ⟨b, -, hb⟩
  have hab : (⟨i, a⟩ : TupleSlot ks) = ⟨j, b⟩ :=
    f.injective (ha.trans hb.symm)
  exact hij (congrArg Sigma.fst hab)

private lemma tupleBlock_injective {n q : ℕ} {ks : Fin q → ℕ}
    (hpos : ∀ i, 0 < ks i) (f : TupleSlot ks ↪ Fin n) :
    Function.Injective (tupleBlock f) := by
  intro i j hij
  by_contra hne
  let a : Fin (ks i) := ⟨0, hpos i⟩
  have ha : f ⟨i, a⟩ ∈ tupleBlock f i := by
    rw [tupleBlock, Finset.mem_map]
    exact ⟨a, Finset.mem_univ _, rfl⟩
  have haj : f ⟨i, a⟩ ∈ tupleBlock f j := hij ▸ ha
  rw [tupleBlock, Finset.mem_map] at haj
  rcases haj with ⟨b, -, hb⟩
  have hsigma : (⟨i, a⟩ : TupleSlot ks) = ⟨j, b⟩ :=
    f.injective hb.symm
  exact hne (congrArg Sigma.fst hsigma)

private def tupleLayoutOfEmbedding {n q : ℕ} {ks : Fin q → ℕ}
    (hpos : ∀ i, 0 < ks i) (f : TupleSlot ks ↪ Fin n) :
    TupleLayout n q ks :=
  ⟨tupleBlock f, tupleBlock_injective hpos f,
    tupleBlock_card f, tupleBlock_pairwise f⟩

private def tupleFiberEquiv {n q : ℕ} {ks : Fin q → ℕ}
    (f : TupleSlot ks ↪ Fin n) (i : Fin q) :
    Fin (ks i) ≃ ↥(tupleBlock f i) :=
  Equiv.ofBijective
    (fun x => ⟨f ⟨i, x⟩, by
      change f ⟨i, x⟩ ∈ Finset.univ.map (tupleFiberEmbedding f i)
      rw [Finset.mem_map]
      exact ⟨x, Finset.mem_univ _, rfl⟩⟩)
    ⟨fun x y h => by
        have hs : (⟨i, x⟩ : TupleSlot ks) = ⟨i, y⟩ :=
          f.injective (congrArg Subtype.val h)
        cases hs
        rfl,
      fun y => by
        have hy : y.val ∈ Finset.univ.map (tupleFiberEmbedding f i) :=
          y.property
        rw [Finset.mem_map] at hy
        rcases hy with ⟨x, -, hx⟩
        exact ⟨x, Subtype.ext hx⟩⟩

def LabelledTupleLayout (n q : ℕ) (ks : Fin q → ℕ) :=
  Σ C : TupleLayout n q ks, ∀ i, Fin (ks i) ≃ ↥(C.1 i)

noncomputable instance labelledTupleLayoutFintype
    (n q : ℕ) (ks : Fin q → ℕ) :
    Fintype (LabelledTupleLayout n q ks) := by
  unfold LabelledTupleLayout
  infer_instance

private def labelledTupleLayoutOfEmbedding {n q : ℕ} {ks : Fin q → ℕ}
    (hpos : ∀ i, 0 < ks i) (f : TupleSlot ks ↪ Fin n) :
    LabelledTupleLayout n q ks :=
  ⟨tupleLayoutOfEmbedding hpos f, tupleFiberEquiv f⟩

private def embeddingOfLabelledTupleLayout {n q : ℕ} {ks : Fin q → ℕ}
    (L : LabelledTupleLayout n q ks) : TupleSlot ks ↪ Fin n where
  toFun x := (L.2 x.1 x.2).val
  inj' x y h := by
    rcases x with ⟨i, x⟩
    rcases y with ⟨j, y⟩
    have hi : (L.2 i x).val ∈ L.1.1 i := (L.2 i x).property
    have hj : (L.2 j y).val ∈ L.1.1 j := (L.2 j y).property
    have hval : (L.2 i x).val = (L.2 j y).val := h
    have hij : i = j := by
      by_contra hij
      have hdis := L.1.2.2.2 (Finset.mem_univ i) (Finset.mem_univ j) hij
      exact Finset.disjoint_left.mp hdis hi (hval ▸ hj)
    subst j
    have hxy : x = y := (L.2 i).injective (Subtype.ext hval)
    subst y
    rfl

private lemma cast_tupleLayoutEquiv_val {n q : ℕ} {ks : Fin q → ℕ}
    {C D : TupleLayout n q ks} (h : C = D)
    (e : ∀ i, Fin (ks i) ≃ ↥(C.1 i)) (i : Fin q) (x : Fin (ks i)) :
    (((Equiv.cast (congrArg
      (fun E : TupleLayout n q ks => ∀ j, Fin (ks j) ≃ ↥(E.1 j)) h)) e) i x).val =
      (e i x).val := by
  cases h
  rfl

private def tupleLayoutEmbeddingEquiv {n q : ℕ} {ks : Fin q → ℕ}
    (hpos : ∀ i, 0 < ks i) :
    (TupleSlot ks ↪ Fin n) ≃ LabelledTupleLayout n q ks where
  toFun := labelledTupleLayoutOfEmbedding hpos
  invFun := embeddingOfLabelledTupleLayout
  left_inv f := by
    ext x
    rfl
  right_inv L := by
    have hL :
        (labelledTupleLayoutOfEmbedding hpos
          (embeddingOfLabelledTupleLayout L)).1 = L.1 := by
      apply Subtype.ext
      funext i
      ext x
      constructor
      · intro hx
        have hx' : x ∈ Finset.univ.map
            (tupleFiberEmbedding (embeddingOfLabelledTupleLayout L) i) := hx
        rw [Finset.mem_map] at hx'
        rcases hx' with ⟨a, -, ha⟩
        exact ha ▸ (L.2 i a).property
      · intro hx
        let a := (L.2 i).symm ⟨x, hx⟩
        change x ∈ Finset.univ.map
          (tupleFiberEmbedding (embeddingOfLabelledTupleLayout L) i)
        rw [Finset.mem_map]
        exact ⟨a, Finset.mem_univ _, congrArg Subtype.val
          ((L.2 i).apply_symm_apply ⟨x, hx⟩)⟩
    apply Sigma.ext hL
    apply (Equiv.cast_eq_iff_heq (congrArg
      (fun C : TupleLayout n q ks =>
        ∀ i, Fin (ks i) ≃ ↥(C.1 i)) hL)).mp
    funext i
    apply Equiv.ext
    intro x
    apply Subtype.ext
    calc
      (((Equiv.cast (congrArg
          (fun C : TupleLayout n q ks =>
            ∀ j, Fin (ks j) ≃ ↥(C.1 j)) hL))
          (labelledTupleLayoutOfEmbedding hpos
            (embeddingOfLabelledTupleLayout L)).2) i x).val =
          ((labelledTupleLayoutOfEmbedding hpos
            (embeddingOfLabelledTupleLayout L)).2 i x).val :=
        cast_tupleLayoutEquiv_val hL _ i x
      _ = (L.2 i x).val := rfl

private lemma card_tupleSlot {q : ℕ} (ks : Fin q → ℕ) :
    Fintype.card (TupleSlot ks) = ∑ i, ks i := by
  rw [Fintype.card_sigma]
  simp

theorem tupleLayout_card_mul_factorial {n q : ℕ} {ks : Fin q → ℕ}
    (hpos : ∀ i, 0 < ks i) :
    Fintype.card (TupleLayout n q ks) * (∏ i, (ks i).factorial) =
      falling n (∑ i, ks i) := by
  have hequiv :
      Fintype.card (TupleSlot ks ↪ Fin n) =
        Fintype.card (LabelledTupleLayout n q ks) :=
    Fintype.card_congr (tupleLayoutEmbeddingEquiv hpos)
  have hleft :
      Fintype.card (TupleSlot ks ↪ Fin n) =
        falling n (∑ i, ks i) := by
    rw [Fintype.card_embedding_eq, card_tupleSlot]
    simp only [Fintype.card_fin]
    unfold falling
    rw [← Nat.descFactorial_eq_prod_range]
  have hfiber (C : TupleLayout n q ks) :
      Fintype.card (∀ i, Fin (ks i) ≃ ↥(C.1 i)) =
        ∏ i, (ks i).factorial := by
    rw [Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro i _
    have e : Fin (ks i) ≃ ↥(C.1 i) :=
      Fintype.equivOfCardEq (by simp [C.2.2.1 i])
    simpa using! Fintype.card_equiv e
  have hright :
      Fintype.card (LabelledTupleLayout n q ks) =
        Fintype.card (TupleLayout n q ks) *
          (∏ i, (ks i).factorial) := by
    change Fintype.card (Σ C : TupleLayout n q ks,
      ∀ i, Fin (ks i) ≃ ↥(C.1 i)) = _
    rw [Fintype.card_sigma]
    simp_rw [hfiber]
    simp [Finset.sum_const, nsmul_eq_mul]
  omega

def TupleEnumerationData (n M q : ℕ) (ks : Fin q → ℕ) : Type :=
  Σ C : TupleLayout n q ks,
    (∀ i, ↑(componentConnectedFamily (ks i) (ks i - 1))) ×
      ↑(fixedGraphs (n - ∑ i, ks i) (M + q - ∑ i, ks i))

noncomputable instance tupleEnumerationDataFintype
    (n M q : ℕ) (ks : Fin q → ℕ) :
    Fintype (TupleEnumerationData n M q ks) := by
  unfold TupleEnumerationData
  infer_instance

theorem tupleEnumerationData_card (n M q : ℕ) (ks : Fin q → ℕ) :
    Fintype.card (TupleEnumerationData n M q ks) =
      Fintype.card (TupleLayout n q ks) *
        (∏ i, connectedCount (ks i) (ks i - 1)) *
        (((n - ∑ i, ks i).choose 2).choose
          (M + q - ∑ i, ks i)) := by
  unfold TupleEnumerationData
  change Fintype.card (Σ _C : TupleLayout n q ks,
    (∀ i, ↑(componentConnectedFamily (ks i) (ks i - 1))) ×
      ↑(fixedGraphs (n - ∑ i, ks i) (M + q - ∑ i, ks i))) = _
  rw [Fintype.card_sigma]
  have hconn (i : Fin q) :
      Fintype.card ↑(componentConnectedFamily (ks i) (ks i - 1)) =
        connectedCount (ks i) (ks i - 1) := by
    rw [Fintype.card_coe]
    rfl
  have hout :
      Fintype.card
          ↑(fixedGraphs (n - ∑ i, ks i) (M + q - ∑ i, ks i)) =
        (((n - ∑ i, ks i).choose 2).choose
          (M + q - ∑ i, ks i)) := by
    rw [Fintype.card_coe, card_fixedGraphs]
    rfl
  simp only [Fintype.card_prod, Fintype.card_pi]
  simp_rw [hconn, hout]
  simp [Finset.sum_const, nsmul_eq_mul, Nat.mul_assoc]

private def tupleVertexUnion {n q : ℕ} {ks : Fin q → ℕ}
    (C : TupleLayout n q ks) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin q)).biUnion C.1

private lemma tupleVertexUnion_card {n q : ℕ} {ks : Fin q → ℕ}
    (C : TupleLayout n q ks) :
    (tupleVertexUnion C).card = ∑ i, ks i := by
  unfold tupleVertexUnion
  rw [Finset.card_biUnion C.2.2.2]
  simp_rw [C.2.2.1]

private lemma tupleVertexComplement_card {n q : ℕ} {ks : Fin q → ℕ}
    (C : TupleLayout n q ks) :
    ((Finset.univ : Finset (Fin n)) \ tupleVertexUnion C).card =
      n - ∑ i, ks i := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Fintype.card_fin, tupleVertexUnion_card]

private def tuplePlacedGraphs {n q : ℕ} {ks : Fin q → ℕ}
    (C : TupleLayout n q ks) (I : ∀ i, Graph (ks i)) :
    Fin q → Graph n :=
  fun i => componentPlace (C.1 i) (C.2.2.1 i) (I i)

private def tupleSelectedGraph {n q : ℕ} {ks : Fin q → ℕ}
    (C : TupleLayout n q ks) (I : ∀ i, Graph (ks i)) : Graph n :=
  (Finset.univ : Finset (Fin q)).biUnion (tuplePlacedGraphs C I)

private lemma tuplePlacedGraphs_pairwise {n q : ℕ} {ks : Fin q → ℕ}
    (C : TupleLayout n q ks) (I : ∀ i, Graph (ks i)) :
    ((Finset.univ : Finset (Fin q)) : Set (Fin q)).PairwiseDisjoint
      (tuplePlacedGraphs C I) := by
  intro i _ j _ hij
  have hCdis := C.2.2.2 (Finset.mem_univ i) (Finset.mem_univ j) hij
  apply Finset.disjoint_left.mpr
  intro e hei hej
  have hi := componentPlace_mem (C.1 i) (C.2.2.1 i) (I i) hei
  have hj := componentPlace_mem (C.1 j) (C.2.2.1 j) (I j) hej
  exact Finset.disjoint_left.mp hCdis hi.1 hj.1

private lemma tupleSelectedGraph_card {n q : ℕ} {ks : Fin q → ℕ}
    (C : TupleLayout n q ks) (I : ∀ i, Graph (ks i)) :
    (tupleSelectedGraph C I).card = ∑ i, (I i).card := by
  unfold tupleSelectedGraph
  rw [Finset.card_biUnion (tuplePlacedGraphs_pairwise C I)]
  simp_rw [tuplePlacedGraphs, componentPlace_card]

private def tupleAssembledGraph {n M q : ℕ} {ks : Fin q → ℕ}
    (D : TupleEnumerationData n M q ks) : Graph n :=
  tupleSelectedGraph D.1 (fun i => (D.2.1 i).1) ∪
    componentPlace
      ((Finset.univ : Finset (Fin n)) \ tupleVertexUnion D.1)
      (tupleVertexComplement_card D.1) D.2.2.1

private lemma tupleSelected_outside_disjoint {n M q : ℕ}
    {ks : Fin q → ℕ} (D : TupleEnumerationData n M q ks) :
    Disjoint
      (tupleSelectedGraph D.1 (fun i => (D.2.1 i).1))
      (componentPlace
        ((Finset.univ : Finset (Fin n)) \ tupleVertexUnion D.1)
        (tupleVertexComplement_card D.1) D.2.2.1) := by
  apply Finset.disjoint_left.mpr
  intro e heS heO
  simp only [tupleSelectedGraph, Finset.mem_biUnion, Finset.mem_univ,
    true_and] at heS
  rcases heS with ⟨i, hei⟩
  have hi := componentPlace_mem (D.1.1 i) (D.1.2.2.1 i)
    (D.2.1 i).1 hei
  have ho := componentPlace_mem
    ((Finset.univ : Finset (Fin n)) \ tupleVertexUnion D.1)
    (tupleVertexComplement_card D.1) D.2.2.1 heO
  have hiU : e.val.1 ∈ tupleVertexUnion D.1 := by
    rw [tupleVertexUnion, Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ _, hi.1⟩
  exact (Finset.mem_sdiff.mp ho.1).2 hiU

private lemma tupleInternal_card_sum {n M q : ℕ}
    {ks : Fin q → ℕ} (hpos : ∀ i, 0 < ks i)
    (D : TupleEnumerationData n M q ks) :
    (∑ i, (D.2.1 i).1.card) = (∑ i, ks i) - q := by
  have hi (i : Fin q) : (D.2.1 i).1.card = ks i - 1 := by
    exact (Finset.mem_filter.mp
      (Finset.mem_filter.mp (D.2.1 i).2).1).2
  simp_rw [hi]
  have hsplit :
      (∑ i, ks i) = (∑ i, (ks i - 1)) + q := by
    calc
      (∑ i, ks i) = ∑ i, ((ks i - 1) + 1) := by
        apply Finset.sum_congr rfl
        intro i _
        have := hpos i
        omega
      _ = (∑ i, (ks i - 1)) + ∑ _i : Fin q, 1 := by
        rw [Finset.sum_add_distrib]
      _ = (∑ i, (ks i - 1)) + q := by simp
  omega

private lemma tupleAssembledGraph_card {n M q : ℕ}
    {ks : Fin q → ℕ} (hpos : ∀ i, 0 < ks i)
    (hKM : (∑ i, ks i) ≤ M + q)
    (D : TupleEnumerationData n M q ks) :
    (tupleAssembledGraph D).card = M := by
  unfold tupleAssembledGraph
  rw [Finset.card_union_of_disjoint (tupleSelected_outside_disjoint D),
    tupleSelectedGraph_card, componentPlace_card,
    (Finset.mem_filter.mp D.2.2.2).2,
    tupleInternal_card_sum hpos D]
  have hqK : q ≤ ∑ i, ks i := by
    calc
      q = ∑ _i : Fin q, 1 := by simp
      _ ≤ ∑ i, ks i := Finset.sum_le_sum
        (fun i _ => hpos i)
  omega

private lemma tupleAssembledGraph_fixed {n M q : ℕ}
    {ks : Fin q → ℕ} (hpos : ∀ i, 0 < ks i)
    (hKM : (∑ i, ks i) ≤ M + q)
    (D : TupleEnumerationData n M q ks) :
    tupleAssembledGraph D ∈ fixedGraphs n M := by
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
    tupleAssembledGraph_card hpos hKM D⟩

private lemma tupleAssembled_componentSeparated {n M q : ℕ}
    {ks : Fin q → ℕ} (D : TupleEnumerationData n M q ks) (i : Fin q) :
    componentSeparated (D.1.1 i) (tupleAssembledGraph D) := by
  intro e he
  rw [tupleAssembledGraph, Finset.mem_union] at he
  rcases he with heS | heO
  · simp only [tupleSelectedGraph, Finset.mem_biUnion, Finset.mem_univ,
      true_and] at heS
    rcases heS with ⟨j, hej⟩
    have hj := componentPlace_mem (D.1.1 j) (D.1.2.2.1 j)
      (D.2.1 j).1 hej
    by_cases hij : i = j
    · subst j
      exact Or.inl hj
    · have hdis := D.1.2.2.2 (Finset.mem_univ i) (Finset.mem_univ j) hij
      exact Or.inr ⟨Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ _, fun h => Finset.disjoint_left.mp hdis h hj.1⟩,
        Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ _, fun h => Finset.disjoint_left.mp hdis h hj.2⟩⟩
  · have ho := componentPlace_mem
      ((Finset.univ : Finset (Fin n)) \ tupleVertexUnion D.1)
      (tupleVertexComplement_card D.1) D.2.2.1 heO
    exact Or.inr ⟨Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, fun hi =>
        (Finset.mem_sdiff.mp ho.1).2 (by
          rw [tupleVertexUnion, Finset.mem_biUnion]
          exact ⟨i, Finset.mem_univ _, hi⟩)⟩,
      Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, fun hi =>
        (Finset.mem_sdiff.mp ho.2).2 (by
          rw [tupleVertexUnion, Finset.mem_biUnion]
          exact ⟨i, Finset.mem_univ _, hi⟩)⟩⟩

private lemma tuplePlaced_subset_assembled {n M q : ℕ}
    {ks : Fin q → ℕ} (D : TupleEnumerationData n M q ks) (i : Fin q) :
    componentPlace (D.1.1 i) (D.1.2.2.1 i) (D.2.1 i).1 ⊆
      tupleAssembledGraph D := by
  intro e he
  rw [tupleAssembledGraph, Finset.mem_union]
  left
  rw [tupleSelectedGraph, Finset.mem_biUnion]
  exact ⟨i, Finset.mem_univ _, he⟩

private lemma tupleAssembled_component {n M q : ℕ}
    {ks : Fin q → ℕ} (hpos : ∀ i, 0 < ks i)
    (D : TupleEnumerationData n M q ks) (i : Fin q) :
    D.1.1 i ∈ components (tupleAssembledGraph D) := by
  let r : Fin (ks i) := ⟨0, hpos i⟩
  let v : Fin n := (D.1.1 i).orderEmbOfFin (D.1.2.2.1 i) r
  have hv : v ∈ D.1.1 i := Finset.orderEmbOfFin_mem _ _ r
  have hcomp :
      componentOf (tupleAssembledGraph D) v = D.1.1 i := by
    ext x
    simp only [mem_componentOf_iff]
    constructor
    · intro hvx
      exact componentSeparated_reach_mem
        (tupleAssembled_componentSeparated D i) hv hvx
    · intro hx
      let y : ↥(D.1.1 i) := ⟨x, hx⟩
      let u : Fin (ks i) :=
        ((D.1.1 i).orderIsoOfFin (D.1.2.2.1 i)).symm y
      have hxu :
          (D.1.1 i).orderEmbOfFin (D.1.2.2.1 i) u = x := by
        exact congrArg Subtype.val
          (((D.1.1 i).orderIsoOfFin (D.1.2.2.1 i)).apply_symm_apply y)
      rw [← hxu]
      apply componentReach_mono (tuplePlaced_subset_assembled D i)
      apply (componentPlace_reach_iff (D.1.1 i) (D.1.2.2.1 i)
        (D.2.1 i).1 r u).mpr
      exact (Finset.mem_filter.mp (D.2.1 i).2).2.2 r u
  rw [← hcomp]
  exact componentOf_mem_components (tupleAssembledGraph D) v

private lemma tupleAssembled_edgesInside {n M q : ℕ}
    {ks : Fin q → ℕ} (D : TupleEnumerationData n M q ks) (i : Fin q) :
    edgesInside (tupleAssembledGraph D) (D.1.1 i) =
      (D.2.1 i).1.card := by
  rw [← componentTake_card_edgesInside (D.1.1 i) (D.1.2.2.1 i)
    (tupleAssembledGraph D)]
  congr 1
  apply componentPlace_injective (D.1.1 i) (D.1.2.2.1 i)
  rw [componentPlace_take]
  ext e
  change e ∈ (tupleAssembledGraph D).filter
      (componentEdgeInside (D.1.1 i)) ↔ e ∈
        componentPlace (D.1.1 i) (D.1.2.2.1 i) (D.2.1 i).1
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨he, hin⟩
    rw [tupleAssembledGraph, Finset.mem_union] at he
    rcases he with heS | heO
    · simp only [tupleSelectedGraph, Finset.mem_biUnion, Finset.mem_univ,
        true_and] at heS
      rcases heS with ⟨j, hej⟩
      by_cases hij : i = j
      · subst j
        exact hej
      · have hj := componentPlace_mem (D.1.1 j) (D.1.2.2.1 j)
          (D.2.1 j).1 hej
        have hdis := D.1.2.2.2 (Finset.mem_univ i)
          (Finset.mem_univ j) hij
        exact False.elim (Finset.disjoint_left.mp hdis hin.1 hj.1)
    · have ho := componentPlace_mem
        ((Finset.univ : Finset (Fin n)) \ tupleVertexUnion D.1)
        (tupleVertexComplement_card D.1) D.2.2.1 heO
      exact False.elim ((Finset.mem_sdiff.mp ho.1).2 (by
        rw [tupleVertexUnion, Finset.mem_biUnion]
        exact ⟨i, Finset.mem_univ _, hin.1⟩))
  · intro he
    refine ⟨?_, componentPlace_mem (D.1.1 i) (D.1.2.2.1 i)
      (D.2.1 i).1 he⟩
    rw [tupleAssembledGraph, Finset.mem_union]
    exact Or.inl (by
      rw [tupleSelectedGraph, Finset.mem_biUnion]
      exact ⟨i, Finset.mem_univ _, he⟩)

private def tupleEnumerationAssemble {n M q : ℕ}
    {ks : Fin q → ℕ} (hpos : ∀ i, 0 < ks i)
    (hKM : (∑ i, ks i) ≤ M + q) :
    TupleEnumerationData n M q ks → tupleMarkedFamily n M q ks :=
  fun D => by
    let G := tupleAssembledGraph D
    have hG : G ∈ fixedGraphs n M :=
      tupleAssembledGraph_fixed hpos hKM D
    let C := D.1.1
    have hC :
        C ∈ (Finset.univ : Finset (Fin q → Finset (Fin n))).filter
          (fun C => Function.Injective C ∧
            ∀ i, isTree G (C i) ∧ (C i).card = ks i) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, D.1.2.1, ?_⟩
      intro i
      refine ⟨⟨tupleAssembled_component hpos D i, ?_⟩, D.1.2.2.1 i⟩
      rw [tupleAssembled_edgesInside D i, D.1.2.2.1 i]
      have hi := (Finset.mem_filter.mp
        (Finset.mem_filter.mp (D.2.1 i).2).1).2
      have hposi := hpos i
      omega
    exact ⟨⟨G, hG⟩, ⟨C, hC⟩⟩

private def tupleLayoutOfMarked {n M q : ℕ} {ks : Fin q → ℕ}
    (P : tupleMarkedFamily n M q ks) : TupleLayout n q ks := by
  let C := P.2.1
  have hC := (Finset.mem_filter.mp P.2.2).2
  refine ⟨C, hC.1, fun i => (hC.2 i).2, ?_⟩
  intro i _ j _ hij
  exact componentMember_disjoint (hC.2 i).1.1 (hC.2 j).1.1
    (hC.1.ne hij)

private lemma tupleMarked_union_separated {n M q : ℕ}
    {ks : Fin q → ℕ} (P : tupleMarkedFamily n M q ks) :
    componentSeparated (tupleVertexUnion (tupleLayoutOfMarked P)) P.1.1 := by
  intro e he
  let C := P.2.1
  have hC := (Finset.mem_filter.mp P.2.2).2
  by_cases h1 : e.val.1 ∈ tupleVertexUnion (tupleLayoutOfMarked P)
  · rw [tupleVertexUnion, Finset.mem_biUnion] at h1
    rcases h1 with ⟨i, -, hi⟩
    have hsep := componentMember_separated (hC.2 i).1.1
    have h2 : e.val.2 ∈ C i :=
      (componentSeparated_adj hsep
        ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩).mp hi
    exact Or.inl ⟨by
      rw [tupleVertexUnion, Finset.mem_biUnion]
      exact ⟨i, Finset.mem_univ _, hi⟩, by
      rw [tupleVertexUnion, Finset.mem_biUnion]
      exact ⟨i, Finset.mem_univ _, h2⟩⟩
  · by_cases h2 : e.val.2 ∈ tupleVertexUnion (tupleLayoutOfMarked P)
    · rw [tupleVertexUnion, Finset.mem_biUnion] at h2
      rcases h2 with ⟨i, -, hi⟩
      have hsep := componentMember_separated (hC.2 i).1.1
      have h1' : e.val.1 ∈ C i :=
        (componentSeparated_adj hsep
          ⟨e, he, Or.inr ⟨rfl, rfl⟩⟩).mp hi
      exact False.elim (h1 (by
        rw [tupleVertexUnion, Finset.mem_biUnion]
        exact ⟨i, Finset.mem_univ _, h1'⟩))
    · exact Or.inr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h1⟩,
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h2⟩⟩

private def tupleInternalEdgeSets {n M q : ℕ} {ks : Fin q → ℕ}
    (P : tupleMarkedFamily n M q ks) : Fin q → Finset (Edge n) :=
  fun i => P.1.1.filter
    (componentEdgeInside ((tupleLayoutOfMarked P).1 i))

private lemma tupleInternalEdgeSets_pairwise {n M q : ℕ}
    {ks : Fin q → ℕ} (P : tupleMarkedFamily n M q ks) :
    ((Finset.univ : Finset (Fin q)) : Set (Fin q)).PairwiseDisjoint
      (tupleInternalEdgeSets P) := by
  intro i _ j _ hij
  have hdis := (tupleLayoutOfMarked P).2.2.2
    (Finset.mem_univ i) (Finset.mem_univ j) hij
  apply Finset.disjoint_left.mpr
  intro e hei hej
  exact Finset.disjoint_left.mp hdis
    (Finset.mem_filter.mp hei).2.1 (Finset.mem_filter.mp hej).2.1

private lemma tupleInternalEdgeUnion_eq_filter {n M q : ℕ}
    {ks : Fin q → ℕ} (P : tupleMarkedFamily n M q ks) :
    (Finset.univ : Finset (Fin q)).biUnion (tupleInternalEdgeSets P) =
      P.1.1.filter
        (componentEdgeInside (tupleVertexUnion (tupleLayoutOfMarked P))) := by
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
    tupleInternalEdgeSets, Finset.mem_filter]
  constructor
  · rintro ⟨i, he, hi⟩
    refine ⟨he, ?_⟩
    constructor
    · rw [tupleVertexUnion, Finset.mem_biUnion]
      exact ⟨i, Finset.mem_univ _, hi.1⟩
    · rw [tupleVertexUnion, Finset.mem_biUnion]
      exact ⟨i, Finset.mem_univ _, hi.2⟩
  · rintro ⟨he, h1, h2⟩
    rw [tupleVertexUnion, Finset.mem_biUnion] at h1
    rcases h1 with ⟨i, -, hi⟩
    have hC := (Finset.mem_filter.mp P.2.2).2
    have hsep := componentMember_separated (hC.2 i).1.1
    have hi2 : e.val.2 ∈ (tupleLayoutOfMarked P).1 i :=
      (componentSeparated_adj hsep
        ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩).mp hi
    exact ⟨i, he, hi, hi2⟩

private lemma tupleMarked_union_edgesInside {n M q : ℕ}
    {ks : Fin q → ℕ} (P : tupleMarkedFamily n M q ks) :
    edgesInside P.1.1 (tupleVertexUnion (tupleLayoutOfMarked P)) =
      ∑ i, edgesInside P.1.1 ((tupleLayoutOfMarked P).1 i) := by
  unfold edgesInside
  have hcard := congrArg Finset.card
    (tupleInternalEdgeUnion_eq_filter P)
  rw [Finset.card_biUnion (tupleInternalEdgeSets_pairwise P)] at hcard
  simp only [tupleInternalEdgeSets] at hcard
  unfold componentEdgeInside at hcard
  convert hcard.symm using 1
  · congr 1
    ext e
    simp
  · apply Finset.sum_congr rfl
    intro i _
    congr 1
    ext e
    simp

private lemma tupleMarked_outside_card {n M q : ℕ}
    {ks : Fin q → ℕ}
    (hguard : (∀ i, 0 < ks i) ∧
      (∑ i, ks i) ≤ n ∧ (∑ i, ks i) ≤ M + q)
    (P : tupleMarkedFamily n M q ks) :
    (componentTake
      ((Finset.univ : Finset (Fin n)) \
        tupleVertexUnion (tupleLayoutOfMarked P))
      (tupleVertexComplement_card (tupleLayoutOfMarked P)) P.1.1).card =
      M + q - ∑ i, ks i := by
  let C := tupleLayoutOfMarked P
  let U := tupleVertexUnion C
  have hU : U.card = ∑ i, ks i := by
    simpa [U, C] using! tupleVertexUnion_card C
  have hdecomp := congrArg Finset.card
    (componentCombine_take U hU P.1.1 (tupleMarked_union_separated P))
  rw [componentCombine_card, componentTake_card_edgesInside,
    tupleMarked_union_edgesInside] at hdecomp
  have hproof : componentComplement_card U hU =
      tupleVertexComplement_card C := Subsingleton.elim _ _
  rw [hproof] at hdecomp
  have hGcard : P.1.1.card = M := (Finset.mem_filter.mp P.1.2).2
  rw [hGcard] at hdecomp
  have hC := (Finset.mem_filter.mp P.2.2).2
  have hedges (i : Fin q) :
      edgesInside P.1.1 ((tupleLayoutOfMarked P).1 i) = ks i - 1 := by
    have ht := (hC.2 i).1.2
    rw [(hC.2 i).2] at ht
    exact Nat.eq_sub_of_add_eq ht
  simp_rw [hedges] at hdecomp
  have hsplit :
      (∑ i, ks i) = (∑ i, (ks i - 1)) + q := by
    calc
      (∑ i, ks i) = ∑ i, ((ks i - 1) + 1) := by
        apply Finset.sum_congr rfl
        intro i _
        have := hguard.1 i
        omega
      _ = (∑ i, (ks i - 1)) + ∑ _i : Fin q, 1 := by
        rw [Finset.sum_add_distrib]
      _ = (∑ i, (ks i - 1)) + q := by simp
  change (componentTake ((Finset.univ : Finset (Fin n)) \ U)
    (tupleVertexComplement_card C) P.1.1).card =
      M + q - ∑ i, ks i
  omega

private def tupleEnumerationDisassemble {n M q : ℕ}
    {ks : Fin q → ℕ}
    (hguard : (∀ i, 0 < ks i) ∧
      (∑ i, ks i) ≤ n ∧ (∑ i, ks i) ≤ M + q) :
    tupleMarkedFamily n M q ks → TupleEnumerationData n M q ks :=
  fun P => by
    let C := tupleLayoutOfMarked P
    let I : ∀ i, ↑(componentConnectedFamily (ks i) (ks i - 1)) :=
      fun i => by
        let H := componentTake (C.1 i) (C.2.2.1 i) P.1.1
        have hC := (Finset.mem_filter.mp P.2.2).2
        have hcard : H.card = ks i - 1 := by
          dsimp [H]
          rw [componentTake_card_edgesInside]
          have ht := (hC.2 i).1.2
          rw [(hC.2 i).2] at ht
          exact Nat.eq_sub_of_add_eq ht
        have hfixed : H ∈ fixedGraphs (ks i) (ks i - 1) :=
          Finset.mem_filter.mpr
            ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hcard⟩
        exact ⟨H, Finset.mem_filter.mpr
          ⟨hfixed, hguard.1 i,
            componentTake_connected_of_member (C.1 i) (C.2.2.1 i)
              P.1.1 (hC.2 i).1.1⟩⟩
    let O := componentTake
      ((Finset.univ : Finset (Fin n)) \ tupleVertexUnion C)
      (tupleVertexComplement_card C) P.1.1
    have hOfixed :
        O ∈ fixedGraphs (n - ∑ i, ks i) (M + q - ∑ i, ks i) :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
          tupleMarked_outside_card hguard P⟩
    exact ⟨C, I, ⟨O, hOfixed⟩⟩

private lemma tupleTake_assembled {n M q : ℕ}
    {ks : Fin q → ℕ} (D : TupleEnumerationData n M q ks) (i : Fin q) :
    componentTake (D.1.1 i) (D.1.2.2.1 i)
      (tupleAssembledGraph D) = (D.2.1 i).1 := by
  apply componentPlace_injective (D.1.1 i) (D.1.2.2.1 i)
  rw [componentPlace_take]
  ext e
  change e ∈ (tupleAssembledGraph D).filter
      (componentEdgeInside (D.1.1 i)) ↔ e ∈
        componentPlace (D.1.1 i) (D.1.2.2.1 i) (D.2.1 i).1
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨he, hin⟩
    rw [tupleAssembledGraph, Finset.mem_union] at he
    rcases he with heS | heO
    · simp only [tupleSelectedGraph, Finset.mem_biUnion, Finset.mem_univ,
        true_and] at heS
      rcases heS with ⟨j, hej⟩
      by_cases hij : i = j
      · subst j
        exact hej
      · have hj := componentPlace_mem (D.1.1 j) (D.1.2.2.1 j)
          (D.2.1 j).1 hej
        have hdis := D.1.2.2.2 (Finset.mem_univ i)
          (Finset.mem_univ j) hij
        exact False.elim (Finset.disjoint_left.mp hdis hin.1 hj.1)
    · have ho := componentPlace_mem
        ((Finset.univ : Finset (Fin n)) \ tupleVertexUnion D.1)
        (tupleVertexComplement_card D.1) D.2.2.1 heO
      exact False.elim ((Finset.mem_sdiff.mp ho.1).2 (by
        rw [tupleVertexUnion, Finset.mem_biUnion]
        exact ⟨i, Finset.mem_univ _, hin.1⟩))
  · intro he
    refine ⟨?_, componentPlace_mem (D.1.1 i) (D.1.2.2.1 i)
      (D.2.1 i).1 he⟩
    rw [tupleAssembledGraph, Finset.mem_union]
    exact Or.inl (by
      rw [tupleSelectedGraph, Finset.mem_biUnion]
      exact ⟨i, Finset.mem_univ _, he⟩)

private lemma tupleOutsideTake_assembled {n M q : ℕ}
    {ks : Fin q → ℕ} (D : TupleEnumerationData n M q ks) :
    componentTake
      ((Finset.univ : Finset (Fin n)) \ tupleVertexUnion D.1)
      (tupleVertexComplement_card D.1) (tupleAssembledGraph D) =
      D.2.2.1 := by
  apply componentPlace_injective _
    (tupleVertexComplement_card D.1)
  rw [componentPlace_take]
  ext e
  simp only [Finset.mem_filter, tupleAssembledGraph, Finset.mem_union]
  constructor
  · rintro ⟨heS | heO, hout⟩
    · simp only [tupleSelectedGraph, Finset.mem_biUnion, Finset.mem_univ,
        true_and] at heS
      rcases heS with ⟨i, hei⟩
      have hi := componentPlace_mem (D.1.1 i) (D.1.2.2.1 i)
        (D.2.1 i).1 hei
      exact False.elim ((Finset.mem_sdiff.mp hout.1).2 (by
        rw [tupleVertexUnion, Finset.mem_biUnion]
        exact ⟨i, Finset.mem_univ _, hi.1⟩))
    · exact heO
  · intro heO
    exact ⟨Or.inr heO, componentPlace_mem
      ((Finset.univ : Finset (Fin n)) \ tupleVertexUnion D.1)
      (tupleVertexComplement_card D.1) D.2.2.1 heO⟩

private lemma tupleAssemble_disassemble_graph {n M q : ℕ}
    {ks : Fin q → ℕ}
    (hguard : (∀ i, 0 < ks i) ∧
      (∑ i, ks i) ≤ n ∧ (∑ i, ks i) ≤ M + q)
    (P : tupleMarkedFamily n M q ks) :
    tupleAssembledGraph (tupleEnumerationDisassemble hguard P) = P.1.1 := by
  let C := tupleLayoutOfMarked P
  let U := tupleVertexUnion C
  have hsep := tupleMarked_union_separated P
  rw [tupleAssembledGraph]
  dsimp [tupleEnumerationDisassemble]
  have hselected :
      tupleSelectedGraph C
        (fun i => ((tupleEnumerationDisassemble hguard P).2.1 i).1) =
      P.1.1.filter (componentEdgeInside U) := by
    rw [← tupleInternalEdgeUnion_eq_filter P]
    unfold tupleSelectedGraph tupleInternalEdgeSets tuplePlacedGraphs
    apply Finset.biUnion_congr rfl
    intro i _
    change componentPlace (C.1 i) (C.2.2.1 i)
      (componentTake (C.1 i) (C.2.2.1 i) P.1.1) =
        P.1.1.filter (componentEdgeInside
          ((tupleLayoutOfMarked P).1 i))
    rw [componentPlace_take]
  change
    tupleSelectedGraph C
        (fun i => ((tupleEnumerationDisassemble hguard P).2.1 i).1) ∪
      componentPlace ((Finset.univ : Finset (Fin n)) \ U)
        (tupleVertexComplement_card C)
        (componentTake ((Finset.univ : Finset (Fin n)) \ U)
          (tupleVertexComplement_card C) P.1.1) = P.1.1
  rw [hselected]
  rw [← componentPlace_take U (tupleVertexUnion_card C) P.1.1]
  change componentCombine U (tupleVertexUnion_card C)
    (componentTake U (tupleVertexUnion_card C) P.1.1)
    (componentTake ((Finset.univ : Finset (Fin n)) \ U)
      (tupleVertexComplement_card C) P.1.1) = P.1.1
  exact componentCombine_take U (tupleVertexUnion_card C) P.1.1 hsep

private def tupleEnumerationEquiv {n M q : ℕ}
    {ks : Fin q → ℕ}
    (hguard : (∀ i, 0 < ks i) ∧
      (∑ i, ks i) ≤ n ∧ (∑ i, ks i) ≤ M + q) :
    TupleEnumerationData n M q ks ≃ tupleMarkedFamily n M q ks where
  toFun := tupleEnumerationAssemble hguard.1 hguard.2.2
  invFun := tupleEnumerationDisassemble hguard
  left_inv D := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Prod.ext
      · funext i
        apply Subtype.ext
        exact tupleTake_assembled D i
      · apply Subtype.ext
        exact tupleOutsideTake_assembled D
  right_inv P := by
    let Q := tupleEnumerationAssemble hguard.1 hguard.2.2
      (tupleEnumerationDisassemble hguard P)
    change Q = P
    have hgraph : Q.1.1 = P.1.1 :=
      tupleAssemble_disassemble_graph hguard P
    have hfirst : Q.1 = P.1 := Subtype.ext hgraph
    apply Sigma.ext hfirst
    apply (Subtype.heq_iff_coe_eq (fun C => by
      rw [hgraph])).2
    rfl

def TupleEnumerationEquivStatement : Prop :=
  ∀ (n M q : ℕ) (ks : Fin q → ℕ), 2 ≤ q →
    ((∀ i, 0 < ks i) ∧
      (∑ i, ks i) ≤ n ∧ (∑ i, ks i) ≤ M + q) →
    Nonempty
      (TupleEnumerationData n M q ks ≃
        tupleMarkedFamily n M q ks)

theorem tupleEnumeration_equiv_statement :
    TupleEnumerationEquivStatement := by
  intro n M q ks _hq hguard
  exact ⟨tupleEnumerationEquiv hguard⟩

theorem tupleMarked_count_of_enumeration_equiv
    (hCayley : CayleyBridge)
    {n M q : ℕ} {ks : Fin q → ℕ}
    (hguard : (∀ i, 0 < ks i) ∧
      (∑ i, ks i) ≤ n ∧ (∑ i, ks i) ≤ M + q)
    (e : TupleEnumerationData n M q ks ≃
      tupleMarkedFamily n M q ks) :
    Fintype.card (tupleMarkedFamily n M q ks) *
        (∏ i, (ks i).factorial) =
      falling n (∑ i, ks i) *
        (∏ i, cayley (ks i)) *
        ((n - ∑ i, ks i).choose 2).choose
          (M + q - ∑ i, ks i) := by
  have hcard :
      Fintype.card (tupleMarkedFamily n M q ks) =
        Fintype.card (TupleEnumerationData n M q ks) :=
    Fintype.card_congr e.symm
  have hlayout := tupleLayout_card_mul_factorial
    (n := n) (ks := ks) hguard.1
  have htrees :
      (∏ i, connectedCount (ks i) (ks i - 1)) =
        ∏ i, cayley (ks i) := by
    apply Finset.prod_congr rfl
    intro i _
    exact hCayley (ks i) (hguard.1 i)
  rw [hcard, tupleEnumerationData_card, htrees]
  calc
    (Fintype.card (TupleLayout n q ks) *
          (∏ i, cayley (ks i)) *
          (((n - ∑ i, ks i).choose 2).choose
            (M + q - ∑ i, ks i))) *
        (∏ i, (ks i).factorial) =
      (Fintype.card (TupleLayout n q ks) *
        (∏ i, (ks i).factorial)) *
        (∏ i, cayley (ks i)) *
        (((n - ∑ i, ks i).choose 2).choose
          (M + q - ∑ i, ks i)) := by ring
    _ = _ := by rw [hlayout]

def FiniteResidualStatement : Prop :=
  TupleEnumerationEquivStatement

theorem finiteResidual : FiniteResidualStatement :=
  tupleEnumeration_equiv_statement

theorem tuple_identity_of_marked_count
    {n M q : ℕ} {ks : Fin q → ℕ}
    (hM : M ≤ capacity n)
    (hguard : (∀ i, 0 < ks i) ∧
      (∑ i, ks i) ≤ n ∧ (∑ i, ks i) ≤ M + q)
    (hcount :
      Fintype.card (tupleMarkedFamily n M q ks) *
          (∏ i, (ks i).factorial) =
        falling n (∑ i, ks i) *
          (∏ i, cayley (ks i)) *
          ((n - ∑ i, ks i).choose 2).choose
            (M + q - ∑ i, ks i)) :
    tupleMoment n M q ks = tupleFormula n M q ks := by
  rw [tupleMoment_eq_marked_card]
  unfold tupleFormula
  rw [if_pos hguard]
  rw [Finset.prod_div_distrib]
  have hprodNat : 0 < ∏ i, (ks i).factorial :=
    Finset.prod_pos (fun _ _ => Nat.factorial_pos _)
  have hprod : (∏ i, ((ks i).factorial : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hprodNat)
  have hden : ((capacity n).choose M : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hM))
  have hcountR :
      (Fintype.card (tupleMarkedFamily n M q ks) : ℝ) *
          (∏ i, ((ks i).factorial : ℝ)) =
        (falling n (∑ i, ks i) : ℝ) *
          (∏ i, (cayley (ks i) : ℝ)) *
          (((n - ∑ i, ks i).choose 2).choose
            (M + q - ∑ i, ks i) : ℝ) := by
    exact_mod_cast hcount
  field_simp [hprod, hden]
  nlinarith [hcountR]

theorem tuple_identity_of_residual (h : FiniteResidualStatement)
    (hCayley : CayleyBridge) :
    ∀ (n M q : ℕ) (ks : Fin q → ℕ), M ≤ capacity n →
      tupleMoment n M q ks = tupleFormula n M q ks := by
  intro n M q ks hM
  by_cases hguard : (∀ i, 0 < ks i) ∧
      (∑ i, ks i) ≤ n ∧ (∑ i, ks i) ≤ M + q
  · by_cases hq0 : q = 0
    · subst q
      exact tuple_identity_zero n M ks hM
    · by_cases hq1 : q = 1
      · subst q
        apply tuple_identity_one hCayley n M ks hM
        · exact hguard.1 0
        · simpa only [Fin.sum_univ_one] using! hguard.2.1
        · simpa only [Fin.sum_univ_one] using! hguard.2.2
      · exact tuple_identity_of_marked_count hM hguard
          (tupleMarked_count_of_enumeration_equiv hCayley hguard
            (h n M q ks (by omega) hguard).some)
  · exact tuple_identity_of_guard_failure n M q ks hguard

/-- The strongest current finite-law export: normalization, the conditional
law, growth averaging, cut avoidance, its exponential bound, and the exact
component identity are discharged here. -/
theorem result (hCayley : CayleyBridge) :
    FiniteCoreStatement := by
  have htuple := tuple_identity_of_residual finiteResidual hCayley
  exact ⟨normalization, conditional_hypergeom, growth_averaging,
    fun n G query t hGt hGQ =>
      ⟨grow_avoid_exact n G query t hGt hGQ,
        grow_avoid_bound n G query t hGt hGQ⟩,
    component_identity, htuple, factorial_moment_of_tuple_formula htuple⟩

end

end Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Finite
