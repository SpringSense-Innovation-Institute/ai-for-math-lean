module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W01_FiniteCore
public import Mathlib.GroupTheory.Perm.Centralizer

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


namespace Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Pruefer

open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Trees
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The endpoint-safe generalized Prüfer code in the non-full-root branch. -/
abbrev Code (k : ℕ) (roots : Finset (Fin k)) :=
  (↥roots) × (Fin (k - roots.card - 1) → Fin k)

/-- The actual finite subtype counted by `rootedForestCount`. -/
abbrev RootedForest (k : ℕ) (roots : Finset (Fin k)) :=
  {G : Graph k // ∀ S ∈ components G,
    isTree G S ∧ (S ∩ roots).card = 1}

lemma card_code (k : ℕ) (roots : Finset (Fin k)) :
    Fintype.card (Code k roots) = roots.card * k ^ (k - roots.card - 1) := by
  simp [Code]

lemma card_rootedForest (k : ℕ) (roots : Finset (Fin k)) :
    Fintype.card (RootedForest k roots) = rootedForestCount k roots := by
  rw [Fintype.card_subtype]
  simp [RootedForest, rootedForestCount, allGraphs]

/-- Once the explicit generalized Prüfer equivalence is supplied, the exact
canonical count follows without any cast or endpoint approximation. -/
lemma count_of_equiv {k : ℕ} {roots : Finset (Fin k)}
    (e : RootedForest k roots ≃ Code k roots) :
    rootedForestCount k roots = roots.card * k ^ (k - roots.card - 1) := by
  rw [← card_rootedForest, Fintype.card_congr e, card_code]

lemma zero_roots_eq_empty (roots : Finset (Fin 0)) : roots = ∅ := by
  ext x
  exact Fin.elim0 x

lemma endpoint_reduction
    (hproper : ∀ (k : ℕ) (roots : Finset (Fin k)),
      roots.card ≠ k → roots ≠ ∅ →
      rootedForestCount k roots = roots.card * k ^ (k - roots.card - 1)) :
    RootedForestFormula := by
  intro k roots
  by_cases hfull : roots.card = k
  · rw [if_pos hfull]
    exact rootedForestCount_full k roots hfull
  · rw [if_neg hfull]
    by_cases hk : k = 0
    · subst k
      have hr : roots = ∅ := zero_roots_eq_empty roots
      subst roots
      exact False.elim (hfull (by simp))
    · by_cases hempty : roots = ∅
      · subst roots
        simpa using! rootedForestCount_empty (Nat.pos_of_ne_zero hk)
      · exact hproper k roots hfull hempty

end Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Pruefer


namespace Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Pruefer

open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Trees
open scoped BigOperators

attribute [local instance] Classical.propDecidable

def edgeOf {k : ℕ} (u v : Fin k) (h : u ≠ v) : Edge k :=
  if huv : u < v then ⟨(u, v), huv⟩
  else ⟨(v, u), lt_of_le_of_ne (le_of_not_gt huv) h.symm⟩

@[simp] lemma edgeOf_endpoints {k : ℕ} (u v : Fin k) (h : u ≠ v) :
    (((edgeOf u v h).val.1 = u ∧ (edgeOf u v h).val.2 = v) ∨
      ((edgeOf u v h).val.1 = v ∧ (edgeOf u v h).val.2 = u)) := by
  unfold edgeOf
  split <;> simp

lemma adj_singleton_edgeOf {k : ℕ} (u v : Fin k) (h : u ≠ v) :
    adj ({edgeOf u v h} : Graph k) u v := by
  exact ⟨edgeOf u v h, by simp, edgeOf_endpoints u v h⟩

def available {k : ℕ} (roots : Finset (Fin k)) (code : List (Fin k)) : Finset (Fin k) :=
  Finset.univ \ (roots ∪ code.toFinset)

def Anchored {k : ℕ} (roots : Finset (Fin k)) (code : List (Fin k)) : Prop :=
  ∃ pre r, r ∈ roots ∧ code = pre ++ [r]

lemma anchored_ne_nil {k : ℕ} {roots : Finset (Fin k)} {code : List (Fin k)}
    (h : Anchored roots code) : code ≠ [] := by
  rintro rfl
  rcases h with ⟨pre, r, -, hp⟩
  simpa using! hp

lemma anchored_tail {k : ℕ} {roots : Finset (Fin k)} {a : Fin k} {code : List (Fin k)}
    (h : Anchored roots (a :: code)) (hne : code ≠ []) : Anchored roots code := by
  rcases h with ⟨pre, r, hr, hp⟩
  cases pre with
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at hp
      exact False.elim (hne hp.2)
  | cons b pre =>
      simp only [List.cons_append, List.cons.injEq] at hp
      exact ⟨pre, r, hr, hp.2⟩

lemma anchored_mono {k : ℕ} {roots roots' : Finset (Fin k)} {code : List (Fin k)}
    (h : Anchored roots code) (hsub : roots ⊆ roots') : Anchored roots' code := by
  rcases h with ⟨pre, r, hr, hcode⟩
  exact ⟨pre, r, hsub hr, hcode⟩

lemma card_nonroots {k : ℕ} (roots : Finset (Fin k)) :
    (Finset.univ \ roots).card = k - roots.card := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ roots)]
  simp

lemma available_nonempty {k : ℕ} {roots : Finset (Fin k)} {code : List (Fin k)}
    (hcard : roots.card + code.length = k) (hanchor : Anchored roots code) :
    (available roots code).Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have hsubset : Finset.univ \ roots ⊆ code.toFinset := by
    intro v hv
    have hvu : v ∈ (Finset.univ : Finset (Fin k)) := by simp
    have hvnot : v ∉ roots := (Finset.mem_sdiff.mp hv).2
    have : v ∉ available roots code := by simp [hempty]
    simpa [available, hvu, hvnot] using! this
  rcases hanchor with ⟨pre, r, hr, rfl⟩
  have hrlist : r ∈ (pre ++ [r]).toFinset := by simp
  have hrnon : r ∉ Finset.univ \ roots := by simp [hr]
  have hstrict : Finset.univ \ roots ⊂ (pre ++ [r]).toFinset :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, by
      intro heq
      exact hrnon (heq ▸ hrlist)⟩
  have hlt := Finset.card_lt_card hstrict
  have hcodecard : (pre ++ [r]).toFinset.card ≤ (pre ++ [r]).length :=
    List.toFinset_card_le _
  rw [card_nonroots] at hlt
  omega

noncomputable def pick {k : ℕ} (roots : Finset (Fin k)) (code : List (Fin k))
    (hcard : roots.card + code.length = k) (hanchor : Anchored roots code) : Fin k :=
  (available roots code).min' (available_nonempty hcard hanchor)

lemma pick_mem_available {k : ℕ} {roots : Finset (Fin k)} {code : List (Fin k)}
    (hcard : roots.card + code.length = k) (hanchor : Anchored roots code) :
    pick roots code hcard hanchor ∈ available roots code := by
  rw [pick]
  exact Finset.min'_mem _ _

lemma pick_not_mem_roots {k : ℕ} {roots : Finset (Fin k)} {code : List (Fin k)}
    (hcard : roots.card + code.length = k) (hanchor : Anchored roots code) :
    pick roots code hcard hanchor ∉ roots := by
  have h := pick_mem_available hcard hanchor
  have h' : pick roots code hcard hanchor ∉ roots ∧
      pick roots code hcard hanchor ∉ code.toFinset := by
    simpa only [available, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_union, not_or] using! h
  exact h'.1

lemma pick_not_mem_code {k : ℕ} {roots : Finset (Fin k)} {code : List (Fin k)}
    (hcard : roots.card + code.length = k) (hanchor : Anchored roots code) :
    pick roots code hcard hanchor ∉ code := by
  have h := pick_mem_available hcard hanchor
  have h' : pick roots code hcard hanchor ∉ roots ∧
      pick roots code hcard hanchor ∉ code.toFinset := by
    simpa only [available, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_union, not_or] using! h
  simpa using! h'.2

lemma card_insert_pick {k : ℕ} {roots : Finset (Fin k)} {a : Fin k}
    {code : List (Fin k)}
    (hcard : roots.card + (a :: code).length = k)
    (hanchor : Anchored roots (a :: code)) :
    (insert (pick roots (a :: code) hcard hanchor) roots).card + code.length = k := by
  rw [Finset.card_insert_of_notMem (pick_not_mem_roots hcard hanchor)]
  simp only [List.length_cons] at hcard
  omega

noncomputable def orderAux {k : ℕ} (roots : Finset (Fin k)) (code : List (Fin k))
    (hcard : roots.card + code.length = k) (hanchor : Anchored roots code) :
    List (Fin k) :=
  match code with
  | [] => False.elim (anchored_ne_nil hanchor rfl)
  | a :: tail =>
      let v := pick roots (a :: tail) hcard hanchor
      if ht : tail = [] then [v]
      else
        v :: orderAux (insert v roots) tail
          (card_insert_pick hcard hanchor)
          (anchored_mono (anchored_tail (roots := roots) hanchor ht)
            (Finset.subset_insert v roots))
termination_by code.length

lemma orderAux_length {k : ℕ} (roots : Finset (Fin k)) (code : List (Fin k))
    (hcard : roots.card + code.length = k) (hanchor : Anchored roots code) :
    (orderAux roots code hcard hanchor).length = code.length := by
  induction code generalizing roots with
  | nil => exact False.elim (anchored_ne_nil hanchor rfl)
  | cons a tail ih =>
      rw [orderAux]
      split_ifs with ht
      · subst tail
        simp
      · simp only [List.length_cons]
        rw [ih]

lemma orderAux_forall_not_mem {k : ℕ} (roots : Finset (Fin k))
    (code : List (Fin k)) (hcard : roots.card + code.length = k)
    (hanchor : Anchored roots code) :
    ∀ v ∈ orderAux roots code hcard hanchor, v ∉ roots := by
  induction code generalizing roots with
  | nil => exact False.elim (anchored_ne_nil hanchor rfl)
  | cons a tail ih =>
      rw [orderAux]
      split_ifs with ht
      · subst tail
        simp only [List.mem_singleton, forall_eq]
        exact pick_not_mem_roots hcard hanchor
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact pick_not_mem_roots hcard hanchor
        · exact fun hxr =>
            ih (insert (pick roots (a :: tail) hcard hanchor) roots)
              (card_insert_pick hcard hanchor)
              (anchored_mono (anchored_tail (roots := roots) hanchor ht)
                (Finset.subset_insert _ _)) _ hx (Finset.mem_insert_of_mem hxr)

lemma orderAux_nodup {k : ℕ} (roots : Finset (Fin k)) (code : List (Fin k))
    (hcard : roots.card + code.length = k) (hanchor : Anchored roots code) :
    (orderAux roots code hcard hanchor).Nodup := by
  induction code generalizing roots with
  | nil => exact False.elim (anchored_ne_nil hanchor rfl)
  | cons a tail ih =>
      rw [orderAux]
      split_ifs with ht
      · simp
      · apply List.nodup_cons.mpr
        constructor
        · intro hmem
          exact orderAux_forall_not_mem
            (insert (pick roots (a :: tail) hcard hanchor) roots) tail
            (card_insert_pick hcard hanchor)
            (anchored_mono (anchored_tail (roots := roots) hanchor ht)
              (Finset.subset_insert _ _)) _ hmem (by simp)
        · exact ih
            (insert (pick roots (a :: tail) hcard hanchor) roots)
            (card_insert_pick hcard hanchor)
            (anchored_mono (anchored_tail (roots := roots) hanchor ht)
              (Finset.subset_insert _ _))

lemma orderAux_toFinset {k : ℕ} (roots : Finset (Fin k)) (code : List (Fin k))
    (hcard : roots.card + code.length = k) (hanchor : Anchored roots code) :
    (orderAux roots code hcard hanchor).toFinset = Finset.univ \ roots := by
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    rw [List.mem_toFinset] at hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ v,
      orderAux_forall_not_mem roots code hcard hanchor v hv⟩
  · rw [card_nonroots, List.toFinset_card_of_nodup
      (orderAux_nodup roots code hcard hanchor), orderAux_length]
    omega

noncomputable def decodeAux {k : ℕ} (roots : Finset (Fin k)) (code : List (Fin k))
    (hcard : roots.card + code.length = k) (hanchor : Anchored roots code) : Graph k :=
  match code with
  | [] => False.elim (anchored_ne_nil hanchor rfl)
  | a :: tail =>
      let v := pick roots (a :: tail) hcard hanchor
      let hva : v ≠ a := fun h =>
        pick_not_mem_code hcard hanchor (by simpa [v, h])
      let e := edgeOf v a hva
      if ht : tail = [] then {e}
      else
        insert e (decodeAux (insert v roots) tail
          (card_insert_pick hcard hanchor)
          (anchored_mono (anchored_tail (roots := roots) hanchor ht)
            (Finset.subset_insert v roots)))
termination_by code.length

lemma decodeAux_eq_singleton {k : ℕ} {roots : Finset (Fin k)} {a : Fin k}
    (hcard : roots.card + [a].length = k) (hanchor : Anchored roots [a]) :
    decodeAux roots [a] hcard hanchor =
      {edgeOf (pick roots [a] hcard hanchor) a
        (fun h => pick_not_mem_code hcard hanchor (by simpa [h]))} := by
  rw [decodeAux]
  rfl

lemma decodeAux_cons {k : ℕ} {roots : Finset (Fin k)} {a : Fin k}
    {tail : List (Fin k)} (hcard : roots.card + (a :: tail).length = k)
    (hanchor : Anchored roots (a :: tail)) (ht : tail ≠ []) :
    decodeAux roots (a :: tail) hcard hanchor =
      insert
        (edgeOf (pick roots (a :: tail) hcard hanchor) a
          (fun h => pick_not_mem_code hcard hanchor (by simpa [h])))
        (decodeAux
          (insert (pick roots (a :: tail) hcard hanchor) roots) tail
          (card_insert_pick hcard hanchor)
          (anchored_mono (anchored_tail (roots := roots) hanchor ht)
            (Finset.subset_insert _ _))) := by
  rw [decodeAux]
  simp only [ht, ↓reduceDIte]

abbrev PrueferCode (k : ℕ) (roots : Finset (Fin k)) :=
  (↥roots) × (Fin (k - roots.card - 1) → Fin k)

def codeList {k : ℕ} {roots : Finset (Fin k)}
    (code : PrueferCode k roots) : List (Fin k) :=
  List.ofFn code.2 ++ [(code.1 : Fin k)]

lemma codeList_length {k : ℕ} {roots : Finset (Fin k)}
    (hproper : roots.card < k) (code : PrueferCode k roots) :
    (codeList code).length = k - roots.card := by
  simp only [codeList, List.length_append, List.length_ofFn, Fintype.card_fin,
    List.length_singleton]
  omega

lemma codeList_anchored {k : ℕ} {roots : Finset (Fin k)}
    (code : PrueferCode k roots) : Anchored roots (codeList code) := by
  exact ⟨List.ofFn code.2, code.1, code.1.property, rfl⟩

lemma codeList_card {k : ℕ} {roots : Finset (Fin k)}
    (hproper : roots.card < k) (code : PrueferCode k roots) :
    roots.card + (codeList code).length = k := by
  rw [codeList_length hproper]
  omega

noncomputable def decodeGraph {k : ℕ} {roots : Finset (Fin k)}
    (hproper : roots.card < k) (code : PrueferCode k roots) : Graph k :=
  decodeAux roots (codeList code) (codeList_card hproper code) (codeList_anchored code)

def Incident {k : ℕ} (x : Fin k) (e : Edge k) : Prop :=
  e.val.1 = x ∨ e.val.2 = x

lemma incident_edgeOf_iff {k : ℕ} (x u v : Fin k) (h : u ≠ v) :
    Incident x (edgeOf u v h) ↔ x = u ∨ x = v := by
  unfold Incident edgeOf
  split <;> simp only [Subtype.mk.injEq] <;> aesop

lemma decodeAux_no_incident {k : ℕ} (roots : Finset (Fin k))
    (code : List (Fin k)) (hcard : roots.card + code.length = k)
    (hanchor : Anchored roots code) {x : Fin k} (hxroot : x ∈ roots)
    (hxcode : x ∉ code) :
    ∀ e ∈ decodeAux roots code hcard hanchor, ¬ Incident x e := by
  induction code generalizing roots with
  | nil => exact False.elim (anchored_ne_nil hanchor rfl)
  | cons a tail ih =>
      rw [decodeAux]
      split_ifs with ht
      · intro e he
        simp only [Finset.mem_singleton] at he
        subst e
        rw [incident_edgeOf_iff]
        push_neg
        constructor
        · intro hxv
          exact pick_not_mem_roots hcard hanchor (hxv ▸ hxroot)
        · intro hxa
          exact hxcode (by simp [hxa])
      · intro e he
        simp only [Finset.mem_insert] at he
        rcases he with rfl | he
        · rw [incident_edgeOf_iff]
          push_neg
          constructor
          · intro hxv
            exact pick_not_mem_roots hcard hanchor (hxv ▸ hxroot)
          · intro hxa
            exact hxcode (by simp [hxa])
        · exact ih
            (insert (pick roots (a :: tail) hcard hanchor) roots)
            (card_insert_pick hcard hanchor)
            (anchored_mono (anchored_tail (roots := roots) hanchor ht)
              (Finset.subset_insert _ _))
            (Finset.mem_insert_of_mem hxroot) (fun hxt => hxcode (by simp [hxt])) e he

lemma decodeAux_card {k : ℕ} (roots : Finset (Fin k)) (code : List (Fin k))
    (hcard : roots.card + code.length = k) (hanchor : Anchored roots code) :
    (decodeAux roots code hcard hanchor).card = code.length := by
  induction code generalizing roots with
  | nil => exact False.elim (anchored_ne_nil hanchor rfl)
  | cons a tail ih =>
      rw [decodeAux]
      split_ifs with ht
      · subst tail
        simp
      · rw [Finset.card_insert_of_notMem]
        · simp only [List.length_cons]
          rw [ih]
        · intro he
          let v := pick roots (a :: tail) hcard hanchor
          let hva : v ≠ a := fun h =>
            pick_not_mem_code hcard hanchor (by simpa [v, h])
          have havoid := decodeAux_no_incident
            (insert v roots) tail (card_insert_pick hcard hanchor)
            (anchored_mono (anchored_tail (roots := roots) hanchor ht)
              (Finset.subset_insert _ _))
            (x := v) (by simp)
            (fun hvt => pick_not_mem_code hcard hanchor (List.mem_cons_of_mem a hvt))
            (edgeOf v a hva) he
          exact havoid ((incident_edgeOf_iff v v a hva).2 (Or.inl rfl))

lemma simpleGraph_insert_edgeOf {k : ℕ} (H : Graph k) (u v : Fin k) (h : u ≠ v) :
    W01_ENUM_Trees.simpleGraph (insert (edgeOf u v h) H) =
      W01_ENUM_Trees.simpleGraph H ⊔ SimpleGraph.edge u v := by
  ext x y
  simp only [SimpleGraph.sup_adj, W01_ENUM_Trees.simpleGraph_adj, adj,
    Finset.mem_insert, SimpleGraph.edge_adj]
  constructor
  · rintro ⟨e, he | he, hep⟩
    · subst e
      right
      unfold edgeOf at hep
      split at hep <;> aesop
    · exact Or.inl ⟨e, he, hep⟩
  · rintro (hxy | hxy)
    · rcases hxy with ⟨e, he, hep⟩
      exact ⟨e, Or.inr he, hep⟩
    · rcases hxy with hxy | hxy
      · exact ⟨edgeOf u v h, Or.inl rfl, by
          unfold edgeOf
          split <;> aesop⟩
      · exact ⟨edgeOf u v h, Or.inl rfl, by
          unfold edgeOf
          split <;> aesop⟩

lemma reach_eq_of_no_incident {k : ℕ} {H : Graph k} {v w : Fin k}
    (hiso : ∀ e ∈ H, ¬ Incident v e) (hreach : reach H v w) : v = w := by
  induction hreach with
  | refl => rfl
  | tail h hAdj ih =>
      subst ih
      rcases hAdj with ⟨e, he, hep | hep⟩
      · exact False.elim (hiso e he (Or.inl hep.1))
      · exact False.elim (hiso e he (Or.inr hep.2))

lemma bot_isAcyclic {V : Type} : (⊥ : SimpleGraph V).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_edge_isBridge]
  simp

lemma edge_isAcyclic {V : Type} (u v : V) (h : u ≠ v) :
    (SimpleGraph.edge u v).IsAcyclic := by
  rw [show SimpleGraph.edge u v = (⊥ : SimpleGraph V) ⊔ SimpleGraph.edge u v by simp]
  exact (SimpleGraph.isAcyclic_add_edge_iff_of_not_reachable u v (by simpa using! h)).2
    bot_isAcyclic

lemma decodeAux_isAcyclic {k : ℕ} (roots : Finset (Fin k)) (code : List (Fin k))
    (hcard : roots.card + code.length = k) (hanchor : Anchored roots code) :
    (W01_ENUM_Trees.simpleGraph (decodeAux roots code hcard hanchor)).IsAcyclic := by
  induction code generalizing roots with
  | nil => exact False.elim (anchored_ne_nil hanchor rfl)
  | cons a tail ih =>
      rw [decodeAux]
      split_ifs with ht
      · have hempty : W01_ENUM_Trees.simpleGraph (∅ : Graph k) = ⊥ := by
          ext x y
          simp [W01_ENUM_Trees.simpleGraph_adj, adj]
        rw [show ({edgeOf (pick roots (a :: tail) hcard hanchor) a _} : Graph k) =
          insert (edgeOf (pick roots (a :: tail) hcard hanchor) a _) ∅ by rfl,
          simpleGraph_insert_edgeOf, hempty]
        simpa using! edge_isAcyclic
          (pick roots (a :: tail) hcard hanchor) a
          (fun h => pick_not_mem_code hcard hanchor (by simpa [h]))
      · let v := pick roots (a :: tail) hcard hanchor
        let hva : v ≠ a := fun h =>
          pick_not_mem_code hcard hanchor (by simpa [v, h])
        let roots' := insert v roots
        let hcard' := card_insert_pick hcard hanchor
        let hanchor' := anchored_mono (anchored_tail (roots := roots) hanchor ht)
          (Finset.subset_insert v roots)
        have hiso : ∀ e ∈ decodeAux roots' tail hcard' hanchor', ¬ Incident v e :=
          decodeAux_no_incident roots' tail hcard' hanchor' (by simp [roots'])
            (fun hvt => pick_not_mem_code hcard hanchor (List.mem_cons_of_mem a hvt))
        have hnreach : ¬ reach (decodeAux roots' tail hcard' hanchor') v a := by
          intro hreach
          exact hva (reach_eq_of_no_incident hiso hreach)
        rw [simpleGraph_insert_edgeOf]
        apply (SimpleGraph.isAcyclic_add_edge_iff_of_not_reachable v a ?_).2
        · exact ih roots' hcard' hanchor'
        · rwa [W01_ENUM_Trees.simpleGraph_reachable_iff]

def edgeSym2 {k : ℕ} (e : Edge k) : Sym2 (Fin k) :=
  s(e.val.1, e.val.2)

lemma edgeSym2_injective {k : ℕ} :
    Function.Injective (@edgeSym2 k) := by
  intro e f hef
  apply Subtype.ext
  apply Prod.ext
  · rcases Sym2.eq_iff.mp hef with h | h
    · exact h.1
    · have hfe : f.val.2 < f.val.1 := by
        simpa [h.1, h.2] using! e.property
      exact False.elim ((lt_asymm f.property hfe))
  · rcases Sym2.eq_iff.mp hef with h | h
    · exact h.2
    · have hfe : f.val.2 < f.val.1 := by
        simpa [h.1, h.2] using! e.property
      exact False.elim ((lt_asymm f.property hfe))

lemma simpleGraph_edgeFinset_card {k : ℕ} (G : Graph k) :
    (W01_ENUM_Trees.simpleGraph G).edgeFinset.card = G.card := by
  symm
  apply Finset.card_bij (fun e _ => edgeSym2 e)
  · intro e he
    rw [SimpleGraph.mem_edgeFinset]
    change s(e.val.1, e.val.2) ∈ (W01_ENUM_Trees.simpleGraph G).edgeSet
    rw [SimpleGraph.mem_edgeSet]
    exact ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
  · intro e₁ _ e₂ _ h
    exact edgeSym2_injective h
  · intro b hb
    induction b using Sym2.inductionOn with
    | _ u v =>
        have hadj : adj G u v := by
          rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hb
          exact hb
        rcases hadj with ⟨e, he, hends⟩
        refine ⟨e, he, ?_⟩
        unfold edgeSym2
        rcases hends with h | h
        · rw [h.1, h.2]
        · rw [h.1, h.2]
          exact Sym2.eq_swap

lemma component_isTree_of_acyclic {k : ℕ} {G : Graph k}
    (hacyclic : (W01_ENUM_Trees.simpleGraph G).IsAcyclic) :
    ∀ S ∈ components G, isTree G S := by
  intro S hS
  refine ⟨hS, ?_⟩
  simp only [components, Finset.mem_image] at hS
  rcases hS with ⟨r, -, rfl⟩
  let c := (W01_ENUM_Trees.simpleGraph G).connectedComponentMk r
  have hc (x : Fin k) :
      x ∈ c.supp ↔ x ∈ componentOf G r := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff,
      SimpleGraph.ConnectedComponent.eq,
      W01_ENUM_Trees.simpleGraph_reachable_iff,
      W01_ENUM_Trees.mem_componentOf_iff]
    exact ⟨W01_ENUM_Trees.reach_symm, W01_ENUM_Trees.reach_symm⟩
  let inside : Graph k :=
    G.filter (fun e => e.val.1 ∈ componentOf G r ∧
      e.val.2 ∈ componentOf G r)
  have hedgecard :
      inside.card = c.toSimpleGraph.edgeFinset.card := by
    apply Finset.card_bij
      (fun e he =>
        s(⟨e.val.1, hc e.val.1 |>.mpr (Finset.mem_filter.mp he).2.1⟩,
          ⟨e.val.2, hc e.val.2 |>.mpr (Finset.mem_filter.mp he).2.2⟩))
    · intro e he
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        SimpleGraph.ConnectedComponent.toSimpleGraph_adj,
        W01_ENUM_Trees.simpleGraph_adj]
      exact ⟨e, (Finset.mem_filter.mp he).1, Or.inl ⟨rfl, rfl⟩⟩
    · intro e₁ he₁ e₂ he₂ h
      apply Subtype.ext
      apply Prod.ext
      · rcases Sym2.eq_iff.mp h with h | h
        · exact congrArg Subtype.val h.1
        · have hlt : e₂.val.2 < e₂.val.1 := by
            calc
              e₂.val.2 = e₁.val.1 := (congrArg Subtype.val h.1).symm
              _ < e₁.val.2 := e₁.property
              _ = e₂.val.1 := congrArg Subtype.val h.2
          exact False.elim (lt_asymm e₂.property hlt)
      · rcases Sym2.eq_iff.mp h with h | h
        · exact congrArg Subtype.val h.2
        · have hlt : e₂.val.2 < e₂.val.1 := by
            calc
              e₂.val.2 = e₁.val.1 := (congrArg Subtype.val h.1).symm
              _ < e₁.val.2 := e₁.property
              _ = e₂.val.1 := congrArg Subtype.val h.2
          exact False.elim (lt_asymm e₂.property hlt)
    · intro b hb
      induction b using Sym2.inductionOn with
      | _ u v =>
          have hadjS : (W01_ENUM_Trees.simpleGraph G).Adj u.val v.val := by
            rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hb
            exact (SimpleGraph.ConnectedComponent.toSimpleGraph_adj c u.property
              v.property).mp hb
          have hadj : adj G u.val v.val := hadjS
          rcases hadj with ⟨e, he, hends⟩
          have hins : e ∈ inside := by
            apply Finset.mem_filter.mpr
            refine ⟨he, ?_⟩
            rcases hends with h | h
            · exact ⟨hc e.val.1 |>.mp (h.1.symm ▸ u.property),
                hc e.val.2 |>.mp (h.2.symm ▸ v.property)⟩
            · exact ⟨hc e.val.1 |>.mp (h.1.symm ▸ v.property),
                hc e.val.2 |>.mp (h.2.symm ▸ u.property)⟩
          refine ⟨e, hins, ?_⟩
          rcases hends with h | h
          · apply Sym2.eq_iff.mpr
            exact Or.inl ⟨Subtype.ext h.1, Subtype.ext h.2⟩
          · apply Sym2.eq_iff.mpr
            exact Or.inr ⟨Subtype.ext h.1, Subtype.ext h.2⟩
  have hcardc : Fintype.card c = (componentOf G r).card := by
    calc
      Fintype.card c = Fintype.card ↥(componentOf G r) :=
        Fintype.card_congr
          { toFun := fun x => ⟨x.val, (hc x.val).mp x.property⟩
            invFun := fun x => ⟨x.val, (hc x.val).mpr x.property⟩
            left_inv := fun x => Subtype.ext rfl
            right_inv := fun x => Subtype.ext rfl }
      _ = (componentOf G r).card := Fintype.card_coe _
  have htree := (hacyclic.isTree_connectedComponent c).card_edgeFinset
  rw [← hedgecard, hcardc] at htree
  exact htree

private lemma reach_mono {k : ℕ} {G H : Graph k} {u v : Fin k}
    (hGH : G ⊆ H) (hreach : reach G u v) : reach H u v := by
  induction hreach with
  | refl => exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      apply ih.tail
      rcases hyz with ⟨e, he, hends⟩
      exact ⟨e, hGH he, hends⟩

private lemma anchored_singleton_root {k : ℕ} {roots : Finset (Fin k)}
    {a : Fin k} (hanchor : Anchored roots [a]) : a ∈ roots := by
  rcases hanchor with ⟨pre, r, hr, hcode⟩
  cases pre with
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at hcode
      simpa [hcode.1] using! hr
  | cons b pre =>
      have hlen := congrArg List.length hcode
      simp only [List.length_cons, List.length_append, List.length_singleton] at hlen
      omega

lemma decodeAux_reaches_root {k : ℕ} (roots : Finset (Fin k))
    (code : List (Fin k)) (hcard : roots.card + code.length = k)
    (hanchor : Anchored roots code) :
    ∀ x : Fin k, ∃ r ∈ roots, reach (decodeAux roots code hcard hanchor) x r := by
  induction code generalizing roots with
  | nil => exact False.elim (anchored_ne_nil hanchor rfl)
  | cons a tail ih =>
      by_cases ht : tail = []
      · subst tail
        intro x
        have ha : a ∈ roots := anchored_singleton_root hanchor
        by_cases hx : x ∈ roots
        · exact ⟨x, hx, W01_ENUM_Trees.reach_refl x⟩
        · let v := pick roots [a] hcard hanchor
          have hxsdiff : x ∈ (Finset.univ : Finset (Fin k)) \ roots :=
            Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
          have hxorder :
              x ∈ (orderAux roots [a] hcard hanchor).toFinset := by
            rw [orderAux_toFinset]
            exact hxsdiff
          have hxv : x = v := by
            rw [orderAux] at hxorder
            simpa only [dif_pos, List.mem_toFinset, List.mem_singleton] using! hxorder
          subst x
          refine ⟨a, ha, ?_⟩
          rw [decodeAux_eq_singleton]
          exact W01_ENUM_Trees.reach_of_adj
            (adj_singleton_edgeOf v a
              (fun h => pick_not_mem_code hcard hanchor (by simpa [v, h])))
      · intro x
        let v := pick roots (a :: tail) hcard hanchor
        let hva : v ≠ a := fun h =>
          pick_not_mem_code hcard hanchor (by simpa [v, h])
        let roots' := insert v roots
        let hcard' := card_insert_pick hcard hanchor
        let hanchor' := anchored_mono (anchored_tail (roots := roots) hanchor ht)
          (Finset.subset_insert v roots)
        let H := decodeAux roots' tail hcard' hanchor'
        have hiso : ∀ e ∈ H, ¬ Incident v e :=
          decodeAux_no_incident roots' tail hcard' hanchor' (by simp [roots'])
            (fun hvt => pick_not_mem_code hcard hanchor (List.mem_cons_of_mem a hvt))
        have hHsub :
            H ⊆ decodeAux roots (a :: tail) hcard hanchor := by
          rw [decodeAux_cons hcard hanchor ht]
          exact Finset.subset_insert _ _
        rcases ih roots' hcard' hanchor' x with ⟨r, hr, hxr⟩
        rcases Finset.mem_insert.mp hr with rfl | hr
        · have hxv : x = v :=
            (reach_eq_of_no_incident hiso (W01_ENUM_Trees.reach_symm hxr)).symm
          subst x
          rcases ih roots' hcard' hanchor' a with ⟨s, hs, has⟩
          have hsv : s ≠ v := by
            intro hsv
            subst s
            have hav : v = a :=
              reach_eq_of_no_incident hiso (W01_ENUM_Trees.reach_symm has)
            exact hva hav
          have hsroot : s ∈ roots := by
            rcases Finset.mem_insert.mp hs with h | h
            · exact False.elim (hsv h)
            · exact h
          refine ⟨s, hsroot, ?_⟩
          have hva_full :
              reach (decodeAux roots (a :: tail) hcard hanchor) v a := by
            apply W01_ENUM_Trees.reach_of_adj
            rw [decodeAux_cons hcard hanchor ht]
            refine ⟨edgeOf v a hva, ?_, edgeOf_endpoints v a hva⟩
            simpa [v] using!
              (Finset.mem_insert_self (edgeOf v a hva) H)
          exact hva_full.trans (reach_mono hHsub has)
        · exact ⟨r, hr, reach_mono hHsub hxr⟩

private lemma components_pairwiseDisjoint {k : ℕ} (G : Graph k) :
    ((components G : Finset (Finset (Fin k))) : Set (Finset (Fin k))).PairwiseDisjoint id := by
  intro S hS T hT hST
  have hSu : ∃ u : Fin k, componentOf G u = S := by
    simpa [components] using! hS
  have hTv : ∃ v : Fin k, componentOf G v = T := by
    simpa [components] using! hT
  obtain ⟨u, hu⟩ := hSu
  obtain ⟨v, hv⟩ := hTv
  apply Finset.disjoint_left.mpr
  intro x hxS hxT
  apply hST
  have hxu : x ∈ componentOf G u := by simpa [hu] using! hxS
  have hxv : x ∈ componentOf G v := by simpa [hv] using! hxT
  calc
    S = componentOf G u := hu.symm
    _ = componentOf G v := componentOf_eq_of_reach
      ((mem_componentOf_iff.mp hxu).trans
        (reach_symm (mem_componentOf_iff.mp hxv)))
    _ = T := hv

private lemma components_biUnion_eq_univ {k : ℕ} (G : Graph k) :
    (components G).biUnion id = (Finset.univ : Finset (Fin k)) := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
  exact ⟨componentOf G x, componentOf_mem_components G x,
    componentOf_self G x⟩

private def componentEdges {k : ℕ} (G : Graph k)
    (S : Finset (Fin k)) : Graph k :=
  G.filter (fun e => e.val.1 ∈ S ∧ e.val.2 ∈ S)

private lemma componentEdges_pairwiseDisjoint {k : ℕ} (G : Graph k) :
    ((components G : Finset (Finset (Fin k))) : Set (Finset (Fin k))).PairwiseDisjoint
      (componentEdges G) := by
  intro S hS T hT hST
  have hdis := components_pairwiseDisjoint G hS hT hST
  apply Finset.disjoint_left.mpr
  intro e heS heT
  exact Finset.disjoint_left.mp hdis
    (Finset.mem_filter.mp heS).2.1 (Finset.mem_filter.mp heT).2.1

private lemma componentEdges_biUnion_eq {k : ℕ} (G : Graph k) :
    (components G).biUnion (componentEdges G) = G := by
  ext e
  simp only [Finset.mem_biUnion, componentEdges, Finset.mem_filter]
  constructor
  · rintro ⟨S, -, he, -⟩
    exact he
  · intro he
    let S := componentOf G e.val.1
    have h1 : e.val.1 ∈ S := componentOf_self G e.val.1
    have hadj : adj G e.val.1 e.val.2 :=
      ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
    have h2 : e.val.2 ∈ S :=
      mem_componentOf_iff.mpr (reach_of_adj hadj)
    exact ⟨S, componentOf_mem_components G e.val.1, he, h1, h2⟩

private lemma sum_component_cards {k : ℕ} (G : Graph k) :
    ∑ S ∈ components G, S.card = k := by
  have h := congrArg Finset.card (components_biUnion_eq_univ G)
  rw [Finset.card_biUnion (components_pairwiseDisjoint G)] at h
  simpa using! h

private lemma sum_component_edges {k : ℕ} (G : Graph k) :
    ∑ S ∈ components G, edgesInside G S = G.card := by
  have h := congrArg Finset.card (componentEdges_biUnion_eq G)
  rw [Finset.card_biUnion (componentEdges_pairwiseDisjoint G)] at h
  simpa [componentEdges, edgesInside] using! h

lemma component_count_of_forest {k : ℕ} (G : Graph k)
    (htree : ∀ S ∈ components G, isTree G S) :
    G.card + (components G).card = k := by
  have hedges := sum_component_edges G
  have hverts := sum_component_cards G
  have hsum :
      ∑ S ∈ components G, (edgesInside G S + 1) =
        ∑ S ∈ components G, S.card := by
    apply Finset.sum_congr rfl
    intro S hS
    exact (htree S hS).2
  rw [Finset.sum_add_distrib] at hsum
  have hones : (∑ _S ∈ components G, (1 : ℕ)) =
      (components G).card := by simp
  rw [hones, hedges, hverts] at hsum
  exact hsum

private def componentRoots {k : ℕ} (roots S : Finset (Fin k)) :
    Finset (Fin k) :=
  S ∩ roots

private lemma componentRoots_pairwiseDisjoint {k : ℕ} (G : Graph k)
    (roots : Finset (Fin k)) :
    ((components G : Finset (Finset (Fin k))) : Set (Finset (Fin k))).PairwiseDisjoint
      (componentRoots roots) := by
  intro S hS T hT hST
  have hdis := components_pairwiseDisjoint G hS hT hST
  apply Finset.disjoint_left.mpr
  intro x hxS hxT
  exact Finset.disjoint_left.mp hdis
    (Finset.mem_inter.mp hxS).1 (Finset.mem_inter.mp hxT).1

private lemma componentRoots_biUnion_eq {k : ℕ} (G : Graph k)
    (roots : Finset (Fin k)) :
    (components G).biUnion (componentRoots roots) = roots := by
  ext r
  simp only [Finset.mem_biUnion, componentRoots, Finset.mem_inter]
  constructor
  · rintro ⟨S, -, -, hr⟩
    exact hr
  · intro hr
    exact ⟨componentOf G r, componentOf_mem_components G r,
      componentOf_self G r, hr⟩

lemma sum_component_root_cards {k : ℕ} (G : Graph k)
    (roots : Finset (Fin k)) :
    ∑ S ∈ components G, (S ∩ roots).card = roots.card := by
  have h := congrArg Finset.card (componentRoots_biUnion_eq G roots)
  rw [Finset.card_biUnion (componentRoots_pairwiseDisjoint G roots)] at h
  simpa [componentRoots] using! h

private lemma decodeGraph_card {k : ℕ} {roots : Finset (Fin k)}
    (hproper : roots.card < k) (code : PrueferCode k roots) :
    (decodeGraph hproper code).card = k - roots.card := by
  unfold decodeGraph
  rw [decodeAux_card, codeList_length hproper]

private lemma decodeGraph_component_count {k : ℕ}
    {roots : Finset (Fin k)} (hproper : roots.card < k)
    (code : PrueferCode k roots) :
    (components (decodeGraph hproper code)).card = roots.card := by
  have hforest := component_count_of_forest (decodeGraph hproper code)
    (component_isTree_of_acyclic
      (decodeAux_isAcyclic roots (codeList code)
        (codeList_card hproper code) (codeList_anchored code)))
  rw [decodeGraph_card hproper code] at hforest
  omega

private lemma decodeGraph_component_has_root {k : ℕ}
    {roots : Finset (Fin k)} (hproper : roots.card < k)
    (code : PrueferCode k roots) (S : Finset (Fin k))
    (hS : S ∈ components (decodeGraph hproper code)) :
    0 < (S ∩ roots).card := by
  simp only [components, Finset.mem_image] at hS
  rcases hS with ⟨x, -, rfl⟩
  rcases decodeAux_reaches_root roots (codeList code)
      (codeList_card hproper code) (codeList_anchored code) x with
    ⟨r, hr, hxr⟩
  apply Finset.card_pos.mpr
  exact ⟨r, Finset.mem_inter.mpr
    ⟨mem_componentOf_iff.mpr hxr, hr⟩⟩

private lemma decodeGraph_component_root_card {k : ℕ}
    {roots : Finset (Fin k)} (hproper : roots.card < k)
    (code : PrueferCode k roots) :
    ∀ S ∈ components (decodeGraph hproper code),
      (S ∩ roots).card = 1 := by
  let G := decodeGraph hproper code
  have hsum := sum_component_root_cards G roots
  have hcount : (components G).card = roots.card :=
    decodeGraph_component_count hproper code
  have hsplit :
      ∑ S ∈ components G, (S ∩ roots).card =
        (∑ S ∈ components G, ((S ∩ roots).card - 1)) +
          (components G).card := by
    calc
      ∑ S ∈ components G, (S ∩ roots).card =
          ∑ S ∈ components G, (((S ∩ roots).card - 1) + 1) := by
        apply Finset.sum_congr rfl
        intro S hS
        have hp := decodeGraph_component_has_root hproper code S hS
        omega
      _ = (∑ S ∈ components G, ((S ∩ roots).card - 1)) +
          ∑ _S ∈ components G, 1 := by
        rw [Finset.sum_add_distrib]
      _ = _ := by simp
  have hzero :
      ∑ S ∈ components G, ((S ∩ roots).card - 1) = 0 := by
    omega
  intro S hS
  have hz : (S ∩ roots).card - 1 = 0 :=
    (Finset.sum_eq_zero_iff.mp hzero) S hS
  have hp := decodeGraph_component_has_root hproper code S hS
  omega

theorem decodeGraph_rootedForest {k : ℕ} {roots : Finset (Fin k)}
    (hproper : roots.card < k) (code : PrueferCode k roots) :
    ∀ S ∈ components (decodeGraph hproper code),
      isTree (decodeGraph hproper code) S ∧ (S ∩ roots).card = 1 := by
  intro S hS
  exact ⟨component_isTree_of_acyclic
      (decodeAux_isAcyclic roots (codeList code)
        (codeList_card hproper code) (codeList_anchored code)) S hS,
    decodeGraph_component_root_card hproper code S hS⟩

noncomputable def decodeRootedForest {k : ℕ}
    {roots : Finset (Fin k)} (hproper : roots.card < k) :
    PrueferCode k roots → RootedForest k roots :=
  fun code => ⟨decodeGraph hproper code,
    decodeGraph_rootedForest hproper code⟩

def PrueferBijectionStatement : Prop :=
  ∀ (k : ℕ) (roots : Finset (Fin k)) (hproper : roots.card < k),
    roots ≠ ∅ → Function.Bijective (decodeRootedForest hproper)

theorem rootedForestFormula_of_prueferBijection
    (hbij : PrueferBijectionStatement) : RootedForestFormula := by
  apply endpoint_reduction
  intro k roots hfull hnonempty
  have hle : roots.card ≤ k := by
    simpa using! Finset.card_le_univ roots
  have hproper : roots.card < k := by omega
  exact count_of_equiv
    (Equiv.ofBijective (decodeRootedForest hproper)
      (hbij k roots hproper hnonempty)).symm

end Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Pruefer


namespace Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Pruefer

open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Trees

attribute [local instance] Classical.propDecidable

private lemma neighborFinset_insert_edgeOf {k : ℕ} (H : Graph k)
    (u v x : Fin k) (h : u ≠ v) :
    (simpleGraph (insert (edgeOf u v h) H)).neighborFinset x =
      (simpleGraph H).neighborFinset x ∪
        if x = u then {v} else if x = v then {u} else ∅ := by
  ext y
  simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset,
    simpleGraph_insert_edgeOf, SimpleGraph.sup_adj, SimpleGraph.edge_adj]
  aesop

private lemma not_mem_neighborFinset_of_no_incident {k : ℕ} {H : Graph k}
    {v x : Fin k} (hiso : ∀ e ∈ H, ¬ Incident v e) :
    v ∉ (simpleGraph H).neighborFinset x := by
  intro hv
  rw [SimpleGraph.mem_neighborFinset, simpleGraph_adj] at hv
  rcases hv with ⟨e, he, hends⟩
  apply hiso e he
  rcases hends with h | h
  · exact Or.inr h.2
  · exact Or.inl h.1

private lemma neighborFinset_eq_empty_of_no_incident {k : ℕ} {H : Graph k}
    {v : Fin k} (hiso : ∀ e ∈ H, ¬ Incident v e) :
    (simpleGraph H).neighborFinset v = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  rw [SimpleGraph.mem_neighborFinset, simpleGraph_adj] at hx
  rcases hx with ⟨e, he, hends⟩
  exact hiso e he (by
    rcases hends with h | h
    · exact Or.inl h.1
    · exact Or.inr h.2)

private lemma nonroot_eq_pick_of_singleton_code {k : ℕ}
    {roots : Finset (Fin k)} {a x : Fin k}
    (hcard : roots.card + [a].length = k)
    (hanchor : Anchored roots [a]) (hx : x ∉ roots) :
    x = pick roots [a] hcard hanchor := by
  have hx' : x ∈ (Finset.univ : Finset (Fin k)) \ roots :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
  have horder := orderAux_toFinset roots [a] hcard hanchor
  rw [← horder] at hx'
  rw [orderAux] at hx'
  simpa only [dif_pos, List.mem_toFinset, List.mem_singleton] using! hx'

private lemma singleton_anchor_mem {k : ℕ} {roots : Finset (Fin k)}
    {a : Fin k} (hanchor : Anchored roots [a]) : a ∈ roots := by
  rcases hanchor with ⟨pre, r, hr, hcode⟩
  cases pre with
  | nil =>
      simp only [List.nil_append, List.cons.injEq] at hcode
      simpa [hcode.1] using! hr
  | cons b pre =>
      have hlen := congrArg List.length hcode
      simp only [List.length_cons, List.length_append, List.length_singleton] at hlen
      omega

/-- Every nonroot contributes its one outgoing edge, while every occurrence in
the generalized Pruefer list contributes one incoming edge. -/
theorem decodeAux_degree {k : ℕ} (roots : Finset (Fin k))
    (code : List (Fin k)) (hcard : roots.card + code.length = k)
    (hanchor : Anchored roots code) (x : Fin k) :
    (simpleGraph (decodeAux roots code hcard hanchor)).degree x =
      code.count x + if x ∈ roots then 0 else 1 := by
  induction code generalizing roots with
  | nil => exact False.elim (anchored_ne_nil hanchor rfl)
  | cons a tail ih =>
      by_cases ht : tail = []
      · subst tail
        let v := pick roots [a] hcard hanchor
        have hva : v ≠ a := fun h =>
          pick_not_mem_code hcard hanchor (by simpa [v, h])
        have ha : a ∈ roots := singleton_anchor_mem hanchor
        rw [decodeAux_eq_singleton]
        rw [show ({edgeOf v a hva} : Graph k) =
          insert (edgeOf v a hva) ∅ by rfl]
        change ((simpleGraph (insert (edgeOf v a hva) ∅)).neighborFinset x).card = _
        rw [neighborFinset_insert_edgeOf]
        have hneigh : (simpleGraph (∅ : Graph k)).neighborFinset x = ∅ := by
          ext y
          simp [SimpleGraph.mem_neighborFinset, simpleGraph_adj, adj]
        by_cases hxv : x = v
        · subst x
          have hcount : [a].count v = 0 :=
            List.count_eq_zero.mpr (pick_not_mem_code hcard hanchor)
          rw [hneigh, hcount]
          simp [v, hva, pick_not_mem_roots hcard hanchor]
        · by_cases hxa : x = a
          · subst x
            rw [hneigh]
            simp [hxv, ha]
          · have hxroot : x ∈ roots := by
              by_contra hxroot
              exact hxv (nonroot_eq_pick_of_singleton_code hcard hanchor hxroot)
            rw [hneigh]
            simp [hxv, hxa, hxroot, List.count_cons, ne_comm]
      · let v := pick roots (a :: tail) hcard hanchor
        let hva : v ≠ a := fun h =>
          pick_not_mem_code hcard hanchor (by simpa [v, h])
        let roots' := insert v roots
        let hcard' := card_insert_pick hcard hanchor
        let hanchor' := anchored_mono (anchored_tail (roots := roots) hanchor ht)
          (Finset.subset_insert v roots)
        let H := decodeAux roots' tail hcard' hanchor'
        have hiso : ∀ e ∈ H, ¬ Incident v e :=
          decodeAux_no_incident roots' tail hcard' hanchor' (by simp [roots'])
            (fun hvt => pick_not_mem_code hcard hanchor
              (List.mem_cons_of_mem a hvt))
        rw [decodeAux_cons hcard hanchor ht]
        change ((simpleGraph (insert (edgeOf v a hva) H)).neighborFinset x).card = _
        rw [neighborFinset_insert_edgeOf]
        by_cases hxv : x = v
        · subst x
          have hempty : (simpleGraph H).neighborFinset v = ∅ :=
            neighborFinset_eq_empty_of_no_incident hiso
          have hcount : (a :: tail).count v = 0 :=
            List.count_eq_zero.mpr (pick_not_mem_code hcard hanchor)
          rw [hempty]
          rw [hcount]
          simp [v, hva, pick_not_mem_roots hcard hanchor]
        · by_cases hxa : x = a
          · subst x
            have hvnot : v ∉ (simpleGraph H).neighborFinset a :=
              not_mem_neighborFinset_of_no_incident hiso
            simp only [if_neg hxv, if_pos]
            rw [Finset.card_union_of_disjoint
              (Finset.disjoint_singleton_right.mpr hvnot)]
            simp only [Finset.card_singleton, List.count_cons,
              beq_self_eq_true, if_true]
            change (simpleGraph H).degree a + 1 = _
            rw [ih roots' hcard' hanchor']
            simp [roots', hxv]
            omega
          · have hroot : x ∈ roots' ↔ x ∈ roots := by
              simp [roots', hxv]
            have hcount : (a :: tail).count x = tail.count x := by
              rw [List.count_cons]
              simp [hxa, ne_comm]
            have hneighbors :
                (simpleGraph H).neighborFinset x ∪
                    (if x = v then {a} else if x = a then {v} else ∅) =
                  (simpleGraph H).neighborFinset x := by
              simp [hxv, hxa]
            rw [hneighbors]
            change (simpleGraph H).degree x = _
            rw [ih roots' hcard' hanchor', hcount]
            simp only [hroot]

lemma mem_available_iff_decodeAux_degree_one {k : ℕ}
    {roots : Finset (Fin k)} {code : List (Fin k)}
    (hcard : roots.card + code.length = k)
    (hanchor : Anchored roots code) (x : Fin k) :
    x ∈ available roots code ↔
      x ∉ roots ∧ (simpleGraph (decodeAux roots code hcard hanchor)).degree x = 1 := by
  rw [decodeAux_degree roots code hcard hanchor x]
  simp only [available, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_union, List.mem_toFinset, not_or]
  constructor
  · rintro ⟨hxroot, hxcode⟩
    refine ⟨hxroot, ?_⟩
    rw [if_neg hxroot, List.count_eq_zero.mpr hxcode]
  · rintro ⟨hxroot, hdeg⟩
    refine ⟨hxroot, ?_⟩
    rw [if_neg hxroot] at hdeg
    have : code.count x = 0 := by omega
    exact List.count_eq_zero.mp this

private lemma decodeAux_pick_adj_iff {k : ℕ} {roots : Finset (Fin k)}
    {a : Fin k} {tail : List (Fin k)}
    (hcard : roots.card + (a :: tail).length = k)
    (hanchor : Anchored roots (a :: tail)) (x : Fin k) :
    adj (decodeAux roots (a :: tail) hcard hanchor)
        (pick roots (a :: tail) hcard hanchor) x ↔ x = a := by
  let v := pick roots (a :: tail) hcard hanchor
  let hva : v ≠ a := fun h =>
    pick_not_mem_code hcard hanchor (by simpa [v, h])
  change adj (decodeAux roots (a :: tail) hcard hanchor) v x ↔ x = a
  by_cases ht : tail = []
  · subst tail
    rw [decodeAux_eq_singleton]
    change adj ({edgeOf v a hva} : Graph k) v x ↔ x = a
    constructor
    · rintro ⟨e, he, hends⟩
      simp only [Finset.mem_singleton] at he
      subst e
      rcases edgeOf_endpoints v a hva with hep | hep
      · rcases hends with hends | hends
        · exact hends.2.symm.trans hep.2
        · exact False.elim (hva (hends.2.symm.trans hep.2))
      · rcases hends with hends | hends
        · exact False.elim (hva (hends.1.symm.trans hep.1))
        · exact hends.1.symm.trans hep.1
    · intro hx
      subst x
      exact adj_singleton_edgeOf v a hva
  · let roots' := insert v roots
    let hcard' := card_insert_pick hcard hanchor
    let hanchor' := anchored_mono (anchored_tail (roots := roots) hanchor ht)
      (Finset.subset_insert v roots)
    let H := decodeAux roots' tail hcard' hanchor'
    have hiso : ∀ e ∈ H, ¬ Incident v e :=
      decodeAux_no_incident roots' tail hcard' hanchor' (by simp [roots'])
        (fun hvt => pick_not_mem_code hcard hanchor
          (List.mem_cons_of_mem a hvt))
    rw [decodeAux_cons hcard hanchor ht]
    change adj (insert (edgeOf v a hva) H) v x ↔ x = a
    constructor
    · rintro ⟨e, he, hends⟩
      simp only [Finset.mem_insert] at he
      rcases he with rfl | he
      · rcases edgeOf_endpoints v a hva with hep | hep
        · rcases hends with hends | hends
          · exact hends.2.symm.trans hep.2
          · exact False.elim (hva (hends.2.symm.trans hep.2))
        · rcases hends with hends | hends
          · exact False.elim (hva (hends.1.symm.trans hep.1))
          · exact hends.1.symm.trans hep.1
      · exact False.elim (hiso e he (by
          rcases hends with h | h
          · exact Or.inl h.1
          · exact Or.inr h.2))
    · intro hx
      subst x
      exact ⟨edgeOf v a hva, Finset.mem_insert_self _ _, edgeOf_endpoints v a hva⟩

/-- The decoded graph recovers the complete anchored generalized Pruefer list. -/
theorem decodeAux_injective {k : ℕ} (roots : Finset (Fin k)) :
    ∀ (code₁ : List (Fin k))
      (hcard₁ : roots.card + code₁.length = k)
      (hanchor₁ : Anchored roots code₁)
      (code₂ : List (Fin k))
      (hcard₂ : roots.card + code₂.length = k)
      (hanchor₂ : Anchored roots code₂),
      decodeAux roots code₁ hcard₁ hanchor₁ =
        decodeAux roots code₂ hcard₂ hanchor₂ → code₁ = code₂ := by
  intro code₁
  induction code₁ generalizing roots with
  | nil =>
      intro hcard₁ hanchor₁
      exact False.elim (anchored_ne_nil hanchor₁ rfl)
  | cons a tail ih =>
      intro hcard₁ hanchor₁ code₂ hcard₂ hanchor₂ heq
      cases code₂ with
      | nil => exact False.elim (anchored_ne_nil hanchor₂ rfl)
      | cons b tail₂ =>
          have hlen : tail.length = tail₂.length := by
            simp only [List.length_cons] at hcard₁ hcard₂
            omega
          have havail : available roots (a :: tail) =
              available roots (b :: tail₂) := by
            ext x
            rw [mem_available_iff_decodeAux_degree_one hcard₁ hanchor₁,
              mem_available_iff_decodeAux_degree_one hcard₂ hanchor₂]
            rw [heq]
          let v₁ := pick roots (a :: tail) hcard₁ hanchor₁
          let v₂ := pick roots (b :: tail₂) hcard₂ hanchor₂
          have hv : v₁ = v₂ := by
            have hv₁mem := pick_mem_available hcard₁ hanchor₁
            have hv₂mem := pick_mem_available hcard₂ hanchor₂
            rw [havail] at hv₁mem
            rw [← havail] at hv₂mem
            exact le_antisymm
              (Finset.min'_le _ v₂ hv₂mem)
              (Finset.min'_le _ v₁ hv₁mem)
          have hab : a = b := by
            have hadj : adj (decodeAux roots (a :: tail) hcard₁ hanchor₁) v₁ b := by
              rw [heq, hv]
              exact (decodeAux_pick_adj_iff hcard₂ hanchor₂ b).2 rfl
            exact (decodeAux_pick_adj_iff hcard₁ hanchor₁ b).1 hadj |>.symm
          subst b
          have hempty : tail = [] ↔ tail₂ = [] := by
            constructor
            · intro h
              apply List.eq_nil_of_length_eq_zero
              rw [← hlen, h]
              rfl
            · intro h
              apply List.eq_nil_of_length_eq_zero
              rw [hlen, h]
              rfl
          by_cases ht : tail = []
          · have ht₂ := hempty.mp ht
            subst tail
            subst tail₂
            rfl
          · have ht₂ : tail₂ ≠ [] := fun h => ht (hempty.mpr h)
            let v := pick roots (a :: tail) hcard₁ hanchor₁
            have hv' : v = pick roots (a :: tail₂) hcard₂ hanchor₂ := hv
            let e := edgeOf v a (fun h =>
              pick_not_mem_code hcard₁ hanchor₁ (by simpa [v, h]))
            let roots' := insert v roots
            let hc₁ := card_insert_pick hcard₁ hanchor₁
            have hc₂ : roots'.card + tail₂.length = k := by
              simpa [roots', v, hv'] using! card_insert_pick hcard₂ hanchor₂
            let ha₁ := anchored_mono (anchored_tail (roots := roots) hanchor₁ ht)
              (Finset.subset_insert v roots)
            have ha₂ : Anchored roots' tail₂ := by
              apply anchored_mono (anchored_tail (roots := roots) hanchor₂ ht₂)
              simpa [roots', v, hv'] using!
                (Finset.subset_insert
                  (pick roots (a :: tail₂) hcard₂ hanchor₂) roots)
            let H₁ := decodeAux roots' tail hc₁ ha₁
            let H₂ := decodeAux roots' tail₂ hc₂ ha₂
            have heq' : insert e H₁ = insert e H₂ := by
              have heq0 := heq
              rw [decodeAux_cons hcard₁ hanchor₁ ht,
                decodeAux_cons hcard₂ hanchor₂ ht₂] at heq0
              simpa [v, e, roots', hc₁, hc₂, ha₁, ha₂, H₁, H₂, hv'] using! heq0
            have heH₁ : e ∉ H₁ := by
              intro he
              have hiso := decodeAux_no_incident roots' tail hc₁ ha₁
                (x := v) (by simp [roots'])
                (fun hvt => pick_not_mem_code hcard₁ hanchor₁
                  (List.mem_cons_of_mem a hvt)) e he
              exact hiso ((incident_edgeOf_iff v v a _).2 (Or.inl rfl))
            have heH₂ : e ∉ H₂ := by
              intro he
              have hiso := decodeAux_no_incident roots' tail₂ hc₂ ha₂
                (x := v) (by simp [roots'])
                (fun hvt => pick_not_mem_code hcard₂ hanchor₂
                  (by simpa [v, hv'] using! List.mem_cons_of_mem a hvt)) e he
              exact hiso ((incident_edgeOf_iff v v a _).2 (Or.inl rfl))
            have htails : H₁ = H₂ := by
              have := congrArg (fun G : Graph k => G.erase e) heq'
              simpa [Finset.erase_insert heH₁, Finset.erase_insert heH₂] using! this
            have htail : tail = tail₂ :=
              ih roots' hc₁ ha₁ tail₂ hc₂ ha₂ htails
            exact congrArg (List.cons a) htail

lemma codeList_injective {k : ℕ} {roots : Finset (Fin k)} :
    Function.Injective (@codeList k roots) := by
  rintro ⟨r₁, f₁⟩ ⟨r₂, f₂⟩ h
  unfold codeList at h
  have hparts := List.append_inj h (by simp)
  have hf : f₁ = f₂ := List.ofFn_injective hparts.1
  have hr : r₁ = r₂ := Subtype.ext (by simpa using! hparts.2)
  cases hf
  cases hr
  rfl

theorem decodeRootedForest_injective {k : ℕ} {roots : Finset (Fin k)}
    (hproper : roots.card < k) :
    Function.Injective (decodeRootedForest hproper) := by
  intro c₁ c₂ h
  apply codeList_injective
  apply decodeAux_injective roots (codeList c₁)
      (codeList_card hproper c₁) (codeList_anchored c₁)
      (codeList c₂) (codeList_card hproper c₂) (codeList_anchored c₂)
  exact congrArg Subtype.val h

lemma rootedForest_component_count {k : ℕ} {roots : Finset (Fin k)}
    (G : RootedForest k roots) : (components G.1).card = roots.card := by
  have hsum := sum_component_root_cards G.1 roots
  calc
    (components G.1).card = ∑ S ∈ components G.1, 1 := by simp
    _ = ∑ S ∈ components G.1, (S ∩ roots).card := by
      apply Finset.sum_congr rfl
      intro S hS
      exact (G.2 S hS).2.symm
    _ = roots.card := hsum

lemma rootedForest_edge_card {k : ℕ} {roots : Finset (Fin k)}
    (G : RootedForest k roots) : G.1.card = k - roots.card := by
  have hcount := component_count_of_forest G.1 (fun S hS => (G.2 S hS).1)
  rw [rootedForest_component_count G] at hcount
  omega

lemma rootedForest_component_root {k : ℕ} {roots : Finset (Fin k)}
    (G : RootedForest k roots) (x : Fin k) :
    ∃ r ∈ roots, reach G.1 x r := by
  let S := componentOf G.1 x
  have hS : S ∈ components G.1 := componentOf_mem_components G.1 x
  have hcard := (G.2 S hS).2
  have hpos : 0 < (S ∩ roots).card := by omega
  obtain ⟨r, hr⟩ := Finset.card_pos.mp hpos
  exact ⟨r, (Finset.mem_inter.mp hr).2,
    mem_componentOf_iff.mp (Finset.mem_inter.mp hr).1⟩

private lemma degree_pos_of_reaches_ne {k : ℕ} {G : Graph k} {x y : Fin k}
    (hxy : reach G x y) (hne : x ≠ y) : 0 < (simpleGraph G).degree x := by
  by_contra hzero
  have hdeg : (simpleGraph G).degree x = 0 := by omega
  have hiso : ∀ e ∈ G, ¬ Incident x e := by
    intro e he hinc
    have hadj : ∃ z, adj G x z := by
      rcases hinc with h | h
      · exact ⟨e.val.2, ⟨e, he, Or.inl ⟨h, rfl⟩⟩⟩
      · exact ⟨e.val.1, ⟨e, he, Or.inr ⟨rfl, h⟩⟩⟩
    have hpos : 0 < (simpleGraph G).degree x :=
      (SimpleGraph.degree_pos_iff_exists_adj (simpleGraph G) x).2 (by
        rcases hadj with ⟨z, hz⟩
        exact ⟨z, hz⟩)
    omega
  exact hne (reach_eq_of_no_incident hiso hxy)

private noncomputable def nonrootLeaves {k : ℕ} (roots : Finset (Fin k))
    (G : Graph k) : Finset (Fin k) :=
  (Finset.univ \ roots).filter (fun x => (simpleGraph G).degree x = 1)

private lemma nonrootLeaves_nonempty {k : ℕ} {roots : Finset (Fin k)}
    (hproper : roots.card < k) (G : RootedForest k roots) :
    (nonrootLeaves roots G.1).Nonempty := by
  let U : Finset (Fin k) := Finset.univ \ roots
  have hUcard : U.card = k - roots.card := card_nonroots roots
  have hUne : U.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have : U.card = 0 := by simp [h]
    omega
  by_contra hnone
  rw [Finset.not_nonempty_iff_eq_empty] at hnone
  have hdegU : ∀ x ∈ U, 2 ≤ (simpleGraph G.1).degree x := by
    intro x hx
    have hxroot : x ∉ roots := (Finset.mem_sdiff.mp hx).2
    obtain ⟨r, hr, hxr⟩ := rootedForest_component_root G x
    have hxrne : x ≠ r := fun h => hxroot (h ▸ hr)
    have hpos := degree_pos_of_reaches_ne hxr hxrne
    have hneone : (simpleGraph G.1).degree x ≠ 1 := by
      intro hone
      have : x ∈ nonrootLeaves roots G.1 := by
        exact Finset.mem_filter.mpr ⟨hx, hone⟩
      simpa [hnone] using! this
    omega
  obtain ⟨x, hxU⟩ := hUne
  have hxroot : x ∉ roots := (Finset.mem_sdiff.mp hxU).2
  obtain ⟨r, hr, hxr⟩ := rootedForest_component_root G x
  have hxrne : x ≠ r := fun h => hxroot (h ▸ hr)
  have hrpos : 0 < (simpleGraph G.1).degree r :=
    degree_pos_of_reaches_ne (reach_symm hxr) hxrne.symm
  have hrnotU : r ∉ U := by simp [U, hr]
  have hsub : insert r U ⊆ (Finset.univ : Finset (Fin k)) :=
    Finset.subset_univ _
  have hsumsub :
      ∑ z ∈ insert r U, (simpleGraph G.1).degree z ≤
        ∑ z : Fin k, (simpleGraph G.1).degree z := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro i hi hj
      exact Nat.zero_le _)
  have hsumU : 2 * U.card ≤ ∑ z ∈ U, (simpleGraph G.1).degree z := by
    calc
      2 * U.card = ∑ _z ∈ U, 2 := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun z hz => hdegU z hz
  rw [Finset.sum_insert hrnotU] at hsumsub
  have hdegrees := (simpleGraph G.1).sum_degrees_eq_twice_card_edges
  rw [simpleGraph_edgeFinset_card, rootedForest_edge_card G] at hdegrees
  omega

private noncomputable def peelVertex {k : ℕ} {roots : Finset (Fin k)}
    (hproper : roots.card < k) (G : RootedForest k roots) : Fin k :=
  (nonrootLeaves roots G.1).min' (nonrootLeaves_nonempty hproper G)

private lemma peelVertex_spec {k : ℕ} {roots : Finset (Fin k)}
    (hproper : roots.card < k) (G : RootedForest k roots) :
    peelVertex hproper G ∉ roots ∧
      (simpleGraph G.1).degree (peelVertex hproper G) = 1 := by
  have hmem := Finset.min'_mem (nonrootLeaves roots G.1)
    (nonrootLeaves_nonempty hproper G)
  exact ⟨(Finset.mem_sdiff.mp (Finset.mem_filter.mp hmem).1).2,
    (Finset.mem_filter.mp hmem).2⟩

private noncomputable def peelNeighbor {k : ℕ} {roots : Finset (Fin k)}
    (hproper : roots.card < k) (G : RootedForest k roots) : Fin k :=
  Classical.choose ((SimpleGraph.degree_eq_one_iff_existsUnique_adj).1
    (peelVertex_spec hproper G).2)

private lemma peelNeighbor_adj {k : ℕ} {roots : Finset (Fin k)}
    (hproper : roots.card < k) (G : RootedForest k roots) :
    adj G.1 (peelVertex hproper G) (peelNeighbor hproper G) := by
  exact (Classical.choose_spec ((SimpleGraph.degree_eq_one_iff_existsUnique_adj).1
    (peelVertex_spec hproper G).2)).1

private lemma peelNeighbor_unique {k : ℕ} {roots : Finset (Fin k)}
    (hproper : roots.card < k) (G : RootedForest k roots) (x : Fin k) :
    adj G.1 (peelVertex hproper G) x ↔ x = peelNeighbor hproper G := by
  let hex := (SimpleGraph.degree_eq_one_iff_existsUnique_adj).1
    (peelVertex_spec hproper G).2
  exact ⟨fun hx => (Classical.choose_spec hex).2 x hx,
    fun hx => hx ▸ (Classical.choose_spec hex).1⟩

private lemma peelVertex_ne_neighbor {k : ℕ} {roots : Finset (Fin k)}
    (hproper : roots.card < k) (G : RootedForest k roots) :
    peelVertex hproper G ≠ peelNeighbor hproper G := by
  intro h
  have := peelNeighbor_adj hproper G
  exact adj_irrefl G.1 (peelVertex hproper G) (h ▸ this)

private lemma edge_eq_edgeOf_of_mem_incident {k : ℕ} {roots : Finset (Fin k)}
    (hproper : roots.card < k) (G : RootedForest k roots)
    {f : Edge k} (hf : f ∈ G.1) (hinc : Incident (peelVertex hproper G) f) :
    f = edgeOf (peelVertex hproper G) (peelNeighbor hproper G)
      (peelVertex_ne_neighbor hproper G) := by
  let v := peelVertex hproper G
  let a := peelNeighbor hproper G
  rcases hinc with hinc | hinc
  · have hadj : adj G.1 v f.val.2 :=
      ⟨f, hf, Or.inl ⟨hinc, rfl⟩⟩
    have ha : f.val.2 = a := (peelNeighbor_unique hproper G _).1 hadj
    apply Subtype.ext
    unfold edgeOf
    split
    · apply Prod.ext <;> simp_all [v, a]
    · exfalso
      apply ‹¬v < a›
      simpa [v, a, hinc, ha] using! f.property
  · have hadj : adj G.1 v f.val.1 :=
      ⟨f, hf, Or.inr ⟨rfl, hinc⟩⟩
    have ha : f.val.1 = a := (peelNeighbor_unique hproper G _).1 hadj
    apply Subtype.ext
    unfold edgeOf
    split
    · exfalso
      have hav : a < v := by simpa [v, a, hinc, ha] using! f.property
      exact (lt_asymm ‹v < a› hav)
    · apply Prod.ext <;> simp_all [v, a]

private lemma adj_erase_peel_of_ne {k : ℕ} {roots : Finset (Fin k)}
    (hproper : roots.card < k) (G : RootedForest k roots)
    {x y : Fin k} (hx : x ≠ peelVertex hproper G)
    (hy : y ≠ peelVertex hproper G) (hxy : adj G.1 x y) :
    adj (G.1.erase (edgeOf (peelVertex hproper G) (peelNeighbor hproper G)
      (peelVertex_ne_neighbor hproper G))) x y := by
  rcases hxy with ⟨f, hf, hends⟩
  refine ⟨f, Finset.mem_erase.mpr ⟨?_, hf⟩, hends⟩
  intro hfe
  subst f
  rcases edgeOf_endpoints (peelVertex hproper G) (peelNeighbor hproper G)
      (peelVertex_ne_neighbor hproper G) with h | h <;>
    rcases hends with h' | h' <;> simp_all

private lemma reach_erase_peel_of_ne {k : ℕ} {roots : Finset (Fin k)}
    (hproper : roots.card < k) (G : RootedForest k roots)
    {x y : Fin k} (hxy : reach G.1 x y)
    (hx : x ≠ peelVertex hproper G) (hy : y ≠ peelVertex hproper G) :
    reach (G.1.erase (edgeOf (peelVertex hproper G) (peelNeighbor hproper G)
      (peelVertex_ne_neighbor hproper G))) x y := by
  let v := peelVertex hproper G
  let a := peelNeighbor hproper G
  let H := G.1.erase (edgeOf v a (peelVertex_ne_neighbor hproper G))
  have hva : v ≠ a := peelVertex_ne_neighbor hproper G
  have hQ : ∀ {p q : Fin k}, reach G.1 p q →
      (p ≠ v → q ≠ v → reach H p q) ∧
      (p ≠ v → q = v → reach H p a) := by
    intro p q hpq
    induction hpq with
    | refl =>
        constructor
        · intro _ _
          exact reach_refl p
        · intro hp hpv
          exact False.elim (hp hpv)
    | @tail b c hpq hqz ih =>
        constructor
        · intro hp hz
          by_cases hb : b = v
          · have hpa := ih.2 hp hb
            have hvc : adj G.1 v c := hb ▸ hqz
            have hca : c = a := (peelNeighbor_unique hproper G c).1 hvc
            simpa [hca] using! hpa
          · exact (ih.1 hp hb).tail
              (adj_erase_peel_of_ne hproper G hb hz hqz)
        · intro hp hz
          subst c
          have hbv : adj G.1 v b := adj_symm hqz
          have hba : b = a := (peelNeighbor_unique hproper G b).1 hbv
          subst b
          exact ih.1 hp hva.symm
  exact (hQ hxy).1 hx hy

private lemma peel_isolated {k : ℕ} {roots : Finset (Fin k)}
    (hproper : roots.card < k) (G : RootedForest k roots) :
    ∀ f ∈ G.1.erase (edgeOf (peelVertex hproper G) (peelNeighbor hproper G)
      (peelVertex_ne_neighbor hproper G)), ¬ Incident (peelVertex hproper G) f := by
  intro f hf hinc
  exact (Finset.mem_erase.mp hf).1
    (edge_eq_edgeOf_of_mem_incident hproper G (Finset.mem_erase.mp hf).2 hinc)

private lemma peelEdge_mem {k : ℕ} {roots : Finset (Fin k)}
    (hproper : roots.card < k) (G : RootedForest k roots) :
    edgeOf (peelVertex hproper G) (peelNeighbor hproper G)
      (peelVertex_ne_neighbor hproper G) ∈ G.1 := by
  rcases peelNeighbor_adj hproper G with ⟨f, hf, hends⟩
  have hfe := edge_eq_edgeOf_of_mem_incident hproper G hf (by
    rcases hends with h | h
    · exact Or.inl h.1
    · exact Or.inr h.2)
  simpa [← hfe] using! hf

private lemma reach_mono_local {k : ℕ} {G H : Graph k} {x y : Fin k}
    (hGH : G ⊆ H) (hxy : reach G x y) : reach H x y := by
  induction hxy with
  | refl => exact reach_refl x
  | tail hxy hyz ih =>
      apply ih.tail
      rcases hyz with ⟨e, he, hends⟩
      exact ⟨e, hGH he, hends⟩

private lemma componentOf_peel_erase {k : ℕ} {roots : Finset (Fin k)}
    (hproper : roots.card < k) (G : RootedForest k roots) (x : Fin k) :
    componentOf
        (G.1.erase (edgeOf (peelVertex hproper G) (peelNeighbor hproper G)
          (peelVertex_ne_neighbor hproper G))) x =
      if x = peelVertex hproper G then {peelVertex hproper G}
      else componentOf G.1 x \ {peelVertex hproper G} := by
  let v := peelVertex hproper G
  let e := edgeOf v (peelNeighbor hproper G) (peelVertex_ne_neighbor hproper G)
  let H := G.1.erase e
  by_cases hx : x = v
  · subst x
    rw [if_pos rfl]
    ext y
    simp only [mem_componentOf_iff, Finset.mem_singleton]
    constructor
    · intro hvy
      have := reach_eq_of_no_incident (peel_isolated hproper G) hvy
      simpa [v, e, H] using! this.symm
    · rintro rfl
      exact reach_refl v
  · rw [if_neg hx]
    ext y
    simp only [mem_componentOf_iff, Finset.mem_sdiff, Finset.mem_singleton,
      Finset.mem_univ, true_and]
    constructor
    · intro hxy
      have hxyG : reach G.1 x y := by
        apply reach_mono_local (Finset.erase_subset e G.1) hxy
      have hyv : y ≠ v := by
        intro hyv
        subst y
        have hvx := reach_eq_of_no_incident (peel_isolated hproper G)
          (reach_symm hxy)
        exact hx hvx.symm
      exact ⟨hxyG, hyv⟩
    · rintro ⟨hxy, hyv⟩
      exact reach_erase_peel_of_ne hproper G hxy hx hyv

private lemma inside_peel_erase {k : ℕ} {roots : Finset (Fin k)}
    (hproper : roots.card < k) (G : RootedForest k roots)
    (T : Finset (Fin k)) :
    (G.1.erase (edgeOf (peelVertex hproper G) (peelNeighbor hproper G)
      (peelVertex_ne_neighbor hproper G))).filter
        (fun f => f.val.1 ∈ T \ {peelVertex hproper G} ∧
          f.val.2 ∈ T \ {peelVertex hproper G}) =
      (G.1.filter (fun f => f.val.1 ∈ T ∧ f.val.2 ∈ T)).erase
        (edgeOf (peelVertex hproper G) (peelNeighbor hproper G)
          (peelVertex_ne_neighbor hproper G)) := by
  let v := peelVertex hproper G
  let e := edgeOf v (peelNeighbor hproper G) (peelVertex_ne_neighbor hproper G)
  ext f
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_sdiff,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hfe, hfG⟩, ⟨hf1T, hf1v⟩, ⟨hf2T, hf2v⟩⟩
    exact ⟨hfe, ⟨hfG, hf1T, hf2T⟩⟩
  · rintro ⟨hfe, ⟨hfG, hf1T, hf2T⟩⟩
    refine ⟨⟨hfe, hfG⟩, ⟨hf1T, ?_⟩, ⟨hf2T, ?_⟩⟩
    · intro h1
      exact hfe (edge_eq_edgeOf_of_mem_incident hproper G hfG (Or.inl h1))
    · intro h2
      exact hfe (edge_eq_edgeOf_of_mem_incident hproper G hfG (Or.inr h2))

private lemma peel_rootedForest {k : ℕ} {roots : Finset (Fin k)}
    (hproper : roots.card < k) (G : RootedForest k roots) :
    ∀ S ∈ components
      (G.1.erase (edgeOf (peelVertex hproper G) (peelNeighbor hproper G)
        (peelVertex_ne_neighbor hproper G))),
      isTree
        (G.1.erase (edgeOf (peelVertex hproper G) (peelNeighbor hproper G)
          (peelVertex_ne_neighbor hproper G))) S ∧
        (S ∩ insert (peelVertex hproper G) roots).card = 1 := by
  let v := peelVertex hproper G
  let a := peelNeighbor hproper G
  let e := edgeOf v a (peelVertex_ne_neighbor hproper G)
  let H := G.1.erase e
  intro S hS
  simp only [components, Finset.mem_image] at hS
  rcases hS with ⟨x, -, rfl⟩
  by_cases hx : x = v
  · subst x
    have hcomp : componentOf H v = {v} := by
      simpa [H, e, v, a] using! componentOf_peel_erase hproper G v
    rw [hcomp]
    constructor
    · refine ⟨by simpa [hcomp] using! componentOf_mem_components H v, ?_⟩
      unfold edgesInside
      have hempty : H.filter (fun f => f.val.1 ∈ ({v} : Finset (Fin k)) ∧
          f.val.2 ∈ ({v} : Finset (Fin k))) = ∅ := by
        ext f
        simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty,
          iff_false]
        rintro ⟨hf, h1, h2⟩
        have : f.val.1 = f.val.2 := h1.trans h2.symm
        exact (ne_of_lt f.property) this
      rw [hempty]
      simp
    · have hvroot : v ∉ roots := (peelVertex_spec hproper G).1
      change (({v} : Finset (Fin k)) ∩ insert v roots).card = 1
      have hinter : ({v} : Finset (Fin k)) ∩ insert v roots = {v} := by
        ext z
        simp only [Finset.mem_inter, Finset.mem_singleton, Finset.mem_insert]
        constructor
        · rintro ⟨hz, -⟩
          exact hz
        · intro hz
          exact ⟨hz, Or.inl hz⟩
      rw [hinter]
      simp
  · have hcomp : componentOf H x = componentOf G.1 x \ {v} := by
      simpa [H, e, v, a, hx] using! componentOf_peel_erase hproper G x
    rw [hcomp]
    let T := componentOf G.1 x
    have hT : T ∈ components G.1 := componentOf_mem_components G.1 x
    have htreeT := (G.2 T hT).1.2
    have hrootT := (G.2 T hT).2
    have hins := inside_peel_erase hproper G T
    have hedges : edgesInside H (T \ {v}) =
        ((G.1.filter (fun f => f.val.1 ∈ T ∧ f.val.2 ∈ T)).erase e).card := by
      unfold edgesInside
      simpa [H, e, v, a] using! congrArg Finset.card hins
    have hrootset : (T \ {v}) ∩ insert v roots = T ∩ roots := by
      ext z
      by_cases hzv : z = v
      · subst z
        have hvroot : v ∉ roots := (peelVertex_spec hproper G).1
        simp [hvroot]
      · simp [hzv]
    constructor
    · refine ⟨by simpa [hcomp] using! componentOf_mem_components H x, ?_⟩
      rw [hedges]
      by_cases hvT : v ∈ T
      · have haT : a ∈ T := by
          rw [mem_componentOf_iff] at hvT ⊢
          exact hvT.trans
            (reach_of_adj (peelNeighbor_adj hproper G))
        have heinside : e ∈ G.1.filter
            (fun f => f.val.1 ∈ T ∧ f.val.2 ∈ T) := by
          apply Finset.mem_filter.mpr
          refine ⟨peelEdge_mem hproper G, ?_⟩
          rcases edgeOf_endpoints v a (peelVertex_ne_neighbor hproper G) with h | h
          · change e.val.1 ∈ T ∧ e.val.2 ∈ T
            simpa [e, h.1, h.2] using! And.intro hvT haT
          · change e.val.1 ∈ T ∧ e.val.2 ∈ T
            simpa [e, h.1, h.2] using! And.intro haT hvT
        rw [Finset.card_erase_of_mem heinside]
        have hcardT : (T \ {v}).card = T.card - 1 := by
          rw [Finset.card_sdiff_of_subset]
          · simp
          · simpa using! hvT
        rw [hcardT]
        have hposinside : 0 < (G.1.filter
            (fun f => f.val.1 ∈ T ∧ f.val.2 ∈ T)).card :=
          Finset.card_pos.mpr ⟨e, heinside⟩
        unfold edgesInside at htreeT
        omega
      · have henot : e ∉ G.1.filter
            (fun f => f.val.1 ∈ T ∧ f.val.2 ∈ T) := by
          intro he
          have hend := (Finset.mem_filter.mp he).2
          rcases edgeOf_endpoints v a (peelVertex_ne_neighbor hproper G) with h | h
          · exact hvT (h.1 ▸ hend.1)
          · exact hvT (h.2 ▸ hend.2)
        rw [Finset.erase_eq_of_notMem henot]
        have hsdiff : T \ {v} = T := by simp [hvT]
        rw [hsdiff]
        exact htreeT
    · rw [hrootset]
      exact hrootT

private noncomputable def peeledRootedForest {k : ℕ}
    {roots : Finset (Fin k)} (hproper : roots.card < k)
    (G : RootedForest k roots) :
    RootedForest k (insert (peelVertex hproper G) roots) :=
  ⟨G.1.erase (edgeOf (peelVertex hproper G) (peelNeighbor hproper G)
      (peelVertex_ne_neighbor hproper G)),
    peel_rootedForest hproper G⟩

private def funOfList {α : Type} {n : ℕ} (l : List α)
    (hlen : l.length = n) : Fin n → α :=
  fun i => l.get (Fin.cast hlen.symm i)

private lemma ofFn_funOfList {α : Type} {n : ℕ} (l : List α)
    (hlen : l.length = n) : List.ofFn (funOfList l hlen) = l := by
  apply List.ext_get
  · simp [funOfList, hlen]
  · intro i hi₁ hi₂
    simp [funOfList]

private lemma available_eq_nonrootLeaves_of_tail {k : ℕ}
    {roots : Finset (Fin k)} (hproper : roots.card < k)
    (G : RootedForest k roots) {tail : List (Fin k)}
    (a : Fin k) (hcard : roots.card + (a :: tail).length = k)
    (hanchor : Anchored roots (a :: tail))
    (hcardtail : (insert (peelVertex hproper G) roots).card + tail.length = k)
    (hanchortail : Anchored (insert (peelVertex hproper G) roots) tail)
    (hdecode : decodeAux
        (insert (peelVertex hproper G) roots) tail
        hcardtail hanchortail =
      (peeledRootedForest hproper G).1)
    (ha : a = peelNeighbor hproper G) :
    available roots (a :: tail) = nonrootLeaves roots G.1 := by
  let v := peelVertex hproper G
  let roots' := insert v roots
  let hc := hcardtail
  let hanc := hanchortail
  let H := (peeledRootedForest hproper G).1
  have hviso : ∀ f ∈ H, ¬ Incident v f := peel_isolated hproper G
  have hGinsert : G.1 = insert
      (edgeOf v (peelNeighbor hproper G) (peelVertex_ne_neighbor hproper G)) H := by
    symm
    exact Finset.insert_erase (peelEdge_mem hproper G)
  ext x
  change x ∈ Finset.univ \ (roots ∪ (a :: tail).toFinset) ↔
    x ∈ (Finset.univ \ roots).filter
      (fun x => (simpleGraph G.1).degree x = 1)
  rw [Finset.mem_filter, Finset.mem_sdiff]
  simp only [Finset.mem_univ, true_and, Finset.mem_union, List.mem_toFinset,
    List.mem_cons, not_or]
  constructor
  · rintro ⟨hxroot, hxa, hxtail⟩
    refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxroot⟩, ?_⟩
    by_cases hxv : x = v
    · subst x
      exact (peelVertex_spec hproper G).2
    · have hdegH := decodeAux_degree roots' tail hc hanc x
      rw [hdecode] at hdegH
      have hcount : tail.count x = 0 := List.count_eq_zero.mpr hxtail
      rw [hcount] at hdegH
      have hxroots' : x ∈ roots' ↔ x ∈ roots := by simp [roots', hxv]
      rw [if_congr hxroots' rfl rfl] at hdegH
      rw [hGinsert]
      change ((simpleGraph (insert
        (edgeOf v (peelNeighbor hproper G) (peelVertex_ne_neighbor hproper G)) H)).neighborFinset x).card = 1
      rw [neighborFinset_insert_edgeOf]
      by_cases hxa' : x = peelNeighbor hproper G
      · subst x
        exact False.elim (hxa ha.symm)
      · rw [if_neg hxv, if_neg hxa', Finset.union_empty]
        change (simpleGraph H).degree x = 1
        rw [if_neg hxroot] at hdegH
        simpa [H] using! hdegH
  · rintro ⟨hxU, hxdeg⟩
    have hxroot : x ∉ roots := (Finset.mem_sdiff.mp hxU).2
    have hxane : x ≠ a := by
      intro hxa
      subst x
      have hav : peelNeighbor hproper G ≠ v :=
        (peelVertex_ne_neighbor hproper G).symm
      have haroots' : peelNeighbor hproper G ∉ roots' := by
        simp only [roots', Finset.mem_insert, not_or]
        exact ⟨hav, ha.symm ▸ hxroot⟩
      obtain ⟨r, hr, har⟩ := rootedForest_component_root
        (peeledRootedForest hproper G) (peelNeighbor hproper G)
      have harne : peelNeighbor hproper G ≠ r := fun h => haroots' (h ▸ hr)
      have hposH : 0 < (simpleGraph H).degree (peelNeighbor hproper G) :=
        degree_pos_of_reaches_ne har harne
      have hvnot : v ∉ (simpleGraph H).neighborFinset (peelNeighbor hproper G) :=
        not_mem_neighborFinset_of_no_incident hviso
      have hdegadd : (simpleGraph G.1).degree (peelNeighbor hproper G) =
          (simpleGraph H).degree (peelNeighbor hproper G) + 1 := by
        rw [hGinsert]
        change ((simpleGraph (insert
          (edgeOf v (peelNeighbor hproper G) (peelVertex_ne_neighbor hproper G)) H)).neighborFinset
            (peelNeighbor hproper G)).card = _
        rw [neighborFinset_insert_edgeOf]
        simp only [if_neg hav, if_pos]
        rw [Finset.card_union_of_disjoint
          (Finset.disjoint_singleton_right.mpr hvnot)]
        change (simpleGraph H).degree (peelNeighbor hproper G) + 1 = _
        rfl
      have hxdeg' := hxdeg
      rw [ha] at hxdeg'
      omega
    refine ⟨hxroot, hxane, ?_⟩
    intro hxtail
    have hcountpos : 0 < tail.count x := by
      apply Nat.pos_of_ne_zero
      intro hz
      exact (List.count_eq_zero.mp hz) hxtail
    have hdegH := decodeAux_degree roots' tail hc hanc x
    rw [hdecode] at hdegH
    change (simpleGraph H).degree x = _ at hdegH
    by_cases hxv : x = v
    · subst x
      have hvroots' : v ∈ roots' := by simp [roots']
      rw [if_pos hvroots'] at hdegH
      have hneigh : (simpleGraph H).neighborFinset v = ∅ :=
        neighborFinset_eq_empty_of_no_incident hviso
      have hzero : (simpleGraph H).degree v = 0 := by
        change ((simpleGraph H).neighborFinset v).card = 0
        rw [hneigh]
        rfl
      change (simpleGraph H).degree v = _ at hdegH
      omega
    have hxroots' : x ∉ roots' := by simp [roots', hxv, hxroot]
    rw [if_neg hxroots'] at hdegH
    have hdegEq : (simpleGraph G.1).degree x = (simpleGraph H).degree x := by
      rw [hGinsert]
      change ((simpleGraph (insert
        (edgeOf v (peelNeighbor hproper G) (peelVertex_ne_neighbor hproper G)) H)).neighborFinset x).card = _
      rw [neighborFinset_insert_edgeOf]
      have hxane' : x ≠ peelNeighbor hproper G := by
        intro h
        exact hxane (h.trans ha.symm)
      rw [if_neg hxv, if_neg hxane', Finset.union_empty]
      rfl
    omega

private theorem decodeRootedForest_surjective_gap (k m : ℕ) :
    ∀ (roots : Finset (Fin k)) (hgap : k - roots.card = m)
      (hproper : roots.card < k), roots ≠ ∅ →
      Function.Surjective (decodeRootedForest hproper) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro roots hgap hproper hroots G
      let v := peelVertex hproper G
      let a := peelNeighbor hproper G
      let e := edgeOf v a (peelVertex_ne_neighbor hproper G)
      let roots' := insert v roots
      let H := peeledRootedForest hproper G
      have hvroot : v ∉ roots := (peelVertex_spec hproper G).1
      have hroots'card : roots'.card = roots.card + 1 := by
        simp [roots', hvroot]
      have hGinsert : G.1 = insert e H.1 := by
        symm
        exact Finset.insert_erase (peelEdge_mem hproper G)
      by_cases hm : m = 1
      · have hcardone : G.1.card = 1 := by
          rw [rootedForest_edge_card G, hgap, hm]
        have hHempty : H.1 = ∅ := by
          apply Finset.card_eq_zero.mp
          rw [show H.1 = G.1.erase e by rfl, Finset.card_erase_of_mem]
          · omega
          · exact peelEdge_mem hproper G
        have haroot : a ∈ roots := by
          by_contra haroot
          have hvU : v ∈ (Finset.univ : Finset (Fin k)) \ roots := by
            simp [hvroot]
          have haU : a ∈ (Finset.univ : Finset (Fin k)) \ roots := by
            simp [haroot]
          have hlt : 1 < ((Finset.univ : Finset (Fin k)) \ roots).card :=
            Finset.one_lt_card.mpr ⟨v, hvU, a, haU,
              peelVertex_ne_neighbor hproper G⟩
          rw [card_nonroots, hgap, hm] at hlt
          omega
        let c : PrueferCode k roots :=
          (⟨a, haroot⟩, fun i => False.elim (by
            have hi := i.isLt
            omega))
        refine ⟨c, Subtype.ext ?_⟩
        have hcl : codeList c = [a] := by
          have hof : List.ofFn c.2 = [] := by
            apply List.eq_nil_of_length_eq_zero
            simp only [List.length_ofFn, Fintype.card_fin]
            omega
          change List.ofFn c.2 ++ [(c.1 : Fin k)] = [a]
          rw [hof]
          simp [c]
        have hpick : pick roots [a]
            (by simpa [hcl] using! codeList_card hproper c)
            (by simpa [hcl] using! codeList_anchored c) = v := by
          symm
          apply nonroot_eq_pick_of_singleton_code
          exact hvroot
        change decodeGraph hproper c = G.1
        unfold decodeGraph
        have hdec : decodeAux roots [a]
            (by simpa [hcl] using! codeList_card hproper c)
            (by simpa [hcl] using! codeList_anchored c) = G.1 := by
          rw [decodeAux_eq_singleton]
          rw [hGinsert, hHempty]
          simpa [e, v, a, hpick]
        simpa [hcl] using! hdec
      · have hmgt : 1 < m := by
          have : 0 < m := by omega
          omega
        have hproper' : roots'.card < k := by
          rw [hroots'card]
          omega
        have hgap' : k - roots'.card = m - 1 := by
          rw [hroots'card]
          omega
        have hrootsne' : roots' ≠ ∅ := by
          exact Finset.ne_empty_of_mem (Finset.mem_insert_self v roots)
        obtain ⟨c₂, hc₂⟩ :=
          ih (m - 1) (by omega) roots' hgap' hproper' hrootsne' H
        have hterminal : (c₂.1 : Fin k) ≠ v := by
          intro hrv
          have hviso := peel_isolated hproper G
          have hneigh : (simpleGraph H.1).neighborFinset v = ∅ :=
            neighborFinset_eq_empty_of_no_incident hviso
          have hdegzero : (simpleGraph H.1).degree v = 0 := by
            simp [SimpleGraph.degree, hneigh]
          have hdeg := decodeAux_degree roots' (codeList c₂)
            (codeList_card hproper' c₂) (codeList_anchored c₂) v
          have hgraph := congrArg Subtype.val hc₂
          change decodeGraph hproper' c₂ = H.1 at hgraph
          unfold decodeGraph at hgraph
          rw [hgraph, hdegzero] at hdeg
          have hvroots' : v ∈ roots' := Finset.mem_insert_self v roots
          rw [if_pos hvroots'] at hdeg
          have hvmem : v ∈ codeList c₂ := by
            simp [codeList, hrv]
          have hpos : 0 < (codeList c₂).count v := by
            apply Nat.pos_of_ne_zero
            intro hz
            exact (List.count_eq_zero.mp hz) hvmem
          omega
        have hc₂root : (c₂.1 : Fin k) ∈ roots := by
          have := c₂.1.property
          rcases Finset.mem_insert.mp this with h | h
          · exact False.elim (hterminal h)
          · exact h
        let pref : List (Fin k) := a :: List.ofFn c₂.2
        have hpref : pref.length = k - roots.card - 1 := by
          simp only [pref, List.length_cons, List.length_ofFn, Fintype.card_fin]
          omega
        let c₁ : PrueferCode k roots :=
          (⟨c₂.1, hc₂root⟩, funOfList pref hpref)
        have hcode : codeList c₁ = a :: codeList c₂ := by
          simp only [codeList, c₁]
          rw [ofFn_funOfList pref hpref]
          rfl
        have hcard₁ := codeList_card hproper c₁
        have hanchor₁ := codeList_anchored c₁
        have htailne : codeList c₂ ≠ [] := anchored_ne_nil
          (codeList_anchored c₂)
        have htaildecode : decodeAux roots' (codeList c₂)
            (codeList_card hproper' c₂) (codeList_anchored c₂) = H.1 := by
          have := congrArg Subtype.val hc₂
          change decodeGraph hproper' c₂ = H.1 at this
          exact this
        have havail := available_eq_nonrootLeaves_of_tail hproper G a
          (by simpa [hcode] using! hcard₁)
          (by simpa [hcode] using! hanchor₁)
          (by simpa [v, roots'] using! codeList_card hproper' c₂)
          (by simpa [v, roots'] using! codeList_anchored c₂)
          (by simpa [v, roots'] using! htaildecode) rfl
        have hpick : pick roots (codeList c₁) hcard₁ hanchor₁ = v := by
          have havail' : available roots (codeList c₁) =
              nonrootLeaves roots G.1 := by simpa [hcode] using! havail
          have hleft : pick roots (codeList c₁) hcard₁ hanchor₁ ∈
              nonrootLeaves roots G.1 := by
            exact havail' ▸ pick_mem_available hcard₁ hanchor₁
          have hright : peelVertex hproper G ∈
              available roots (codeList c₁) := by
            have hvleaf := Finset.min'_mem (nonrootLeaves roots G.1)
              (nonrootLeaves_nonempty hproper G)
            exact havail'.symm ▸ hvleaf
          apply le_antisymm
          · exact Finset.min'_le _ _ hright
          · exact Finset.min'_le _ _ hleft
        refine ⟨c₁, Subtype.ext ?_⟩
        change decodeGraph hproper c₁ = G.1
        unfold decodeGraph
        have hdec : decodeAux roots (a :: codeList c₂)
            (by simpa [hcode] using! hcard₁)
            (by simpa [hcode] using! hanchor₁) = G.1 := by
          have hpick' : pick roots (a :: codeList c₂)
              (by simpa [hcode] using! hcard₁)
              (by simpa [hcode] using! hanchor₁) = v := by
            simpa [hcode] using! hpick
          rw [decodeAux_cons]
          · rw [hGinsert]
            have hins := congrArg (fun Q : Graph k => insert e Q) htaildecode
            simpa [v, a, e, roots', hpick'] using! hins
          · exact htailne
        simpa [hcode] using! hdec

theorem decodeRootedForest_surjective {k : ℕ} {roots : Finset (Fin k)}
    (hproper : roots.card < k) (hroots : roots ≠ ∅) :
    Function.Surjective (decodeRootedForest hproper) := by
  exact decodeRootedForest_surjective_gap k (k - roots.card) roots rfl
    hproper hroots

theorem prueferBijection : PrueferBijectionStatement := by
  intro k roots hproper hroots
  exact ⟨decodeRootedForest_injective hproper,
    decodeRootedForest_surjective hproper hroots⟩

theorem rootedForestFormula : RootedForestFormula :=
  rootedForestFormula_of_prueferBijection prueferBijection

end Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Pruefer


namespace Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Cycle

open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Trees
open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Pruefer
open scoped BigOperators Sym2

attribute [local instance] Classical.propDecidable

/-- The unoriented edge set traced by a permutation.  For a cyclic
permutation of support at least three this is a simple cycle. -/
def cycleEdges {k : ℕ} (σ : Equiv.Perm (Fin k)) : Graph k :=
  Finset.univ.filter fun e =>
    σ e.val.1 = e.val.2 ∨ σ e.val.2 = e.val.1

@[simp] lemma mem_cycleEdges {k : ℕ} (σ : Equiv.Perm (Fin k))
    (e : Edge k) :
    e ∈ cycleEdges σ ↔
      σ e.val.1 = e.val.2 ∨ σ e.val.2 = e.val.1 := by
  simp [cycleEdges]

lemma adj_cycleEdges_iff {k : ℕ} (σ : Equiv.Perm (Fin k))
    (u v : Fin k) :
    adj (cycleEdges σ) u v ↔
      u ≠ v ∧ (σ u = v ∨ σ v = u) := by
  constructor
  · rintro ⟨e, he, huv | hvu⟩
    · have hlt : u < v := by simpa [huv.1, huv.2] using! e.property
      refine ⟨ne_of_lt hlt, ?_⟩
      simpa [huv.1, huv.2] using! (mem_cycleEdges σ e).mp he
    · have hlt : v < u := by simpa [hvu.1, hvu.2] using! e.property
      refine ⟨ne_of_gt hlt, ?_⟩
      simpa [hvu.1, hvu.2, or_comm] using! (mem_cycleEdges σ e).mp he
  · rintro ⟨huv, hσ⟩
    by_cases hlt : u < v
    · let e : Edge k := ⟨(u, v), hlt⟩
      exact ⟨e, (mem_cycleEdges σ e).mpr (by simpa [e] using! hσ),
        Or.inl ⟨rfl, rfl⟩⟩
    · have hvu : v < u := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm huv)
      let e : Edge k := ⟨(v, u), hvu⟩
      exact ⟨e, (mem_cycleEdges σ e).mpr (by simpa [e, or_comm] using! hσ),
        Or.inr ⟨rfl, rfl⟩⟩

lemma cycleEdges_inv {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    cycleEdges σ⁻¹ = cycleEdges σ := by
  ext e
  simp only [mem_cycleEdges]
  constructor
  · rintro (h | h)
    · exact Or.inr (by simpa using! (congrArg σ h).symm)
    · exact Or.inl (by simpa using! (congrArg σ h).symm)
  · rintro (h | h)
    · exact Or.inr (by simpa using! (congrArg σ.symm h).symm)
    · exact Or.inl (by simpa using! (congrArg σ.symm h).symm)

lemma support_of_cycle_edge_left {k : ℕ} {σ : Equiv.Perm (Fin k)}
    {u v : Fin k} (huv : u ≠ v) (h : σ u = v ∨ σ v = u) :
    u ∈ σ.support := by
  rw [Equiv.Perm.mem_support]
  intro hfix
  rcases h with h | h
  · exact huv (hfix.symm.trans h)
  · exact huv (σ.injective (hfix.trans h.symm))

lemma support_of_cycle_edge_right {k : ℕ} {σ : Equiv.Perm (Fin k)}
    {u v : Fin k} (huv : u ≠ v) (h : σ u = v ∨ σ v = u) :
    v ∈ σ.support := by
  exact support_of_cycle_edge_left huv.symm (h.elim Or.inr Or.inl)

lemma cycleEdges_mono_support {k : ℕ} {σ : Equiv.Perm (Fin k)}
    {e : Edge k} (he : e ∈ cycleEdges σ) :
    e.val.1 ∈ σ.support ∧ e.val.2 ∈ σ.support := by
  have hne : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  have h := (mem_cycleEdges σ e).mp he
  exact ⟨support_of_cycle_edge_left hne h,
    support_of_cycle_edge_right hne h⟩

lemma reach_cycle_pow {k : ℕ} (σ : Equiv.Perm (Fin k))
    (u : Fin k) : ∀ n : ℕ, reach (cycleEdges σ) u ((σ ^ n) u)
  | 0 => by simpa using! W01_ENUM_Trees.reach_refl u
  | n + 1 => by
      have ih := reach_cycle_pow σ u n
      have hpow : (σ ^ (n + 1)) u = σ ((σ ^ n) u) := by
        simp [pow_succ', Equiv.Perm.mul_apply]
      by_cases hfix : σ ((σ ^ n) u) = (σ ^ n) u
      · simpa [hpow, hfix] using! ih
      · exact W01_ENUM_Trees.reach_trans ih
          (W01_ENUM_Trees.reach_of_adj (by
            rw [adj_cycleEdges_iff, hpow]
            exact ⟨fun h => hfix h.symm, Or.inl rfl⟩))

lemma reach_cycle_support {k : ℕ} {σ : Equiv.Perm (Fin k)}
    (hσ : σ.IsCycle) {u v : Fin k}
    (hu : u ∈ σ.support) (hv : v ∈ σ.support) :
    reach (cycleEdges σ) u v := by
  obtain ⟨n, hn⟩ := hσ.exists_pow_eq
    (Equiv.Perm.mem_support.mp hu) (Equiv.Perm.mem_support.mp hv)
  simpa [hn] using! reach_cycle_pow σ u n

lemma cycleEdge_sym2_injOn {k : ℕ} {σ : Equiv.Perm (Fin k)}
    (hσ : σ.IsCycle) (hlen : 3 ≤ σ.support.card) :
    Set.InjOn (fun u : Fin k => s(u, σ u)) σ.support := by
  intro u hu v hv huv
  rcases Sym2.eq_iff.mp huv with h | h
  · exact h.1
  · have hσ2v : (σ ^ 2) v = v := by
      simp only [pow_two, Equiv.Perm.mul_apply]
      exact congrArg σ h.1.symm |>.trans h.2
    have hpow : σ ^ 2 = 1 :=
      (hσ.pow_eq_one_iff' (Equiv.Perm.mem_support.mp hv)).2 hσ2v
    have hord : orderOf σ ≤ 2 := orderOf_le_of_pow_eq_one (by omega) hpow
    rw [hσ.orderOf] at hord
    omega

lemma cycleEdges_card {k : ℕ} {σ : Equiv.Perm (Fin k)}
    (hσ : σ.IsCycle) (hlen : 3 ≤ σ.support.card) :
    (cycleEdges σ).card = σ.support.card := by
  let image : Finset (Sym2 (Fin k)) :=
    σ.support.image (fun u => s(u, σ u))
  have himage : image.card = σ.support.card := by
    exact Finset.card_image_of_injOn (cycleEdge_sym2_injOn hσ hlen)
  have hedge : (simpleGraph (cycleEdges σ)).edgeFinset = image := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        simpleGraph_adj, adj_cycleEdges_iff, image, Finset.mem_image]
      constructor
      · rintro ⟨huv, h | h⟩
        · exact ⟨u, support_of_cycle_edge_left huv (Or.inl h), by simp [h]⟩
        · exact ⟨v, support_of_cycle_edge_right huv (Or.inr h), by
            rw [h]
            exact Sym2.eq_swap⟩
      · rintro ⟨w, hw, hwuv⟩
        rcases Sym2.eq_iff.mp hwuv with h | h
        · rcases h with ⟨rfl, rfl⟩
          exact ⟨(Equiv.Perm.mem_support.mp hw).symm, Or.inl rfl⟩
        · rcases h with ⟨rfl, rfl⟩
          exact ⟨Equiv.Perm.mem_support.mp hw, Or.inr rfl⟩
  rw [← simpleGraph_edgeFinset_card, hedge, himage]

lemma mem_support_iff_exists_cycleAdj {k : ℕ} {σ : Equiv.Perm (Fin k)}
    (hσ : σ.IsCycle) (hlen : 3 ≤ σ.support.card) (u : Fin k) :
    u ∈ σ.support ↔ ∃ v, adj (cycleEdges σ) u v := by
  constructor
  · intro hu
    refine ⟨σ u, ?_⟩
    rw [adj_cycleEdges_iff]
    exact ⟨(Equiv.Perm.mem_support.mp hu).symm, Or.inl rfl⟩
  · rintro ⟨v, hv⟩
    rw [adj_cycleEdges_iff] at hv
    exact support_of_cycle_edge_left hv.1 hv.2

lemma support_eq_of_cycleEdges_eq {k : ℕ}
    {σ τ : Equiv.Perm (Fin k)} (hσ : σ.IsCycle) (hτ : τ.IsCycle)
    (hσlen : 3 ≤ σ.support.card) (hτlen : 3 ≤ τ.support.card)
    (hedges : cycleEdges σ = cycleEdges τ) :
    σ.support = τ.support := by
  ext u
  rw [mem_support_iff_exists_cycleAdj hσ hσlen,
    mem_support_iff_exists_cycleAdj hτ hτlen, hedges]

private lemma pow_apply_mem_support {k : ℕ} {σ : Equiv.Perm (Fin k)}
    {u : Fin k} (hu : u ∈ σ.support) (n : ℕ) :
    (σ ^ n) u ∈ σ.support := by
  rw [Equiv.Perm.mem_support]
  intro hfix
  apply Equiv.Perm.mem_support.mp hu
  apply (σ ^ n).injective
  calc
    (σ ^ n) (σ u) = (σ ^ n * σ) u := by
      rw [Equiv.Perm.mul_apply]
    _ = (σ * σ ^ n) u := congrArg (fun f : Equiv.Perm (Fin k) => f u)
      (Commute.pow_self σ n).eq
    _ = σ ((σ ^ n) u) := by rw [Equiv.Perm.mul_apply]
    _ = (σ ^ n) u := hfix

private lemma cycle_perm_eq_of_edges_eq_of_apply_eq {k : ℕ}
    {σ τ : Equiv.Perm (Fin k)} (hσ : σ.IsCycle) (hτ : τ.IsCycle)
    (hσlen : 3 ≤ σ.support.card) (hτlen : 3 ≤ τ.support.card)
    (hedges : cycleEdges σ = cycleEdges τ) {u : Fin k}
    (hu : u ∈ σ.support) (huv : τ u = σ u) : τ = σ := by
  have hsupport : τ.support = σ.support :=
    (support_eq_of_cycleEdges_eq hτ hσ hτlen hσlen hedges.symm)
  have hτorder : 3 ≤ orderOf τ := by
    rw [hτ.orderOf, hsupport]
    exact hσlen
  have hagree : ∀ n : ℕ, τ ((σ ^ n) u) = (σ ^ (n + 1)) u := by
    intro n
    induction n with
    | zero => simpa using! huv
    | succ n ih =>
      have hxmem : (σ ^ (n + 1)) u ∈ σ.support :=
        pow_apply_mem_support hu (n + 1)
      have hadjτ : adj (cycleEdges τ) ((σ ^ (n + 1)) u)
          (τ ((σ ^ (n + 1)) u)) := by
        rw [adj_cycleEdges_iff]
        have hxmemτ : (σ ^ (n + 1)) u ∈ τ.support := by
          rw [hsupport]
          exact hxmem
        exact ⟨(Equiv.Perm.mem_support.mp hxmemτ).symm, Or.inl rfl⟩
      have hadjσ : adj (cycleEdges σ) ((σ ^ (n + 1)) u)
          (τ ((σ ^ (n + 1)) u)) := by simpa [hedges] using! hadjτ
      rw [adj_cycleEdges_iff] at hadjσ
      rcases hadjσ.2 with hforward | hback
      · simpa [pow_succ', Equiv.Perm.mul_apply] using! hforward.symm
      · have hprev : τ ((σ ^ (n + 1)) u) = (σ ^ n) u := by
          apply σ.injective
          simpa [pow_succ', Equiv.Perm.mul_apply] using! hback
        have hτ2 : (τ ^ 2) ((σ ^ n) u) = (σ ^ n) u := by
          simp only [pow_two, Equiv.Perm.mul_apply, ih, hprev]
        have hτmem : (σ ^ n) u ∈ τ.support := by
          rw [hsupport]
          exact pow_apply_mem_support hu n
        have hp2 : τ ^ 2 = 1 :=
          (hτ.pow_eq_one_iff' (Equiv.Perm.mem_support.mp hτmem)).2 hτ2
        exact False.elim (by
          have := orderOf_le_of_pow_eq_one (by omega) hp2
          omega)
  apply Equiv.ext
  intro v
  by_cases hv : v ∈ σ.support
  · obtain ⟨n, hn⟩ := hσ.exists_pow_eq
      (Equiv.Perm.mem_support.mp hu) (Equiv.Perm.mem_support.mp hv)
    subst v
    simpa [pow_succ', Equiv.Perm.mul_apply] using! hagree n
  · have hτv : v ∉ τ.support := by
      intro hvt
      exact hv (hsupport ▸ hvt)
    have hσfix : σ v = v :=
      not_ne_iff.mp ((Equiv.Perm.mem_support (f := σ) (x := v)).not.mp hv)
    have hτfix : τ v = v :=
      not_ne_iff.mp ((Equiv.Perm.mem_support (f := τ) (x := v)).not.mp hτv)
    rw [hσfix, hτfix]

lemma cycle_perm_eq_or_inv_of_edges_eq {k : ℕ}
    {σ τ : Equiv.Perm (Fin k)} (hσ : σ.IsCycle) (hτ : τ.IsCycle)
    (hσlen : 3 ≤ σ.support.card) (hτlen : 3 ≤ τ.support.card)
    (hedges : cycleEdges σ = cycleEdges τ) :
    τ = σ ∨ τ = σ⁻¹ := by
  have hsupport : τ.support = σ.support :=
    support_eq_of_cycleEdges_eq hτ hσ hτlen hσlen hedges.symm
  obtain ⟨u, hu⟩ := hσ.nonempty_support
  have huτ : u ∈ τ.support := by rw [hsupport]; exact hu
  have hadjτ : adj (cycleEdges τ) u (τ u) := by
    rw [adj_cycleEdges_iff]
    exact ⟨(Equiv.Perm.mem_support.mp huτ).symm, Or.inl rfl⟩
  have hadjσ : adj (cycleEdges σ) u (τ u) := by simpa [hedges] using! hadjτ
  rw [adj_cycleEdges_iff] at hadjσ
  rcases hadjσ.2 with hforward | hback
  · exact Or.inl (cycle_perm_eq_of_edges_eq_of_apply_eq hσ hτ
      hσlen hτlen hedges hu hforward.symm)
  · right
    have hinv : σ⁻¹ u = τ u := by
      apply σ.injective
      simpa using! hback.symm
    apply cycle_perm_eq_of_edges_eq_of_apply_eq hσ.inv hτ
      (by simpa [Equiv.Perm.support_inv] using! hσlen) hτlen
      (by calc
        cycleEdges σ⁻¹ = cycleEdges σ := cycleEdges_inv σ
        _ = cycleEdges τ := hedges) (by
        simpa [Equiv.Perm.support_inv] using! hu)
    exact hinv.symm

lemma forest_cycle_disjoint {k : ℕ} {σ : Equiv.Perm (Fin k)}
    (F : RootedForest k σ.support) :
    Disjoint F.1 (cycleEdges σ) := by
  rw [Finset.disjoint_left]
  intro e heF heC
  obtain ⟨h1, h2⟩ := cycleEdges_mono_support heC
  let S := componentOf F.1 e.val.1
  have hS : S ∈ components F.1 := componentOf_mem_components F.1 e.val.1
  have hs1 : e.val.1 ∈ S := componentOf_self F.1 e.val.1
  have hs2 : e.val.2 ∈ S := mem_componentOf_iff.mpr
    (reach_of_adj ⟨e, heF, Or.inl ⟨rfl, rfl⟩⟩)
  have hroot := (F.2 S hS).2
  have hcardtwo : 1 < (S ∩ σ.support).card :=
    Finset.one_lt_card.mpr
      ⟨e.val.1, Finset.mem_inter.mpr ⟨hs1, h1⟩,
        e.val.2, Finset.mem_inter.mpr ⟨hs2, h2⟩,
        ne_of_lt e.property⟩
  omega

lemma rootedForest_isAcyclic {k : ℕ} {roots : Finset (Fin k)}
    (F : RootedForest k roots) :
    (simpleGraph F.1).IsAcyclic := by
  by_cases hfull : roots.card = k
  · have hru : roots = Finset.univ := by
      apply Finset.eq_univ_of_card
      simpa using! hfull
    subst roots
    have hempty : F.1 = ∅ := full_roots_force_empty F.2
    rw [hempty]
    have hbot : simpleGraph (∅ : Graph k) = (⊥ : SimpleGraph (Fin k)) := by
      ext u v
      simp [simpleGraph, adj]
    rw [hbot]
    exact bot_isAcyclic
  · have hle : roots.card ≤ k := by
      simpa using! Finset.card_le_univ roots
    have hproper : roots.card < k := by omega
    have hnonempty : roots ≠ ∅ := by
      intro h
      subst roots
      have hk : 0 < k := by omega
      let u : Fin k := ⟨0, hk⟩
      have hc := (F.2 (componentOf F.1 u)
        (componentOf_mem_components F.1 u)).2
      simpa using! hc
    obtain ⟨code, hcode⟩ := decodeRootedForest_surjective hproper hnonempty F
    subst F
    exact decodeAux_isAcyclic roots (codeList code)
      (codeList_card hproper code) (codeList_anchored code)

lemma simpleGraph_erase {k : ℕ} (G : Graph k) (e : Edge k) :
    simpleGraph (G.erase e) =
      (simpleGraph G).deleteEdges {edgeSym2 e} := by
  ext u v
  simp only [simpleGraph_adj]
  constructor
  · rintro ⟨f, hf, hends⟩
    have hf' := Finset.mem_erase.mp hf
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨⟨f, hf'.2, hends⟩, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro heq
    apply hf'.1
    apply edgeSym2_injective
    calc
      edgeSym2 f = s(u, v) := by
        unfold edgeSym2
        rcases hends with h | h
        · simp [h.1, h.2]
        · simpa [h.1, h.2] using! Sym2.eq_swap
      _ = edgeSym2 e := heq
  · intro h
    rw [SimpleGraph.deleteEdges_adj] at h
    rcases h.1 with ⟨f, hf, hends⟩
    refine ⟨f, Finset.mem_erase.mpr ⟨?_, hf⟩, hends⟩
    intro hfe
    subst f
    exact h.2 (by
      simp only [Set.mem_singleton_iff]
      rcases hends with hends | hends
      · unfold edgeSym2
        simp [hends.1, hends.2]
      · unfold edgeSym2
        simpa [hends.1, hends.2] using! Sym2.eq_swap)

lemma cycleGraph_isCycles {k : ℕ} {σ : Equiv.Perm (Fin k)}
    (hσ : σ.IsCycle) (hlen : 3 ≤ σ.support.card) :
    (simpleGraph (cycleEdges σ)).IsCycles := by
  intro u hneigh
  have hu : u ∈ σ.support := by
    obtain ⟨v, hv⟩ := hneigh
    rw [SimpleGraph.mem_neighborSet, simpleGraph_adj,
      adj_cycleEdges_iff] at hv
    exact support_of_cycle_edge_left hv.1 hv.2
  have hpair : (simpleGraph (cycleEdges σ)).neighborSet u =
      {σ u, σ⁻¹ u} := by
    ext v
    simp only [SimpleGraph.mem_neighborSet, simpleGraph_adj,
      adj_cycleEdges_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨huv, h | h⟩
      · exact Or.inl h.symm
      · exact Or.inr (by apply σ.injective; simpa using! h)
    · rintro (rfl | rfl)
      · exact ⟨(Equiv.Perm.mem_support.mp hu).symm, Or.inl rfl⟩
      · refine ⟨?_, Or.inr ?_⟩
        · intro hfix
          have : σ u = u := by simpa using! congrArg σ hfix
          exact Equiv.Perm.mem_support.mp hu this
        · simp
  rw [hpair, Set.ncard_pair]
  have hne : σ u ≠ σ⁻¹ u := by
    intro heq
    have hσ2 : (σ ^ 2) u = u := by
      simp only [pow_two, Equiv.Perm.mul_apply]
      simpa using! congrArg σ heq
    have hp2 : σ ^ 2 = 1 :=
      (hσ.pow_eq_one_iff' (Equiv.Perm.mem_support.mp hu)).2 hσ2
    have hord := orderOf_le_of_pow_eq_one (by omega) hp2
    rw [hσ.orderOf] at hord
    omega
  exact hne

lemma reach_mono {k : ℕ} {F G : Graph k} (hFG : F ⊆ G)
    {u v : Fin k} (h : reach F u v) : reach G u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h huv ih =>
      exact Relation.ReflTransGen.tail ih (by
        rcases huv with ⟨e, he, hend⟩
        exact ⟨e, hFG he, hend⟩)

/-- Oriented cycle plus a forest rooted on precisely its support. -/
structure OrientedCycleForest (k r : ℕ) where
  cycle : Equiv.Perm (Fin k)
  isCycle : cycle.IsCycle
  support_card : cycle.support.card = r
  three_le : 3 ≤ r
  forest : RootedForest k cycle.support

noncomputable instance (k r : ℕ) : Fintype (OrientedCycleForest k r) := by
  let Aux := {p : Σ σ : Equiv.Perm (Fin k), RootedForest k σ.support //
    p.1.IsCycle ∧ p.1.support.card = r ∧ 3 ≤ r}
  letI : Fintype Aux := Fintype.ofFinite _
  exact Fintype.ofEquiv Aux
    { toFun := fun d => ⟨d.1.1, d.2.1, d.2.2.1, d.2.2.2, d.1.2⟩
      invFun := fun d => ⟨⟨d.cycle, d.forest⟩,
        d.isCycle, d.support_card, d.three_le⟩
      left_inv := fun d => by cases d with | mk val property => cases val; rfl
      right_inv := fun d => by cases d; rfl }

def assemble {k r : ℕ} (d : OrientedCycleForest k r) : Graph k :=
  d.forest.1 ∪ cycleEdges d.cycle

def reverseDatum {k r : ℕ} (d : OrientedCycleForest k r) :
    OrientedCycleForest k r where
  cycle := d.cycle⁻¹
  isCycle := d.isCycle.inv
  support_card := by simpa [Equiv.Perm.support_inv] using! d.support_card
  three_le := d.three_le
  forest := ⟨d.forest.1, by
    simpa [Equiv.Perm.support_inv] using! d.forest.2⟩

@[simp] lemma assemble_reverseDatum {k r : ℕ}
    (d : OrientedCycleForest k r) :
    assemble (reverseDatum d) = assemble d := by
  simp [assemble, reverseDatum, cycleEdges_inv]

lemma OrientedCycleForest.ext' {k r : ℕ}
    {d e : OrientedCycleForest k r}
    (hc : d.cycle = e.cycle) (hf : d.forest.1 = e.forest.1) : d = e := by
  cases d with
  | mk dc dhc dcard dthree df =>
    cases e with
    | mk ec ehc ecard ethree ef =>
      dsimp at hc hf
      subst ec
      have hef : df = ef := Subtype.ext hf
      subst ef
      rfl

lemma cycle_edge_not_bridge_assemble {k r : ℕ}
    (d : OrientedCycleForest k r) {e : Edge k}
    (he : e ∈ cycleEdges d.cycle) :
    ¬ (simpleGraph (assemble d)).IsBridge (edgeSym2 e) := by
  intro hbridge
  have hadjC : (simpleGraph (cycleEdges d.cycle)).Adj e.val.1 e.val.2 :=
    ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
  have hreachC := (cycleGraph_isCycles d.isCycle
    (by simpa [d.support_card] using! d.three_le)).reachable_deleteEdges hadjC
  have hle : simpleGraph (cycleEdges d.cycle) ≤ simpleGraph (assemble d) := by
    intro u v huv
    rcases huv with ⟨f, hf, hends⟩
    exact ⟨f, Finset.subset_union_right hf, hends⟩
  have hdel : (simpleGraph (cycleEdges d.cycle)).deleteEdges {edgeSym2 e} ≤
      (simpleGraph (assemble d)).deleteEdges {edgeSym2 e} := by
    exact SimpleGraph.deleteEdges_mono hle
  have hreach := SimpleGraph.Reachable.mono hdel hreachC
  have hb := (SimpleGraph.isBridge_iff.mp hbridge)
  exact hb hreach

lemma forest_edge_bridge_assemble {k r : ℕ}
    (d : OrientedCycleForest k r) {e : Edge k}
    (he : e ∈ d.forest.1) :
    (simpleGraph (assemble d)).IsBridge (edgeSym2 e) := by
  let a := e.val.1
  let b := e.val.2
  have hab : a ≠ b := ne_of_lt e.property
  have hadjF : (simpleGraph d.forest.1).Adj a b :=
    ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
  have hbF : (simpleGraph d.forest.1).IsBridge (edgeSym2 e) :=
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp
      (rootedForest_isAcyclic d.forest)) hadjF
  have hnab : ¬ reach (d.forest.1.erase e) a b := by
    intro hreach
    have hsreach : (simpleGraph (d.forest.1.erase e)).Reachable a b :=
      simpleGraph_reachable_iff.mpr hreach
    rw [simpleGraph_erase] at hsreach
    exact (SimpleGraph.isBridge_iff.mp hbF) hsreach
  obtain ⟨root, hroot, haroot⟩ := rootedForest_component_root d.forest a
  let S := componentOf d.forest.1 a
  have hS : S ∈ components d.forest.1 := componentOf_mem_components _ _
  have haS : a ∈ S := componentOf_self _ _
  have hbS : b ∈ S := mem_componentOf_iff.mpr
    (reach_of_adj ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩)
  have hrS : root ∈ S := mem_componentOf_iff.mpr haroot
  have hroot_unique : ∀ z, z ∈ S → z ∈ d.cycle.support → z = root := by
    intro z hzS hzroot
    have hcard := (d.forest.2 S hS).2
    have hz : z ∈ S ∩ d.cycle.support := Finset.mem_inter.mpr ⟨hzS, hzroot⟩
    have hr : root ∈ S ∩ d.cycle.support := Finset.mem_inter.mpr ⟨hrS, hroot⟩
    have hone := Finset.card_eq_one.mp hcard
    obtain ⟨w, hw⟩ := hone
    rw [hw] at hz hr
    simp only [Finset.mem_singleton] at hz hr
    exact hz.trans hr.symm
  have hmonoErase : d.forest.1.erase e ⊆ d.forest.1 :=
    Finset.erase_subset _ _
  by_cases har : reach (d.forest.1.erase e) a root
  · have hbr : ¬ reach (d.forest.1.erase e) b root := by
      intro hbr
      exact hnab (reach_trans har (reach_symm hbr))
    have hba : ¬ reach (d.forest.1.erase e) b a := by
      intro hba
      exact hnab (reach_symm hba)
    apply SimpleGraph.isBridge_iff.mpr
    change ¬((simpleGraph (assemble d)).deleteEdges {edgeSym2 e}).Reachable a b
    rw [← simpleGraph_erase]
    rw [simpleGraph_reachable_iff]
    intro hreach
    have closure : ∀ z, reach ((assemble d).erase e) b z →
        reach (d.forest.1.erase e) b z := by
      intro z hz
      induction hz with
      | refl => exact reach_refl b
      | tail hxy hyz ih =>
        rename_i x y
        rcases hyz with ⟨f, hf, hends⟩
        have hferase := Finset.mem_erase.mp hf
        have hfunion := Finset.mem_union.mp hferase.2
        rcases hfunion with hfF | hfC
        · exact reach_trans ih (reach_of_adj
            ⟨f, Finset.mem_erase.mpr ⟨hferase.1, hfF⟩, hends⟩)
        · have hsupp := cycleEdges_mono_support hfC
          have hyroot : x ∈ d.cycle.support := by
            rcases hends with hh | hh
            · simpa [hh.1] using! hsupp.1
            · simpa [hh.2] using! hsupp.2
          have hyS : x ∈ S := by
            rw [mem_componentOf_iff]
            exact reach_trans (reach_of_adj
              ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩) (reach_mono hmonoErase ih)
          have hyr : x = root := hroot_unique _ hyS hyroot
          exact False.elim (hbr (hyr ▸ ih))
    exact hba (closure a (reach_symm hreach))
  · apply SimpleGraph.isBridge_iff.mpr
    change ¬((simpleGraph (assemble d)).deleteEdges {edgeSym2 e}).Reachable a b
    rw [← simpleGraph_erase]
    rw [simpleGraph_reachable_iff]
    intro hreach
    have closure : ∀ z, reach ((assemble d).erase e) a z →
        reach (d.forest.1.erase e) a z := by
      intro z hz
      induction hz with
      | refl => exact reach_refl a
      | tail hxy hyz ih =>
        rename_i x y
        rcases hyz with ⟨f, hf, hends⟩
        have hferase := Finset.mem_erase.mp hf
        have hfunion := Finset.mem_union.mp hferase.2
        rcases hfunion with hfF | hfC
        · exact reach_trans ih (reach_of_adj
            ⟨f, Finset.mem_erase.mpr ⟨hferase.1, hfF⟩, hends⟩)
        · have hsupp := cycleEdges_mono_support hfC
          have hyroot : x ∈ d.cycle.support := by
            rcases hends with hh | hh
            · simpa [hh.1] using! hsupp.1
            · simpa [hh.2] using! hsupp.2
          have hyS : x ∈ S := by
            rw [mem_componentOf_iff]
            exact reach_mono hmonoErase ih
          have hyr : x = root := hroot_unique _ hyS hyroot
          exact False.elim (har (hyr ▸ ih))
    exact hnab (closure b hreach)

lemma mem_cycleEdges_iff_nonbridge {k r : ℕ}
    (d : OrientedCycleForest k r) (e : Edge k) :
    e ∈ cycleEdges d.cycle ↔
      e ∈ assemble d ∧
        ¬ (simpleGraph (assemble d)).IsBridge (edgeSym2 e) := by
  constructor
  · intro he
    exact ⟨Finset.mem_union_right _ he,
      cycle_edge_not_bridge_assemble d he⟩
  · rintro ⟨heG, hnbridge⟩
    rcases Finset.mem_union.mp heG with heF | heC
    · exact False.elim (hnbridge (forest_edge_bridge_assemble d heF))
    · exact heC

lemma cycleEdges_eq_of_assemble_eq {k r s : ℕ}
    (d : OrientedCycleForest k r) (e : OrientedCycleForest k s)
    (h : assemble d = assemble e) :
    cycleEdges d.cycle = cycleEdges e.cycle := by
  ext f
  rw [mem_cycleEdges_iff_nonbridge d, mem_cycleEdges_iff_nonbridge e, h]

lemma forest_eq_of_assemble_eq {k r s : ℕ}
    (d : OrientedCycleForest k r) (e : OrientedCycleForest k s)
    (h : assemble d = assemble e) :
    d.forest.1 = e.forest.1 := by
  have hc := cycleEdges_eq_of_assemble_eq d e h
  ext f
  have hdDis := Finset.disjoint_left.mp (forest_cycle_disjoint d.forest)
  have heDis := Finset.disjoint_left.mp (forest_cycle_disjoint e.forest)
  constructor
  · intro hf
    have hfG : f ∈ assemble e := by
      rw [← h]
      exact Finset.mem_union_left _ hf
    rcases Finset.mem_union.mp hfG with hfE | hfC
    · exact hfE
    · exact False.elim (hdDis hf (hc ▸ hfC))
  · intro hf
    have hfG : f ∈ assemble d := by
      rw [h]
      exact Finset.mem_union_left _ hf
    rcases Finset.mem_union.mp hfG with hfD | hfC
    · exact hfD
    · exact False.elim (heDis hf (hc.symm ▸ hfC))

lemma assemble_eq_iff {k r : ℕ}
    (d e : OrientedCycleForest k r) :
    assemble d = assemble e ↔ e = d ∨ e = reverseDatum d := by
  constructor
  · intro h
    have hc := cycleEdges_eq_of_assemble_eq d e h
    have hperm := cycle_perm_eq_or_inv_of_edges_eq d.isCycle e.isCycle
      (by simpa [d.support_card] using! d.three_le)
      (by simpa [e.support_card] using! e.three_le) hc
    have hf := forest_eq_of_assemble_eq d e h
    rcases hperm with hcycle | hcycle
    · left
      apply OrientedCycleForest.ext'
      · exact hcycle
      · exact hf.symm
    · right
      apply OrientedCycleForest.ext'
      · exact hcycle
      · simpa [reverseDatum] using! hf.symm
  · rintro (rfl | rfl)
    · rfl
    · exact (assemble_reverseDatum d).symm

@[simp] lemma reverseDatum_cycle {k r : ℕ} (d : OrientedCycleForest k r) :
    (reverseDatum d).cycle = d.cycle⁻¹ := rfl

lemma reverseDatum_ne {k r : ℕ} (d : OrientedCycleForest k r) :
    reverseDatum d ≠ d := by
  intro h
  have hinv : d.cycle⁻¹ = d.cycle := congrArg OrientedCycleForest.cycle h
  have hp2 : d.cycle ^ 2 = 1 := by
    calc
      d.cycle ^ 2 = d.cycle * d.cycle := pow_two _
      _ = d.cycle⁻¹ * d.cycle := by rw [hinv]
      _ = 1 := by simp
  have hord := orderOf_le_of_pow_eq_one (by omega) hp2
  rw [d.isCycle.orderOf, d.support_card] at hord
  exact (not_lt_of_ge d.three_le) (lt_of_le_of_lt hord (by omega))

@[simp] lemma reverseDatum_reverseDatum {k r : ℕ}
    (d : OrientedCycleForest k r) :
    reverseDatum (reverseDatum d) = d := by
  apply OrientedCycleForest.ext'
  · simp [reverseDatum]
  · rfl

lemma assemble_card {k r : ℕ} (d : OrientedCycleForest k r) :
    (assemble d).card = k := by
  rw [assemble, Finset.card_union_of_disjoint (forest_cycle_disjoint d.forest),
    rootedForest_edge_card d.forest,
    cycleEdges_card d.isCycle (by simpa [d.support_card] using! d.three_le),
    d.support_card]
  have hrk : r ≤ k := by
    rw [← d.support_card]
    simpa using! Finset.card_le_univ d.cycle.support
  omega

lemma assemble_connected {k r : ℕ} (d : OrientedCycleForest k r) :
    ∀ u v : Fin k, reach (assemble d) u v := by
  intro u v
  obtain ⟨ru, hru, hureach⟩ := rootedForest_component_root d.forest u
  obtain ⟨rv, hrv, hvreach⟩ := rootedForest_component_root d.forest v
  have hFC : d.forest.1 ⊆ assemble d := Finset.subset_union_left
  have hCC : cycleEdges d.cycle ⊆ assemble d := Finset.subset_union_right
  exact reach_trans (reach_mono hFC hureach)
    (reach_trans (reach_mono hCC
      (reach_cycle_support d.isCycle hru hrv))
      (reach_symm (reach_mono hFC hvreach)))

abbrev ConnectedKGraph (k : ℕ) :=
  {G : Graph k // G.card = k ∧ ∀ u v : Fin k, reach G u v}

noncomputable instance (k : ℕ) : Fintype (ConnectedKGraph k) :=
  Fintype.ofFinite _

lemma card_connectedKGraph {k : ℕ} (hk : 0 < k) :
    Fintype.card (ConnectedKGraph k) = connectedCount k k := by
  classical
  simp only [Fintype.card_subtype]
  unfold connectedCount fixedGraphs allGraphs
  apply congrArg Finset.card
  ext G
  simp [hk, Finset.mem_powersetCard, and_left_comm, and_assoc]

abbrev CyclePerm (k r : ℕ) :=
  {σ : Equiv.Perm (Fin k) // σ.cycleType = ({r} : Multiset ℕ)}

noncomputable def cycleForestSigmaEquiv {k r : ℕ} (hr : 3 ≤ r) :
    OrientedCycleForest k r ≃
      Σ σ : CyclePerm k r, RootedForest k σ.1.support where
  toFun d := ⟨⟨d.cycle, by simpa [d.support_card] using! d.isCycle.cycleType⟩,
    d.forest⟩
  invFun d := by
    have hcyc : d.1.1.IsCycle := by
      rw [← Equiv.Perm.card_cycleType_eq_one]
      simp [d.1.2]
    have hcard : d.1.1.support.card = r := by
      have hs := hcyc.cycleType
      rw [d.1.2] at hs
      simpa using! hs.symm
    exact ⟨d.1.1, hcyc, hcard, hr, d.2⟩
  left_inv d := by cases d; rfl
  right_inv d := by cases d; rfl

lemma card_cyclePerm {k r : ℕ} (hr : 3 ≤ r) (hrk : r ≤ k) :
    Fintype.card (CyclePerm k r) =
      (r - 1).factorial * k.choose r := by
  simpa [CyclePerm, Fintype.card_subtype]
    using! (Equiv.Perm.card_of_cycleType_singleton
      (α := Fin k) (by omega : 2 ≤ r) (by simpa using! hrk))

lemma card_orientedCycleForest
    (hforest : W01_ENUM_Trees.RootedForestFormula)
    {k r : ℕ} (hr : 3 ≤ r) (hrk : r ≤ k) :
    Fintype.card (OrientedCycleForest k r) =
      ((r - 1).factorial * k.choose r) *
        (if r = k then 1 else r * k ^ (k - r - 1)) := by
  rw [Fintype.card_congr (cycleForestSigmaEquiv hr), Fintype.card_sigma]
  calc
    (∑ σ : CyclePerm k r,
        Fintype.card (RootedForest k σ.1.support)) =
        ∑ _σ : CyclePerm k r,
          (if r = k then 1 else r * k ^ (k - r - 1)) := by
      apply Finset.sum_congr rfl
      intro σ _
      have hcyc : σ.1.IsCycle := by
        rw [← Equiv.Perm.card_cycleType_eq_one]
        simp [σ.2]
      have hcard : σ.1.support.card = r := by
        have hs := hcyc.cycleType
        rw [σ.2] at hs
        simpa using! hs.symm
      calc
        Fintype.card (RootedForest k σ.1.support) =
            rootedForestCount k σ.1.support :=
          W01_ENUM_Pruefer.card_rootedForest k σ.1.support
        _ = (if r = k then 1 else r * k ^ (k - r - 1)) := by
          rw [hforest k σ.1.support, hcard]
    _ = Fintype.card (CyclePerm k r) *
        (if r = k then 1 else r * k ^ (k - r - 1)) := by simp
    _ = _ := by rw [card_cyclePerm hr hrk]

/-- The actual unoriented cycle/forest objects, represented by their assembled
edge set.  The preceding bridge classification proves that orientation is the
only multiplicity in this image. -/
abbrev UnorientedCycleForest (k r : ℕ) :=
  {G : Graph k // ∃ d : OrientedCycleForest k r, assemble d = G}

noncomputable instance (k r : ℕ) : Fintype (UnorientedCycleForest k r) :=
  Fintype.ofFinite _

def assembleToRange {k r : ℕ} (d : OrientedCycleForest k r) :
    UnorientedCycleForest k r := ⟨assemble d, d, rfl⟩

noncomputable def fiberBase {k r : ℕ} (G : UnorientedCycleForest k r) :
    OrientedCycleForest k r := G.2.choose

lemma fiberBase_spec {k r : ℕ} (G : UnorientedCycleForest k r) :
    assemble (fiberBase G) = G.1 := G.2.choose_spec

noncomputable def assembleFiberEquiv {k r : ℕ}
    (G : UnorientedCycleForest k r) :
    Fin 2 ≃ {d : OrientedCycleForest k r // assembleToRange d = G} where
  toFun i := if hi : i = 0 then
      ⟨fiberBase G, by
        apply Subtype.ext
        exact fiberBase_spec G⟩
    else
      ⟨reverseDatum (fiberBase G), by
        apply Subtype.ext
        change assemble (reverseDatum (fiberBase G)) = G.1
        rw [assemble_reverseDatum]
        exact fiberBase_spec G⟩
  invFun d := if d.1 = fiberBase G then 0 else 1
  left_inv i := by
    fin_cases i
    · simp
    · simp [reverseDatum_ne]
  right_inv d := by
    have hd : assemble d.1 = assemble (fiberBase G) := by
      have h1 := congrArg Subtype.val d.2
      simpa [assembleToRange, fiberBase_spec] using! h1
    rcases (assemble_eq_iff (fiberBase G) d.1).mp hd.symm with h | h
    · simp only [h, ↓reduceIte]
      exact Subtype.ext h.symm
    · simp only [h, reverseDatum_ne, ↓reduceIte]
      exact Subtype.ext h.symm

lemma card_oriented_eq_two_mul_unoriented {k r : ℕ} :
    Fintype.card (OrientedCycleForest k r) =
      2 * Fintype.card (UnorientedCycleForest k r) := by
  calc
    Fintype.card (OrientedCycleForest k r) =
        Fintype.card
          (Σ G : UnorientedCycleForest k r,
            {d : OrientedCycleForest k r // assembleToRange d = G}) :=
      Fintype.card_congr (Equiv.sigmaFiberEquiv assembleToRange).symm
    _ = ∑ G : UnorientedCycleForest k r,
          Fintype.card
            {d : OrientedCycleForest k r // assembleToRange d = G} :=
      Fintype.card_sigma
    _ = ∑ _G : UnorientedCycleForest k r, 2 := by
      apply Finset.sum_congr rfl
      intro G _
      exact Fintype.card_congr (assembleFiberEquiv G).symm
    _ = 2 * Fintype.card (UnorientedCycleForest k r) := by
      simp [mul_comm]

end Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Cycle
