module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W06_P03
public import Erdos745.WrapUp.Proofs.Internal.Linked.W04_Foundation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


namespace Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_Finite

noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

def treeClass {n : ℕ} (G : Graph n) (k : ℕ) : Finset (Finset (Fin n)) :=
  (components G).filter (fun S => isTree G S ∧ S.card = k)

def treeComponentCount {n : ℕ} (G : Graph n) (k : ℕ) : ℕ :=
  (treeClass G k).card

def treeMassSum {n : ℕ} (G : Graph n) (s : Finset ℕ) : ℝ :=
  ∑ k ∈ s, (k : ℝ) * treeComponentCount G k

def pairSizes (k l : ℕ) : Fin 2 → ℕ :=
  fun i => if i.val = 0 then k else l

def orderedTreePairs {n : ℕ} (G : Graph n) (k l : ℕ) :
    Finset (Finset (Fin n) × Finset (Fin n)) :=
  ((treeClass G k).product (treeClass G l)).filter (fun p => p.1 ≠ p.2)

lemma treeTupleCount_one {n k : ℕ} (G : Graph n) :
    treeTupleCount G 1 (fun _ => k) = treeComponentCount G k := by
  unfold treeTupleCount treeComponentCount treeClass
  apply Finset.card_bij (fun C _ => C 0)
  · intro C hC
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC
    exact Finset.mem_filter.mpr ⟨(hC.2 0).1.1, hC.2 0⟩
  · intro C₁ hC₁ C₂ hC₂ hzero
    funext i
    simpa [Subsingleton.elim i 0] using! hzero
  · intro S hS
    simp only [Finset.mem_filter] at hS
    let C : Fin 1 → Finset (Fin n) := fun _ => S
    refine ⟨C, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun i j _ => Subsingleton.elim i j, ?_⟩
    intro i
    simpa [C] using! hS.2

lemma treeTupleCount_two {n k l : ℕ} (G : Graph n) :
    treeTupleCount G 2 (pairSizes k l) = (orderedTreePairs G k l).card := by
  unfold treeTupleCount orderedTreePairs treeClass
  apply Finset.card_bij (fun C _ => (C 0, C 1))
  · intro C hC
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC
    have h0 := hC.2 0
    have h1 := hC.2 1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_filter.mpr ⟨h0.1.1, by simpa [pairSizes] using! h0⟩
    · exact Finset.mem_filter.mpr ⟨h1.1.1, by simpa [pairSizes] using! h1⟩
    · intro heq
      have h01 : (0 : Fin 2) = 1 := hC.1 heq
      omega
  · intro C₁ hC₁ C₂ hC₂ hpair
    funext i
    fin_cases i
    · exact congrArg Prod.fst hpair
    · exact congrArg Prod.snd hpair
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hprod := Finset.mem_product.mp hp'.1
    have hp0 := Finset.mem_filter.mp hprod.1
    have hp1 := Finset.mem_filter.mp hprod.2
    let C : Fin 2 → Finset (Fin n) := ![p.1, p.2]
    refine ⟨C, ?_, by simp [C]⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · simpa [C, injective_pair_iff_ne] using! hp'.2
    · intro i
      fin_cases i
      · simpa [C, pairSizes] using! hp0.2
      · simpa [C, pairSizes] using! hp1.2

private lemma equal_pairs_card {α : Type*} [DecidableEq α] (s : Finset α) :
    ((s.product s).filter (fun p => ¬p.1 ≠ p.2)).card = s.card := by
  apply Finset.card_bij (fun p _ => p.1)
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact (Finset.mem_product.mp hp'.1).1
  · intro p hp q hq heq
    have hp' := Finset.mem_filter.mp hp
    have hq' := Finset.mem_filter.mp hq
    have hpeq : p.1 = p.2 := not_ne_iff.mp hp'.2
    have hqeq : q.1 = q.2 := not_ne_iff.mp hq'.2
    apply Prod.ext
    · exact heq
    · exact hpeq.symm.trans (heq.trans hqeq)
  · intro a ha
    exact ⟨(a, a), by simp [ha], rfl⟩

lemma pair_count_identity {n : ℕ} (G : Graph n) (k l : ℕ) :
    treeComponentCount G k * treeComponentCount G l =
      (if k = l then treeComponentCount G k else 0) +
        treeTupleCount G 2 (pairSizes k l) := by
  rw [treeTupleCount_two]
  unfold orderedTreePairs treeComponentCount
  by_cases hkl : k = l
  · subst l
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := (treeClass G k).product (treeClass G k)) (fun p => p.1 ≠ p.2)
    rw [equal_pairs_card] at hpartition
    simp only [ite_true]
    rw [← Finset.card_product]
    simpa [Nat.add_comm] using! hpartition.symm
  · have hneq : ∀ p ∈ (treeClass G k).product (treeClass G l), p.1 ≠ p.2 := by
      intro p hp heq
      have hp' := Finset.mem_product.mp hp
      have hk := (Finset.mem_filter.mp hp'.1).2.2
      have hl := (Finset.mem_filter.mp hp'.2).2.2
      exact hkl (hk.symm.trans (congrArg Finset.card heq) |>.trans hl)
    rw [Finset.filter_eq_self.2 hneq, if_neg hkl, zero_add]
    exact (Finset.card_product (treeClass G k) (treeClass G l)).symm

lemma treeMassBelow_eq_sum {n h : ℕ} (G : Graph n) :
    treeMassBelow G h =
      ∑ k ∈ Finset.Ico 1 h, (k : ℝ) * treeComponentCount G k := by
  unfold treeMassBelow treeComponentCount treeClass
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases ht : isTree G S ∧ S.card < h
  · have hk : S.card ∈ Finset.Ico 1 h := by
      refine Finset.mem_Ico.mpr ⟨?_, ht.2⟩
      have hnonempty : S.Nonempty := by
        rw [components, Finset.mem_image] at hS
        obtain ⟨v, -, rfl⟩ := hS
        refine ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, ?_⟩⟩
        exact Relation.ReflTransGen.refl
      exact Finset.card_pos.mpr hnonempty
    rw [if_pos ht]
    rw [Finset.sum_eq_single S.card]
    · simp [hS, ht.1]
    · intro b hb hne
      have : ¬S.card = b := Ne.symm hne
      simp [this]
    · exact fun hnot => (hnot hk).elim
  · rw [if_neg ht]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hcard : S.card = k
    · have hk' := Finset.mem_Ico.mp hk
      have hnotTree : ¬isTree G S := by
        intro htree
        exact ht ⟨htree, hcard.trans_lt hk'.2⟩
      simp [hnotTree]
    · simp [hcard]

lemma treeMassSum_sq_eq {n : ℕ} (G : Graph n) (s : Finset ℕ) :
    treeMassSum G s ^ 2 =
      (∑ k ∈ s, (k : ℝ) ^ 2 * treeComponentCount G k) +
      ∑ k ∈ s, ∑ l ∈ s,
        (k : ℝ) * l * treeTupleCount G 2 (pairSizes k l) := by
  unfold treeMassSum
  have hterm (k l : ℕ) :
      ((k : ℝ) * treeComponentCount G k) *
          ((l : ℝ) * treeComponentCount G l) =
        (k : ℝ) * l * (if k = l then treeComponentCount G k else 0) +
          (k : ℝ) * l * treeTupleCount G 2 (pairSizes k l) := by
    have hcount :
        (treeComponentCount G k : ℝ) * treeComponentCount G l =
          (if k = l then treeComponentCount G k else 0) +
            treeTupleCount G 2 (pairSizes k l) := by
      exact_mod_cast pair_count_identity G k l
    calc
      ((k : ℝ) * treeComponentCount G k) *
          ((l : ℝ) * treeComponentCount G l) =
          (k : ℝ) * l *
            ((treeComponentCount G k : ℝ) * treeComponentCount G l) := by ring
      _ = _ := by rw [hcount]; ring
  calc
    (∑ k ∈ s, (k : ℝ) * treeComponentCount G k) ^ 2 =
        ∑ k ∈ s, ∑ l ∈ s,
          ((k : ℝ) * treeComponentCount G k) *
            ((l : ℝ) * treeComponentCount G l) := by
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
    _ = (∑ k ∈ s, ∑ l ∈ s,
          (k : ℝ) * l * (if k = l then treeComponentCount G k else 0)) +
        ∑ k ∈ s, ∑ l ∈ s,
          (k : ℝ) * l * treeTupleCount G 2 (pairSizes k l) := by
      simp_rw [hterm, Finset.sum_add_distrib]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_eq_single k]
      · simp [pow_two]
      · intro l hl hlk
        simp [Ne.symm hlk]
      · exact fun hnot => (hnot hk).elim

lemma expectM_nonneg {n M : ℕ} {f : Graph n → ℝ}
    (hf : ∀ G, 0 ≤ f G) : 0 ≤ expectM n M f := by
  unfold expectM
  exact div_nonneg (Finset.sum_nonneg fun G _ => hf G) (by positivity)

lemma expectM_mono {n M : ℕ} {f g : Graph n → ℝ}
    (hfg : ∀ G, f G ≤ g G) : expectM n M f ≤ expectM n M g := by
  unfold expectM
  apply div_le_div_of_nonneg_right
  · exact Finset.sum_le_sum fun G _ => hfg G
  · positivity

lemma expectM_add {n M : ℕ} (f g : Graph n → ℝ) :
    expectM n M (fun G => f G + g G) = expectM n M f + expectM n M g := by
  unfold expectM
  rw [Finset.sum_add_distrib]
  ring

lemma expectM_sub {n M : ℕ} (f g : Graph n → ℝ) :
    expectM n M (fun G => f G - g G) = expectM n M f - expectM n M g := by
  unfold expectM
  rw [Finset.sum_sub_distrib]
  ring

lemma expectM_mul_const {n M : ℕ} (f : Graph n → ℝ) (c : ℝ) :
    expectM n M (fun G => f G * c) = expectM n M f * c := by
  unfold expectM
  rw [← Finset.sum_mul]
  ring

lemma expectM_const {n M : ℕ} (hNorm : expectM n M (fun _ => 1) = 1) (c : ℝ) :
    expectM n M (fun _ => c) = c := by
  have h := expectM_mul_const (n := n) (M := M) (fun _ => 1) c
  simpa [hNorm] using! h

lemma expectM_finset_sum {ι : Type*} {s : Finset ι} {n M : ℕ}
    (f : ι → Graph n → ℝ) :
    expectM n M (fun G => ∑ i ∈ s, f i G) =
      ∑ i ∈ s, expectM n M (f i) := by
  unfold expectM
  rw [Finset.sum_comm]
  simp only [Finset.sum_div]

lemma tupleMoment_one_eq_expect {n M k : ℕ} :
    tupleMoment n M 1 (fun _ => k) =
      expectM n M (fun G => (treeComponentCount G k : ℝ)) := by
  unfold tupleMoment
  congr 1
  funext G
  rw [treeTupleCount_one]

lemma expect_treeMassBelow {n M h : ℕ} :
    expectM n M (fun G => treeMassBelow G h) =
      ∑ k ∈ Finset.Ico 1 h,
        (k : ℝ) * tupleMoment n M 1 (fun _ => k) := by
  simp_rw [treeMassBelow_eq_sum]
  rw [expectM_finset_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hmul := expectM_mul_const (n := n) (M := M)
    (fun G => (treeComponentCount G k : ℝ)) (k : ℝ)
  calc
    expectM n M (fun G => (k : ℝ) * treeComponentCount G k) =
        expectM n M (fun G => (treeComponentCount G k : ℝ) * k) := by
      congr 1
      funext G
      ring
    _ = expectM n M (fun G => (treeComponentCount G k : ℝ)) * k := hmul
    _ = (k : ℝ) * tupleMoment n M 1 (fun _ => k) := by
      rw [tupleMoment_one_eq_expect]
      ring

lemma expect_treeMassSum {n M : ℕ} (s : Finset ℕ) :
    expectM n M (fun G => treeMassSum G s) =
      ∑ k ∈ s, (k : ℝ) * tupleMoment n M 1 (fun _ => k) := by
  unfold treeMassSum
  rw [expectM_finset_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hmul := expectM_mul_const (n := n) (M := M)
    (fun G => (treeComponentCount G k : ℝ)) (k : ℝ)
  calc
    expectM n M (fun G => (k : ℝ) * treeComponentCount G k) =
        expectM n M (fun G => (treeComponentCount G k : ℝ) * k) := by
      congr 1
      funext G
      ring
    _ = expectM n M (fun G => (treeComponentCount G k : ℝ)) * k := hmul
    _ = (k : ℝ) * tupleMoment n M 1 (fun _ => k) := by
      rw [tupleMoment_one_eq_expect]
      ring

lemma expect_treeMassSum_sq {n M : ℕ} (s : Finset ℕ) :
    expectM n M (fun G => treeMassSum G s ^ 2) =
      (∑ k ∈ s, (k : ℝ) ^ 2 * tupleMoment n M 1 (fun _ => k)) +
      ∑ k ∈ s, ∑ l ∈ s,
        (k : ℝ) * l * tupleMoment n M 2 (pairSizes k l) := by
  simp_rw [treeMassSum_sq_eq]
  rw [expectM_add]
  congr 1
  · rw [expectM_finset_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hmul := expectM_mul_const (n := n) (M := M)
      (fun G => (treeComponentCount G k : ℝ)) ((k : ℝ) ^ 2)
    calc
      expectM n M (fun G => (k : ℝ) ^ 2 * treeComponentCount G k) =
          expectM n M (fun G => (treeComponentCount G k : ℝ) * k ^ 2) := by
        congr 1
        funext G
        ring
      _ = expectM n M (fun G => (treeComponentCount G k : ℝ)) * k ^ 2 := hmul
      _ = (k : ℝ) ^ 2 * tupleMoment n M 1 (fun _ => k) := by
        rw [tupleMoment_one_eq_expect]
        ring
  · rw [expectM_finset_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [expectM_finset_sum]
    apply Finset.sum_congr rfl
    intro l hl
    unfold tupleMoment expectM
    rw [← Finset.mul_sum]
    ring

lemma treeMassBelow_split {n h H : ℕ} (G : Graph n) (hH : H + 1 ≤ h) :
    treeMassBelow G h =
      treeMassSum G (Finset.Ico 1 (H + 1)) +
        treeMassSum G (Finset.Ico (H + 1) h) := by
  rw [treeMassBelow_eq_sum]
  unfold treeMassSum
  exact (Finset.sum_Ico_consecutive
    (fun k => (k : ℝ) * treeComponentCount G k)
    (by omega : 1 ≤ H + 1) hH).symm

lemma variance_eq_second_sub_sq {n M : ℕ} (f : Graph n → ℝ)
    (hNorm : expectM n M (fun _ => 1) = 1) :
    varianceM n M f = expectM n M (fun G => f G ^ 2) - (expectM n M f) ^ 2 := by
  unfold varianceM
  have hpoint : (fun G => (f G - expectM n M f) ^ 2) =
      fun G => f G ^ 2 - 2 * f G * expectM n M f + (expectM n M f) ^ 2 := by
    funext G
    ring
  rw [hpoint, expectM_add, expectM_sub]
  have hmul := expectM_mul_const (n := n) (M := M) f (2 * expectM n M f)
  have hconst := expectM_const (n := n) (M := M) hNorm ((expectM n M f) ^ 2)
  rw [hconst]
  have : expectM n M (fun G => 2 * f G * expectM n M f) =
      expectM n M f * (2 * expectM n M f) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using! hmul
  rw [this]
  ring

lemma variance_nonneg {n M : ℕ} (f : Graph n → ℝ) :
    0 ≤ varianceM n M f := by
  unfold varianceM
  apply expectM_nonneg
  intro G
  positivity

lemma variance_le_second {n M : ℕ} (f : Graph n → ℝ)
    (hNorm : expectM n M (fun _ => 1) = 1) :
    varianceM n M f ≤ expectM n M (fun G => f G ^ 2) := by
  rw [variance_eq_second_sub_sq f hNorm]
  nlinarith [sq_nonneg (expectM n M f)]

lemma variance_add_le {n M : ℕ} (f g : Graph n → ℝ) :
    varianceM n M (fun G => f G + g G) ≤
      2 * varianceM n M f + 2 * varianceM n M g := by
  unfold varianceM
  have hadd := expectM_add (n := n) (M := M) f g
  calc
    expectM n M (fun G => (f G + g G - expectM n M (fun G => f G + g G)) ^ 2) ≤
        expectM n M (fun G =>
          2 * (f G - expectM n M f) ^ 2 +
            2 * (g G - expectM n M g) ^ 2) := by
      apply expectM_mono
      intro G
      rw [hadd]
      nlinarith [sq_nonneg ((f G - expectM n M f) -
        (g G - expectM n M g))]
    _ = 2 * expectM n M (fun G => (f G - expectM n M f) ^ 2) +
        2 * expectM n M (fun G => (g G - expectM n M g) ^ 2) := by
      rw [expectM_add]
      have hf := expectM_mul_const (n := n) (M := M)
        (fun G => (f G - expectM n M f) ^ 2) 2
      have hg := expectM_mul_const (n := n) (M := M)
        (fun G => (g G - expectM n M g) ^ 2) 2
      rw [show (fun G => 2 * (f G - expectM n M f) ^ 2) =
          fun G => (f G - expectM n M f) ^ 2 * 2 by
            funext G; ring,
        show (fun G => 2 * (g G - expectM n M g) ^ 2) =
          fun G => (g G - expectM n M g) ^ 2 * 2 by
            funext G; ring,
        hf, hg]
      ring

lemma variance_treeMassSum_eq {n M : ℕ} (s : Finset ℕ)
    (hNorm : expectM n M (fun _ => 1) = 1) :
    varianceM n M (fun G => treeMassSum G s) =
      (∑ k ∈ s, (k : ℝ) ^ 2 * tupleMoment n M 1 (fun _ => k)) +
      ∑ k ∈ s, ∑ l ∈ s,
        ((k : ℝ) * l * tupleMoment n M 2 (pairSizes k l) -
          ((k : ℝ) * tupleMoment n M 1 (fun _ => k)) *
            ((l : ℝ) * tupleMoment n M 1 (fun _ => l))) := by
  rw [variance_eq_second_sub_sq _ hNorm, expect_treeMassSum_sq,
    expect_treeMassSum]
  have hsquare :
      (∑ k ∈ s, (k : ℝ) * tupleMoment n M 1 (fun _ => k)) ^ 2 =
        ∑ k ∈ s, ∑ l ∈ s,
          ((k : ℝ) * tupleMoment n M 1 (fun _ => k)) *
            ((l : ℝ) * tupleMoment n M 1 (fun _ => l)) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mul_sum]
  rw [hsquare]
  simp_rw [Finset.sum_sub_distrib]
  ring

end
end Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_Finite


namespace Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_Analytic

noncomputable section
open Filter
open scoped BigOperators Topology
open Erdos745.WrapUp.Proofs.W06_POISSON
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_Finite

def momentOne (n M k : ℕ) : ℝ := tupleMoment n M 1 (fun _ => k)

def momentTwo (n M k l : ℕ) : ℝ := tupleMoment n M 2 (pairSizes k l)

def massTerm (n M k : ℕ) : ℝ := (k : ℝ) * momentOne n M k

def leadingMassTerm (n M k : ℕ) : ℝ := (k : ℝ) * treeLeading n M k

lemma momentOne_nonneg (n M k : ℕ) : 0 ≤ momentOne n M k := by
  unfold momentOne tupleMoment
  exact W09_TREE_MASS_Finite.expectM_nonneg fun G => by positivity

lemma momentTwo_nonneg (n M k l : ℕ) : 0 ≤ momentTwo n M k l := by
  unfold momentTwo tupleMoment
  exact W09_TREE_MASS_Finite.expectM_nonneg fun G => by positivity

lemma massTerm_nonneg (n M k : ℕ) : 0 ≤ massTerm n M k := by
  unfold massTerm
  exact mul_nonneg (by positivity) (momentOne_nonneg n M k)

lemma leadingMassTerm_nonneg {n M k : ℕ} (hlam : 0 < degreeAt n M) :
    0 ≤ leadingMassTerm n M k := by
  unfold leadingMassTerm treeLeading
  split_ifs
  · positivity
  · positivity

lemma abs_log_ratio_to_relative {x y E : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hlog : |Real.log (x / y)| ≤ E)
    (hE : E ≤ 1) : |x - y| ≤ 2 * y * E := by
  have hratio : 0 < x / y := div_pos hx hy
  have hexp : Real.exp (Real.log (x / y)) = x / y := Real.exp_log hratio
  have habs : |Real.log (x / y)| ≤ 1 := hlog.trans hE
  have hmain := Real.abs_exp_sub_one_le habs
  rw [hexp] at hmain
  have hy0 : 0 ≤ y := hy.le
  calc
    |x - y| = y * |x / y - 1| := by
      have hxy : x - y = y * (x / y - 1) := by
        field_simp [hy.ne']
      rw [hxy, abs_mul, abs_of_pos hy]
    _ ≤ y * (2 * |Real.log (x / y)|) :=
      mul_le_mul_of_nonneg_left hmain hy0
    _ ≤ 2 * y * E := by nlinarith

lemma pairLeading_eq (n M k l : ℕ) :
    tupleLeading n M 2 (pairSizes k l) =
      treeLeading n M k * treeLeading n M l := by
  unfold tupleLeading pairSizes
  simp [Fin.prod_univ_two]

lemma leadingMassTerm_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ n M k : ℕ, 0 < k →
      1 / 2 ≤ degreeAt n M →
      leadingMassTerm n M k ≤ D * (n : ℝ) *
        Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
        Real.exp (-rate (degreeAt n M) * k) := by
  obtain ⟨R, hR, hRb⟩ := cayleyStirlingRatio_bddAbove
  let D := 2 * R / Real.sqrt (2 * Real.pi)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro n M k hk hlo
  have hlam : 0 < degreeAt n M := lt_of_lt_of_le (by norm_num) hlo
  have hdegree : (n : ℝ) / degreeAt n M ≤ 2 * n := by
    apply (div_le_iff₀ hlam).2
    nlinarith [show 0 ≤ (n : ℝ) by positivity]
  have hrpow : (k : ℝ) * Real.rpow (k : ℝ) (-(5 / 2) : ℝ) =
      Real.rpow (k : ℝ) (-(3 / 2) : ℝ) := by
    have hkR : 0 < (k : ℝ) := by positivity
    calc
      (k : ℝ) * Real.rpow (k : ℝ) (-(5 / 2) : ℝ) =
          Real.rpow (k : ℝ) (1 + (-(5 / 2) : ℝ)) := by
        simpa only [Real.rpow_one] using!
          (Real.rpow_add hkR (1 : ℝ) (-(5 / 2) : ℝ)).symm
      _ = _ := by norm_num
  unfold leadingMassTerm
  rw [treeLeading_eq_cayleyKernel n M k hk hlam,
    cayleyKernel_eq_stirling k hk]
  change (k : ℝ) * ((n : ℝ) / degreeAt n M *
      (cayleyStirlingRatio k / Real.sqrt (2 * Real.pi) *
        Real.rpow (k : ℝ) (-(5 / 2) : ℝ)) *
      Real.exp (-rate (degreeAt n M) * (k : ℝ))) ≤ _
  have hratio := hRb k
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hfac : cayleyStirlingRatio k / Real.sqrt (2 * Real.pi) ≤
      R / Real.sqrt (2 * Real.pi) := (div_le_div_iff₀ hsqrt hsqrt).2 (by nlinarith)
  have hratio0 : 0 ≤ cayleyStirlingRatio k / Real.sqrt (2 * Real.pi) :=
    (div_nonneg (cayleyStirlingRatio_pos k hk).le hsqrt.le)
  have hrpow0 : 0 ≤ Real.rpow (k : ℝ) (-(5 / 2) : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have hrpow' : (k : ℝ) * ((k : ℝ) ^ (-(5 / 2) : ℝ)) =
      (k : ℝ) ^ (-(3 / 2) : ℝ) := by
    exact hrpow
  calc
    _ ≤ (k : ℝ) * ((2 * n) *
          (R / Real.sqrt (2 * Real.pi) *
            Real.rpow (k : ℝ) (-(5 / 2) : ℝ)) *
          Real.exp (-rate (degreeAt n M) * (k : ℝ))) := by
      gcongr
    _ = D * (n : ℝ) * Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
          Real.exp (-rate (degreeAt n M) * k) := by
      dsimp [D]
      calc
        (k : ℝ) * (2 * n *
            (R / Real.sqrt (2 * Real.pi) * ((k : ℝ) ^ (-(5 / 2) : ℝ))) *
            Real.exp (-rate (degreeAt n M) * k)) =
            2 * R / Real.sqrt (2 * Real.pi) * n *
              ((k : ℝ) * ((k : ℝ) ^ (-(5 / 2) : ℝ))) *
              Real.exp (-rate (degreeAt n M) * k) := by ring
        _ = _ := by rw [hrpow']

private lemma k_mul_cayley {k : ℕ} (hk : 0 < k) :
    k * cayley k = k ^ (k - 1) := by
  by_cases hk1 : k = 1
  · subst k; simp [cayley]
  · have hk2 : 2 ≤ k := by omega
    rw [cayley_eq_pow_sub_two k hk]
    have he : k - 1 = (k - 2) + 1 := by omega
    rw [he, pow_succ]
    exact Nat.mul_comm _ _

lemma leadingMassTerm_eq_rooted {n M k : ℕ} (hlam : 0 < degreeAt n M) :
    leadingMassTerm n M k =
      (n : ℝ) / degreeAt n M *
        rootedTerm (degreeAt n M * Real.exp (-degreeAt n M)) k := by
  by_cases hk : k = 0
  · subst k
    simp [leadingMassTerm, treeLeading, rootedTerm]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    unfold leadingMassTerm treeLeading rootedTerm
    rw [if_neg hk, if_neg hk]
    have hkc : (k : ℝ) * (cayley k : ℝ) = (k : ℝ) ^ (k - 1) := by
      exact_mod_cast k_mul_cayley hkpos
    calc
      (k : ℝ) *
          ((n : ℝ) / degreeAt n M * (cayley k : ℝ) / (k.factorial : ℝ) *
            (degreeAt n M * Real.exp (-degreeAt n M)) ^ k) =
          (n : ℝ) / degreeAt n M *
            (((k : ℝ) * cayley k) *
              (degreeAt n M * Real.exp (-degreeAt n M)) ^ k /
                (k.factorial : ℝ)) := by ring
      _ = _ := by rw [hkc]

lemma leadingMassTerm_hasSum (hA : AnalyticSumsStatement)
    {n M : ℕ} (hlam : 1 < degreeAt n M) :
    HasSum (leadingMassTerm n M)
      ((n : ℝ) * conjugate (degreeAt n M) / degreeAt n M) := by
  have hseries := hA.1 (degreeAt n M) (zero_lt_one.trans hlam) hlam.ne'
  rw [if_neg (not_lt_of_ge hlam.le)] at hseries
  have hmul := hseries.mul_left ((n : ℝ) / degreeAt n M)
  convert hmul using 1
  · funext k
    exact leadingMassTerm_eq_rooted (zero_lt_one.trans hlam)
  · ring

def negThreeHalfTail (N h : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico h (N + 1), Real.rpow (k : ℝ) (-(3 / 2) : ℝ)

private lemma sum_Ico_negThreeHalf_split (h N : ℕ) (hhN : h ≤ N) :
    (∑ k ∈ Finset.Ico h (N + 1), Real.rpow (k : ℝ) (-(3 / 2) : ℝ)) =
      Real.rpow (h : ℝ) (-(3 / 2) : ℝ) +
        ∑ k ∈ Finset.Ico h N,
          Real.rpow ((k + 1 : ℕ) : ℝ) (-(3 / 2) : ℝ) := by
  induction N, hhN using Nat.le_induction with
  | base => simp
  | succ N hhN ih =>
      conv_lhs => rw [Finset.sum_Ico_succ_top (Nat.le_succ_of_le hhN)]
      rw [ih]
      rw [Finset.sum_Ico_succ_top hhN]
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_succ]
      ring

lemma negThreeHalfTail_le (N h : ℕ) (hh : 0 < h) :
    negThreeHalfTail N h ≤ 3 * Real.rpow (h : ℝ) (-(1 / 2) : ℝ) := by
  by_cases hhN : h ≤ N
  · unfold negThreeHalfTail
    rw [sum_Ico_negThreeHalf_split]
    · have hanti : AntitoneOn (fun x : ℝ => Real.rpow x (-(3 / 2) : ℝ))
          (Set.Icc (h : ℝ) (N : ℝ)) :=
        (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)).mono (by
          intro x hx
          exact lt_of_lt_of_le (by exact_mod_cast hh) hx.1)
      have hsum := hanti.sum_le_integral_Ico hhN
      have hzero : (0 : ℝ) ∉ Set.uIcc (h : ℝ) (N : ℝ) := by
        rw [Set.uIcc_of_le (by exact_mod_cast hhN)]
        intro hz
        exact (not_le_of_gt (by exact_mod_cast hh : (0 : ℝ) < h)) hz.1
      have hintEq : (∫ x : ℝ in (h : ℝ)..(N : ℝ),
          Real.rpow x (-(3 / 2) : ℝ)) =
          (Real.rpow (N : ℝ) (-(1 / 2) : ℝ) -
            Real.rpow (h : ℝ) (-(1 / 2) : ℝ)) / (-(1 / 2) : ℝ) := by
        convert integral_rpow (r := (-(3 / 2) : ℝ))
          (Or.inr ⟨by norm_num, hzero⟩) using 1 <;> norm_num
      have hNnonneg : 0 ≤ Real.rpow (N : ℝ) (-(1 / 2) : ℝ) :=
        Real.rpow_nonneg (by positivity) _
      have hint : (∫ x : ℝ in (h : ℝ)..(N : ℝ),
          Real.rpow x (-(3 / 2) : ℝ)) ≤
          2 * Real.rpow (h : ℝ) (-(1 / 2) : ℝ) := by
        rw [hintEq]
        nlinarith
      have hfirst : Real.rpow (h : ℝ) (-(3 / 2) : ℝ) ≤
          Real.rpow (h : ℝ) (-(1 / 2) : ℝ) := by
        exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hh) (by norm_num)
      nlinarith [hsum.trans hint,
        Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ h) (-(1 / 2) : ℝ)]
    · exact hhN
  · have hempty : Finset.Ico h (N + 1) = ∅ := by
      rw [Finset.Ico_eq_empty]
      omega
    unfold negThreeHalfTail
    rw [hempty]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _)

lemma negThreeHalf_exp_tail_le {N H : ℕ} {u : ℝ}
    (hu : 0 ≤ u) :
    (∑ k ∈ Finset.Ico (H + 1) (N + 1),
      Real.rpow (k : ℝ) (-(3 / 2) : ℝ) * Real.exp (-u * k)) ≤
      3 * Real.rpow ((H + 1 : ℕ) : ℝ) (-(1 / 2) : ℝ) *
        Real.exp (-u * H) := by
  calc
    (∑ k ∈ Finset.Ico (H + 1) (N + 1),
        Real.rpow (k : ℝ) (-(3 / 2) : ℝ) * Real.exp (-u * k)) ≤
        Real.exp (-u * H) * negThreeHalfTail N (H + 1) := by
      unfold negThreeHalfTail
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k hk
      have hkH : H ≤ k := by
        have := (Finset.mem_Ico.mp hk).1
        omega
      have hexp : Real.exp (-u * k) ≤ Real.exp (-u * H) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonpos_left (by exact_mod_cast hkH) (neg_nonpos.mpr hu)
      simpa [mul_comm] using!
        (mul_le_mul_of_nonneg_left hexp
          (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ k) _))
    _ ≤ Real.exp (-u * H) *
        (3 * Real.rpow ((H + 1 : ℕ) : ℝ) (-(1 / 2) : ℝ)) := by
      gcongr
      exact negThreeHalfTail_le N (H + 1) (by omega)
    _ = _ := by ring

lemma analytic_power_bound (hA : AnalyticSumsStatement) (beta : ℝ)
    (hbeta : -1 < beta) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 0 < u → u ≤ 1 →
      Summable (fun k : ℕ => Real.rpow ((k + 1 : ℕ) : ℝ) beta *
        Real.exp (-u * (k + 1))) ∧
      (∑' k : ℕ, Real.rpow ((k + 1 : ℕ) : ℝ) beta *
        Real.exp (-u * (k + 1))) ≤
          C * Real.rpow u (-beta - 1) := by
  exact hA.2.1 beta hbeta

lemma shifted_finite_sum_le_tsum {N : ℕ} (f : ℕ → ℝ)
    (hf : ∀ k, 0 ≤ f k) (hs : Summable (fun j => f (j + 1))) :
    (∑ k ∈ Finset.Ico 1 (N + 1), f k) ≤ ∑' j : ℕ, f (j + 1) := by
  have hshift : (∑ k ∈ Finset.Ico 1 (N + 1), f k) =
      ∑ j ∈ Finset.range N, f (j + 1) := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_add' f 0 N 1]
  rw [hshift]
  exact hs.sum_le_tsum (Finset.range N) (fun j _ => hf (j + 1))

lemma finite_power_exp_sum_le (hA : AnalyticSumsStatement)
    {beta u : ℝ} (hbeta : -1 < beta) (hu : 0 < u) (hu1 : u ≤ 1)
    (H : ℕ) :
    (∑ k ∈ Finset.Ico 1 (H + 1),
      Real.rpow (k : ℝ) beta * Real.exp (-u * k)) ≤
      Classical.choose (analytic_power_bound hA beta hbeta) *
        Real.rpow u (-beta - 1) := by
  let C := Classical.choose (analytic_power_bound hA beta hbeta)
  have hCspec := Classical.choose_spec (analytic_power_bound hA beta hbeta)
  have hs := (hCspec.2 u hu hu1).1
  have hsum := (hCspec.2 u hu hu1).2
  have hfin := shifted_finite_sum_le_tsum (N := H)
    (f := fun k => Real.rpow (k : ℝ) beta * Real.exp (-u * k))
    (fun k => mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le)
    (by simpa [Nat.cast_add, Nat.cast_one] using! hs)
  exact hfin.trans (by simpa [Nat.cast_add, Nat.cast_one] using! hsum)

lemma cutoff_below_large_of_error
    {M : NatSeq} (hbare : bareSub M ∨ bareSuper M) (B : ℝ) (hB : 0 < B) :
    ∀ᶠ n in atTop, nearCutoff B M n < largeCutoff n := by
  have herr := near_cutoff_error_tendsto_zero hbare 1 B 1 hB
  have hlt : ∀ᶠ n in atTop,
      (1 : ℝ) * ((1 : ℝ) * (nearCutoff B M n : ℝ) / n +
        epsilon M n * ((1 : ℝ) * (nearCutoff B M n : ℝ)) ^ 2 / n +
        ((1 : ℝ) * (nearCutoff B M n : ℝ)) ^ 3 / (n : ℝ) ^ 2) < 1 :=
    by simpa using! (tendsto_order.1 herr).2 1 zero_lt_one
  filter_upwards [hlt, eventually_ge_atTop 1] with n hn hn1
  have hnR : 0 < (n : ℝ) := by positivity
  have hthird : (nearCutoff B M n : ℝ) ^ 3 / (n : ℝ) ^ 2 < 1 := by
    have hnonneg1 : 0 ≤ (nearCutoff B M n : ℝ) / n := by positivity
    have hnonneg2 : 0 ≤ epsilon M n * (nearCutoff B M n : ℝ) ^ 2 / n := by
      exact div_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _)) (by positivity)
    norm_num at hn
    have hle : (nearCutoff B M n : ℝ) ^ 3 / (n : ℝ) ^ 2 ≤
        (nearCutoff B M n : ℝ) / n +
          epsilon M n * (nearCutoff B M n : ℝ) ^ 2 / n +
          (nearCutoff B M n : ℝ) ^ 3 / (n : ℝ) ^ 2 := by nlinarith
    exact hle.trans_lt hn
  have hn23cube : Real.rpow (n : ℝ) (2 / 3 : ℝ) ^ 3 = (n : ℝ) ^ 2 := by
    calc
      Real.rpow (n : ℝ) (2 / 3 : ℝ) ^ 3 =
          Real.rpow (Real.rpow (n : ℝ) (2 / 3 : ℝ)) (3 : ℝ) := by
        exact (Real.rpow_natCast _ 3).symm
      _ = Real.rpow (n : ℝ) ((2 / 3 : ℝ) * 3) :=
        (Real.rpow_mul hnR.le (2 / 3 : ℝ) 3).symm
      _ = (n : ℝ) ^ 2 := by norm_num
  have hcast : (nearCutoff B M n : ℝ) < n23 n := by
    unfold n23
    have hcub : (nearCutoff B M n : ℝ) ^ 3 < (n : ℝ) ^ 2 := by
      exact (div_lt_one (sq_pos_of_pos hnR)).1 hthird
    rw [← hn23cube] at hcub
    exact (pow_lt_pow_iff_left₀ (by positivity)
      (Real.rpow_nonneg hnR.le (2 / 3 : ℝ)) (by norm_num : (3 : ℕ) ≠ 0)).mp hcub
  exact Nat.lt_ceil.mpr hcast

lemma rpow_sq_quarter_neg_half {e : ℝ} (he : 0 < e) :
    Real.rpow (e ^ 2 / 4) (-(1 / 2) : ℝ) = 2 / e := by
  have he2 : 0 ≤ e / 2 := by positivity
  calc
    Real.rpow (e ^ 2 / 4) (-(1 / 2) : ℝ) =
        Real.rpow (Real.rpow (e / 2) 2) (-(1 / 2) : ℝ) := by
      congr 2
      calc
        e ^ 2 / 4 = (e / 2) ^ 2 := by ring
        _ = Real.rpow (e / 2) 2 := (Real.rpow_two _).symm
    _ = Real.rpow (e / 2) ((2 : ℝ) * (-(1 / 2) : ℝ)) :=
      (Real.rpow_mul he2 2 (-(1 / 2) : ℝ)).symm
    _ = 2 / e := by
      norm_num
      rw [Real.rpow_neg he2, Real.rpow_one]
      field_simp [he.ne']

lemma rpow_sq_quarter_neg_three_half {e : ℝ} (he : 0 < e) :
    Real.rpow (e ^ 2 / 4) (-(3 / 2) : ℝ) = 8 / e ^ 3 := by
  have he2 : 0 ≤ e / 2 := by positivity
  calc
    Real.rpow (e ^ 2 / 4) (-(3 / 2) : ℝ) =
        Real.rpow (Real.rpow (e / 2) 2) (-(3 / 2) : ℝ) := by
      congr 2
      calc
        e ^ 2 / 4 = (e / 2) ^ 2 := by ring
        _ = Real.rpow (e / 2) 2 := (Real.rpow_two _).symm
    _ = Real.rpow (e / 2) ((2 : ℝ) * (-(3 / 2) : ℝ)) :=
      (Real.rpow_mul he2 2 (-(3 / 2) : ℝ)).symm
    _ = 8 / e ^ 3 := by
      norm_num
      field_simp [he.ne']
      ring

lemma rpow_sq_quarter_neg_five_half {e : ℝ} (he : 0 < e) :
    Real.rpow (e ^ 2 / 4) (-(5 / 2) : ℝ) = 32 / e ^ 5 := by
  have he2 : 0 ≤ e / 2 := by positivity
  calc
    Real.rpow (e ^ 2 / 4) (-(5 / 2) : ℝ) =
        Real.rpow (Real.rpow (e / 2) 2) (-(5 / 2) : ℝ) := by
      congr 2
      calc
        e ^ 2 / 4 = (e / 2) ^ 2 := by ring
        _ = Real.rpow (e / 2) 2 := (Real.rpow_two _).symm
    _ = Real.rpow (e / 2) ((2 : ℝ) * (-(5 / 2) : ℝ)) :=
      (Real.rpow_mul he2 2 (-(5 / 2) : ℝ)).symm
    _ = 32 / e ^ 5 := by
      norm_num
      field_simp [he.ne']
      ring

lemma mul_rpow_neg_three_half (k : ℕ) (hk : 0 < k) :
    (k : ℝ) * Real.rpow (k : ℝ) (-(3 / 2) : ℝ) =
      Real.rpow (k : ℝ) (-(1 / 2) : ℝ) := by
  have hkR : 0 < (k : ℝ) := by positivity
  calc
    (k : ℝ) * Real.rpow (k : ℝ) (-(3 / 2) : ℝ) =
        Real.rpow (k : ℝ) (1 + (-(3 / 2) : ℝ)) := by
      simpa only [Real.rpow_one] using!
        (Real.rpow_add hkR (1 : ℝ) (-(3 / 2) : ℝ)).symm
    _ = _ := by norm_num

lemma sq_mul_rpow_neg_three_half (k : ℕ) (hk : 0 < k) :
    (k : ℝ) ^ 2 * Real.rpow (k : ℝ) (-(3 / 2) : ℝ) =
      Real.rpow (k : ℝ) (1 / 2 : ℝ) := by
  have hkR : 0 < (k : ℝ) := by positivity
  calc
    (k : ℝ) ^ 2 * Real.rpow (k : ℝ) (-(3 / 2) : ℝ) =
        Real.rpow (k : ℝ) (2 + (-(3 / 2) : ℝ)) := by
      simpa only [Real.rpow_two] using!
        (Real.rpow_add hkR (2 : ℝ) (-(3 / 2) : ℝ)).symm
    _ = _ := by norm_num

lemma cube_mul_rpow_neg_three_half (k : ℕ) (hk : 0 < k) :
    (k : ℝ) ^ 3 * Real.rpow (k : ℝ) (-(3 / 2) : ℝ) =
      Real.rpow (k : ℝ) (3 / 2 : ℝ) := by
  have hkR : 0 < (k : ℝ) := by positivity
  calc
    (k : ℝ) ^ 3 * Real.rpow (k : ℝ) (-(3 / 2) : ℝ) =
        Real.rpow (k : ℝ) (3 : ℝ) *
          Real.rpow (k : ℝ) (-(3 / 2) : ℝ) := by
      congr 1
      exact (Real.rpow_natCast _ 3).symm
    _ = Real.rpow (k : ℝ) (3 + (-(3 / 2) : ℝ)) :=
      (Real.rpow_add hkR (3 : ℝ) (-(3 / 2) : ℝ)).symm
    _ = _ := by norm_num

lemma local_one_relative {n M k : ℕ} {C e : ℝ}
    (hk : 0 < k) (hlam : 0 < degreeAt n M)
    (hloc : tupleLocalBound n M 1 (fun _ => k) C)
    (heq : e = C * ((k : ℝ) / n + |degreeAt n M - 1| * k ^ 2 / n +
      (k : ℝ) ^ 3 / (n : ℝ) ^ 2))
    (he1 : e ≤ 1) :
    |massTerm n M k - leadingMassTerm n M k| ≤
      2 * C * leadingMassTerm n M k *
        ((k : ℝ) / n + |degreeAt n M - 1| * k ^ 2 / n +
          (k : ℝ) ^ 3 / (n : ℝ) ^ 2) := by
  rw [tupleLocalBound] at hloc
  have hlead : 0 < treeLeading n M k := by
    unfold treeLeading
    rw [if_neg hk.ne']
    have hc : 0 < (cayley k : ℝ) := by exact_mod_cast W04_TUPLES_Foundation.cayley_pos hk
    have hn : 0 < n := by
      by_contra hn0
      have : n = 0 := Nat.eq_zero_of_not_pos hn0
      subst n
      simp [degreeAt] at hlam
    positivity
  have hlog : |Real.log (tupleMoment n M 1 (fun _ => k) /
      treeLeading n M k)| ≤
      C * ((k : ℝ) / n + |degreeAt n M - 1| * k ^ 2 / n +
        (k : ℝ) ^ 3 / (n : ℝ) ^ 2) := by
    simpa [tupleLeading] using! hloc.2
  have hrel := abs_log_ratio_to_relative hloc.1 hlead hlog
    (by simpa [heq] using! he1)
  unfold massTerm momentOne leadingMassTerm
  rw [show (k : ℝ) * tupleMoment n M 1 (fun _ => k) -
      k * treeLeading n M k = (k : ℝ) *
        (tupleMoment n M 1 (fun _ => k) - treeLeading n M k) by ring,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k)]
  nlinarith

lemma local_one_upper {n M k : ℕ} {C e : ℝ}
    (hk : 0 < k) (hlam : 0 < degreeAt n M)
    (hloc : tupleLocalBound n M 1 (fun _ => k) C)
    (heq : e = C * ((k : ℝ) / n + |degreeAt n M - 1| * k ^ 2 / n +
      (k : ℝ) ^ 3 / (n : ℝ) ^ 2))
    (he1 : e ≤ 1) :
    massTerm n M k ≤ 3 * leadingMassTerm n M k := by
  have hrel := local_one_relative hk hlam hloc heq he1
  have hnonneg := leadingMassTerm_nonneg (n := n) (M := M) (k := k) hlam
  have habs := le_trans (le_abs_self (massTerm n M k - leadingMassTerm n M k)) hrel
  have habs' : massTerm n M k - leadingMassTerm n M k ≤
      2 * leadingMassTerm n M k * e := by
    calc
      massTerm n M k - leadingMassTerm n M k ≤
          2 * C * leadingMassTerm n M k *
            ((k : ℝ) / n + |degreeAt n M - 1| * k ^ 2 / n +
              (k : ℝ) ^ 3 / (n : ℝ) ^ 2) := habs
      _ = 2 * leadingMassTerm n M k * e := by rw [heq]; ring
  nlinarith

lemma mixed_relative {n M k l : ℕ} {C e : ℝ}
    (hk : 0 < k) (hl : 0 < l)
    (hJk : 0 < momentOne n M k) (hJl : 0 < momentOne n M l)
    (hJ2 : 0 < momentTwo n M k l)
    (hlog : |Real.log (momentTwo n M k l /
      (momentOne n M k * momentOne n M l))| ≤
        C * (((k : ℝ) + l) / n + |degreeAt n M - 1| * k * l / n +
          (k : ℝ) * l * (k + l) / (n : ℝ) ^ 2))
    (heq : e = C * (((k : ℝ) + l) / n +
      |degreeAt n M - 1| * k * l / n +
      (k : ℝ) * l * (k + l) / (n : ℝ) ^ 2))
    (he1 : e ≤ 1) :
    |(k : ℝ) * l * momentTwo n M k l -
        massTerm n M k * massTerm n M l| ≤
      2 * C * massTerm n M k * massTerm n M l *
        (((k : ℝ) + l) / n + |degreeAt n M - 1| * k * l / n +
          (k : ℝ) * l * (k + l) / (n : ℝ) ^ 2) := by
  have hprod : 0 < momentOne n M k * momentOne n M l := mul_pos hJk hJl
  have hrel := abs_log_ratio_to_relative hJ2 hprod hlog (by simpa [heq] using! he1)
  unfold massTerm
  rw [show (k : ℝ) * l * momentTwo n M k l -
      (k * momentOne n M k) * (l * momentOne n M l) =
      ((k : ℝ) * l) *
        (momentTwo n M k l - momentOne n M k * momentOne n M l) by ring,
    abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) * l)]
  have hscale := mul_le_mul_of_nonneg_left hrel
    (by positivity : (0 : ℝ) ≤ (k : ℝ) * l)
  simpa [massTerm, mul_assoc, mul_left_comm, mul_comm] using! hscale

lemma weighted_le_neg_half {n M k : ℕ} {D u : ℝ}
    (hn : 0 < n) (hk : 0 < k)
    (hb : leadingMassTerm n M k ≤
      D * n * Real.rpow (k : ℝ) (-(3 / 2) : ℝ) * Real.exp (-u * k)) :
    leadingMassTerm n M k * ((k : ℝ) / n) ≤
      D * (Real.rpow (k : ℝ) (-(1 / 2) : ℝ) * Real.exp (-u * k)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc
    leadingMassTerm n M k * ((k : ℝ) / n) ≤
        (D * n * Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
          Real.exp (-u * k)) * ((k : ℝ) / n) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _ = _ := by
      rw [← mul_rpow_neg_three_half k hk]
      field_simp [hn0]

lemma weighted_le_half {n M k : ℕ} {D e u : ℝ}
    (hn : 0 < n) (hk : 0 < k) (he : 0 ≤ e)
    (hb : leadingMassTerm n M k ≤
      D * n * Real.rpow (k : ℝ) (-(3 / 2) : ℝ) * Real.exp (-u * k)) :
    leadingMassTerm n M k * (e * (k : ℝ) ^ 2 / n) ≤
      D * e * (Real.rpow (k : ℝ) (1 / 2 : ℝ) * Real.exp (-u * k)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc
    leadingMassTerm n M k * (e * (k : ℝ) ^ 2 / n) ≤
        (D * n * Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
          Real.exp (-u * k)) * (e * (k : ℝ) ^ 2 / n) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _ = _ := by
      rw [← sq_mul_rpow_neg_three_half k hk]
      field_simp [hn0]

lemma weighted_le_three_half {n M k : ℕ} {D u : ℝ}
    (hn : 0 < n) (hk : 0 < k)
    (hb : leadingMassTerm n M k ≤
      D * n * Real.rpow (k : ℝ) (-(3 / 2) : ℝ) * Real.exp (-u * k)) :
    leadingMassTerm n M k * ((k : ℝ) ^ 3 / (n : ℝ) ^ 2) ≤
      (D / n) * (Real.rpow (k : ℝ) (3 / 2 : ℝ) * Real.exp (-u * k)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc
    leadingMassTerm n M k * ((k : ℝ) ^ 3 / (n : ℝ) ^ 2) ≤
        (D * n * Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
          Real.exp (-u * k)) * ((k : ℝ) ^ 3 / (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _ = _ := by
      rw [← cube_mul_rpow_neg_three_half k hk]
      field_simp [hn0]


end
end Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_Analytic


namespace Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_LocalMean

noncomputable section
open Filter
open scoped BigOperators Topology
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_Analytic

private def powerTerm (u beta : ℝ) (k : ℕ) : ℝ :=
  Real.rpow (k : ℝ) beta * Real.exp (-u * k)

lemma leadingMassTerm_bound_at_rate_floor
    {n M k : ℕ} {D u : ℝ}
    (hk : 0 < k) (hD : 0 ≤ D)
    (hbound : leadingMassTerm n M k ≤
      D * n * Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
        Real.exp (-rate (degreeAt n M) * k))
    (hfloor : u ≤ rate (degreeAt n M)) :
    leadingMassTerm n M k ≤
      D * n * Real.rpow (k : ℝ) (-(3 / 2) : ℝ) * Real.exp (-u * k) := by
  have hexp : Real.exp (-rate (degreeAt n M) * k) ≤ Real.exp (-u * k) := by
    apply Real.exp_le_exp.mpr
    have hkR : 0 ≤ (k : ℝ) := by positivity
    nlinarith
  have hfactor : 0 ≤ D * (n : ℝ) * Real.rpow (k : ℝ) (-(3 / 2) : ℝ) :=
    mul_nonneg (mul_nonneg hD (by positivity)) (Real.rpow_nonneg (by positivity) _)
  exact hbound.trans (mul_le_mul_of_nonneg_left hexp hfactor)

lemma local_mean_error_term_bound
    {n M k : ℕ} {C D e u : ℝ}
    (hn : 0 < n) (hk : 0 < k)
    (hlam : 0 < degreeAt n M) (hC : 0 ≤ C)
    (he : e = |degreeAt n M - 1|)
    (hlocal : tupleLocalBound n M 1 (fun _ => k) C)
    (hsmall : C * ((k : ℝ) / n + e * k ^ 2 / n +
      (k : ℝ) ^ 3 / (n : ℝ) ^ 2) ≤ 1)
    (hbound : leadingMassTerm n M k ≤
      D * n * Real.rpow (k : ℝ) (-(3 / 2) : ℝ) * Real.exp (-u * k)) :
    |massTerm n M k - leadingMassTerm n M k| ≤
      2 * C * D * (powerTerm u (-(1 / 2) : ℝ) k +
        e * powerTerm u (1 / 2 : ℝ) k +
        (1 / n : ℝ) * powerTerm u (3 / 2 : ℝ) k) := by
  have he0 : 0 ≤ e := by rw [he]; exact abs_nonneg _
  have hrel := local_one_relative hk hlam hlocal
    (e := C * ((k : ℝ) / n + e * k ^ 2 / n +
      (k : ℝ) ^ 3 / (n : ℝ) ^ 2))
    (by rw [he]) (by simpa [he] using! hsmall)
  have h0 := weighted_le_neg_half hn hk hbound
  have h1 := weighted_le_half hn hk he0 hbound
  have h2 := weighted_le_three_half hn hk hbound
  calc
    |massTerm n M k - leadingMassTerm n M k| ≤
        2 * C * leadingMassTerm n M k *
          ((k : ℝ) / n + e * k ^ 2 / n +
            (k : ℝ) ^ 3 / (n : ℝ) ^ 2) := by simpa [he] using! hrel
    _ = 2 * C * (leadingMassTerm n M k * ((k : ℝ) / n) +
          leadingMassTerm n M k * (e * k ^ 2 / n) +
          leadingMassTerm n M k * ((k : ℝ) ^ 3 / (n : ℝ) ^ 2)) := by ring
    _ ≤ 2 * C * (D * powerTerm u (-(1 / 2) : ℝ) k +
          D * e * powerTerm u (1 / 2 : ℝ) k +
          (D / n) * powerTerm u (3 / 2 : ℝ) k) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (add_le_add h0 h1) h2
    _ = _ := by unfold powerTerm; ring

lemma near_local_mean_sum_bound
    (hA : AnalyticSumsStatement)
    {n M H : ℕ} {C e u : ℝ}
    (hn : 0 < n) (hlo : 1 / 2 ≤ degreeAt n M)
    (hC : 0 ≤ C) (he : e = |degreeAt n M - 1|)
    (hu : 0 < u) (hu1 : u ≤ 1)
    (hfloor : u ≤ rate (degreeAt n M))
    (hlocal : ∀ k ∈ Finset.Ico 1 (H + 1),
      tupleLocalBound n M 1 (fun _ => k) C)
    (hsmall : ∀ k ∈ Finset.Ico 1 (H + 1),
      C * ((k : ℝ) / n + e * k ^ 2 / n +
        (k : ℝ) ^ 3 / (n : ℝ) ^ 2) ≤ 1) :
    (∑ k ∈ Finset.Ico 1 (H + 1),
      |massTerm n M k - leadingMassTerm n M k|) ≤
      2 * C * Classical.choose leadingMassTerm_bound *
        (Classical.choose (analytic_power_bound hA (-(1 / 2) : ℝ) (by norm_num)) *
            Real.rpow u (-(1 / 2) : ℝ) +
          e * Classical.choose (analytic_power_bound hA (1 / 2 : ℝ) (by norm_num)) *
            Real.rpow u (-(3 / 2) : ℝ) +
          (1 / n : ℝ) *
            Classical.choose (analytic_power_bound hA (3 / 2 : ℝ) (by norm_num)) *
              Real.rpow u (-(5 / 2) : ℝ)) := by
  let D := Classical.choose leadingMassTerm_bound
  have hDspec := Classical.choose_spec leadingMassTerm_bound
  have hD : 0 ≤ D := hDspec.1.le
  have hlam : 0 < degreeAt n M := lt_of_lt_of_le (by norm_num) hlo
  have he0 : 0 ≤ e := by rw [he]; exact abs_nonneg _
  have hterm : ∀ k ∈ Finset.Ico 1 (H + 1),
      |massTerm n M k - leadingMassTerm n M k| ≤
        2 * C * D * (powerTerm u (-(1 / 2) : ℝ) k +
          e * powerTerm u (1 / 2 : ℝ) k +
          (1 / n : ℝ) * powerTerm u (3 / 2 : ℝ) k) := by
    intro k hk
    have hkpos : 0 < k := (Finset.mem_Ico.mp hk).1
    have hbound := leadingMassTerm_bound_at_rate_floor hkpos hD
      (hDspec.2 n M k hkpos hlo) hfloor
    exact local_mean_error_term_bound hn hkpos hlam hC he
      (hlocal k hk) (hsmall k hk) hbound
  have hsum0 := finite_power_exp_sum_le hA (beta := (-(1 / 2) : ℝ))
    (by norm_num) hu hu1 H
  have hsum1 := finite_power_exp_sum_le hA (beta := (1 / 2 : ℝ))
    (by norm_num) hu hu1 H
  have hsum2 := finite_power_exp_sum_le hA (beta := (3 / 2 : ℝ))
    (by norm_num) hu hu1 H
  have hpow0 : -(-(1 / 2 : ℝ)) - 1 = -(1 / 2 : ℝ) := by norm_num
  have hpow1 : -(1 / 2 : ℝ) - 1 = -(3 / 2 : ℝ) := by norm_num
  have hpow2 : -(3 / 2 : ℝ) - 1 = -(5 / 2 : ℝ) := by norm_num
  have hsum0' :
      (∑ k ∈ Finset.Ico 1 (H + 1), powerTerm u (-(1 / 2) : ℝ) k) ≤
        Classical.choose (analytic_power_bound hA (-(1 / 2) : ℝ) (by norm_num)) *
          Real.rpow u (-(1 / 2) : ℝ) := by
    calc
      _ ≤ Classical.choose (analytic_power_bound hA (-(1 / 2) : ℝ) (by norm_num)) *
          Real.rpow u (-(-(1 / 2 : ℝ)) - 1) := by simpa [powerTerm] using! hsum0
      _ = _ := congrArg (fun t : ℝ =>
        Classical.choose (analytic_power_bound hA (-(1 / 2) : ℝ) (by norm_num)) *
          Real.rpow u t) hpow0
  have hsum1' :
      (∑ k ∈ Finset.Ico 1 (H + 1), powerTerm u (1 / 2 : ℝ) k) ≤
        Classical.choose (analytic_power_bound hA (1 / 2 : ℝ) (by norm_num)) *
          Real.rpow u (-(3 / 2) : ℝ) := by
    calc
      _ ≤ Classical.choose (analytic_power_bound hA (1 / 2 : ℝ) (by norm_num)) *
          Real.rpow u (-(1 / 2 : ℝ) - 1) := by simpa [powerTerm] using! hsum1
      _ = _ := congrArg (fun t : ℝ =>
        Classical.choose (analytic_power_bound hA (1 / 2 : ℝ) (by norm_num)) *
          Real.rpow u t) hpow1
  have hsum2' :
      (∑ k ∈ Finset.Ico 1 (H + 1), powerTerm u (3 / 2 : ℝ) k) ≤
        Classical.choose (analytic_power_bound hA (3 / 2 : ℝ) (by norm_num)) *
          Real.rpow u (-(5 / 2) : ℝ) := by
    calc
      _ ≤ Classical.choose (analytic_power_bound hA (3 / 2 : ℝ) (by norm_num)) *
          Real.rpow u (-(3 / 2 : ℝ) - 1) := by simpa [powerTerm] using! hsum2
      _ = _ := congrArg (fun t : ℝ =>
        Classical.choose (analytic_power_bound hA (3 / 2 : ℝ) (by norm_num)) *
          Real.rpow u t) hpow2
  have hnR : 0 ≤ (1 / n : ℝ) := by positivity
  calc
    (∑ k ∈ Finset.Ico 1 (H + 1),
      |massTerm n M k - leadingMassTerm n M k|) ≤
        ∑ k ∈ Finset.Ico 1 (H + 1),
          2 * C * D * (powerTerm u (-(1 / 2) : ℝ) k +
            e * powerTerm u (1 / 2 : ℝ) k +
            (1 / n : ℝ) * powerTerm u (3 / 2 : ℝ) k) :=
      Finset.sum_le_sum hterm
    _ = 2 * C * D *
          ((∑ k ∈ Finset.Ico 1 (H + 1), powerTerm u (-(1 / 2) : ℝ) k) +
            e * (∑ k ∈ Finset.Ico 1 (H + 1), powerTerm u (1 / 2 : ℝ) k) +
            (1 / n : ℝ) *
              (∑ k ∈ Finset.Ico 1 (H + 1), powerTerm u (3 / 2 : ℝ) k)) := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 2 * C * D *
          (Classical.choose (analytic_power_bound hA (-(1 / 2) : ℝ) (by norm_num)) *
              Real.rpow u (-(1 / 2) : ℝ) +
            e * Classical.choose (analytic_power_bound hA (1 / 2 : ℝ) (by norm_num)) *
              Real.rpow u (-(3 / 2) : ℝ) +
            (1 / n : ℝ) *
              Classical.choose (analytic_power_bound hA (3 / 2 : ℝ) (by norm_num)) *
                Real.rpow u (-(5 / 2) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add
      · exact add_le_add hsum0' (by simpa only [mul_assoc] using!
          (mul_le_mul_of_nonneg_left hsum1' he0))
      · simpa only [mul_assoc] using!
          (mul_le_mul_of_nonneg_left hsum2' hnR)
    _ = _ := by rfl

end
end Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_LocalMean


namespace Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_NearCutoff

noncomputable section
open Filter
open scoped BigOperators Topology
open Erdos745.WrapUp.Proofs.W06_POISSON
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_Analytic

def cutoffError (q : ℕ) (C B : ℝ) (M : NatSeq) (n : ℕ) : ℝ :=
  C * ((q : ℝ) * (nearCutoff B M n : ℝ) / n +
    epsilon M n * ((q : ℝ) * (nearCutoff B M n : ℝ)) ^ 2 / n +
    ((q : ℝ) * (nearCutoff B M n : ℝ)) ^ 3 / (n : ℝ) ^ 2)

lemma near_cutoff_rate_floor
    (hRate : RateStatement) {M : NatSeq} (hbare : bareSuper M) :
    ∀ᶠ n in atTop,
      epsilon M n ^ 2 / 4 ≤ rate (degree M n) := by
  have hratio := rate_over_epsilon_sq_tendsto hRate (Or.inr hbare)
  have hquot : ∀ᶠ n in atTop,
      (1 / 4 : ℝ) < rate (degree M n) / epsilon M n ^ 2 :=
    (tendsto_order.1 hratio).1 (1 / 4) (by norm_num)
  filter_upwards [hquot, bare_epsilon_pos (Or.inr hbare)] with n hq he
  have he2 : 0 < epsilon M n ^ 2 := sq_pos_of_pos he
  have := (lt_div_iff₀ he2).1 hq
  nlinarith

lemma near_cutoff_pair_range
    {M : NatSeq} (hbare : bareSuper M) (B : ℝ) (hB : 0 < B) :
    ∀ᶠ n in atTop,
      ((2 * nearCutoff B M n : ℕ) : ℝ) ≤ (n : ℝ) / 16 := by
  have herr := near_cutoff_error_tendsto_zero (Or.inr hbare) 2 B 1 hB
  have hsmall : ∀ᶠ n in atTop, cutoffError 2 1 B M n < 1 / 16 := by
    simpa [cutoffError] using!
      (tendsto_order.1 herr).2 (1 / 16 : ℝ) (by norm_num)
  filter_upwards [hsmall, bare_epsilon_pos (Or.inr hbare), eventually_ge_atTop 1]
    with n hs he hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hfirst :
      2 * (nearCutoff B M n : ℝ) / n ≤ cutoffError 2 1 B M n := by
    dsimp [cutoffError]
    have hsecond : 0 ≤ epsilon M n * (2 * (nearCutoff B M n : ℝ)) ^ 2 / n :=
      div_nonneg (mul_nonneg he.le (sq_nonneg _)) hnR.le
    have hthird : 0 ≤ (2 * (nearCutoff B M n : ℝ)) ^ 3 / (n : ℝ) ^ 2 := by
      positivity
    norm_num
    nlinarith
  have hratio : 2 * (nearCutoff B M n : ℝ) / n < 1 / 16 :=
    lt_of_le_of_lt hfirst hs
  have hmul := (div_lt_iff₀ hnR).1 hratio
  have hcast : ((2 * nearCutoff B M n : ℕ) : ℝ) =
      2 * (nearCutoff B M n : ℝ) := by norm_num
  rw [hcast]
  nlinarith

lemma near_cutoff_eventually_positive
    (hRate : RateStatement) {M : NatSeq} (hbare : bareSuper M)
    (B : ℝ) (hB : 4 < B) :
    ∀ᶠ n in atTop, 1 ≤ nearCutoff B M n := by
  exact (tendsto_atTop.1
    (near_cutoff_basic hRate (Or.inr hbare) 0 B hB).1) 1

lemma near_common_cutoff_ranges
    (hRate : RateStatement) {M : NatSeq} (hbare : bareSuper M)
    (B C₁ C₂ Cmix : ℝ) (hB : 4 < B) (n₀ : ℕ) :
    ∀ᶠ n in atTop,
      0 < n ∧ n₀ ≤ n ∧ M n ≤ capacity n ∧
      1 ≤ nearCutoff B M n ∧
      nearCutoff B M n < largeCutoff n ∧
      ((2 * nearCutoff B M n : ℕ) : ℝ) ≤ (n : ℝ) / 16 ∧
      1 / 2 ≤ degree M n ∧ degree M n ≤ 3 / 2 ∧
      epsilon M n = degree M n - 1 ∧
      0 < epsilon M n ∧ epsilon M n ≤ 1 ∧
      1 ≤ widthParameter M n ∧
      epsilon M n ^ 2 / 4 ≤ rate (degree M n) ∧
      cutoffError 1 C₁ B M n ≤ 1 ∧
      cutoffError 2 C₂ B M n ≤ 1 ∧
      cutoffError 2 Cmix B M n ≤ 1 := by
  have hBpos : 0 < B := lt_trans (by norm_num) hB
  have hdeg := hbare.2.2.1
  have hdeglo : ∀ᶠ n in atTop, 1 / 2 ≤ degree M n :=
    ((tendsto_order.1 hdeg).1 (1 / 2) (by norm_num)).mono fun _ h => h.le
  have hdeghi : ∀ᶠ n in atTop, degree M n ≤ 3 / 2 :=
    ((tendsto_order.1 hdeg).2 (3 / 2) (by norm_num)).mono fun _ h => h.le
  have hsuper := hbare.2.1
  have hepos := bare_epsilon_pos (Or.inr hbare)
  have heone : ∀ᶠ n in atTop, epsilon M n ≤ 1 :=
    ((tendsto_order.1 (bare_epsilon_tendsto_zero (Or.inr hbare))).2
      1 (by norm_num)).mono fun _ h => h.le
  have hw : ∀ᶠ n in atTop, 1 ≤ widthParameter M n :=
    (tendsto_atTop.1 (bare_width_tendsto_atTop (Or.inr hbare))) 1
  have hrate := near_cutoff_rate_floor hRate hbare
  have hpositive := near_cutoff_eventually_positive hRate hbare B hB
  have hlarge := cutoff_below_large_of_error (Or.inr hbare) B hBpos
  have hpair := near_cutoff_pair_range hbare B hBpos
  have herr₁ : ∀ᶠ n in atTop, cutoffError 1 C₁ B M n ≤ 1 := by
    have ht := near_cutoff_error_tendsto_zero (Or.inr hbare) 1 B C₁ hBpos
    exact ((tendsto_order.1 ht).2 1 (by norm_num)).mono
      (by intro n hn; simpa [cutoffError] using! hn.le)
  have herr₂ : ∀ᶠ n in atTop, cutoffError 2 C₂ B M n ≤ 1 := by
    have ht := near_cutoff_error_tendsto_zero (Or.inr hbare) 2 B C₂ hBpos
    exact ((tendsto_order.1 ht).2 1 (by norm_num)).mono
      (by intro n hn; simpa [cutoffError] using! hn.le)
  have herrmix : ∀ᶠ n in atTop, cutoffError 2 Cmix B M n ≤ 1 := by
    have ht := near_cutoff_error_tendsto_zero (Or.inr hbare) 2 B Cmix hBpos
    exact ((tendsto_order.1 ht).2 1 (by norm_num)).mono
      (by intro n hn; simpa [cutoffError] using! hn.le)
  filter_upwards [eventually_gt_atTop 0, eventually_ge_atTop n₀,
    hbare.1, hpositive, hlarge, hpair, hdeglo, hdeghi, hsuper,
    hepos, heone, hw, hrate, herr₁, herr₂, herrmix]
    with n hn hn₀ hcap hpos hlg hp hlo hhi hsup he he1 hwidth hr he₁ he₂ hemix
  have heq : epsilon M n = degree M n - 1 := by
    rw [epsilon, abs_of_pos (sub_pos.mpr hsup)]
  exact ⟨hn, hn₀, hcap, hpos, hlg, hp, hlo, hhi, heq, he, he1,
    hwidth, hr, he₁, he₂, hemix⟩

lemma one_error_below_cutoff
    {M : NatSeq} {B C : ℝ} {n k : ℕ}
    (hn : 0 < n) (he : 0 ≤ epsilon M n) (hC : 0 ≤ C)
    (hk : k ≤ nearCutoff B M n)
    (hcut : cutoffError 1 C B M n ≤ 1) :
    C * ((k : ℝ) / n + epsilon M n * k ^ 2 / n +
      (k : ℝ) ^ 3 / (n : ℝ) ^ 2) ≤ 1 := by
  have hkR : (k : ℝ) ≤ nearCutoff B M n := by exact_mod_cast hk
  have hnR : 0 ≤ (n : ℝ) := by positivity
  have hfirst : (k : ℝ) / n ≤ (nearCutoff B M n : ℝ) / n := by gcongr
  have hsecond : epsilon M n * (k : ℝ) ^ 2 / n ≤
      epsilon M n * (nearCutoff B M n : ℝ) ^ 2 / n := by gcongr
  have hthird : (k : ℝ) ^ 3 / (n : ℝ) ^ 2 ≤
      (nearCutoff B M n : ℝ) ^ 3 / (n : ℝ) ^ 2 := by gcongr
  have hmain :
      (k : ℝ) / n + epsilon M n * k ^ 2 / n + (k : ℝ) ^ 3 / (n : ℝ) ^ 2 ≤
      (nearCutoff B M n : ℝ) / n +
        epsilon M n * (nearCutoff B M n : ℝ) ^ 2 / n +
        (nearCutoff B M n : ℝ) ^ 3 / (n : ℝ) ^ 2 := by linarith
  calc
    _ ≤ C * ((nearCutoff B M n : ℝ) / n +
        epsilon M n * (nearCutoff B M n : ℝ) ^ 2 / n +
        (nearCutoff B M n : ℝ) ^ 3 / (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hmain hC
    _ ≤ 1 := by simpa [cutoffError] using! hcut

lemma pair_size_below_cutoff
    {M : NatSeq} {B : ℝ} {n k l : ℕ}
    (hk : k ≤ nearCutoff B M n) (hl : l ≤ nearCutoff B M n)
    (hrange : ((2 * nearCutoff B M n : ℕ) : ℝ) ≤ (n : ℝ) / 16) :
    ((k + l : ℕ) : ℝ) ≤ (n : ℝ) / 16 := by
  have hkl : k + l ≤ 2 * nearCutoff B M n := by omega
  exact (by exact_mod_cast hkl : ((k + l : ℕ) : ℝ) ≤
    ((2 * nearCutoff B M n : ℕ) : ℝ)).trans hrange

end
end Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_NearCutoff


namespace Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_NearLocal

noncomputable section
open Filter
open scoped BigOperators Topology
open Erdos745.WrapUp.Proofs.W06_POISSON
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_Analytic
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_LocalMean
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_NearCutoff

private lemma near_mean_numeric_absorption
    {n : ℕ} {e A₀ A₁ A₂ : ℝ}
    (hn : 0 < n) (he : 0 < e) (he1 : e ≤ 1)
    (hw : 1 ≤ (n : ℝ) * e ^ 3)
    (hA₀ : 0 ≤ A₀) (hA₂ : 0 ≤ A₂) :
    A₀ * (2 / e) + e * A₁ * (8 / e ^ 3) +
      (1 / n : ℝ) * A₂ * (32 / e ^ 5) ≤
      (2 * A₀ + 8 * A₁ + 32 * A₂) / e ^ 2 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have he2 : 0 < e ^ 2 := sq_pos_of_pos he
  have he5 : 0 < e ^ 5 := pow_pos he _
  have hden : 0 < (n : ℝ) * e ^ 5 := mul_pos hnR he5
  have hinv1 : 1 / e ≤ 1 / e ^ 2 := by
    apply (div_le_div_iff₀ he he2).2
    nlinarith
  have hprod : e ^ 2 ≤ (n : ℝ) * e ^ 5 := by
    have hmul := mul_le_mul_of_nonneg_right hw (sq_nonneg e)
    nlinarith [hmul]
  have hinv3 : 1 / ((n : ℝ) * e ^ 5) ≤ 1 / e ^ 2 := by
    exact (div_le_div_iff₀ hden he2).2 (by nlinarith)
  have hterm0 : A₀ * (2 / e) ≤ 2 * A₀ / e ^ 2 := by
    calc
      A₀ * (2 / e) = (2 * A₀) * (1 / e) := by ring
      _ ≤ (2 * A₀) * (1 / e ^ 2) :=
        mul_le_mul_of_nonneg_left hinv1 (by positivity)
      _ = 2 * A₀ / e ^ 2 := by ring
  have hterm1 : e * A₁ * (8 / e ^ 3) = 8 * A₁ / e ^ 2 := by
    field_simp [he.ne']
  have hterm2 : (1 / n : ℝ) * A₂ * (32 / e ^ 5) ≤
      32 * A₂ / e ^ 2 := by
    calc
      (1 / n : ℝ) * A₂ * (32 / e ^ 5) =
          (32 * A₂) * (1 / ((n : ℝ) * e ^ 5)) := by ring
      _ ≤ (32 * A₂) * (1 / e ^ 2) :=
        mul_le_mul_of_nonneg_left hinv3 (by positivity)
      _ = 32 * A₂ / e ^ 2 := by ring
  calc
    _ ≤ 2 * A₀ / e ^ 2 + 8 * A₁ / e ^ 2 + 32 * A₂ / e ^ 2 := by
      rw [hterm1]
      exact add_le_add (add_le_add hterm0 le_rfl) hterm2
    _ = (2 * A₀ + 8 * A₁ + 32 * A₂) / e ^ 2 := by ring

lemma near_local_mean_eventual_bound
    (hRate : RateStatement) (hT : TupleEstimatesStatement)
    (hA : AnalyticSumsStatement)
    {M : NatSeq} (hbare : bareSuper M)
    (B : ℝ) (hB : 4 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      (∑ k ∈ Finset.Ico 1 (nearCutoff B M n + 1),
        |massTerm n (M n) k - leadingMassTerm n (M n) k|) ≤
        C * (epsilon M n)⁻¹ ^ 2 := by
  obtain ⟨C₁, κ₁, hC₁, hκ₁, n₀, htuple⟩ := hT.1 1 (by omega)
  let D := Classical.choose leadingMassTerm_bound
  let A₀ := Classical.choose
    (analytic_power_bound hA (-(1 / 2) : ℝ) (by norm_num))
  let A₁ := Classical.choose
    (analytic_power_bound hA (1 / 2 : ℝ) (by norm_num))
  let A₂ := Classical.choose
    (analytic_power_bound hA (3 / 2 : ℝ) (by norm_num))
  let C := 2 * C₁ * D * (2 * A₀ + 8 * A₁ + 32 * A₂)
  have hD : 0 < D := (Classical.choose_spec leadingMassTerm_bound).1
  have hA₀ : 0 < A₀ :=
    (Classical.choose_spec (analytic_power_bound hA (-(1 / 2) : ℝ) (by norm_num))).1
  have hA₁ : 0 < A₁ :=
    (Classical.choose_spec (analytic_power_bound hA (1 / 2 : ℝ) (by norm_num))).1
  have hA₂ : 0 < A₂ :=
    (Classical.choose_spec (analytic_power_bound hA (3 / 2 : ℝ) (by norm_num))).1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hcommon := near_common_cutoff_ranges hRate hbare B C₁ 0 0 hB n₀
  filter_upwards [hcommon] with n h
  obtain ⟨hn, hn₀, hcap, hKpos, hKlarge, hpair, hlo, hhi,
    heq, he, he1, hw, hrate, herr, _, _⟩ := h
  let e := epsilon M n
  let u := e ^ 2 / 4
  have hu : 0 < u := by dsimp [u, e]; positivity
  have hu1 : u ≤ 1 := by dsimp [u, e]; nlinarith [sq_nonneg (epsilon M n)]
  have hfloor : u ≤ rate (degreeAt n (M n)) := by
    simpa [u, e, degree, degreeAt] using! hrate
  have hlocal : ∀ k ∈ Finset.Ico 1 (nearCutoff B M n + 1),
      tupleLocalBound n (M n) 1 (fun _ => k) C₁ := by
    intro k hk
    have hkpos : 0 < k := (Finset.mem_Ico.mp hk).1
    have hkK : k ≤ nearCutoff B M n := Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hk).2
    have hkr : (k : ℝ) ≤ (nearCutoff B M n : ℝ) := by exact_mod_cast hkK
    have hsum : (∑ i : Fin 1, ((fun _ => k) i : ℝ)) ≤ (n : ℝ) / 16 := by
      simp only [Fin.sum_univ_one]
      have hcast : ((2 * nearCutoff B M n : ℕ) : ℝ) =
          2 * (nearCutoff B M n : ℝ) := by norm_num
      rw [hcast] at hpair
      linarith
    exact ((htuple n (M n) (fun _ => k) hn₀ hcap hlo hhi
      (fun _ => hkpos)).2 hsum)
  have hsmall : ∀ k ∈ Finset.Ico 1 (nearCutoff B M n + 1),
      C₁ * ((k : ℝ) / n + e * k ^ 2 / n +
        (k : ℝ) ^ 3 / (n : ℝ) ^ 2) ≤ 1 := by
    intro k hk
    have hkK : k ≤ nearCutoff B M n := Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hk).2
    exact one_error_below_cutoff hn he.le hC₁.le hkK herr
  have hsum := near_local_mean_sum_bound hA hn hlo hC₁.le
    (e := e) (u := u) (by rfl) hu hu1 hfloor hlocal hsmall
  have hpow :
      A₀ * Real.rpow u (-(1 / 2) : ℝ) +
        e * A₁ * Real.rpow u (-(3 / 2) : ℝ) +
        (1 / n : ℝ) * A₂ * Real.rpow u (-(5 / 2) : ℝ) =
      A₀ * (2 / e) + e * A₁ * (8 / e ^ 3) +
        (1 / n : ℝ) * A₂ * (32 / e ^ 5) := by
    have he' : 0 < e := he
    dsimp [u]
    change A₀ * Real.rpow (e ^ 2 / 4) (-(1 / 2) : ℝ) +
      e * A₁ * Real.rpow (e ^ 2 / 4) (-(3 / 2) : ℝ) +
      (1 / n : ℝ) * A₂ * Real.rpow (e ^ 2 / 4) (-(5 / 2) : ℝ) =
      A₀ * (2 / e) + e * A₁ * (8 / e ^ 3) +
        (1 / n : ℝ) * A₂ * (32 / e ^ 5)
    rw [rpow_sq_quarter_neg_half (e := e) he',
      rpow_sq_quarter_neg_three_half (e := e) he',
      rpow_sq_quarter_neg_five_half (e := e) he']
  have hsum' :
      (∑ k ∈ Finset.Ico 1 (nearCutoff B M n + 1),
        |massTerm n (M n) k - leadingMassTerm n (M n) k|) ≤
        2 * C₁ * D *
          (A₀ * (2 / e) + e * A₁ * (8 / e ^ 3) +
            (1 / n : ℝ) * A₂ * (32 / e ^ 5)) := by
    calc
      _ ≤ 2 * C₁ * D *
          (A₀ * Real.rpow u (-(1 / 2) : ℝ) +
            e * A₁ * Real.rpow u (-(3 / 2) : ℝ) +
            (1 / n : ℝ) * A₂ * Real.rpow u (-(5 / 2) : ℝ)) := by
        simpa only [D, A₀, A₁, A₂] using! hsum
      _ = _ := congrArg (fun x : ℝ => 2 * C₁ * D * x) hpow
  have hw' : 1 ≤ (n : ℝ) * e ^ 3 := by simpa [e, widthParameter] using! hw
  have hnum := near_mean_numeric_absorption (A₀ := A₀) (A₁ := A₁) (A₂ := A₂)
    hn he he1 hw' hA₀.le hA₂.le
  have hscale :
      (∑ k ∈ Finset.Ico 1 (nearCutoff B M n + 1),
        |massTerm n (M n) k - leadingMassTerm n (M n) k|) ≤
        C / e ^ 2 := by
    calc
      _ ≤ 2 * C₁ * D *
          (A₀ * (2 / e) + e * A₁ * (8 / e ^ 3) +
            (1 / n : ℝ) * A₂ * (32 / e ^ 5)) := hsum'
      _ ≤ 2 * C₁ * D * ((2 * A₀ + 8 * A₁ + 32 * A₂) / e ^ 2) :=
        mul_le_mul_of_nonneg_left hnum (by positivity)
      _ = C / e ^ 2 := by dsimp [C]; ring
  calc
    _ ≤ C / e ^ 2 := hscale
    _ = C * (epsilon M n)⁻¹ ^ 2 := by
      dsimp [e]
      field_simp [he.ne']

end
end Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_NearLocal


namespace Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_NearTail

noncomputable section
open Filter
open scoped BigOperators Topology
open Erdos745.WrapUp.Proofs.W06_POISSON
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_Analytic
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_LocalMean
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_NearCutoff

lemma cutoff_exp_le_width_inv {M : NatSeq} {B κ : ℝ} {n : ℕ}
    (he : 0 < epsilon M n) (hw : 1 ≤ widthParameter M n)
    (hκ : 0 < κ) (hκB : 1 ≤ κ * B) :
    Real.exp (-κ * epsilon M n ^ 2 * (nearCutoff B M n : ℝ)) ≤
      (widthParameter M n)⁻¹ := by
  let e := epsilon M n
  let w := widthParameter M n
  have hlog : 0 ≤ Real.log w := Real.log_nonneg hw
  have hceil := Nat.le_ceil (B * e⁻¹ ^ 2 * Real.log w)
  have harg : B * Real.log w ≤ e ^ 2 * (nearCutoff B M n : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hceil (sq_nonneg e)
    have heq : e ^ 2 * (B * e⁻¹ ^ 2 * Real.log w) =
        B * Real.log w := by
      calc
        _ = (e * e⁻¹) ^ 2 * (B * Real.log w) := by ring
        _ = _ := by rw [mul_inv_cancel₀ (show e ≠ 0 from he.ne')]; norm_num
    exact heq ▸ (by simpa only [nearCutoff, e, w] using! hmul)
  have hlarge : Real.log w ≤ κ * e ^ 2 * (nearCutoff B M n : ℝ) := by
    have hscaled := mul_le_mul_of_nonneg_left harg hκ.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hκB) hlog]
  calc
    _ ≤ Real.exp (-Real.log w) := Real.exp_le_exp.mpr (by linarith)
    _ = w⁻¹ := by rw [Real.exp_neg, Real.exp_log (lt_of_lt_of_le zero_lt_one hw)]

lemma cutoff_rpow_le_epsilon {M : NatSeq} {B : ℝ} {n : ℕ}
    (he : 0 < epsilon M n) (hB : 1 ≤ B)
    (hlog : 1 ≤ Real.log (widthParameter M n)) :
    Real.rpow ((nearCutoff B M n + 1 : ℕ) : ℝ) (-(1 / 2) : ℝ) ≤
      epsilon M n := by
  let e := epsilon M n
  have hceil := Nat.le_ceil
    (B * e⁻¹ ^ 2 * Real.log (widthParameter M n))
  have hbase : 0 < e⁻¹ ^ 2 := by positivity
  have hsmall : e⁻¹ ^ 2 ≤
      ((nearCutoff B M n + 1 : ℕ) : ℝ) := by
    have hfactor : 1 ≤ B * Real.log (widthParameter M n) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hfactor hbase.le
    have hceil' : B * e⁻¹ ^ 2 * Real.log (widthParameter M n) ≤
        (nearCutoff B M n : ℝ) := by simpa [nearCutoff, e] using! hceil
    have hcast : ((nearCutoff B M n + 1 : ℕ) : ℝ) =
        (nearCutoff B M n : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    nlinarith
  have hrpow : Real.rpow (e⁻¹ ^ 2) (-(1 / 2) : ℝ) = e := by
    calc
      Real.rpow (e⁻¹ ^ 2) (-(1 / 2) : ℝ) =
          Real.rpow (Real.rpow e (-2 : ℝ)) (-(1 / 2) : ℝ) := by
        congr 1
        calc
          e⁻¹ ^ 2 = (e ^ 2)⁻¹ := inv_pow e 2
          _ = (Real.rpow e 2)⁻¹ :=
            (congrArg Inv.inv (Real.rpow_natCast e 2)).symm
          _ = Real.rpow e (-2 : ℝ) := (Real.rpow_neg he.le _).symm
      _ = Real.rpow e ((-2 : ℝ) * (-(1 / 2) : ℝ)) :=
        (Real.rpow_mul he.le _ _).symm
      _ = e := by norm_num
  exact (Real.rpow_le_rpow_of_nonpos hbase hsmall (by norm_num)).trans hrpow.le

lemma cutoff_negThreeHalf_tail_bound {M : NatSeq} {B κ : ℝ} {n N : ℕ}
    (he : 0 < epsilon M n) (hB : 1 ≤ B)
    (hw : 1 ≤ widthParameter M n)
    (hlog : 1 ≤ Real.log (widthParameter M n))
    (hκ : 0 < κ) (hκB : 1 ≤ κ * B) :
    (∑ k ∈ Finset.Ico (nearCutoff B M n + 1) (N + 1),
      Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
        Real.exp (-κ * epsilon M n ^ 2 * k)) ≤
      3 / ((n : ℝ) * epsilon M n ^ 2) := by
  let e := epsilon M n
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    norm_num [widthParameter] at hw
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have htail := negThreeHalf_exp_tail_le
    (N := N) (H := nearCutoff B M n)
    (u := κ * e ^ 2) (by positivity)
  have hpow := cutoff_rpow_le_epsilon he hB hlog
  have hexp := cutoff_exp_le_width_inv he hw hκ hκB
  have hwpos : 0 < widthParameter M n := lt_of_lt_of_le zero_lt_one hw
  have hprod :
      Real.rpow ((nearCutoff B M n + 1 : ℕ) : ℝ) (-(1 / 2) : ℝ) *
          Real.exp (-κ * e ^ 2 * (nearCutoff B M n : ℝ)) ≤
        e * (widthParameter M n)⁻¹ :=
    mul_le_mul hpow hexp (Real.exp_pos _).le (by positivity)
  have hscale : 3 * (e * (widthParameter M n)⁻¹) =
      3 / ((n : ℝ) * e ^ 2) := by
    dsimp [widthParameter, e]
    field_simp [he.ne', hnR.ne'] <;> ring
  calc
    _ ≤ 3 * Real.rpow ((nearCutoff B M n + 1 : ℕ) : ℝ) (-(1 / 2) : ℝ) *
        Real.exp (-κ * e ^ 2 * (nearCutoff B M n : ℝ)) := by
      simpa [e] using! htail
    _ = 3 * (Real.rpow ((nearCutoff B M n + 1 : ℕ) : ℝ)
        (-(1 / 2) : ℝ) * Real.exp (-κ * e ^ 2 * (nearCutoff B M n : ℝ))) := by ring
    _ ≤ 3 * (e * (widthParameter M n)⁻¹) :=
      mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = _ := hscale

lemma mul_rpow_neg_five_half {k : ℕ} (hk : 0 < k) :
    (k : ℝ) * Real.rpow (k : ℝ) (-(5 / 2) : ℝ) =
      Real.rpow (k : ℝ) (-(3 / 2) : ℝ) := by
  have hkR : 0 < (k : ℝ) := by positivity
  calc
    _ = Real.rpow (k : ℝ) (1 + (-(5 / 2) : ℝ)) := by
      simpa only [Real.rpow_one] using!
        (Real.rpow_add hkR (1 : ℝ) (-(5 / 2) : ℝ)).symm
    _ = _ := by norm_num

lemma global_one_mass_bound {n M k : ℕ} {C κ : ℝ}
    (hk : 0 < k) (hC : 0 ≤ C) (hκ : 0 < κ)
    (hg : tupleGlobalBound n M 1 (fun _ => k) C κ) :
    massTerm n M k ≤ C * n * Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
      Real.exp (-κ * |degreeAt n M - 1| ^ 2 * k) := by
  have hnonneg : 0 ≤ (k : ℝ) ^ 3 / (n : ℝ) ^ 2 := by positivity
  have hexp : Real.exp (-κ * (|degreeAt n M - 1| ^ 2 * (k : ℝ) +
      (k : ℝ) ^ 3 / (n : ℝ) ^ 2)) ≤
      Real.exp (-κ * |degreeAt n M - 1| ^ 2 * k) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hglobal : momentOne n M k ≤
      C * (n : ℝ) * Real.rpow (k : ℝ) (-(5 / 2) : ℝ) *
        Real.exp (-κ * (|degreeAt n M - 1| ^ 2 * k +
          (k : ℝ) ^ 3 / (n : ℝ) ^ 2)) := by
    simpa [tupleGlobalBound, momentOne, Fin.sum_univ_one,
      Fin.prod_univ_one, sq_abs, neg_div] using! hg
  calc
    massTerm n M k = (k : ℝ) * momentOne n M k := rfl
    _ ≤ (k : ℝ) * (C * n * Real.rpow (k : ℝ) (-(5 / 2) : ℝ) *
        Real.exp (-κ * (|degreeAt n M - 1| ^ 2 * k +
          (k : ℝ) ^ 3 / (n : ℝ) ^ 2))) :=
      mul_le_mul_of_nonneg_left hglobal (by positivity)
    _ ≤ (k : ℝ) * (C * n * Real.rpow (k : ℝ) (-(5 / 2) : ℝ) *
        Real.exp (-κ * |degreeAt n M - 1| ^ 2 * k)) := by
      have hfactor :
          0 ≤ C * (n : ℝ) * Real.rpow (k : ℝ) (-(5 / 2) : ℝ) :=
        mul_nonneg (mul_nonneg hC (by positivity))
          (Real.rpow_nonneg (by positivity) _)
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hexp hfactor) (by positivity)
    _ = _ := by
      calc
        _ = C * n * ((k : ℝ) * Real.rpow (k : ℝ) (-(5 / 2) : ℝ)) *
            Real.exp (-κ * |degreeAt n M - 1| ^ 2 * k) := by ring
        _ = _ := by rw [mul_rpow_neg_five_half hk]

lemma near_actual_mean_tail_bound_of_witness
    {M : NatSeq} (hbare : bareSuper M)
    (C κ : ℝ) (hC : 0 < C) (hκ : 0 < κ) (n₀ : ℕ)
    (htuple : ∀ (n M : ℕ) (ks : Fin 1 → ℕ), n₀ ≤ n → M ≤ capacity n →
      1 / 2 ≤ degreeAt n M → degreeAt n M ≤ 3 / 2 → (∀ i, 0 < ks i) →
      tupleGlobalBound n M 1 ks C κ ∧
      (((∑ i, (ks i : ℝ)) ≤ (n : ℝ) / 16) → tupleLocalBound n M 1 ks C))
    (B : ℝ) (hB : 1 ≤ B) (hκB : 1 ≤ κ * B) :
    ∀ᶠ n in atTop,
      (∑ k ∈ Finset.Ico (nearCutoff B M n + 1) (largeCutoff n),
        massTerm n (M n) k) ≤ (3 * C) * (epsilon M n)⁻¹ ^ 2 := by
  have hlog : ∀ᶠ n in atTop, 1 ≤ Real.log (widthParameter M n) :=
    (tendsto_atTop.1 (Real.tendsto_log_atTop.comp
      (bare_width_tendsto_atTop (Or.inr hbare)))) 1
  have hw : ∀ᶠ n in atTop, 1 ≤ widthParameter M n :=
    (tendsto_atTop.1 (bare_width_tendsto_atTop (Or.inr hbare))) 1
  have hdeglo : ∀ᶠ n in atTop, 1 / 2 ≤ degree M n :=
    ((tendsto_order.1 hbare.2.2.1).1 (1 / 2) (by norm_num)).mono
      (fun _ h => h.le)
  have hdeghi : ∀ᶠ n in atTop, degree M n ≤ 3 / 2 :=
    ((tendsto_order.1 hbare.2.2.1).2 (3 / 2) (by norm_num)).mono
      (fun _ h => h.le)
  filter_upwards [hlog, hw, bare_epsilon_pos (Or.inr hbare),
    hbare.1, (eventually_ge_atTop n₀), hdeglo, hdeghi]
    with n hlog hw he hcap hn₀ hlo hhi
  have hn : 0 < n := by
    by_contra hn
    have : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    norm_num [widthParameter] at hw
  have hpoint : ∀ k ∈ Finset.Ico (nearCutoff B M n + 1) (largeCutoff n),
      massTerm n (M n) k ≤ C * n *
        (Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
          Real.exp (-κ * epsilon M n ^ 2 * k)) := by
    intro k hk
    have hkpos : 0 < k :=
      lt_of_lt_of_le (by omega : 0 < nearCutoff B M n + 1)
        (Finset.mem_Ico.mp hk).1
    have hg := (htuple n (M n) (fun _ => k) hn₀ hcap hlo hhi
      (fun _ => hkpos)).1
    simpa [epsilon, degree, degreeAt, mul_assoc] using!
      global_one_mass_bound hkpos hC.le hκ hg
  have hsum := cutoff_negThreeHalf_tail_bound
    (N := largeCutoff n) he hB hw hlog hκ hκB
  have hmajor : (∑ k ∈ Finset.Ico (nearCutoff B M n + 1) (largeCutoff n),
      massTerm n (M n) k) ≤
      C * n * (∑ k ∈ Finset.Ico (nearCutoff B M n + 1) (largeCutoff n),
        Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
          Real.exp (-κ * epsilon M n ^ 2 * k)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hpoint
  have hbound :
      (∑ k ∈ Finset.Ico (nearCutoff B M n + 1) (largeCutoff n),
        Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
          Real.exp (-κ * epsilon M n ^ 2 * k)) ≤
        3 / ((n : ℝ) * epsilon M n ^ 2) := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Ico_subset_Ico_right (Nat.le_succ _))
      (fun k _ _ => mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.exp_pos _).le))
    exact hsum
  calc
    _ ≤ C * n * (3 / ((n : ℝ) * epsilon M n ^ 2)) :=
      hmajor.trans (mul_le_mul_of_nonneg_left hbound (by positivity))
    _ = 3 * C * (epsilon M n)⁻¹ ^ 2 := by
      field_simp [he.ne', (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0)] <;> ring

lemma near_leading_mean_finite_tail_bound
    (hRate : RateStatement) {M : NatSeq} (hbare : bareSuper M)
    (B : ℝ) (hB : 4 < B) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n in atTop, ∀ N : ℕ,
      (∑ k ∈ Finset.Ico (nearCutoff B M n + 1) (N + 1),
        leadingMassTerm n (M n) k) ≤
        D * (epsilon M n)⁻¹ ^ 2 := by
  let D := Classical.choose leadingMassTerm_bound
  have hDspec := Classical.choose_spec leadingMassTerm_bound
  have hD : 0 < D := hDspec.1
  refine ⟨3 * D, by positivity, ?_⟩
  have hlog : ∀ᶠ n in atTop, 1 ≤ Real.log (widthParameter M n) :=
    (tendsto_atTop.1 (Real.tendsto_log_atTop.comp
      (bare_width_tendsto_atTop (Or.inr hbare)))) 1
  have hw : ∀ᶠ n in atTop, 1 ≤ widthParameter M n :=
    (tendsto_atTop.1 (bare_width_tendsto_atTop (Or.inr hbare))) 1
  have hlo : ∀ᶠ n in atTop, 1 / 2 ≤ degree M n :=
    ((tendsto_order.1 hbare.2.2.1).1 (1 / 2) (by norm_num)).mono
      (fun _ h => h.le)
  filter_upwards [hlog, hw, hlo, bare_epsilon_pos (Or.inr hbare),
    near_cutoff_rate_floor hRate hbare] with n hlog hw hlo he hfloor
  intro N
  have hn : 0 < n := by
    by_contra hn
    have : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    norm_num [widthParameter] at hw
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hκB : 1 ≤ (1 / 4 : ℝ) * B := by nlinarith
  have hterm : ∀ k ∈ Finset.Ico (nearCutoff B M n + 1) (N + 1),
      leadingMassTerm n (M n) k ≤
        D * n * (Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
          Real.exp (-(1 / 4 : ℝ) * epsilon M n ^ 2 * k)) := by
    intro k hk
    have hkpos : 0 < k :=
      lt_of_lt_of_le (by omega : 0 < nearCutoff B M n + 1)
        (Finset.mem_Ico.mp hk).1
    have hbound := leadingMassTerm_bound_at_rate_floor hkpos hD.le
      (hDspec.2 n (M n) k hkpos (by simpa [degree, degreeAt] using! hlo))
      (by simpa [degree, degreeAt, mul_assoc] using! hfloor)
    convert hbound using 1 <;> ring_nf
  have hsum := cutoff_negThreeHalf_tail_bound
    (N := N) he (by linarith : 1 ≤ B) hw hlog
      (by norm_num : 0 < (1 / 4 : ℝ)) hκB
  have hmajor :
      (∑ k ∈ Finset.Ico (nearCutoff B M n + 1) (N + 1),
        leadingMassTerm n (M n) k) ≤
        D * n * (∑ k ∈ Finset.Ico (nearCutoff B M n + 1) (N + 1),
          Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
            Real.exp (-(1 / 4 : ℝ) * epsilon M n ^ 2 * k)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  calc
    _ ≤ D * n * (3 / ((n : ℝ) * epsilon M n ^ 2)) :=
      hmajor.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
    _ = 3 * D * (epsilon M n)⁻¹ ^ 2 := by
      field_simp [he.ne', hnR.ne'] <;> ring

end
end Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_NearTail


namespace Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_NearMean

noncomputable section
open Filter
open scoped BigOperators Topology
open Erdos745.WrapUp.Proofs.W06_POISSON
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_Analytic
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_Finite
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_NearCutoff
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_NearLocal
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_NearTail

private lemma finite_head_series_error
    {f g : ℕ → ℝ} {H h : ℕ} {z L A D : ℝ}
    (hseries : HasSum g z) (hgzero : g 0 = 0)
    (hg : ∀ k, 0 ≤ g k) (hf : ∀ k, 0 ≤ f k)
    (hH : H + 1 ≤ h)
    (hlocal : (∑ k ∈ Finset.Ico 1 (H + 1), |f k - g k|) ≤ L)
    (hactual : (∑ k ∈ Finset.Ico (H + 1) h, f k) ≤ A)
    (hleading : ∀ N : ℕ,
      (∑ k ∈ Finset.Ico (H + 1) (N + 1), g k) ≤ D) :
    |(∑ k ∈ Finset.Ico 1 h, f k) - z| ≤ L + A + D := by
  let head := ∑ k ∈ Finset.Ico 1 (H + 1), g k
  have hprefix : ∀ N : ℕ,
      (∑ k ∈ Finset.Ico 1 N, g k) = ∑ k ∈ Finset.range N, g k := by
    intro N
    by_cases hN : 1 ≤ N
    · have hs := Finset.sum_Ico_consecutive g (m := 0) (n := 1) (k := N)
        (by omega) hN
      have hzero : (∑ k ∈ Finset.Ico 0 1, g k) = 0 := by
        simp [hgzero]
      rw [Finset.range_eq_Ico]
      simpa only [hzero, zero_add] using! hs
    · have hN0 : N = 0 := by omega
      subst N
      simp
  have hfull : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Ico 1 N, g k)
      atTop (𝓝 z) := by
    simpa only [hprefix] using! hseries.tendsto_sum_nat
  have hhead_le : head ≤ z := by
    rw [← hseries.tsum_eq]
    exact hseries.summable.sum_le_tsum (Finset.Ico 1 (H + 1))
      (fun k _ => hg k)
  have hz_le : z ≤ head + D := by
    apply le_of_tendsto hfull
    filter_upwards [eventually_ge_atTop (H + 1)] with N hN
    have htail : (∑ k ∈ Finset.Ico (H + 1) N, g k) ≤ D := by
      have hsubset : Finset.Ico (H + 1) N ⊆
          Finset.Ico (H + 1) (N + 1) :=
        Finset.Ico_subset_Ico_right (Nat.le_succ N)
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun k _ _ => hg k)).trans (hleading N)
    have hs := Finset.sum_Ico_consecutive g (m := 1) (n := H + 1)
      (k := N) (by omega) hN
    dsimp [head] at *
    linarith
  have hhead_diff :
      |(∑ k ∈ Finset.Ico 1 (H + 1), f k) - head| ≤ L := by
    calc
      _ = |∑ k ∈ Finset.Ico 1 (H + 1), (f k - g k)| := by
        simp only [Finset.sum_sub_distrib, head]
      _ ≤ ∑ k ∈ Finset.Ico 1 (H + 1), |f k - g k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ L := hlocal
  have hactual_nonneg : 0 ≤ ∑ k ∈ Finset.Ico (H + 1) h, f k :=
    Finset.sum_nonneg (fun k _ => hf k)
  have hsplit := Finset.sum_Ico_consecutive f (m := 1) (n := H + 1)
    (k := h) (by omega) hH
  rw [← hsplit]
  have hdiff := abs_sub_le_iff.mp hhead_diff
  apply abs_sub_le_iff.mpr
  constructor <;> dsimp [head] at * <;> linarith

lemma near_mean_boundedBy
    (hRate : RateStatement) (hT : TupleEstimatesStatement)
    (hA : AnalyticSumsStatement) {M : NatSeq} (hbare : bareSuper M) :
    boundedBy (treeMeanError M) (fun n => (epsilon M n)⁻¹ ^ 2) := by
  obtain ⟨C₁, κ₁, hC₁, hκ₁, n₀, htuple⟩ := hT.1 1 (by omega)
  let B : ℝ := 5 + κ₁⁻¹
  have hB : 4 < B := by
    dsimp [B]
    have hinv : 0 ≤ κ₁⁻¹ := inv_nonneg.mpr hκ₁.le
    linarith
  have hB1 : 1 ≤ B := by linarith
  have hκB : 1 ≤ κ₁ * B := by
    dsimp [B]
    rw [mul_add, mul_inv_cancel₀ hκ₁.ne']
    nlinarith
  obtain ⟨CL, hCL, hlocal⟩ := near_local_mean_eventual_bound
    hRate hT hA hbare B hB
  obtain ⟨D, hD, hleading⟩ := near_leading_mean_finite_tail_bound
    hRate hbare B hB
  have hactual := near_actual_mean_tail_bound_of_witness hbare
    C₁ κ₁ hC₁ hκ₁ n₀ htuple B hB1 hκB
  have hcut := cutoff_below_large_of_error (Or.inr hbare) B
    (lt_trans (by norm_num) hB)
  have hsuper := hbare.2.1
  refine ⟨CL + 3 * C₁ + D, by positivity, ?_⟩
  filter_upwards [hlocal, hactual, hleading, hcut, hsuper]
    with n hlocaln hactualn hleadingn hcutn hsupern
  have hdegree : 1 < degreeAt n (M n) := by
    simpa [degree, degreeAt] using! hsupern
  have hseries := leadingMassTerm_hasSum hA hdegree
  have hbridge := finite_head_series_error
    (f := massTerm n (M n)) (g := leadingMassTerm n (M n))
    (H := nearCutoff B M n) (h := largeCutoff n)
    (L := CL * (epsilon M n)⁻¹ ^ 2)
    (A := (3 * C₁) * (epsilon M n)⁻¹ ^ 2)
    (D := D * (epsilon M n)⁻¹ ^ 2)
    hseries (by simp [leadingMassTerm])
    (fun k => leadingMassTerm_nonneg (zero_lt_one.trans hdegree))
    (fun k => massTerm_nonneg n (M n) k)
    (by omega) hlocaln hactualn hleadingn
  have hmean :
      |treeMeanError M n| ≤
        CL * (epsilon M n)⁻¹ ^ 2 +
        (3 * C₁) * (epsilon M n)⁻¹ ^ 2 +
        D * (epsilon M n)⁻¹ ^ 2 := by
    simpa [treeMeanError, expect_treeMassBelow, massTerm, degree,
      degreeAt] using! hbridge
  calc
    |treeMeanError M n| ≤ _ := hmean
    _ = (CL + 3 * C₁ + D) * (epsilon M n)⁻¹ ^ 2 := by ring

end
end Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_NearMean
