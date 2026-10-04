module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W14_Horizon
public import Erdos745.WrapUp.Proofs.Internal.Linked.W14_Base

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


/-!
# History atoms as finite averages

An atom containing a fixed-edge graph is positive.  The conditional raw
moments are exactly finite averages of realized query counts on that atom.
This removes the positive-history side condition from the uniform horizon
estimates whenever a graph lies in the support of the fixed-edge law.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteAtoms

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Reveal
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Conditional
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteHorizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Asymptotics
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_MomentBounds
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_PoolUniform
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Horizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_CriticalBudget
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

def historyAtom {n : ℕ} (M : ℕ) (G : Graph n) (j : ℕ) :
    Finset (Graph n) :=
  (fixedGraphs n M).filter (fun H => revealTrace H j = revealTrace G j)

def historyAverage {n : ℕ} (M : ℕ) (G : Graph n) (j : ℕ)
    (f : Graph n → ℝ) : ℝ :=
  (historyAtom M G j).sum f / (historyAtom M G j).card

theorem graph_mem_fixedGraphs {n M : ℕ} (G : Graph n)
    (hG : G.card = M) : G ∈ fixedGraphs n M := by
  unfold fixedGraphs allGraphs
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.subset_univ G), hG⟩

theorem historyAtom_nonempty {n M : ℕ} (G : Graph n) (j : ℕ)
    (hG : G.card = M) : (historyAtom M G j).Nonempty := by
  exact ⟨G, Finset.mem_filter.mpr ⟨graph_mem_fixedGraphs G hG, rfl⟩⟩

theorem historyAtom_probability_pos {n M : ℕ} (G : Graph n)
    (j : ℕ) (hG : G.card = M) :
    0 < probM n M (fun H => revealTrace H j = revealTrace G j) := by
  unfold probM
  have hfixed : (fixedGraphs n M).Nonempty :=
    (historyAtom_nonempty G j hG).mono (Finset.filter_subset _ _)
  exact div_pos
    (by exact_mod_cast (Finset.card_pos.mpr (historyAtom_nonempty G j hG)))
    (by exact_mod_cast (Finset.card_pos.mpr hfixed))

theorem queryCount_on_history {n : ℕ} (G H : Graph n) (j : ℕ)
    (h : revealTrace H j = revealTrace G j) :
    queryCount H j = (H ∩ revealQuery (explore G j)).card := by
  have hbfs := congrArg RevealState.bfs h
  have hexplore : explore H j = explore G j := by
    simpa [revealTrace_bfs] using! hbfs
  simp [queryCount, hexplore]

private theorem conditionalProbM_eq_card_ratio {n M : ℕ}
    (hM : M ≤ capacity n) (P A : Graph n → Prop)
    (hP : ((fixedGraphs n M).filter P).Nonempty) :
    conditionalProbM n M P A =
      (((fixedGraphs n M).filter P).filter A).card /
        ((fixedGraphs n M).filter P).card := by
  have hfixed : ((fixedGraphs n M).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr (fixedGraphs_nonempty hM))
  have hfilter : (((fixedGraphs n M).filter P).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hP)
  unfold conditionalProbM probM
  field_simp [hfixed, hfilter]
  congr 1
  congr 1
  ext H
  simp [and_assoc]

private theorem sum_by_values {α : Type*} [DecidableEq α]
    (s : Finset α) (q : α → ℕ) (d : ℕ) (f : ℕ → ℝ)
    (hq : ∀ x ∈ s, q x ≤ d) :
    s.sum (fun x => f (q x)) =
      ∑ y ∈ Finset.range (d + 1),
        ((s.filter (fun x => q x = y)).card : ℝ) * f y := by
  have hmaps : ∀ x ∈ s, q x ∈ Finset.range (d + 1) := by
    intro x hx
    simp only [Finset.mem_range]
    exact Nat.lt_succ_of_le (hq x hx)
  calc
    s.sum (fun x => f (q x)) =
        ∑ y ∈ Finset.range (d + 1), ∑ x ∈ s with q x = y, f (q x) :=
          (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ y ∈ Finset.range (d + 1),
          ((s.filter (fun x => q x = y)).card : ℝ) * f y := by
      apply Finset.sum_congr rfl
      intro y hy
      calc
        ∑ x ∈ s with q x = y, f (q x) =
            ∑ _x ∈ s.filter (fun x => q x = y), f y := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [(Finset.mem_filter.mp hx).2]
        _ = ((s.filter (fun x => q x = y)).card : ℝ) * f y := by simp

/-- Every conditional raw moment is the ordinary average on its realized atom. -/
theorem historyAverage_queryPower {n M : ℕ} (hM : M ≤ capacity n)
    (G : Graph n) (j r : ℕ) (hG : G.card = M) :
    historyAverage M G j (fun H => (queryCount H j : ℝ) ^ r) =
      conditionalQueryRawMoment M G j r := by
  let atom := historyAtom M G j
  let d := (revealQuery (explore G j)).card
  have hne : (atom.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr (historyAtom_nonempty G j hG))
  have hbound : ∀ H ∈ atom, queryCount H j ≤ d := by
    intro H hH
    have htrace := (Finset.mem_filter.mp hH).2
    rw [queryCount_on_history G H j htrace]
    exact Finset.card_le_card Finset.inter_subset_right
  have hsum := sum_by_values atom (fun H => queryCount H j) d
    (fun y => (y : ℝ) ^ r) hbound
  have hcount (y : ℕ) :
      (atom.filter (fun H => queryCount H j = y)).card =
      (atom.filter (fun H => (H ∩ revealQuery (explore G j)).card = y)).card := by
    congr 1
    ext H
    constructor
    · intro hH
      have hmem := (Finset.mem_filter.mp hH).1
      have htrace := (Finset.mem_filter.mp hmem).2
      exact Finset.mem_filter.mpr
        ⟨hmem, (queryCount_on_history G H j htrace) ▸ (Finset.mem_filter.mp hH).2⟩
    · intro hH
      have hmem := (Finset.mem_filter.mp hH).1
      have htrace := (Finset.mem_filter.mp hmem).2
      exact Finset.mem_filter.mpr
        ⟨hmem, (queryCount_on_history G H j htrace).symm ▸
          (Finset.mem_filter.mp hH).2⟩
  unfold historyAverage conditionalQueryRawMoment rawMoment weightedMoment
  change (atom.sum (fun H => (queryCount H j : ℝ) ^ r)) / atom.card = _
  rw [hsum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y hy
  have hcond := conditionalProbM_eq_card_ratio hM
    (fun H => revealTrace H j = revealTrace G j)
    (fun H => (H ∩ revealQuery (explore G j)).card = y)
    (historyAtom_nonempty G j hG)
  have hatom : (fixedGraphs n M).filter
      (fun H => revealTrace H j = revealTrace G j) = atom := by
    ext H
    simp [atom, historyAtom]
  rw [hatom] at hcond
  have hcond' : conditionalProbM n M
      (fun H => revealTrace H j = revealTrace G j)
      (fun H => (H ∩ revealQuery (explore G j)).card = y) =
    ((atom.filter (fun H => (H ∩ revealQuery (explore G j)).card = y)).card : ℝ) /
      atom.card := by
    convert hcond using 1
    congr 1
    congr 1
    congr 1
    ext H
    simp
  change ((atom.filter (fun H => queryCount H j = y)).card : ℝ) *
      (y : ℝ) ^ r / atom.card =
      conditionalProbM n M
        (fun H => revealTrace H j = revealTrace G j)
        (fun H => (H ∩ revealQuery (explore G j)).card = y) * (y : ℝ) ^ r
  rw [hcond', ← hcount y]
  ring

theorem historyAverage_queryCount {n M : ℕ} (hM : M ≤ capacity n)
    (G : Graph n) (j : ℕ) (hG : G.card = M) :
    historyAverage M G j (fun H => (queryCount H j : ℝ)) =
      conditionalQueryRawMoment M G j 1 := by
  simpa using! historyAverage_queryPower hM G j 1 hG

theorem historyAverage_querySquare {n M : ℕ} (hM : M ≤ capacity n)
    (G : Graph n) (j : ℕ) (hG : G.card = M) :
    historyAverage M G j (fun H => (queryCount H j : ℝ) ^ 2) =
      conditionalQueryRawMoment M G j 2 :=
  historyAverage_queryPower hM G j 2 hG

theorem historyAverage_queryFourth {n M : ℕ} (hM : M ≤ capacity n)
    (G : Graph n) (j : ℕ) (hG : G.card = M) :
    historyAverage M G j (fun H => (queryCount H j : ℝ) ^ 4) =
      conditionalQueryRawMoment M G j 4 :=
  historyAverage_queryPower hM G j 4 hG

theorem historyAverage_const {n M : ℕ} (G : Graph n) (j : ℕ)
    (hG : G.card = M) (c : ℝ) :
    historyAverage M G j (fun _ => c) = c := by
  have hne : ((historyAtom M G j).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr (historyAtom_nonempty G j hG))
  simp [historyAverage, hne]

/-- The realized query count minus its atom mean has zero atom average. -/
theorem historyAverage_centeredQuery_zero {n M : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (G : Graph n) (j : ℕ) (hG : G.card = M) :
    historyAverage M G j (fun H => (queryCount H j : ℝ) -
      ((revealQuery (explore G j)).card : ℝ) * poolDensity M G j) = 0 := by
  have hpos := historyAtom_probability_pos G j hG
  have hEeq : poolEdgeCount G j = capacity n -
      (revealTrace G j).yes.card - (revealTrace G j).no.card := by
    unfold poolEdgeCount answeredCount
    rw [Finset.card_union_of_disjoint (revealTrace_yes_no_disjoint G j)]
    omega
  have hR : M - (revealTrace G j).yes.card ≤
      capacity n - (revealTrace G j).yes.card -
        (revealTrace G j).no.card := by
    change poolSuccessCount M G j ≤ _
    rw [← hEeq]
    exact poolSuccessCount_le_poolEdgeCount G j hG
  have hd : (revealQuery (explore G j)).card ≤
      capacity n - (revealTrace G j).yes.card -
        (revealTrace G j).no.card := by
    rw [← hEeq]
    exact queryCard_le_poolEdgeCount G j
  have hmean := conditionalQueryMean_all hfinite hM G j hpos
    hR hd
  have hmean' : conditionalQueryRawMoment M G j 1 =
      ((revealQuery (explore G j)).card : ℝ) * poolDensity M G j := by
    simpa [poolDensity, poolSuccessCount, hEeq] using! hmean
  have havg := historyAverage_queryCount hM G j hG
  have hconst := historyAverage_const G j hG
    (((revealQuery (explore G j)).card : ℝ) * poolDensity M G j)
  have hlinear : historyAverage M G j (fun H => (queryCount H j : ℝ) -
      ((revealQuery (explore G j)).card : ℝ) * poolDensity M G j) =
      historyAverage M G j (fun H => (queryCount H j : ℝ)) -
      historyAverage M G j (fun _ =>
        ((revealQuery (explore G j)).card : ℝ) * poolDensity M G j) := by
    unfold historyAverage
    rw [Finset.sum_sub_distrib, sub_div]
  rw [hlinear, havg, hconst]
  exact sub_eq_zero.mpr hmean'

/-- Uniform atom moment bounds on every graph in the fixed-edge support. -/
theorem historyAtom_horizon_moments {n M J : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (G : Graph n) (j : ℕ) (hG : G.card = M)
    (hbudget : HorizonBudget n M J 8) (hj : j < J) :
    historyAverage M G j (fun H => (queryCount H j : ℝ)) ≤ 4 ∧
    0 ≤ conditionalQueryRawMoment M G j 2 -
      (conditionalQueryRawMoment M G j 1) ^ 2 ∧
    conditionalQueryRawMoment M G j 2 -
      (conditionalQueryRawMoment M G j 1) ^ 2 ≤ 4 ∧
    historyAverage M G j (fun H => (queryCount H j : ℝ) ^ 4) ≤
      (8 : ℝ) ^ 4 + 6 * 8 ^ 3 + 7 * 8 ^ 2 + 8 := by
  have hpos := historyAtom_probability_pos G j hG
  rw [historyAverage_queryCount hM G j hG,
    historyAverage_queryFourth hM G j hG]
  have hmean := horizon_conditional_mean_le hfinite hM G j hG hbudget hj hpos
  have hvar := horizon_conditional_variance_le hfinite hM G j hG hbudget hj hpos
  have hfour := horizon_conditional_fourth_le hfinite hM G j hG hbudget hj hpos
  have hmean' : conditionalQueryRawMoment M G j 1 ≤ 4 := by
    simpa only [show (8 : ℝ) / 2 = 4 by norm_num] using! hmean
  have hvar' : 0 ≤ conditionalQueryRawMoment M G j 2 -
      (conditionalQueryRawMoment M G j 1) ^ 2 ∧
      conditionalQueryRawMoment M G j 2 -
      (conditionalQueryRawMoment M G j 1) ^ 2 ≤ 4 := by
    simpa only [show (8 : ℝ) / 2 = 4 by norm_num] using! hvar
  exact ⟨hmean', hvar'.1, hvar'.2, hfour⟩

end

end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteAtoms


/-!
# A finite-atom martingale maximal inequality

This argument uses ordinary sums on a finite support.  Its filtration is a
sequence of nested finite partitions, so no ambient conditional-expectation
choice is needed.  The first-crossing proof retains the sharp second-moment
scale required by the exploration horizon.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteMaximal

open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def atom (s : Finset α) (h : ℕ → α → β) (j : ℕ) (x : α) : Finset α :=
  s.filter (fun y => h j y = h j x)

def increment (X : ℕ → α → ℝ) (j : ℕ) (x : α) : ℝ :=
  X (j + 1) x - X j x

def restrictedEnergy (s : Finset α) (X : ℕ → α → ℝ)
    (P : α → Prop) (j : ℕ) : ℝ :=
  ∑ x ∈ s, if P x then (X j x) ^ 2 else 0

def firstCross (X : ℕ → α → ℝ) (ε : ℝ) (k : ℕ) (x : α) : Prop :=
  ε ≤ |X k x| ∧ ∀ i < k, |X i x| < ε

def crossesBy (X : ℕ → α → ℝ) (ε : ℝ) (J : ℕ) (x : α) : Prop :=
  ∃ k ≤ J, ε ≤ |X k x|

private theorem sum_fiber_zero (s : Finset α) (h : α → β)
    (D F : α → ℝ)
    (hD : ∀ x ∈ s, ∑ y ∈ s with h y = h x, D y = 0)
    (hF : ∀ x ∈ s, ∀ y ∈ s, h y = h x → F y = F x) :
    ∑ x ∈ s, F x * D x = 0 := by
  let t := s.image h
  have hmaps : ∀ x ∈ s, h x ∈ t := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun x => F x * D x)]
  apply Finset.sum_eq_zero
  intro b hb
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
  calc
    (∑ y ∈ s with h y = h x, F y * D y) =
        F x * (∑ y ∈ s with h y = h x, D y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      rw [hF x hx y (Finset.mem_filter.mp hy).1
        (Finset.mem_filter.mp hy).2]
    _ = 0 := by rw [hD x hx]; ring

private theorem sum_fiber_bound (s : Finset α) (h : α → β)
    (D : α → ℝ) (c : ℝ)
    (hD : ∀ x ∈ s,
      ∑ y ∈ s with h y = h x, (D y) ^ 2 ≤
        c * (((s.filter (fun y => h y = h x)).card : ℝ))) :
    ∑ x ∈ s, (D x) ^ 2 ≤ c * (s.card : ℝ) := by
  let t := s.image h
  have hmaps : ∀ x ∈ s, h x ∈ t := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hsum : ∑ b ∈ t, ∑ y ∈ s with h y = b, (D y) ^ 2 ≤
      ∑ b ∈ t, c * (((s.filter (fun y => h y = b)).card : ℝ)) := by
    apply Finset.sum_le_sum
    intro b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
    exact hD x hx
  have hcard : ∑ b ∈ t, (s.filter (fun y => h y = b)).card = s.card := by
    calc
      (∑ b ∈ t, (s.filter (fun y => h y = b)).card) =
          ∑ b ∈ t, ∑ y ∈ s with h y = b, (1 : ℕ) := by simp
      _ = ∑ y ∈ s, (1 : ℕ) := Finset.sum_fiberwise_of_maps_to hmaps _
      _ = s.card := by simp
  calc
    (∑ x ∈ s, (D x) ^ 2) =
        ∑ b ∈ t, ∑ y ∈ s with h y = b, (D y) ^ 2 :=
          (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ b ∈ t, c * (((s.filter (fun y => h y = b)).card : ℝ)) := hsum
    _ = c * (s.card : ℝ) := by
      rw [← Finset.mul_sum]
      norm_cast
      rw [hcard]

private theorem firstCross_unique (X : ℕ → α → ℝ) (ε : ℝ)
    {k l : ℕ} {x : α} (hk : firstCross X ε k x)
    (hl : firstCross X ε l x) : k = l := by
  rcases lt_trichotomy k l with h | h | h
  · exact False.elim ((not_lt_of_ge hk.1) (hl.2 k h))
  · exact h
  · exact False.elim ((not_lt_of_ge hl.1) (hk.2 l h))

private theorem crossesBy_iff_firstCross (X : ℕ → α → ℝ)
    (ε : ℝ) (J : ℕ) (x : α) :
    crossesBy X ε J x ↔ ∃ k ∈ Finset.range (J + 1),
      firstCross X ε k x := by
  constructor
  · rintro ⟨k, hkJ, hk⟩
    let q : ℕ → Prop := fun i => ε ≤ |X i x|
    have hq : ∃ i, q i := ⟨k, hk⟩
    let m := Nat.find hq
    have hm : q m := Nat.find_spec hq
    have hmJ : m ≤ J := (Nat.find_min' hq hk).trans hkJ
    refine ⟨m, Finset.mem_range.mpr (Nat.lt_succ_of_le hmJ), hm, ?_⟩
    intro i hi
    exact lt_of_not_ge (Nat.find_min hq hi)
  · rintro ⟨k, hk, hfirst⟩
    exact ⟨k, Nat.le_of_lt_succ (Finset.mem_range.mp hk), hfirst.1⟩

private theorem sum_firstCross (s : Finset α) (X : ℕ → α → ℝ)
    (ε : ℝ) (J : ℕ) (f : α → ℝ) :
    (∑ k ∈ Finset.range (J + 1),
      ∑ x ∈ s, if firstCross X ε k x then f x else 0) =
      ∑ x ∈ s, if crossesBy X ε J x then f x else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hhit : crossesBy X ε J x
  · obtain ⟨k, hk, hfirst⟩ :=
      (crossesBy_iff_firstCross X ε J x).mp hhit
    rw [if_pos hhit]
    simpa [hfirst] using! (Finset.sum_eq_single k
      (s := Finset.range (J + 1))
      (f := fun l => if firstCross X ε l x then f x else 0)
      (by
        intro l hl hlk
        have hnot : ¬ firstCross X ε l x := by
          intro hother
          exact hlk (firstCross_unique X ε hother hfirst)
        simp [hnot])
      (by intro hnot; exact False.elim (hnot hk)))
  · rw [if_neg hhit]
    apply Finset.sum_eq_zero
    intro k hk
    have hnot : ¬ firstCross X ε k x := by
      intro hfirst
      exact hhit ((crossesBy_iff_firstCross X ε J x).mpr
        ⟨k, hk, hfirst⟩)
    simp [hnot]

/-- A finite nested-partition martingale admits the usual second-moment
first-crossing bound.  The support need not be the entire ambient type. -/
theorem finite_maximal_square (s : Finset α) (h : ℕ → α → β)
    (X : ℕ → α → ℝ) (J : ℕ) (c ε : ℝ)
    (htrace : ∀ i j x y, i ≤ j → h j x = h j y → h i x = h i y)
    (hadapt : ∀ j x y, x ∈ s → y ∈ s →
      h j x = h j y → X j x = X j y)
    (hzero : ∀ j < J, ∀ x ∈ s,
      ∑ y ∈ atom s h j x, increment X j y = 0)
    (hsquare : ∀ j < J, ∀ x ∈ s,
      ∑ y ∈ atom s h j x, (increment X j y) ^ 2 ≤
        c * ((atom s h j x).card : ℝ))
    (hinit : ∀ x ∈ s, X 0 x = 0) (hε : 0 ≤ ε) :
    ε ^ 2 * (((s.filter (crossesBy X ε J)).card : ℝ)) ≤
      J * c * (s.card : ℝ) := by
  have horth (j : ℕ) (hj : j < J) (F : α → ℝ)
      (hF : ∀ x ∈ s, ∀ y ∈ s, h j y = h j x → F y = F x) :
      ∑ x ∈ s, F x * increment X j x = 0 := by
    apply sum_fiber_zero s (h j) (increment X j) F
    · intro x hx
      exact hzero j hj x hx
    · exact hF
  have hstep (j : ℕ) (hj : j < J) (P : α → Prop)
      (hP : ∀ x ∈ s, ∀ y ∈ s, h j y = h j x → (P y ↔ P x)) :
      restrictedEnergy s X P (j + 1) = restrictedEnergy s X P j +
        ∑ x ∈ s, if P x then (increment X j x) ^ 2 else 0 := by
    have hcross := horth j hj (fun x => if P x then 2 * X j x else 0)
      (by
        intro x hx y hy heq
        have hp := hP x hx y hy heq
        have hX := hadapt j y x hy hx heq
        by_cases hPx : P x <;> simp [hPx, hp, hX])
    unfold restrictedEnergy
    calc
      (∑ x ∈ s, if P x then (X (j + 1) x) ^ 2 else 0) =
          ∑ x ∈ s, ((if P x then (X j x) ^ 2 else 0) +
            (if P x then (increment X j x) ^ 2 else 0) +
            (if P x then 2 * X j x else 0) * increment X j x) := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hPx : P x
        · simp only [if_pos hPx]
          unfold increment
          ring
        · simp [hPx]
      _ = (∑ x ∈ s, if P x then (X j x) ^ 2 else 0) +
          (∑ x ∈ s, if P x then (increment X j x) ^ 2 else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hcross]
        ring
  have hmono (k r : ℕ) (hkr : k ≤ r) (hrJ : r ≤ J)
      (P : α → Prop)
      (hP : ∀ x ∈ s, ∀ y ∈ s, h k y = h k x → (P y ↔ P x)) :
      restrictedEnergy s X P k ≤ restrictedEnergy s X P r := by
    induction r, hkr using Nat.le_induction with
    | base => exact le_rfl
    | succ r hkr ih =>
        have hr : r < J := by omega
        have hPr : ∀ x ∈ s, ∀ y ∈ s,
            h r y = h r x → (P y ↔ P x) := by
          intro x hx y hy heq
          exact hP x hx y hy (htrace k r y x hkr heq)
        calc
          restrictedEnergy s X P k ≤ restrictedEnergy s X P r :=
            ih (by omega)
          _ ≤ restrictedEnergy s X P (r + 1) := by
            rw [hstep r hr P hPr]
            exact le_add_of_nonneg_right (Finset.sum_nonneg fun x hx => by
              by_cases hp : P x
              · simp only [if_pos hp]
                exact sq_nonneg _
              · simp [hp])
  have hglobal (k : ℕ) (hk : k ≤ J) :
      restrictedEnergy s X (fun _ => True) k ≤
        k * c * (s.card : ℝ) := by
    induction k with
    | zero =>
        unfold restrictedEnergy
        simp only [if_true, Nat.cast_zero, zero_mul]
        apply le_of_eq
        apply Finset.sum_eq_zero
        intro x hx
        rw [hinit x hx]
        ring
    | succ k ih =>
        have hk' : k < J := by omega
        have hsq : ∑ x ∈ s, (increment X k x) ^ 2 ≤
            c * (s.card : ℝ) := by
          apply sum_fiber_bound s (h k) (increment X k) c
          intro x hx
          exact hsquare k hk' x hx
        have hprior := ih (Nat.le_of_lt hk')
        calc
          restrictedEnergy s X (fun _ => True) (k + 1) =
              restrictedEnergy s X (fun _ => True) k +
                ∑ x ∈ s, (increment X k x) ^ 2 := by
            rw [hstep k hk' (fun _ => True) (by simp)]
            simp
          _ ≤ (k : ℝ) * c * (s.card : ℝ) + c * (s.card : ℝ) :=
            add_le_add hprior hsq
          _ = ((k + 1 : ℕ) : ℝ) * c * (s.card : ℝ) := by
            push_cast
            ring
  have hfirst_adapt (k r : ℕ) (hkr : k ≤ r)
      (x y : α) (hx : x ∈ s) (hy : y ∈ s)
      (heq : h r y = h r x) :
      firstCross X ε k y ↔ firstCross X ε k x := by
    have heqk := htrace k r y x hkr heq
    unfold firstCross at *
    constructor <;> intro hfirst
    · constructor
      · rw [hadapt k y x hy hx heqk] at hfirst
        exact hfirst.1
      · intro i hi
        have heqi := htrace i r y x (le_trans (Nat.le_of_lt hi) hkr) heq
        rw [← hadapt i y x hy hx heqi]
        exact hfirst.2 i hi
    · constructor
      · rw [hadapt k y x hy hx heqk]
        exact hfirst.1
      · intro i hi
        have heqi := htrace i r y x (le_trans (Nat.le_of_lt hi) hkr) heq
        rw [hadapt i y x hy hx heqi]
        exact hfirst.2 i hi
  have hfirst_energy (k : ℕ) (hk : k ∈ Finset.range (J + 1)) :
      ε ^ 2 * (((s.filter (firstCross X ε k)).card : ℝ)) ≤
        restrictedEnergy s X (firstCross X ε k) J := by
    have hkJ : k ≤ J := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hmin := hmono k J hkJ le_rfl (firstCross X ε k)
      (by intro x hx y hy heq; exact hfirst_adapt k k le_rfl x y hx hy heq)
    have hthreshold : ε ^ 2 * (((s.filter (firstCross X ε k)).card : ℝ)) ≤
        restrictedEnergy s X (firstCross X ε k) k := by
      have hsum : ε ^ 2 * (((s.filter (firstCross X ε k)).card : ℝ)) =
          ∑ x ∈ s.filter (firstCross X ε k), ε ^ 2 := by simp [mul_comm]
      rw [hsum]
      unfold restrictedEnergy
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum
      intro x hx
      have hcross := (Finset.mem_filter.mp hx).2
      have habs := hcross.1
      nlinarith [sq_nonneg (X k x), abs_nonneg (X k x),
        sq_abs (X k x)]
    exact hthreshold.trans hmin
  have hsum_first :
      ∑ k ∈ Finset.range (J + 1),
        ε ^ 2 * (((s.filter (firstCross X ε k)).card : ℝ)) =
      ε ^ 2 * (((s.filter (crossesBy X ε J)).card : ℝ)) := by
    have hcard (P : α → Prop) :
        (((s.filter P).card : ℝ)) =
          ∑ x ∈ s, if P x then (1 : ℝ) else 0 := by
      rw [← Finset.sum_filter]
      simp
    calc
      (∑ k ∈ Finset.range (J + 1),
        ε ^ 2 * (((s.filter (firstCross X ε k)).card : ℝ))) =
          ε ^ 2 * (∑ k ∈ Finset.range (J + 1),
            ∑ x ∈ s, if firstCross X ε k x then (1 : ℝ) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [hcard]
      _ = ε ^ 2 * (∑ x ∈ s,
          if crossesBy X ε J x then (1 : ℝ) else 0) := by
        rw [sum_firstCross]
      _ = ε ^ 2 * (((s.filter (crossesBy X ε J)).card : ℝ)) := by
        rw [hcard]
  have hpartition :
      ∑ k ∈ Finset.range (J + 1),
        restrictedEnergy s X (firstCross X ε k) J =
      restrictedEnergy s X (crossesBy X ε J) J := by
    unfold restrictedEnergy
    exact sum_firstCross s X ε J (fun x => (X J x) ^ 2)
  calc
    ε ^ 2 * (((s.filter (crossesBy X ε J)).card : ℝ)) =
        ∑ k ∈ Finset.range (J + 1),
          ε ^ 2 * (((s.filter (firstCross X ε k)).card : ℝ)) :=
            hsum_first.symm
    _ ≤ ∑ k ∈ Finset.range (J + 1),
          restrictedEnergy s X (firstCross X ε k) J := by
            exact Finset.sum_le_sum fun k hk => hfirst_energy k hk
    _ = restrictedEnergy s X (crossesBy X ε J) J := hpartition
    _ ≤ restrictedEnergy s X (fun _ => True) J := by
      unfold restrictedEnergy
      apply Finset.sum_le_sum
      intro x hx
      by_cases hhit : crossesBy X ε J x
      · simp [hhit]
      · simp only [if_neg hhit, if_true]
        exact sq_nonneg _
    _ ≤ J * c * (s.card : ℝ) := hglobal J le_rfl

end

end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteMaximal


/-!
# Pool density as a finite-atom martingale

The trace fibers form nested partitions.  On each realized fiber the next
query has the exact hypergeometric mean.  This module transfers that identity
and its conditional variance bound to the density increments, then applies
the finite first-crossing inequality.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_PoolMartingale

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Reveal
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Conditional
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteHorizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_PoolUniform
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Horizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteAtoms
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteMaximal
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The cumulative answer sets make the current trace determine every past
trace, even though the trace stores only the current BFS state. -/
theorem trace_eq_of_later {n : ℕ} (G H : Graph n) {i j : ℕ}
    (hij : i ≤ j) (htrace : revealTrace H j = revealTrace G j) :
    revealTrace H i = revealTrace G i := by
  have hpattern := (history_fiber_eq_patternEvent G H j).mp htrace
  apply (history_fiber_eq_patternEvent G H i).mpr
  constructor
  · exact (revealTrace_yes_mono G hij).trans hpattern.1
  · exact hpattern.2.mono_left (revealTrace_no_mono G hij)

theorem poolDensity_eq_of_trace {n M : ℕ} (G H : Graph n) (j : ℕ)
    (htrace : revealTrace H j = revealTrace G j) :
    poolDensity M H j = poolDensity M G j := by
  unfold poolDensity poolSuccessCount poolEdgeCount answeredCount
  rw [htrace]

theorem queryCard_eq_of_trace {n : ℕ} (G H : Graph n) (j : ℕ)
    (htrace : revealTrace H j = revealTrace G j) :
    (revealQuery (explore H j)).card =
      (revealQuery (explore G j)).card := by
  have hbfs := congrArg RevealState.bfs htrace
  simp only [revealTrace_bfs] at hbfs
  rw [hbfs]

theorem poolEdgeCount_eq_of_trace {n : ℕ} (G H : Graph n) (j : ℕ)
    (htrace : revealTrace H j = revealTrace G j) :
    poolEdgeCount H j = poolEdgeCount G j := by
  unfold poolEdgeCount answeredCount
  rw [htrace]

private theorem atom_centered_query_sum {n M : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (G : Graph n) (j : ℕ) (hG : G.card = M) :
    ∑ H ∈ historyAtom M G j,
      ((queryCount H j : ℝ) -
        ((revealQuery (explore G j)).card : ℝ) * poolDensity M G j) = 0 := by
  have h := historyAverage_centeredQuery_zero hfinite hM G j hG
  unfold historyAverage at h
  have hcard : ((historyAtom M G j).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr (historyAtom_nonempty G j hG))
  exact (div_eq_zero_iff).mp h |>.resolve_right hcard

/-- The query's centered square sum is bounded on every realized history. -/
theorem atom_centered_query_square_le {n M J : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (G : Graph n) (j : ℕ) (hG : G.card = M)
    (hbudget : HorizonBudget n M J 8) (hj : j < J) :
    ∑ H ∈ historyAtom M G j,
      ((queryCount H j : ℝ) -
        ((revealQuery (explore G j)).card : ℝ) * poolDensity M G j) ^ 2 ≤
      4 * (((historyAtom M G j).card : ℝ)) := by
  let s := historyAtom M G j
  let a : ℝ := ((revealQuery (explore G j)).card : ℝ) * poolDensity M G j
  have hspos : (0 : ℝ) < s.card := by
    exact_mod_cast (Finset.card_pos.mpr (historyAtom_nonempty G j hG))
  have hmean : historyAverage M G j (fun H => (queryCount H j : ℝ)) = a := by
    have hz := historyAverage_centeredQuery_zero hfinite hM G j hG
    have hc := historyAverage_const G j hG a
    unfold historyAverage at hz hc ⊢
    simp only [Finset.sum_sub_distrib] at hz
    have hconst : (∑ _H ∈ s, a) = (s.card : ℝ) * a := by simp
    dsimp [s, a] at *
    rw [hconst] at hz
    apply (div_eq_iff (ne_of_gt hspos)).mpr
    apply (div_eq_iff (ne_of_gt hspos)).mp at hz
    nlinarith
  have hraw := (historyAtom_horizon_moments hfinite hM G j hG hbudget hj).2.2.1
  have hq1 := historyAverage_queryCount hM G j hG
  have hq2 := historyAverage_querySquare hM G j hG
  have hsum1 : (∑ H ∈ s, (queryCount H j : ℝ)) = a * s.card := by
    dsimp [historyAverage, s] at hmean
    exact (div_eq_iff (ne_of_gt hspos)).mp hmean
  have hsum2 : (∑ H ∈ s, (queryCount H j : ℝ) ^ 2) ≤
      (4 + a ^ 2) * s.card := by
    rw [← hq1, ← hq2] at hraw
    rw [hmean] at hraw
    unfold historyAverage at hraw
    have h : (∑ H ∈ s, (queryCount H j : ℝ) ^ 2) / s.card ≤
        4 + a ^ 2 := by
      dsimp [s]
      linarith
    exact (div_le_iff₀ hspos).mp h
  have hexpand : (∑ H ∈ s, ((queryCount H j : ℝ) - a) ^ 2) =
      (∑ H ∈ s, (queryCount H j : ℝ) ^ 2) -
        2 * a * (∑ H ∈ s, (queryCount H j : ℝ)) +
        a ^ 2 * s.card := by
    calc
      (∑ H ∈ s, ((queryCount H j : ℝ) - a) ^ 2) =
          ∑ H ∈ s, ((queryCount H j : ℝ) ^ 2 -
            2 * a * (queryCount H j : ℝ) + a ^ 2) := by
            apply Finset.sum_congr rfl
            intro H hH
            ring
      _ = (∑ H ∈ s, (queryCount H j : ℝ) ^ 2) -
          2 * a * (∑ H ∈ s, (queryCount H j : ℝ)) + a ^ 2 * s.card := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            simp only [← Finset.mul_sum, Finset.sum_const]
            ring
  dsimp [s, a] at *
  rw [hexpand, hsum1]
  nlinarith

private theorem density_increment_on_atom {n M J : ℕ}
    (G H : Graph n) (j : ℕ) (hH : H ∈ historyAtom M G j)
    (hbudget : HorizonBudget n M J 8) (hj : j < J) :
    poolDensity M H (j + 1) - poolDensity M H j =
      (((revealQuery (explore G j)).card : ℝ) * poolDensity M G j -
        queryCount H j) /
      ((poolEdgeCount G j : ℝ) -
        (revealQuery (explore G j)).card) := by
  have hfixed := (Finset.mem_filter.mp hH).1
  have hcard : H.card = M := by
    exact (Finset.mem_filter.mp hfixed).2
  have htrace := (Finset.mem_filter.mp hH).2
  have hstrict : (revealQuery (explore H j)).card < poolEdgeCount H j := by
    have hnext := poolEdgeCount_ge_eight H (j + 1) hbudget (by omega)
    rw [poolEdgeCount_succ] at hnext
    omega
  rw [poolDensity_increment H j hcard hstrict]
  rw [poolDensity_eq_of_trace G H j htrace,
    queryCard_eq_of_trace G H j htrace,
    poolEdgeCount_eq_of_trace G H j htrace]

private theorem density_denominator_lower {n M J : ℕ}
    (G : Graph n) (j : ℕ) (hbudget : HorizonBudget n M J 8)
    (hj : j < J) :
    (capacity n - J * n : ℝ) ≤
      (poolEdgeCount G j : ℝ) -
        (revealQuery (explore G j)).card := by
  have hnext := poolEdgeCount_ge_horizon G (j + 1) hbudget (by omega)
  rw [poolEdgeCount_succ] at hnext
  have hquery := queryCard_le_poolEdgeCount G j
  have hreal : ((capacity n - J * n : ℕ) : ℝ) ≤
      (poolEdgeCount G j - (revealQuery (explore G j)).card : ℕ) := by
    exact_mod_cast hnext
  rw [Nat.cast_sub hquery] at hreal
  have hJcap : J * n ≤ capacity n := by
    have hb := hbudget.2.1
    omega
  rw [Nat.cast_sub hJcap, Nat.cast_mul] at hreal
  exact hreal

/-- The density increments have zero atom sum and a uniform square budget. -/
theorem density_atom_moments {n M J : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (G : Graph n) (j : ℕ) (hG : G.card = M)
    (hbudget : HorizonBudget n M J 8) (hj : j < J) :
    (∑ H ∈ historyAtom M G j,
      (poolDensity M H (j + 1) - poolDensity M H j)) = 0 ∧
    (∑ H ∈ historyAtom M G j,
      (poolDensity M H (j + 1) - poolDensity M H j) ^ 2) ≤
      (4 / ((capacity n - J * n : ℝ) ^ 2)) *
        ((historyAtom M G j).card : ℝ) := by
  let s := historyAtom M G j
  let a : ℝ := ((revealQuery (explore G j)).card : ℝ) * poolDensity M G j
  let b : ℝ := (poolEdgeCount G j : ℝ) -
    (revealQuery (explore G j)).card
  let L : ℝ := (capacity n : ℝ) - J * n
  have hL8 : (8 : ℝ) ≤ L := by
    have h := hbudget.2.1
    have hnat : 8 ≤ capacity n - J * n := by omega
    have hJcap : J * n ≤ capacity n := by omega
    have hreal : (8 : ℝ) ≤ ((capacity n - J * n : ℕ) : ℝ) := by
      exact_mod_cast hnat
    rw [Nat.cast_sub hJcap, Nat.cast_mul] at hreal
    exact hreal
  have hbL : L ≤ b := density_denominator_lower G j hbudget hj
  have hbpos : 0 < b := by linarith
  have hLpos : 0 < L := by linarith
  have hrewrite (H : Graph n) (hH : H ∈ s) :
      poolDensity M H (j + 1) - poolDensity M H j =
        (a - queryCount H j) / b :=
    density_increment_on_atom G H j hH hbudget hj
  have hcenter := atom_centered_query_sum hfinite hM G j hG
  have hcenter2 := atom_centered_query_square_le hfinite hM G j hG hbudget hj
  constructor
  · calc
      (∑ H ∈ s, (poolDensity M H (j + 1) - poolDensity M H j)) =
          ∑ H ∈ s, (a - queryCount H j) / b := by
        apply Finset.sum_congr rfl
        intro H hH
        exact hrewrite H hH
      _ = -((∑ H ∈ s, ((queryCount H j : ℝ) - a)) / b) := by
        rw [Finset.sum_div]
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro H hH
        ring
      _ = 0 := by rw [hcenter]; simp
  · calc
      (∑ H ∈ s, (poolDensity M H (j + 1) - poolDensity M H j) ^ 2) =
          (∑ H ∈ s, ((queryCount H j : ℝ) - a) ^ 2) / b ^ 2 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro H hH
        rw [hrewrite H hH]
        ring_nf
      _ ≤ (4 * (s.card : ℝ)) / b ^ 2 := by
        apply div_le_div_of_nonneg_right hcenter2
        positivity
      _ ≤ (4 / L ^ 2) * (s.card : ℝ) := by
        have hs : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
        have hpow : L ^ 2 ≤ b ^ 2 := by gcongr
        have hLp : 0 < L ^ 2 := sq_pos_of_pos hLpos
        have hbp : 0 < b ^ 2 := sq_pos_of_pos hbpos
        rw [div_mul_eq_mul_div]
        apply (div_le_div_iff₀ hbp hLp).mpr
        nlinarith [mul_nonneg hs (sub_nonneg.mpr hpow)]

/-- Sharp finite-horizon maximal inequality for the pool density. -/
theorem poolDensity_maximal_finite {n M J : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (hbudget : HorizonBudget n M J 8) (ε : ℝ) (hε : 0 ≤ ε) :
    ε ^ 2 * (((fixedGraphs n M).filter
      (fun G => ∃ k ≤ J,
        ε ≤ |poolDensity M G k - poolDensity M G 0|)).card : ℝ) ≤
      J * (4 / ((capacity n - J * n : ℝ) ^ 2)) *
        ((fixedGraphs n M).card : ℝ) := by
  let X : ℕ → Graph n → ℝ :=
    fun k G => poolDensity M G k - poolDensity M G 0
  have hincrement (j : ℕ) (G : Graph n) :
      increment X j G = poolDensity M G (j + 1) - poolDensity M G j := by
    dsimp [increment, X]
    ring
  have htrace : ∀ i j (G H : Graph n), i ≤ j →
      revealTrace G j = revealTrace H j →
      revealTrace G i = revealTrace H i := by
    intro i j G H hij heq
    exact trace_eq_of_later H G hij heq
  have hadapt : ∀ j (G H : Graph n), G ∈ fixedGraphs n M →
      H ∈ fixedGraphs n M →
      revealTrace G j = revealTrace H j → X j G = X j H := by
    intro j G H hG hH heq
    have h0 := trace_eq_of_later H G (Nat.zero_le j) heq
    dsimp [X]
    rw [poolDensity_eq_of_trace H G j heq,
      poolDensity_eq_of_trace H G 0 h0]
  have hzero : ∀ j < J, ∀ G ∈ fixedGraphs n M,
      ∑ H ∈ atom (fixedGraphs n M) (fun j G => revealTrace G j) j G,
        increment X j H = 0 := by
    intro j hj G hG
    have hcard : G.card = M := (Finset.mem_filter.mp hG).2
    have hm := (density_atom_moments hfinite hM G j hcard hbudget hj).1
    simpa only [atom, historyAtom, hincrement] using! hm
  have hsquare : ∀ j < J, ∀ G ∈ fixedGraphs n M,
      ∑ H ∈ atom (fixedGraphs n M) (fun j G => revealTrace G j) j G,
        (increment X j H) ^ 2 ≤
          (4 / ((capacity n - J * n : ℝ) ^ 2)) *
            ((atom (fixedGraphs n M) (fun j G => revealTrace G j) j G).card : ℝ) := by
    intro j hj G hG
    have hcard : G.card = M := (Finset.mem_filter.mp hG).2
    have hm := (density_atom_moments hfinite hM G j hcard hbudget hj).2
    simpa only [atom, historyAtom, hincrement] using! hm
  have hbound := finite_maximal_square (fixedGraphs n M) (fun j G => revealTrace G j) X J
    (4 / ((capacity n - J * n : ℝ) ^ 2)) ε
    htrace hadapt hzero hsquare (by intro G hG; simp [X]) hε
  have hfilter : (fixedGraphs n M).filter (crossesBy X ε J) =
      (fixedGraphs n M).filter (fun G => ∃ k ≤ J,
        ε ≤ |poolDensity M G k - poolDensity M G 0|) := by
    ext G
    simp [crossesBy, X]
  rw [hfilter] at hbound
  exact hbound

end

end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_PoolMartingale


/-!
# Critical-window concentration of the unrevealed-edge density

The finite maximal inequality is combined with the critical-window horizon
budget.  The estimate is uniform over all times up to a fixed multiple of
`n23 n`, at the scale needed in the exploration drift.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_PoolConcentration

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteHorizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Horizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_CriticalBudget
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_PoolMartingale
open Filter
open scoped Topology

noncomputable section
attribute [local instance] Classical.propDecidable

theorem horizon_pool_lower {n M J : ℕ}
    (hn : 32 ≤ n) (hJ : 8 * J ≤ n)
    (hbudget : HorizonBudget n M J 8) :
    (n : ℝ) ^ 2 / 4 ≤ (capacity n - J * n : ℕ) := by
  have hcap : n * (n - 1) ≤ 2 * capacity n + 1 := by
    rw [capacity, Nat.choose_two_right]
    omega
  have hJn : 8 * (J * n) ≤ n * n := by
    nlinarith [Nat.mul_le_mul_right n hJ]
  have hsub : capacity n - J * n + J * n = capacity n := by
    have hh := hbudget.2.1
    omega
  have hnn : 32 * n ≤ n * n := Nat.mul_le_mul_right n hn
  have hsub1 : n - 1 + 1 = n := by omega
  have hmult : n * (n - 1) + n = n * n := by
    nlinarith [congrArg (n * ·) hsub1]
  have hNat : n * n ≤ 4 * (capacity n - J * n) := by
    nlinarith
  have hReal : (n : ℝ) ^ 2 ≤ 4 * ((capacity n - J * n : ℕ) : ℝ) := by
    have hcast : ((n * n : ℕ) : ℝ) ≤
        4 * ((capacity n - J * n : ℕ) : ℝ) := by exact_mod_cast hNat
    simpa only [Nat.cast_mul, pow_two] using! hcast
  linarith

theorem n13_cube (n : ℕ) (hn : 0 < n) :
    n13 n ^ 3 = (n : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold n13
  change ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = (n : ℝ)
  rw [← Real.rpow_mul_natCast hn'.le (1 / 3 : ℝ) 3]
  norm_num only
  exact Real.rpow_one (n : ℝ)

theorem finite_poolDensity_probability_bound {n M J : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (hn : 32 ≤ n) (hJ : 8 * J ≤ n)
    (hbudget : HorizonBudget n M J 8)
    (ε : ℝ) (hε : 0 < ε) :
    probM n M (fun G => ∃ k ≤ J,
      ε ≤ |poolDensity M G k - poolDensity M G 0|) ≤
      64 * (n : ℝ) / (ε ^ 2 * (n : ℝ) ^ 4) := by
  let L : ℝ := (capacity n : ℝ) - J * n
  let F : ℝ := ((fixedGraphs n M).card : ℝ)
  let B : ℝ := (((fixedGraphs n M).filter
    (fun G => ∃ k ≤ J,
      ε ≤ |poolDensity M G k - poolDensity M G 0|)).card : ℝ)
  have hF : 0 < F := by
    change (0 : ℝ) < ((fixedGraphs n M).card : ℝ)
    exact_mod_cast (Finset.card_pos.mpr (fixedGraphs_nonempty hM))
  have hL : (n : ℝ) ^ 2 / 4 ≤ L := by
    have hnat := horizon_pool_lower hn hJ hbudget
    have hJcap : J * n ≤ capacity n := by
      have hb := hbudget.2.1
      omega
    rw [Nat.cast_sub hJcap, Nat.cast_mul] at hnat
    exact hnat
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hLpos : 0 < L := by nlinarith
  have hLpow : (n : ℝ) ^ 4 / 16 ≤ L ^ 2 := by
    nlinarith [sq_nonneg (L - (n : ℝ) ^ 2 / 4)]
  have hJreal : (J : ℝ) ≤ n := by
    exact_mod_cast hbudget.1
  have hmax := poolDensity_maximal_finite hfinite hM hbudget ε hε.le
  change ε ^ 2 * B ≤ (J : ℝ) * (4 / L ^ 2) * F at hmax
  have hprob : probM n M (fun G => ∃ k ≤ J,
      ε ≤ |poolDensity M G k - poolDensity M G 0|) = B / F := by
    simp only [probM, B, F]
    congr 1
    congr 1
    congr 1
    ext G
    simp
  rw [hprob]
  have hB : 0 ≤ B := Nat.cast_nonneg _
  have hbound : B / F ≤ 4 * (J : ℝ) / (ε ^ 2 * L ^ 2) := by
    have hLp : 0 < L ^ 2 := sq_pos_of_pos hLpos
    have hden : 0 < ε ^ 2 * L ^ 2 := mul_pos (sq_pos_of_pos hε) hLp
    have hmax' : ε ^ 2 * B ≤ (4 * (J : ℝ) * F) / L ^ 2 := by
      convert hmax using 1; ring
    have hcross := (le_div_iff₀ hLp).mp hmax'
    exact (div_le_div_iff₀ hF hden).mpr (by nlinarith [hcross])
  calc
    B / F ≤ 4 * (J : ℝ) / (ε ^ 2 * L ^ 2) := hbound
    _ ≤ 64 * (n : ℝ) / (ε ^ 2 * (n : ℝ) ^ 4) := by
      have hden : 0 < ε ^ 2 * L ^ 2 := mul_pos (sq_pos_of_pos hε) (sq_pos_of_pos hLpos)
      have hden2 : 0 < ε ^ 2 * (n : ℝ) ^ 4 := by positivity
      have hJn := mul_le_mul_of_nonneg_right hJreal
        (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 4)
      have hLn := mul_le_mul_of_nonneg_left hLpow hnpos.le
      have hcore : (J : ℝ) * (n : ℝ) ^ 4 ≤
          16 * (n : ℝ) * L ^ 2 := by nlinarith [hJn, hLn]
      have hcore' := mul_le_mul_of_nonneg_left hcore (sq_nonneg ε)
      exact (div_le_div_iff₀ hden hden2).mpr (by nlinarith [hcore'])

/-- Uniform pool-density error is negligible at the drift scale. -/
theorem critical_poolDensity_concentration
    (hfinite : FiniteEnumerationStatement) (M : NatSeq) (lam T δ : ℝ)
    (hcritical : criticalWindow M lam) (hT : 0 ≤ T) (hδ : 0 < δ) :
    Tendsto
      (fun n => probM n (M n) (fun G => ∃ k ≤ ⌊T * n23 n⌋₊,
        δ / (n13 n) ^ 4 ≤
          |poolDensity (M n) G k - poolDensity (M n) G 0|))
      atTop (𝓝 0) := by
  let J : ℕ → ℕ := fun n => ⌊T * n23 n⌋₊
  let upper : ℕ → ℝ := fun n => 64 / (δ ^ 2 * n13 n)
  have hupper : Tendsto upper atTop (𝓝 0) := by
    have hinv : Tendsto (fun n => (n13 n)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp n13_tendsto_atTop
    have heq : upper = fun n => (64 / δ ^ 2) * (n13 n)⁻¹ := by
      funext n
      dsimp [upper]
      rw [div_eq_mul_inv, mul_inv_rev, div_eq_mul_inv]
      ring
    rw [heq]
    simpa only [mul_zero] using!
      (tendsto_const_nhds (x := 64 / δ ^ 2)).mul hinv
  have hgood : ∀ᶠ n : ℕ in atTop,
      probM n (M n) (fun G => ∃ k ≤ J n,
        δ / (n13 n) ^ 4 ≤
          |poolDensity (M n) G k - poolDensity (M n) G 0|) ≤
        upper n := by
    filter_upwards [eventually_horizonBudget M lam T hcritical hT,
      eventually_eighth_horizon T hT, eventually_ge_atTop (32 : ℕ),
      hcritical.1] with n hbudget hJ hn hM
    have h13pos : 0 < n13 n := by
      unfold n13
      exact Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < n)) _
    have hε : 0 < δ / (n13 n) ^ 4 :=
      div_pos hδ (pow_pos h13pos _)
    have hfin := finite_poolDensity_probability_bound hfinite hM hn hJ
      hbudget (δ / (n13 n) ^ 4) hε
    have hcub : n13 n ^ 3 = (n : ℝ) := n13_cube n (by omega)
    have heq : 64 * (n : ℝ) /
        ((δ / (n13 n) ^ 4) ^ 2 * (n : ℝ) ^ 4) = upper n := by
      dsimp [upper]
      rw [← hcub]
      field_simp
    exact hfin.trans_eq heq
  have hnonneg : ∀ n, 0 ≤ probM n (M n) (fun G => ∃ k ≤ J n,
      δ / (n13 n) ^ 4 ≤
        |poolDensity (M n) G k - poolDensity (M n) G 0|) := by
    intro n
    unfold probM
    positivity
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
  · exact Filter.Eventually.of_forall hnonneg
  · exact hgood

end

end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_PoolConcentration


/-!
# The finite exploration queue on a critical horizon

The centered query sum is adapted to the actual reveal trace.  The minimum
below is the running minimum of the same concrete BFS walk, not a second walk.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_QueueControl

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Finite
open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Pruefer
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Reveal
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteHorizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteAtoms
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Horizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_PoolUniform
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_CriticalBudget
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteMaximal
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_PoolMartingale
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_PoolConcentration
open Filter
open scoped BigOperators Topology

noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000

private theorem edgeOf_eq_endpoints {n : ℕ} (v u : Fin n) (hvu : v ≠ u)
    (e : Edge n)
    (he : (e.val.1 = v ∧ e.val.2 = u) ∨
      (e.val.1 = u ∧ e.val.2 = v)) : edgeOf v u hvu = e := by
  rcases e with ⟨⟨a, b⟩, hab⟩
  rcases he with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · dsimp at ha hb
    subst a
    subst b
    apply Subtype.ext
    simp [edgeOf, hab]
  · dsimp at ha hb
    subst a
    subst b
    have hnot : ¬ v < u := not_lt.mpr (le_of_lt hab)
    apply Subtype.ext
    simp [edgeOf, hnot]

private theorem edgeOf_right_injective {n : ℕ} (v u w : Fin n)
    (hu : v ≠ u) (hw : v ≠ w)
    (heq : edgeOf v u hu = edgeOf v w hw) : u = w := by
  have h₁ := edgeOf_endpoints v u hu
  have h₂ := edgeOf_endpoints v w hw
  rw [heq] at h₁
  rcases h₁ with ⟨h₁a, h₁b⟩ | ⟨h₁a, h₁b⟩ <;>
    rcases h₂ with ⟨h₂a, h₂b⟩ | ⟨h₂a, h₂b⟩ <;> omega

private theorem queryCount_incident_eq_children {n : ℕ} (G : Graph n)
    (discovered : Finset (Fin n)) (v : Fin n)
    (hv : v ∈ discovered) :
    (G ∩ incidentQuery v discovered).card =
      (newChildren G discovered v).card := by
  symm
  apply Finset.card_bij
    (fun u hu => edgeOf v u (by
      have hnot := ((mem_newChildren_iff G discovered v u).mp hu).1
      intro heq
      exact hnot (heq ▸ hv)))
  · intro u hu
    have hnot := ((mem_newChildren_iff G discovered v u).mp hu).1
    have hadj := ((mem_newChildren_iff G discovered v u).mp hu).2
    rcases hadj with ⟨e, heG, he⟩
    have hEq : edgeOf v u (by
        intro heq
        exact hnot (heq ▸ hv)) = e :=
      edgeOf_eq_endpoints v u (by
        intro heq
        exact hnot (heq ▸ hv)) e he
    rw [hEq]
    refine Finset.mem_inter.mpr ⟨heG, ?_⟩
    rcases he with h | h
    · exact (mem_incidentQuery_iff v discovered e).mpr
        (Or.inl ⟨h.1, by simpa [h.2] using! hnot⟩)
    · exact (mem_incidentQuery_iff v discovered e).mpr
        (Or.inr ⟨h.2, by simpa [h.1] using! hnot⟩)
  · intro u hu w hw heq
    exact edgeOf_right_injective v u w
      (by intro h; exact ((mem_newChildren_iff G discovered v u).mp hu).1 (h ▸ hv))
      (by intro h; exact ((mem_newChildren_iff G discovered v w).mp hw).1 (h ▸ hv)) heq
  · intro e he
    have heG := (Finset.mem_inter.mp he).1
    have heQ := (Finset.mem_inter.mp he).2
    rcases (mem_incidentQuery_iff v discovered e).mp heQ with h | h
    · have hne : v ≠ e.val.2 := by
        intro heq
        exact (ne_of_lt e.property) (h.1.trans heq)
      refine ⟨e.val.2, (mem_newChildren_iff G discovered v e.val.2).mpr
        ⟨h.2, ⟨e, heG, Or.inl ⟨h.1, rfl⟩⟩⟩, ?_⟩
      exact edgeOf_eq_endpoints v e.val.2 hne e (Or.inl ⟨h.1, rfl⟩)
    · have hne : v ≠ e.val.1 := by
        intro heq
        exact (ne_of_lt e.property) (heq.symm.trans h.1.symm)
      refine ⟨e.val.1, (mem_newChildren_iff G discovered v e.val.1).mpr
        ⟨h.2, ⟨e, heG, Or.inr ⟨rfl, h.1⟩⟩⟩, ?_⟩
      exact edgeOf_eq_endpoints v e.val.1 hne e (Or.inr ⟨rfl, h.1⟩)

/-- The successful reveal queries are exactly the new BFS children. -/
theorem queryCount_eq_children {n : ℕ} (G : Graph n) (j : ℕ)
    (hj : j < n) :
    queryCount G j =
      match selectRoot (explore G j) with
      | none => 0
      | some (v, _, discovered) => (newChildren G discovered v).card := by
  have hp := processed_card_of_le G j hj.le
  have hpart := processed_partition G j
  rcases hstate : explore G j with ⟨seen, queue, z⟩
  cases queue with
  | cons v rest =>
      have hv : v ∈ seen := by
        have hs := explore_queue_subset_seen G j
        rw [hstate] at hs
        exact hs (by simp)
      simp only [hstate, selectRoot_queue_cons, queryCount,
        revealQuery_queue_cons]
      exact queryCount_incident_eq_children G seen v hv
  | nil =>
      have hseen : seen.card = j := by
        have heq : processed G j = seen := by
          simpa [hstate] using! hpart.2
        simpa [heq] using! hp
      have hnonempty : ((Finset.univ : Finset (Fin n)) \ seen).Nonempty := by
        apply Finset.sdiff_nonempty_of_card_lt_card
        simpa [hseen] using! hj
      let v := ((Finset.univ : Finset (Fin n)) \ seen).min' hnonempty
      simp only [hstate, selectRoot_queue_nil_of_nonempty seen z hnonempty,
        queryCount, revealQuery_queue_nil_of_nonempty seen z hnonempty]
      exact queryCount_incident_eq_children G (insert v seen) v
        (Finset.mem_insert_self _ _)

theorem actualWalkIncrement_eq_queryCount {n : ℕ} (G : Graph n) (j : ℕ)
    (hj : j < n) :
    actualWalkIncrement G j = (queryCount G j : ℝ) - 1 := by
  have hq := queryCount_eq_children G j hj
  rcases hstate : explore G j with ⟨seen, queue, z⟩
  cases queue with
  | cons v rest =>
      simp only [hstate, selectRoot_queue_cons] at hq
      unfold actualWalkIncrement
      rw [explore_succ, hstate, bfsStep_queue_cons]
      rw [hq]
      norm_num
      ring
  | nil =>
      have hp := processed_card_of_le G j hj.le
      have hpart := processed_partition G j
      have hseen : seen.card = j := by
        have heq : processed G j = seen := by
          simpa [hstate] using! hpart.2
        simpa [heq] using! hp
      have hnonempty : ((Finset.univ : Finset (Fin n)) \ seen).Nonempty := by
        apply Finset.sdiff_nonempty_of_card_lt_card
        simpa [hseen] using! hj
      simp only [hstate, selectRoot_queue_nil_of_nonempty seen z hnonempty] at hq
      unfold actualWalkIncrement
      rw [explore_succ, hstate,
        bfsStep_queue_nil_of_nonempty G seen z hnonempty]
      rw [hq]
      norm_num
      ring

def queryMean {n : ℕ} (M : ℕ) (G : Graph n) (j : ℕ) : ℝ :=
  ((revealQuery (explore G j)).card : ℝ) * poolDensity M G j

def centeredPartial {n : ℕ} (M : ℕ) (G : Graph n) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, ((queryCount G j : ℝ) - queryMean M G j)

def predictablePartial {n : ℕ} (M : ℕ) (G : Graph n) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, (queryMean M G j - 1)

theorem queryMean_eq_of_trace {n M : ℕ} (G H : Graph n) (j : ℕ)
    (h : revealTrace H j = revealTrace G j) :
    queryMean M H j = queryMean M G j := by
  unfold queryMean
  rw [queryCard_eq_of_trace G H j h, poolDensity_eq_of_trace G H j h]

theorem queryCount_eq_of_later_trace {n : ℕ} (G H : Graph n) {i j : ℕ}
    (hij : i < j) (h : revealTrace H j = revealTrace G j) :
    queryCount H i = queryCount G i := by
  have hi := trace_eq_of_later G H hij.le h
  have his := trace_eq_of_later G H (Nat.succ_le_of_lt hij) h
  have hH := revealedYes_card_succ H i
  have hG := revealedYes_card_succ G i
  have hi' : (revealTrace H i).yes.card = (revealTrace G i).yes.card :=
    congrArg (fun r : RevealState n => r.yes.card) hi
  have his' : (revealTrace H (i + 1)).yes.card =
      (revealTrace G (i + 1)).yes.card :=
    congrArg (fun r : RevealState n => r.yes.card) his
  omega

theorem centeredPartial_eq_of_trace {n M : ℕ} (G H : Graph n) (j : ℕ)
    (h : revealTrace H j = revealTrace G j) :
    centeredPartial M H j = centeredPartial M G j := by
  unfold centeredPartial
  apply Finset.sum_congr rfl
  intro i hi
  have hij := Finset.mem_range.mp hi
  rw [queryCount_eq_of_later_trace G H hij h]
  exact congrArg (fun x : ℝ => (queryCount G i : ℝ) - x)
    (queryMean_eq_of_trace G H i (trace_eq_of_later G H hij.le h))

theorem centeredPartial_zero {n M : ℕ} (G : Graph n) :
    centeredPartial M G 0 = 0 := by simp [centeredPartial]

theorem centeredPartial_increment {n M : ℕ} (G : Graph n) (j : ℕ) :
    increment (fun k H => centeredPartial M H k) j G =
      (queryCount G j : ℝ) - queryMean M G j := by
  simp [increment, centeredPartial, Finset.sum_range_succ,
    Finset.sum_sub_distrib]
  ring

theorem centered_atom_zero {n M : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (G : Graph n) (j : ℕ) (hG : G.card = M) :
    ∑ H ∈ historyAtom M G j,
      increment (fun k H => centeredPartial M H k) j H = 0 := by
  have hz := historyAverage_centeredQuery_zero hfinite hM G j hG
  unfold historyAverage at hz
  have hcard : ((historyAtom M G j).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr (historyAtom_nonempty G j hG))
  have hsum := (div_eq_zero_iff).mp hz |>.resolve_right hcard
  calc
    (∑ H ∈ historyAtom M G j,
      increment (fun k H => centeredPartial M H k) j H) =
        ∑ H ∈ historyAtom M G j,
          ((queryCount H j : ℝ) - queryMean M G j) := by
      apply Finset.sum_congr rfl
      intro H hH
      rw [centeredPartial_increment (M := M)]
      have ht := (Finset.mem_filter.mp hH).2
      rw [queryMean_eq_of_trace G H j ht]
    _ = 0 := by simpa only [queryMean] using! hsum

theorem centered_atom_square {n M J : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (G : Graph n) (j : ℕ) (hG : G.card = M)
    (hbudget : HorizonBudget n M J 8) (hj : j < J) :
    ∑ H ∈ historyAtom M G j,
      (increment (fun k H => centeredPartial M H k) j H) ^ 2 ≤
        4 * ((historyAtom M G j).card : ℝ) := by
  have hs := atom_centered_query_square_le hfinite hM G j hG hbudget hj
  convert hs using 1
  apply Finset.sum_congr rfl
  intro H hH
  rw [centeredPartial_increment]
  have ht := (Finset.mem_filter.mp hH).2
  rw [queryMean_eq_of_trace G H j ht]
  rfl

/-- The centered query sum has the finite first-crossing bound on the
realized fixed-edge law. -/
theorem centeredPartial_maximal_finite {n M J : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (hbudget : HorizonBudget n M J 8) (ε : ℝ) (hε : 0 ≤ ε) :
    ε ^ 2 * (((fixedGraphs n M).filter
      (fun G => ∃ k ≤ J, ε ≤ |centeredPartial M G k|)).card : ℝ) ≤
      (J : ℝ) * 4 * ((fixedGraphs n M).card : ℝ) := by
  let X : ℕ → Graph n → ℝ := fun k G => centeredPartial M G k
  have htrace : ∀ i j (G H : Graph n), i ≤ j →
      revealTrace G j = revealTrace H j →
      revealTrace G i = revealTrace H i := by
    intro i j G H hij heq
    exact trace_eq_of_later H G hij heq
  have hadapt : ∀ j (G H : Graph n), G ∈ fixedGraphs n M →
      H ∈ fixedGraphs n M →
      revealTrace G j = revealTrace H j → X j G = X j H := by
    intro j G H hG hH heq
    exact centeredPartial_eq_of_trace H G j heq
  have hzero : ∀ j < J, ∀ G ∈ fixedGraphs n M,
      ∑ H ∈ atom (fixedGraphs n M) (fun j G => revealTrace G j) j G,
        increment X j H = 0 := by
    intro j hj G hG
    have hc : G.card = M := (Finset.mem_filter.mp hG).2
    simpa only [atom, historyAtom, X] using! centered_atom_zero hfinite hM G j hc
  have hsquare : ∀ j < J, ∀ G ∈ fixedGraphs n M,
      ∑ H ∈ atom (fixedGraphs n M) (fun j G => revealTrace G j) j G,
        (increment X j H) ^ 2 ≤
          4 * ((atom (fixedGraphs n M) (fun j G => revealTrace G j) j G).card : ℝ) := by
    intro j hj G hG
    have hc : G.card = M := (Finset.mem_filter.mp hG).2
    simpa only [atom, historyAtom, X] using!
      centered_atom_square hfinite hM G j hc hbudget hj
  have hb := finite_maximal_square (fixedGraphs n M)
    (fun j G => revealTrace G j) X J 4 ε htrace hadapt hzero hsquare
    (by intro G hG; exact centeredPartial_zero G) hε
  have hf : (fixedGraphs n M).filter (crossesBy X ε J) =
      (fixedGraphs n M).filter (fun G => ∃ k ≤ J,
        ε ≤ |centeredPartial M G k|) := by
    ext G
    simp [crossesBy, X]
  rw [hf] at hb
  exact hb

/-- A recursive integer minimum of the concrete BFS walk. -/
def walkMinimum {n : ℕ} (G : Graph n) : ℕ → ℤ
  | 0 => (explore G 0).walk
  | j + 1 => min (walkMinimum G j) (explore G (j + 1)).walk

@[simp] theorem walkMinimum_zero {n : ℕ} (G : Graph n) :
    walkMinimum G 0 = 0 := by simp [walkMinimum, initialState]

@[simp] theorem walkMinimum_succ {n : ℕ} (G : Graph n) (j : ℕ) :
    walkMinimum G (j + 1) =
      min (walkMinimum G j) (explore G (j + 1)).walk := rfl

theorem walkMinimum_le {n : ℕ} (G : Graph n) {i k : ℕ} (hik : i ≤ k) :
    walkMinimum G k ≤ (explore G i).walk := by
  induction k, hik using Nat.le_induction with
  | base =>
      induction i with
      | zero => simp
      | succ i => exact min_le_right _ _
  | succ k hik ih =>
      exact le_trans (min_le_left _ _) ih

theorem walkMinimum_attained {n : ℕ} (G : Graph n) (k : ℕ) :
    ∃ i ≤ k, walkMinimum G k = (explore G i).walk := by
  induction k with
  | zero => exact ⟨0, le_rfl, by simp⟩
  | succ k ih =>
      rcases ih with ⟨i, hik, hi⟩
      rcases le_total (walkMinimum G k) (explore G (k + 1)).walk with h | h
      · exact ⟨i, by omega, by rw [walkMinimum_succ, min_eq_left h, hi]⟩
      · exact ⟨k + 1, le_rfl, by rw [walkMinimum_succ, min_eq_right h]⟩

private theorem rootCount_step_before_order {n : ℕ} (G : Graph n) (j : ℕ)
    (hj : j < n) :
    rootCount G (j + 1) = rootCount G j +
      if (explore G j).queue = [] then 1 else 0 := by
  rw [rootCount_succ]
  by_cases hq : (explore G j).queue = []
  · have hp := processed_card_of_le G j hj.le
    have hpart := processed_partition G j
    have hseen : (explore G j).seen.card = j := by
      have heq : processed G j = (explore G j).seen := by
        simpa [hq] using! hpart.2
      simpa [heq] using! hp
    have hne : (explore G j).seen ≠ (Finset.univ : Finset (Fin n)) := by
      intro heq
      have hc : n = j := by simpa [heq] using! hseen
      omega
    simp [rootStarts, hq, hne]
  · simp [rootStarts, hq]

/-- Before termination, the running minimum is exactly the root correction
with one unit retained while a component has an active queue. -/
theorem walkMinimum_rootCount {n : ℕ} (G : Graph n) :
    ∀ k ≤ n, walkMinimum G k =
      -((rootCount G k : ℕ) : ℤ) +
        if (explore G k).queue = [] then 0 else 1 := by
  intro k hk
  induction k with
  | zero => simp [initialState]
  | succ k ih =>
      have hklt : k < n := by omega
      have ih' := ih (by omega)
      have hr := rootCount_step_before_order G k hklt
      have hw := walk_eq_queue_sub_rootCount G k
      have hws := walk_eq_queue_sub_rootCount G (k + 1)
      rw [walkMinimum_succ, ih']
      by_cases hq : (explore G k).queue = []
      · have hr' : rootCount G (k + 1) = rootCount G k + 1 := by
          simpa [hq] using! hr
        rw [hr'] at hws ⊢
        by_cases hqs : (explore G (k + 1)).queue = []
        · simp only [hq, hqs, ↓reduceIte, Nat.cast_add, Nat.cast_one,
            List.length_nil, Nat.cast_zero] at hw hws ⊢
          simp only [min_def]
          split_ifs <;> omega
        · have hlens : 0 < (explore G (k + 1)).queue.length :=
            List.length_pos_of_ne_nil hqs
          simp only [hq, hqs, ↓reduceIte, Nat.cast_add, Nat.cast_one,
            List.length_nil, Nat.cast_zero] at hw hws ⊢
          simp only [min_def]
          split_ifs <;> omega
      · have hr' : rootCount G (k + 1) = rootCount G k := by
          simpa [hq] using! hr
        rw [hr'] at hws ⊢
        by_cases hqs : (explore G (k + 1)).queue = []
        · have hlen : 0 < (explore G k).queue.length :=
            List.length_pos_of_ne_nil hq
          simp only [hq, hqs, ↓reduceIte, List.length_nil,
            Nat.cast_zero] at hw hws ⊢
          simp only [min_def]
          split_ifs <;> omega
        · have hlen : 0 < (explore G k).queue.length :=
            List.length_pos_of_ne_nil hq
          have hlens : 0 < (explore G (k + 1)).queue.length :=
            List.length_pos_of_ne_nil hqs
          simp only [hq, hqs, ↓reduceIte] at hw hws ⊢
          simp only [min_def]
          split_ifs <;> omega

/-- The actual queue differs from the reflected concrete walk by at most
one, with the integer minimum taken over every time up to `k`. -/
theorem queue_running_minimum_bound {n : ℕ} (G : Graph n) (k : ℕ)
    (hk : k ≤ n) :
    0 ≤ ((explore G k).queue.length : ℤ) -
      ((explore G k).walk - walkMinimum G k) ∧
    ((explore G k).queue.length : ℤ) -
      ((explore G k).walk - walkMinimum G k) ≤ 1 := by
  have hm := walkMinimum_rootCount G k hk
  have hw := walk_eq_queue_sub_rootCount G k
  by_cases hq : (explore G k).queue = []
  · simp [hq] at hm
    omega
  · simp [hq] at hm
    omega

theorem walk_centered_predictable {n M : ℕ} (G : Graph n) (k : ℕ)
    (hk : k ≤ n) :
    ((explore G k).walk : ℝ) =
      centeredPartial M G k + predictablePartial M G k := by
  rw [walk_eq_sum_actualIncrements]
  unfold centeredPartial predictablePartial
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk := Finset.mem_range.mp hj
  rw [actualWalkIncrement_eq_queryCount G j (by omega)]
  ring

theorem queryMean_one_sided {n M J : ℕ} (G : Graph n) (j : ℕ)
    (hj : j < J) (hJ : J ≤ n) (v : ℝ) (_hv : 0 ≤ v)
    (hp : |poolDensity M G j - poolDensity M G 0| ≤ v) :
    queryMean M G j - 1 ≤
      max (0 : ℝ) ((n : ℝ) * poolDensity M G 0 - 1) +
        (n : ℝ) * v := by
  have hd := queryCard_le_order G j (by omega : j < n)
  have hdreal : ((revealQuery (explore G j)).card : ℝ) ≤ n := by
    exact_mod_cast hd
  have hpnonneg : 0 ≤ poolDensity M G j := by
    unfold poolDensity
    positivity
  have hmean : queryMean M G j ≤ (n : ℝ) * poolDensity M G j := by
    unfold queryMean
    exact mul_le_mul_of_nonneg_right hdreal hpnonneg
  have hp' : poolDensity M G j ≤ poolDensity M G 0 + v := by
    have hh := (abs_le.mp hp).2
    linarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hbase : (n : ℝ) * poolDensity M G 0 - 1 ≤
      max (0 : ℝ) ((n : ℝ) * poolDensity M G 0 - 1) :=
    le_max_right _ _
  nlinarith [mul_le_mul_of_nonneg_left hp' hn]

private theorem predictable_interval_upper {n M J : ℕ} (G : Graph n)
    (hJ : J ≤ n) (v : ℝ) (hv : 0 ≤ v)
    (hp : ∀ j < J, |poolDensity M G j - poolDensity M G 0| ≤ v)
    (i k : ℕ) (hik : i ≤ k) (hk : k ≤ J) :
    predictablePartial M G k - predictablePartial M G i ≤
      ((k - i : ℕ) : ℝ) *
        (max (0 : ℝ) ((n : ℝ) * poolDensity M G 0 - 1) +
          (n : ℝ) * v) := by
  let c : ℝ := max (0 : ℝ) ((n : ℝ) * poolDensity M G 0 - 1) +
    (n : ℝ) * v
  induction k, hik using Nat.le_induction with
  | base => simp
  | succ k hik ih =>
      have hk' : k < J := by omega
      have hstep := queryMean_one_sided G k hk' hJ v hv (hp k hk')
      have hprior := ih (by omega)
      rw [predictablePartial, Finset.sum_range_succ]
      change predictablePartial M G k + (queryMean M G k - 1) -
        predictablePartial M G i ≤ ((k + 1 - i : ℕ) : ℝ) * c
      have hsub : k + 1 - i = k - i + 1 := by omega
      rw [hsub, Nat.cast_add, Nat.cast_one]
      dsimp [c] at *
      nlinarith

/-- One-sided drift control bounds the queue without assuming that the queue
is already small. -/
theorem queue_upper_of_uniform_controls {n M J : ℕ} (G : Graph n)
    (hJ : J ≤ n) (u v : ℝ) (_hu : 0 ≤ u) (hv : 0 ≤ v)
    (hA : ∀ k ≤ J, |centeredPartial M G k| ≤ u)
    (hp : ∀ j < J, |poolDensity M G j - poolDensity M G 0| ≤ v) :
    ∀ k ≤ J,
      ((explore G k).queue.length : ℝ) ≤
        1 + 2 * u + (J : ℝ) *
          (max (0 : ℝ) ((n : ℝ) * poolDensity M G 0 - 1) +
            (n : ℝ) * v) := by
  intro k hk
  have hrefl := (queue_running_minimum_bound G k (hk.trans hJ)).2
  obtain ⟨i, hik, hmin⟩ := walkMinimum_attained G k
  have hki := predictable_interval_upper G hJ v hv hp i k hik hk
  have hwk := walk_centered_predictable (M := M) G k (hk.trans hJ)
  have hwi := walk_centered_predictable (M := M) G i
    ((hik.trans hk).trans hJ)
  have hAk := hA k hk
  have hAi := hA i (hik.trans hk)
  have hAkle := (abs_le.mp hAk).2
  have hAile := (abs_le.mp hAi).1
  have hc : 0 ≤ max (0 : ℝ) ((n : ℝ) * poolDensity M G 0 - 1) +
      (n : ℝ) * v := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    positivity
  have hkiJ : ((k - i : ℕ) : ℝ) ≤ J := by
    exact_mod_cast (by omega : k - i ≤ J)
  have hdrift : predictablePartial M G k - predictablePartial M G i ≤
      (J : ℝ) *
        (max (0 : ℝ) ((n : ℝ) * poolDensity M G 0 - 1) +
          (n : ℝ) * v) :=
    hki.trans (mul_le_mul_of_nonneg_right hkiJ hc)
  have hreal : ((explore G k).queue.length : ℝ) -
      (((explore G k).walk : ℝ) - ((explore G i).walk : ℝ)) ≤ 1 := by
    rw [← hmin]
    exact_mod_cast hrefl
  linarith

private theorem probM_mono {n M : ℕ} (P Q : Graph n → Prop)
    (h : ∀ G, P G → Q G) : probM n M P ≤ probM n M Q := by
  unfold probM
  have hs : (fixedGraphs n M).filter P ⊆
      (fixedGraphs n M).filter Q := by
    intro G hG
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hG).1, h G (Finset.mem_filter.mp hG).2⟩
  have hc : (((fixedGraphs n M).filter P).card : ℝ) ≤
      (((fixedGraphs n M).filter Q).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hs
  exact div_le_div_of_nonneg_right hc (Nat.cast_nonneg _)

private theorem probM_or_le {n M : ℕ} (P Q : Graph n → Prop)
    (hM : M ≤ capacity n) :
    probM n M (fun G => P G ∨ Q G) ≤
      probM n M P + probM n M Q := by
  have hF : (0 : ℝ) < ((fixedGraphs n M).card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr (fixedGraphs_nonempty hM))
  have hfilter : (fixedGraphs n M).filter (fun G => P G ∨ Q G) =
      (fixedGraphs n M).filter P ∪ (fixedGraphs n M).filter Q := by
    ext G
    simp [and_or_left]
  have hc := Finset.card_union_le
    ((fixedGraphs n M).filter P) ((fixedGraphs n M).filter Q)
  have hcr : (((fixedGraphs n M).filter P ∪
      (fixedGraphs n M).filter Q).card : ℝ) ≤
      ((fixedGraphs n M).filter P).card +
        ((fixedGraphs n M).filter Q).card := by
    exact_mod_cast hc
  unfold probM
  rw [← add_div]
  have hbound := div_le_div_of_nonneg_right hcr hF.le
  convert hbound using 1
  congr 1
  congr 1
  congr 1
  ext G
  simp [and_or_left]

private theorem centered_probability_bound {n M J : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (hbudget : HorizonBudget n M J 8) (ε : ℝ) (hε : 0 < ε) :
    probM n M (fun G => ∃ k ≤ J, ε ≤ |centeredPartial M G k|) ≤
      4 * (J : ℝ) / ε ^ 2 := by
  let F : ℝ := ((fixedGraphs n M).card : ℝ)
  let B : ℝ := (((fixedGraphs n M).filter
    (fun G => ∃ k ≤ J, ε ≤ |centeredPartial M G k|)).card : ℝ)
  have hF : 0 < F := by
    change (0 : ℝ) < ((fixedGraphs n M).card : ℝ)
    exact_mod_cast (Finset.card_pos.mpr (fixedGraphs_nonempty hM))
  have hmax := centeredPartial_maximal_finite hfinite hM hbudget ε hε.le
  change ε ^ 2 * B ≤ (J : ℝ) * 4 * F at hmax
  have hprob : probM n M
      (fun G => ∃ k ≤ J, ε ≤ |centeredPartial M G k|) = B / F := by
    unfold probM B F
    congr 1
    congr 1
    congr 1
    ext G
    simp
  rw [hprob]
  have hden : 0 < ε ^ 2 := sq_pos_of_pos hε
  exact (div_le_div_iff₀ hF hden).mpr (by nlinarith [hmax])

theorem initial_pool_density {n M : ℕ} (G : Graph n) :
    poolDensity M G 0 = (M : ℝ) / (capacity n : ℝ) := by
  simp [poolDensity, poolSuccessCount_initial, poolEdgeCount_initial]

theorem n23_eq_n13_square (n : ℕ) (hn : 0 < n) :
    n23 n = n13 n ^ 2 := by
  have h13 : 0 < n13 n := by
    unfold n13
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hcub := n13_cube n hn
  have hprod := n23_mul_n13 n hn
  nlinarith

/-- The fixed-edge critical window bounds the initial predictable drift
at the exact cube-root scale. -/
theorem critical_initial_drift_upper (M : NatSeq) (lam : ℝ)
    (hcritical : criticalWindow M lam) :
    ∀ᶠ n : ℕ in atTop,
      ∀ G : Graph n,
        n13 n * max (0 : ℝ)
          ((n : ℝ) * poolDensity (M n) G 0 - 1) ≤
          2 * (|lam| + 2) := by
  let C : ℝ := |lam| + 1
  have hLamC : lam < C := by
    dsimp [C]
    have hh := le_abs_self lam
    linarith
  have hratio := hcritical.2.eventually_le_const hLamC
  have hb := n13_tendsto_atTop.eventually_ge_atTop (2 : ℝ)
  filter_upwards [hratio, hb, eventually_ge_atTop (32 : ℕ)] with n hr hb hn G
  have hn0 : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn0
  have ha := n23_pos n hn0
  have hprod := n23_mul_n13 n hn0
  have hcub := n13_cube n hn0
  have hbpos : 0 < n13 n := by linarith
  have hCpos : 0 ≤ C := by dsimp [C]; positivity
  have hcap : (capacity n : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    simpa only [capacity] using! (Nat.cast_choose_two (K := ℝ) n)
  have hnminus : (0 : ℝ) < (n : ℝ) - 1 := by
    have hnr : (32 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hraw : (n : ℝ) * ((M n : ℝ) / (capacity n : ℝ)) - 1 =
      (2 * (M n : ℝ) - (n : ℝ) + 1) / ((n : ℝ) - 1) := by
    rw [hcap]
    field_simp
    ring
  have hnum : 2 * (M n : ℝ) - (n : ℝ) ≤ C * n23 n :=
    (div_le_iff₀ ha).mp hr
  have hbn : n13 n ≤ (n : ℝ) / 2 := by
    nlinarith [sq_nonneg (n13 n - 2)]
  have hden : (n : ℝ) / 2 ≤ (n : ℝ) - 1 := by
    have hnr : (32 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hscaled : n13 n *
      ((n : ℝ) * ((M n : ℝ) / (capacity n : ℝ)) - 1) ≤
        2 * (C + 1) := by
    rw [hraw]
    have heq : n13 n * ((2 * (M n : ℝ) - (n : ℝ) + 1) /
        ((n : ℝ) - 1)) =
      n13 n * (2 * (M n : ℝ) - (n : ℝ) + 1) /
        ((n : ℝ) - 1) := by ring
    rw [heq]
    apply (div_le_iff₀ hnminus).mpr
    have hh := mul_le_mul_of_nonneg_left hnum hbpos.le
    have hprod' : n13 n * n23 n = (n : ℝ) := by nlinarith [hprod]
    nlinarith [hh, hbn, hden]
  rw [initial_pool_density]
  have hmax : n13 n * max (0 : ℝ)
      ((n : ℝ) * ((M n : ℝ) / (capacity n : ℝ)) - 1) =
      max 0 (n13 n * ((n : ℝ) * ((M n : ℝ) / (capacity n : ℝ)) - 1)) := by
    by_cases hx : 0 ≤ (n : ℝ) * ((M n : ℝ) / (capacity n : ℝ)) - 1
    · simp [max_eq_right hx, mul_nonneg hbpos.le hx]
    · have hneg : (n : ℝ) * ((M n : ℝ) / (capacity n : ℝ)) - 1 ≤ 0 := le_of_not_ge hx
      simp [max_eq_left hneg, mul_nonpos_of_nonneg_of_nonpos hbpos.le hneg]
  rw [hmax]
  have hzero : (0 : ℝ) ≤ 2 * (C + 1) := by dsimp [C]; positivity
  have hfinal := max_le hzero hscaled
  dsimp [C] at hfinal
  nlinarith

/-- On every fixed critical horizon the maximal queue, divided by `n13`,
is tight under the same fixed-edge law used for the pool and query counts. -/
theorem critical_queue_tight
    (hfinite : FiniteEnumerationStatement) (M : NatSeq) (lam T d : ℝ)
    (hcritical : criticalWindow M lam) (hT : 0 ≤ T) (hd : 0 < d) :
    ∃ K : ℝ, 0 < K ∧
      ∀ᶠ n : ℕ in atTop,
        probM n (M n) (fun G => ∃ k ≤ ⌊T * n23 n⌋₊,
          K * n13 n < ((explore G k).queue.length : ℝ)) ≤ d := by
  let C : ℝ := 2 * (|lam| + 2)
  let U : ℝ := max 1 (8 * (T + 1) / d)
  let K : ℝ := 2 + 2 * U + (T + 1) * (C + 1)
  have hT1 : 0 < T + 1 := by linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hU : 1 ≤ U := le_max_left _ _
  have hUpos : 0 < U := by linarith
  have hUlarge : 8 * (T + 1) / d ≤ U := le_max_right _ _
  have hU2 : U ≤ U ^ 2 := by nlinarith [sq_nonneg (U - 1)]
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  have hpool := (critical_poolDensity_concentration hfinite M lam T 1
    hcritical hT (by norm_num)).eventually_le_const
      (by linarith : (0 : ℝ) < d / 2)
  filter_upwards [hcritical.1, eventually_horizonBudget M lam T hcritical hT,
    critical_initial_drift_upper M lam hcritical,
    n13_tendsto_atTop.eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (1 : ℕ), hpool]
    with n hM hbudget hinit hb1 hn hpoolbound
  let J : ℕ := ⌊T * n23 n⌋₊
  let b : ℝ := n13 n
  have hbpos : 0 < b := by dsimp [b]; linarith
  have ha : 0 < n23 n := n23_pos n hn
  have hab : n23 n = b ^ 2 := by
    dsimp [b]
    exact n23_eq_n13_square n hn
  have hcub : b ^ 3 = (n : ℝ) := by
    dsimp [b]
    exact n13_cube n hn
  have hfloor : (J : ℝ) ≤ (T + 1) * b ^ 2 := by
    have hh : (J : ℝ) ≤ T * n23 n :=
      Nat.floor_le (mul_nonneg hT ha.le)
    rw [hab] at hh
    nlinarith [sq_nonneg b]
  have hJ : J ≤ n := hbudget.1
  let A : Graph n → Prop := fun G =>
    ∃ k ≤ J, U * b ≤ |centeredPartial (M n) G k|
  let P : Graph n → Prop := fun G =>
    ∃ k ≤ J, 1 / b ^ 4 ≤
      |poolDensity (M n) G k - poolDensity (M n) G 0|
  let Q : Graph n → Prop := fun G =>
    ∃ k ≤ J, K * b < ((explore G k).queue.length : ℝ)
  have hcent0 := centered_probability_bound hfinite hM hbudget
    (U * b) (mul_pos hUpos hbpos)
  have hcent : probM n (M n) A ≤ d / 2 := by
    have hden : 0 < (U * b) ^ 2 := sq_pos_of_pos (mul_pos hUpos hbpos)
    have hJbound : 4 * (J : ℝ) / (U * b) ^ 2 ≤ d / 2 := by
      apply (div_le_iff₀ hden).mpr
      have hUd : 8 * (T + 1) ≤ d * U := by
        nlinarith [(div_le_iff₀ hd).mp hUlarge]
      have hUd2 : d * U ≤ d * U ^ 2 :=
        mul_le_mul_of_nonneg_left hU2 hd.le
      have hmain : 8 * (T + 1) ≤ d * U ^ 2 := hUd.trans hUd2
      have hmainb := mul_le_mul_of_nonneg_right hmain (sq_nonneg b)
      dsimp [U, b] at hcent0 ⊢
      nlinarith [hfloor, hmainb]
    exact hcent0.trans hJbound
  have hpool' : probM n (M n) P ≤ d / 2 := by
    simpa only [P, J, b] using! hpoolbound
  have hcontain : ∀ G : Graph n, Q G → A G ∨ P G := by
    intro G hq
    by_cases hA : A G
    · exact Or.inl hA
    by_cases hP : P G
    · exact Or.inr hP
    exfalso
    have hAnot : ∀ k ≤ J, |centeredPartial (M n) G k| ≤ U * b := by
      intro k hk
      have hh : ¬ U * b ≤ |centeredPartial (M n) G k| := by
        intro he
        exact hA ⟨k, hk, he⟩
      exact le_of_lt (lt_of_not_ge hh)
    have hPnot : ∀ j < J,
        |poolDensity (M n) G j - poolDensity (M n) G 0| ≤ 1 / b ^ 4 := by
      intro j hj
      have hh : ¬ 1 / b ^ 4 ≤
          |poolDensity (M n) G j - poolDensity (M n) G 0| := by
        intro he
        exact hP ⟨j, hj.le, he⟩
      exact le_of_lt (lt_of_not_ge hh)
    have hv : 0 ≤ 1 / b ^ 4 := by positivity
    obtain ⟨k, hk, hqk⟩ := hq
    have hfinitequeue := queue_upper_of_uniform_controls G hJ
      (U * b) (1 / b ^ 4) (mul_nonneg hUpos.le hbpos.le)
      hv hAnot hPnot k hk
    have hstart : b * max (0 : ℝ)
        ((n : ℝ) * poolDensity (M n) G 0 - 1) ≤ C := by
      simpa only [b, C] using! hinit G
    have hstep : max (0 : ℝ)
        ((n : ℝ) * poolDensity (M n) G 0 - 1) +
        (n : ℝ) * (1 / b ^ 4) ≤ (C + 1) / b := by
      have heq : (n : ℝ) * (1 / b ^ 4) = 1 / b := by
        rw [← hcub]
        field_simp
      rw [heq]
      have hstart' :
          max (0 : ℝ) ((n : ℝ) * poolDensity (M n) G 0 - 1) * b ≤ C := by
        nlinarith [hstart]
      have hh := (le_div_iff₀ hbpos).mpr hstart'
      calc
        max (0 : ℝ) ((n : ℝ) * poolDensity (M n) G 0 - 1) +
            1 / b ≤ C / b + 1 / b := by nlinarith [hh]
        _ = (C + 1) / b := by ring
    have hstep0 : 0 ≤ max (0 : ℝ)
        ((n : ℝ) * poolDensity (M n) G 0 - 1) +
        (n : ℝ) * (1 / b ^ 4) := by positivity
    have hdrift : (J : ℝ) *
        (max (0 : ℝ) ((n : ℝ) * poolDensity (M n) G 0 - 1) +
          (n : ℝ) * (1 / b ^ 4)) ≤ (T + 1) * (C + 1) * b := by
      have hJnonneg : (0 : ℝ) ≤ J := Nat.cast_nonneg _
      have hfirst := mul_le_mul_of_nonneg_left hstep hJnonneg
      have hfac : 0 ≤ (C + 1) / b := by positivity
      have hsecond := mul_le_mul_of_nonneg_right hfloor
        hfac
      calc
        (J : ℝ) * (max (0 : ℝ)
            ((n : ℝ) * poolDensity (M n) G 0 - 1) +
              (n : ℝ) * (1 / b ^ 4)) ≤
            (J : ℝ) * ((C + 1) / b) := hfirst
        _ ≤ (T + 1) * b ^ 2 * ((C + 1) / b) := hsecond
        _ = (T + 1) * (C + 1) * b := by field_simp
    have hKbound : 1 + 2 * (U * b) +
        (T + 1) * (C + 1) * b ≤ K * b := by
      dsimp [K]
      nlinarith [hb1]
    have hqbound : ((explore G k).queue.length : ℝ) ≤ K * b := by
      calc
        ((explore G k).queue.length : ℝ) ≤
            1 + 2 * (U * b) + (J : ℝ) *
              (max (0 : ℝ) ((n : ℝ) * poolDensity (M n) G 0 - 1) +
                (n : ℝ) * (1 / b ^ 4)) := hfinitequeue
        _ ≤ 1 + 2 * (U * b) + (T + 1) * (C + 1) * b := by
          linarith [hdrift]
        _ ≤ K * b := hKbound
    exact (not_lt_of_ge hqbound) hqk
  have hqprob := probM_mono (n := n) (M := M n) Q
    (fun G => A G ∨ P G) hcontain
  have hsum := probM_or_le A P hM
  have hfinal : probM n (M n) Q ≤ d := by
    linarith [hqprob, hsum, hcent, hpool']
  unfold probM at hfinal ⊢
  convert hfinal using 1

end

end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_QueueControl
