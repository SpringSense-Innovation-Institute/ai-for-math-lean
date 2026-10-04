module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W14_Base
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Erdos745.WrapUp.Proofs.Internal.Linked.W01_Pruefer

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


/-!
# Adaptive reveal atoms and their conditional law

This module closes the finite bridge from the concrete reveal trace to the
hypergeometric clause of `FiniteEnumerationStatement`.  The central point is
that an entire realized trace fiber is exactly one `patternEvent`; no
exchangeability or independence premise is inserted.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Conditional

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Reveal
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_TailsFinite

noncomputable section
attribute [local instance] Classical.propDecidable

/-! ## A BFS step only depends on the edges in its current query -/

lemma newChildren_eq_of_inter_incidentQuery_eq {n : ℕ}
    (G H : Graph n) (discovered : Finset (Fin n)) (v : Fin n)
    (hinter : G ∩ incidentQuery v discovered =
      H ∩ incidentQuery v discovered) :
    newChildren G discovered v = newChildren H discovered v := by
  ext u
  simp only [mem_newChildren_iff]
  constructor
  · rintro ⟨hu, e, heG, he⟩
    have heq : e ∈ incidentQuery v discovered := by
      rw [mem_incidentQuery_iff]
      rcases he with he | he
      · exact Or.inl ⟨he.1, by simpa [he.2] using! hu⟩
      · exact Or.inr ⟨he.2, by simpa [he.1] using! hu⟩
    have heH : e ∈ H := by
      have : e ∈ G ∩ incidentQuery v discovered := by simp [heG, heq]
      rw [hinter] at this
      exact (Finset.mem_inter.mp this).1
    exact ⟨hu, e, heH, he⟩
  · rintro ⟨hu, e, heH, he⟩
    have heq : e ∈ incidentQuery v discovered := by
      rw [mem_incidentQuery_iff]
      rcases he with he | he
      · exact Or.inl ⟨he.1, by simpa [he.2] using! hu⟩
      · exact Or.inr ⟨he.2, by simpa [he.1] using! hu⟩
    have heG : e ∈ G := by
      have : e ∈ H ∩ incidentQuery v discovered := by simp [heH, heq]
      rw [← hinter] at this
      exact (Finset.mem_inter.mp this).1
    exact ⟨hu, e, heG, he⟩

lemma bfsStep_eq_of_inter_revealQuery_eq {n : ℕ} (G H : Graph n)
    (s : BFSState n)
    (hinter : G ∩ revealQuery s = H ∩ revealQuery s) :
    bfsStep G s = bfsStep H s := by
  rcases s with ⟨seen, queue, z⟩
  cases queue with
  | cons v rest =>
      have hchildren :=
        newChildren_eq_of_inter_incidentQuery_eq G H seen v hinter
      simp only [revealQuery_queue_cons] at hinter
      rw [bfsStep_queue_cons, bfsStep_queue_cons, hchildren]
  | nil =>
      by_cases hneutral : ((Finset.univ : Finset (Fin n)) \ seen).Nonempty
      · let v := ((Finset.univ : Finset (Fin n)) \ seen).min' hneutral
        have hquery :
            revealQuery (⟨seen, [], z⟩ : BFSState n) =
              incidentQuery v (insert v seen) :=
          revealQuery_queue_nil_of_nonempty seen z hneutral
        have hchildren :
            newChildren G (insert v seen) v =
              newChildren H (insert v seen) v := by
          apply newChildren_eq_of_inter_incidentQuery_eq
          simpa [hquery] using! hinter
        rw [bfsStep_queue_nil_of_nonempty G seen z hneutral,
          bfsStep_queue_nil_of_nonempty H seen z hneutral, hchildren]
      · rw [bfsStep_queue_nil_of_empty G seen z hneutral,
          bfsStep_queue_nil_of_empty H seen z hneutral]

/-! ## Every old answer touches a processed vertex; the next query does not -/

def edgesTouching {n : ℕ} (S : Finset (Fin n)) : Graph n :=
  (Finset.univ : Finset (Edge n)).filter fun e =>
    e.val.1 ∈ S ∨ e.val.2 ∈ S

@[simp] lemma mem_edgesTouching_iff {n : ℕ} (S : Finset (Fin n))
    (e : Edge n) :
    e ∈ edgesTouching S ↔ e.val.1 ∈ S ∨ e.val.2 ∈ S := by
  simp [edgesTouching]

lemma edgesTouching_mono {n : ℕ} {S T : Finset (Fin n)} (hST : S ⊆ T) :
    edgesTouching S ⊆ edgesTouching T := by
  intro e he
  rw [mem_edgesTouching_iff] at he ⊢
  exact he.elim (fun h => Or.inl (hST h)) (fun h => Or.inr (hST h))

lemma revealQuery_disjoint_edgesTouching_stateProcessed {n : ℕ}
    (s : BFSState n) :
    Disjoint (revealQuery s) (edgesTouching (stateProcessed s)) := by
  rcases s with ⟨seen, queue, z⟩
  rw [Finset.disjoint_left]
  intro e heq hetouch
  rw [mem_edgesTouching_iff] at hetouch
  cases queue with
  | cons v rest =>
      rw [revealQuery_queue_cons, mem_incidentQuery_iff] at heq
      simp only [stateProcessed, List.toFinset_cons, Finset.mem_sdiff,
        Finset.mem_insert] at hetouch
      rcases heq with ⟨h1, h2⟩ | ⟨h2, h1⟩
      · rcases hetouch with htouch | htouch
        · exact htouch.2 (Or.inl h1)
        · exact h2 htouch.1
      · rcases hetouch with htouch | htouch
        · exact h1 htouch.1
        · exact htouch.2 (Or.inl h2)
  | nil =>
      by_cases hneutral : ((Finset.univ : Finset (Fin n)) \ seen).Nonempty
      · let v := ((Finset.univ : Finset (Fin n)) \ seen).min' hneutral
        rw [revealQuery_queue_nil_of_nonempty seen z hneutral,
          mem_incidentQuery_iff] at heq
        have hv : v ∉ seen := by
          exact Finset.mem_sdiff.mp
            (((Finset.univ : Finset (Fin n)) \ seen).min'_mem hneutral) |>.2
        simp only [stateProcessed, List.toFinset_nil, Finset.sdiff_empty,
          mem_edgesTouching_iff] at hetouch
        rcases heq with ⟨h1, h2⟩ | ⟨h2, h1⟩
        · rcases hetouch with htouch | htouch
          · exact hv (by simpa [h1] using! htouch)
          · exact h2 (Finset.mem_insert_of_mem htouch)
        · rcases hetouch with htouch | htouch
          · exact h1 (Finset.mem_insert_of_mem htouch)
          · exact hv (by simpa [h2] using! htouch)
      · simpa [revealQuery_queue_nil_of_empty seen z hneutral] using! heq

lemma revealQuery_subset_edgesTouching_stepProcessed {n : ℕ}
    (G : Graph n) (s : BFSState n) (hs : QueueWellFormed s) :
    revealQuery s ⊆ edgesTouching (stateProcessed (bfsStep G s)) := by
  rcases s with ⟨seen, queue, z⟩
  rcases hs with ⟨hnodup, hsubset⟩
  cases queue with
  | cons v rest =>
      intro e he
      rw [revealQuery_queue_cons, mem_incidentQuery_iff] at he
      rw [stateProcessed_active G seen v rest z hnodup hsubset,
        mem_edgesTouching_iff]
      exact he.elim (fun h => Or.inl (by simpa [h.1]))
        (fun h => Or.inr (by simpa [h.1]))
  | nil =>
      by_cases hneutral : ((Finset.univ : Finset (Fin n)) \ seen).Nonempty
      · let v := ((Finset.univ : Finset (Fin n)) \ seen).min' hneutral
        intro e he
        rw [revealQuery_queue_nil_of_nonempty seen z hneutral,
          mem_incidentQuery_iff] at he
        rw [stateProcessed_root G seen z hneutral, mem_edgesTouching_iff]
        exact he.elim (fun h => Or.inl (by simpa [h.1]))
          (fun h => Or.inr (by simpa [h.1]))
      · simp [revealQuery_queue_nil_of_empty seen z hneutral]

theorem answeredEdges_subset_edgesTouching_processed {n : ℕ} (G : Graph n) :
    ∀ j : ℕ,
      (revealTrace G j).yes ∪ (revealTrace G j).no ⊆
        edgesTouching (processed G j)
  | 0 => by simp [initialReveal, processed, initialState]
  | j + 1 => by
      rw [revealTrace_coverage_succ]
      apply Finset.union_subset
      · exact (answeredEdges_subset_edgesTouching_processed G j).trans
          (edgesTouching_mono (processed_subset_succ G j))
      · rw [← stateProcessed_explore, explore_succ]
        exact revealQuery_subset_edgesTouching_stepProcessed G (explore G j)
          (explore_queueWellFormed G j)

theorem revealQuery_fresh {n : ℕ} (G : Graph n) (j : ℕ) :
    Disjoint (revealQuery (explore G j))
      ((revealTrace G j).yes ∪ (revealTrace G j).no) := by
  apply (revealQuery_disjoint_edgesTouching_stateProcessed (explore G j)).mono_right
  simpa [stateProcessed_explore] using!
    answeredEdges_subset_edgesTouching_processed G j

/-! ## A realized trace fiber is exactly one pattern event -/

lemma inter_query_eq_of_terminal_pattern {n : ℕ} (G H query yes no : Graph n)
    (hyes : G ∩ query ⊆ yes) (hno : query \ G ⊆ no)
    (hpattern : patternEvent yes no H) :
    H ∩ query = G ∩ query := by
  rcases hpattern with ⟨hyesH, hnoH⟩
  ext e
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨heH, heq⟩
    refine ⟨?_, heq⟩
    by_contra heG
    have heno : e ∈ no := hno (Finset.mem_sdiff.mpr ⟨heq, heG⟩)
    exact Finset.disjoint_left.mp hnoH heno heH
  · rintro ⟨heG, heq⟩
    exact ⟨hyesH (hyes (Finset.mem_inter.mpr ⟨heG, heq⟩)), heq⟩

theorem history_fiber_eq_patternEvent {n : ℕ} (G H : Graph n) :
    ∀ j : ℕ,
      revealTrace H j = revealTrace G j ↔
        patternEvent (revealTrace G j).yes (revealTrace G j).no H
  | 0 => by simp [initialReveal, patternEvent]
  | j + 1 => by
      constructor
      · intro htrace
        rw [← htrace]
        exact revealTrace_patternEvent H (j + 1)
      · intro hpattern
        have hprevious :
            patternEvent (revealTrace G j).yes (revealTrace G j).no H := by
          rcases hpattern with ⟨hyes, hno⟩
          constructor
          · exact (revealTrace_yes_mono G (Nat.le_succ j)).trans hyes
          · exact hno.mono_left (revealTrace_no_mono G (Nat.le_succ j))
        have ih : revealTrace H j = revealTrace G j :=
          (history_fiber_eq_patternEvent G H j).2 hprevious
        let query := revealQuery (explore G j)
        have hyes : G ∩ query ⊆ (revealTrace G (j + 1)).yes := by
          rw [revealTrace_yes_succ]
          exact Finset.subset_union_right
        have hno : query \ G ⊆ (revealTrace G (j + 1)).no := by
          rw [revealTrace_no_succ]
          exact Finset.subset_union_right
        have hinter : H ∩ query = G ∩ query :=
          inter_query_eq_of_terminal_pattern G H query _ _ hyes hno hpattern
        have hsdiff : query \ H = query \ G := by
          ext e
          have hmem := Finset.ext_iff.mp hinter e
          simp only [Finset.mem_inter, Finset.mem_sdiff] at hmem ⊢
          tauto
        rw [revealTrace_succ, revealTrace_succ, ih]
        have hbfs : bfsStep H (revealTrace G j).bfs =
            bfsStep G (revealTrace G j).bfs := by
          apply bfsStep_eq_of_inter_revealQuery_eq
          simpa [query, revealTrace_bfs] using! hinter
        have hinter' :
            H ∩ revealQuery (revealTrace G j).bfs =
              G ∩ revealQuery (revealTrace G j).bfs := by
          simpa [query, revealTrace_bfs] using! hinter
        have hsdiff' :
            revealQuery (revealTrace G j).bfs \ H =
              revealQuery (revealTrace G j).bfs \ G := by
          simpa [query, revealTrace_bfs] using! hsdiff
        simp only [revealStep]
        rw [hbfs, hinter', hsdiff']

theorem conditional_query_eq_hypergeom
    (hfinite : FiniteEnumerationStatement) {n M : ℕ}
    (hM : M ≤ capacity n) (G : Graph n) (j y : ℕ)
    (hpos : 0 < probM n M
      (patternEvent (revealTrace G j).yes (revealTrace G j).no)) :
    conditionalProbM n M
        (patternEvent (revealTrace G j).yes (revealTrace G j).no)
        (fun H => (H ∩ revealQuery (explore G j)).card = y) =
      hypergeomMass
        (capacity n - (revealTrace G j).yes.card -
          (revealTrace G j).no.card)
        (M - (revealTrace G j).yes.card)
        (revealQuery (explore G j)).card y := by
  exact hfinite.2.1 n M (revealTrace G j).yes (revealTrace G j).no
    (revealQuery (explore G j)) hM (revealTrace_yes_no_disjoint G j)
    (revealQuery_fresh G j) hpos y

theorem conditional_history_query_eq_hypergeom
    (hfinite : FiniteEnumerationStatement) {n M : ℕ}
    (hM : M ≤ capacity n) (G : Graph n) (j y : ℕ)
    (hpos : 0 < probM n M (fun H => revealTrace H j = revealTrace G j)) :
    conditionalProbM n M
        (fun H => revealTrace H j = revealTrace G j)
        (fun H => (H ∩ revealQuery (explore G j)).card = y) =
      hypergeomMass
        (capacity n - (revealTrace G j).yes.card -
          (revealTrace G j).no.card)
        (M - (revealTrace G j).yes.card)
        (revealQuery (explore G j)).card y := by
  have hfiber : (fun H : Graph n => revealTrace H j = revealTrace G j) =
      patternEvent (revealTrace G j).yes (revealTrace G j).no := by
    funext H
    exact propext (history_fiber_eq_patternEvent G H j)
  rw [hfiber] at hpos ⊢
  exact conditional_query_eq_hypergeom hfinite hM G j y hpos

end

end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Conditional


/-!
# Finite-horizon exploration algebra

This file is the first limit-facing layer above the adaptive hypergeometric
law.  It deliberately keeps the finite sums visible.  In particular, the
characteristic-function recursion below is telescoped as an adapted recursion;
no product of random conditional characteristic functions is introduced.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteHorizon

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Reveal
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Conditional
open MeasureTheory
open scoped BigOperators ComplexConjugate

noncomputable section
attribute [local instance] Classical.propDecidable

/-! ## Factorial and ordinary moments through order four -/

def fallingReal (x : ℝ) : ℕ → ℝ
  | 0 => 1
  | r + 1 => fallingReal x r * (x - r)

@[simp] lemma fallingReal_zero (x : ℝ) : fallingReal x 0 = 1 := rfl

@[simp] lemma fallingReal_succ (x : ℝ) (r : ℕ) :
    fallingReal x (r + 1) = fallingReal x r * (x - r) := rfl

lemma fallingReal_one (x : ℝ) : fallingReal x 1 = x := by
  simp [fallingReal]

lemma fallingReal_two (x : ℝ) : fallingReal x 2 = x * (x - 1) := by
  simp [fallingReal]

lemma fallingReal_three (x : ℝ) :
    fallingReal x 3 = x * (x - 1) * (x - 2) := by
  simp [fallingReal]

lemma fallingReal_four (x : ℝ) :
    fallingReal x 4 = x * (x - 1) * (x - 2) * (x - 3) := by
  simp [fallingReal]

lemma square_eq_falling (x : ℝ) : x ^ 2 = fallingReal x 2 + fallingReal x 1 := by
  rw [fallingReal_one, fallingReal_two]
  ring

lemma fourth_eq_falling (x : ℝ) :
    x ^ 4 = fallingReal x 4 + 6 * fallingReal x 3 +
      7 * fallingReal x 2 + fallingReal x 1 := by
  rw [fallingReal_one, fallingReal_two, fallingReal_three, fallingReal_four]
  ring

def weightedMoment (d : ℕ) (mass : ℕ → ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ y ∈ Finset.range (d + 1), mass y * f y

def factorialMoment (d : ℕ) (mass : ℕ → ℝ) (r : ℕ) : ℝ :=
  weightedMoment d mass (fun x => fallingReal x r)

def rawMoment (d : ℕ) (mass : ℕ → ℝ) (r : ℕ) : ℝ :=
  weightedMoment d mass (fun x => x ^ r)

lemma rawMoment_one (d : ℕ) (mass : ℕ → ℝ) :
    rawMoment d mass 1 = factorialMoment d mass 1 := by
  unfold rawMoment factorialMoment weightedMoment
  apply Finset.sum_congr rfl
  intro y hy
  simp

lemma rawMoment_two (d : ℕ) (mass : ℕ → ℝ) :
    rawMoment d mass 2 =
      factorialMoment d mass 2 + factorialMoment d mass 1 := by
  simp only [rawMoment, factorialMoment, weightedMoment, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← mul_add, ← square_eq_falling]

lemma rawMoment_four (d : ℕ) (mass : ℕ → ℝ) :
    rawMoment d mass 4 = factorialMoment d mass 4 +
      6 * factorialMoment d mass 3 + 7 * factorialMoment d mass 2 +
      factorialMoment d mass 1 := by
  simp only [rawMoment, factorialMoment, weightedMoment, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  rw [fourth_eq_falling]
  ring

def queryCount {n : ℕ} (G : Graph n) (j : ℕ) : ℕ :=
  (G ∩ revealQuery (explore G j)).card

def answeredCount {n : ℕ} (G : Graph n) (j : ℕ) : ℕ :=
  ((revealTrace G j).yes ∪ (revealTrace G j).no).card

def poolEdgeCount {n : ℕ} (G : Graph n) (j : ℕ) : ℕ :=
  capacity n - answeredCount G j

def poolSuccessCount {n : ℕ} (M : ℕ) (G : Graph n) (j : ℕ) : ℕ :=
  M - (revealTrace G j).yes.card

def poolDensity {n : ℕ} (M : ℕ) (G : Graph n) (j : ℕ) : ℝ :=
  (poolSuccessCount M G j : ℝ) / (poolEdgeCount G j : ℝ)

theorem answeredCount_succ {n : ℕ} (G : Graph n) (j : ℕ) :
    answeredCount G (j + 1) = answeredCount G j +
      (revealQuery (explore G j)).card := by
  unfold answeredCount
  rw [revealTrace_coverage_succ]
  rw [Finset.card_union_of_disjoint]
  exact (revealQuery_fresh G j).symm

theorem poolEdgeCount_succ {n : ℕ} (G : Graph n) (j : ℕ) :
    poolEdgeCount G (j + 1) =
      poolEdgeCount G j - (revealQuery (explore G j)).card := by
  unfold poolEdgeCount
  rw [answeredCount_succ]
  omega

theorem revealedYes_card_succ {n : ℕ} (G : Graph n) (j : ℕ) :
    (revealTrace G (j + 1)).yes.card =
      (revealTrace G j).yes.card + queryCount G j := by
  rw [revealTrace_yes_succ, Finset.card_union_of_disjoint]
  · rfl
  · apply Finset.disjoint_left.mpr
    intro e heyes heinter
    have hequery := (Finset.mem_inter.mp heinter).2
    exact Finset.disjoint_left.mp (revealQuery_fresh G j) hequery
      (Finset.mem_union_left _ heyes)

theorem poolSuccessCount_succ {n : ℕ} (M : ℕ) (G : Graph n) (j : ℕ) :
    poolSuccessCount M G (j + 1) =
      poolSuccessCount M G j - queryCount G j := by
  unfold poolSuccessCount
  rw [revealedYes_card_succ]
  omega

def actualWalkIncrement {n : ℕ} (G : Graph n) (j : ℕ) : ℝ :=
  ((explore G (j + 1)).walk : ℝ) - ((explore G j).walk : ℝ)

def martingalePartial {n : ℕ} (G : Graph n) (mean : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, (actualWalkIncrement G j - mean j)

def driftPartial (mean : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, mean j

theorem walk_eq_sum_actualIncrements {n : ℕ} (G : Graph n) (k : ℕ) :
    ((explore G k).walk : ℝ) =
      ∑ j ∈ Finset.range k, actualWalkIncrement G j := by
  induction k with
  | zero => simp [initialState]
  | succ k ih =>
      rw [Finset.sum_range_succ]
      calc
        ((explore G (k + 1)).walk : ℝ) =
            ((explore G k).walk : ℝ) + actualWalkIncrement G k := by
              unfold actualWalkIncrement
              ring
        _ = (∑ j ∈ Finset.range k, actualWalkIncrement G j) +
            actualWalkIncrement G k := by rw [ih]

theorem walk_martingale_drift_decomposition {n : ℕ} (G : Graph n)
    (mean : ℕ → ℝ) (k : ℕ) :
    ((explore G k).walk : ℝ) =
      martingalePartial G mean k + driftPartial mean k := by
  rw [walk_eq_sum_actualIncrements]
  unfold martingalePartial driftPartial
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem characteristic_telescope
    (alpha gaussian error : ℕ → ℂ) (J : ℕ)
    (hzero : alpha 0 = 1)
    (hstep : ∀ j < J, alpha (j + 1) = gaussian j * alpha j + error j)
    (hgaussian : ∀ j < J, ‖gaussian j‖ ≤ 1) :
    ‖alpha J - ∏ j ∈ Finset.range J, gaussian j‖ ≤
      ∑ j ∈ Finset.range J, ‖error j‖ := by
  induction J with
  | zero => simp [hzero]
  | succ J ih =>
      have ih' : ‖alpha J - ∏ j ∈ Finset.range J, gaussian j‖ ≤
          ∑ j ∈ Finset.range J, ‖error j‖ :=
        ih (fun j hj => hstep j (Nat.lt_succ_of_lt hj))
          (fun j hj => hgaussian j (Nat.lt_succ_of_lt hj))
      rw [Finset.prod_range_succ, Finset.sum_range_succ,
        hstep J (Nat.lt_succ_self J)]
      calc
        ‖gaussian J * alpha J + error J -
            (∏ j ∈ Finset.range J, gaussian j) * gaussian J‖
            = ‖gaussian J *
                (alpha J - ∏ j ∈ Finset.range J, gaussian j) + error J‖ := by
                congr 1
                ring
        _ ≤ ‖gaussian J *
                (alpha J - ∏ j ∈ Finset.range J, gaussian j)‖ +
              ‖error J‖ := norm_add_le _ _
        _ = ‖gaussian J‖ *
                ‖alpha J - ∏ j ∈ Finset.range J, gaussian j‖ +
              ‖error J‖ := by rw [norm_mul]
        _ ≤ 1 * (∑ j ∈ Finset.range J, ‖error j‖) + ‖error J‖ := by
              gcongr
              exact hgaussian J (Nat.lt_succ_self J)
        _ = ∑ j ∈ Finset.range J, ‖error j‖ + ‖error J‖ := by ring

end

end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteHorizon


/-!
# Explicit finite-horizon hypergeometric moments

This layer evaluates the weighted sums left visible by
`W14_EXPLORATION_FiniteHorizon`.  The main identity is proved over `Nat`
before casting: marking an ordered `r`-tuple among the sampled successes
reduces the remaining sum to Vandermonde's identity.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Asymptotics

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteHorizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Reveal
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Conditional
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

def hypergeomNumerator (E R d y : ℕ) : ℕ :=
  R.choose y * (E - R).choose (d - y)

lemma fallingReal_natCast (x r : ℕ) :
    fallingReal (x : ℝ) r = (x.descFactorial r : ℝ) := by
  induction r with
  | zero => simp [fallingReal]
  | succ r ih =>
      rw [fallingReal_succ, Nat.descFactorial_succ]
      by_cases hr : r ≤ x
      · rw [Nat.cast_mul, Nat.cast_sub hr, ih]
        ring
      · have hxr : x < r := Nat.lt_of_not_ge hr
        have hz : x.descFactorial r = 0 :=
          Nat.descFactorial_eq_zero_iff_lt.mpr hxr
        rw [ih, hz]
        simp

lemma sum_hypergeomNumerator_mul_descFactorial
    (E R d r : ℕ) (hR : R ≤ E) (hrR : r ≤ R) (hrd : r ≤ d) :
    (∑ y ∈ Finset.range (d + 1),
        hypergeomNumerator E R d y * y.descFactorial r) =
      R.descFactorial r * (E - r).choose (d - r) := by
  have hsplit : d + 1 = r + (d + 1 - r) := by omega
  rw [hsplit, Finset.sum_range_add]
  have hzero :
      (∑ y ∈ Finset.range r,
        hypergeomNumerator E R d y * y.descFactorial r) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    have hyr : y < r := Finset.mem_range.mp hy
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr hyr, Nat.mul_zero]
  rw [hzero, zero_add]
  have hrle : r ≤ d + 1 := le_trans hrd (Nat.le_succ d)
  have hrange : d + 1 - r = d - r + 1 := by omega
  rw [hrange]
  calc
    (∑ z ∈ Finset.range (d - r + 1),
        hypergeomNumerator E R d (r + z) * (r + z).descFactorial r) =
        ∑ z ∈ Finset.range (d - r + 1),
          R.descFactorial r *
            ((R - r).choose z * (E - R).choose ((d - r) - z)) := by
              apply Finset.sum_congr rfl
              intro z hz
              unfold hypergeomNumerator
              have hchoose : R.choose (r + z) * (r + z).choose r =
                  R.choose r * (R - r).choose z := by
                simpa [Nat.add_sub_cancel_left] using!
                  (Nat.choose_mul (n := R) (k := r + z) (s := r)
                    (Nat.le_add_right r z))
              rw [Nat.descFactorial_eq_factorial_mul_choose,
                Nat.descFactorial_eq_factorial_mul_choose]
              have hsub₂ : d - (r + z) = d - r - z := by omega
              rw [hsub₂]
              calc
                R.choose (r + z) * (E - R).choose (d - r - z) *
                    (r.factorial * (r + z).choose r) =
                    (R.choose (r + z) * (r + z).choose r) *
                      r.factorial * (E - R).choose (d - r - z) := by ring
                _ = (r.factorial * R.choose r) *
                    ((R - r).choose z * (E - R).choose (d - r - z)) := by
                      rw [hchoose]
                      ring
    _ = R.descFactorial r *
          ∑ z ∈ Finset.range (d - r + 1),
            ((R - r).choose z * (E - R).choose ((d - r) - z)) := by
              rw [Finset.mul_sum]
    _ = R.descFactorial r *
          ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (d - r),
            ((R - r).choose ij.1 * (E - R).choose ij.2) := by
              rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    _ = R.descFactorial r * ((R - r + (E - R)).choose (d - r)) := by
              rw [Nat.add_choose_eq]
    _ = R.descFactorial r * (E - r).choose (d - r) := by
              have hsum : R - r + (E - R) = E - r := by omega
              rw [hsum]

def explicitHypergeomFactorialMoment (E R d r : ℕ) : ℝ :=
  (R.descFactorial r : ℝ) * ((E - r).choose (d - r) : ℝ) /
    (E.choose d : ℝ)

theorem factorialMoment_hypergeomMass
    (E R d r : ℕ) (hR : R ≤ E) (hd : d ≤ E)
    (hrR : r ≤ R) (hrd : r ≤ d) :
    factorialMoment d (hypergeomMass E R d) r =
      explicitHypergeomFactorialMoment E R d r := by
  unfold factorialMoment weightedMoment explicitHypergeomFactorialMoment
  have hguard : R ≤ E ∧ d ≤ E := ⟨hR, hd⟩
  simp only [hypergeomMass, hguard, true_and]
  have hchoose : (E.choose d : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hd
  calc
    (∑ y ∈ Finset.range (d + 1),
        (if y ≤ d then
          (R.choose y : ℝ) * ((E - R).choose (d - y) : ℝ) /
            (E.choose d : ℝ)
        else 0) * fallingReal (y : ℝ) r) =
        ∑ y ∈ Finset.range (d + 1),
          ((hypergeomNumerator E R d y * y.descFactorial r : ℕ) : ℝ) /
            (E.choose d : ℝ) := by
              apply Finset.sum_congr rfl
              intro y hy
              have hyd : y ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hy)
              rw [if_pos hyd, fallingReal_natCast]
              simp only [hypergeomNumerator, Nat.cast_mul]
              field_simp
    _ = ((∑ y ∈ Finset.range (d + 1),
          hypergeomNumerator E R d y * y.descFactorial r : ℕ) : ℝ) /
          (E.choose d : ℝ) := by
            rw [Nat.cast_sum]
            exact (Finset.sum_div _ _ _).symm
    _ = (R.descFactorial r : ℝ) * ((E - r).choose (d - r) : ℝ) /
          (E.choose d : ℝ) := by
            rw [sum_hypergeomNumerator_mul_descFactorial E R d r hR hrR hrd]
            norm_cast

theorem factorialMoment_hypergeomMass_ratio
    (E R d r : ℕ) (hR : R ≤ E) (hd : d ≤ E)
    (hrR : r ≤ R) (hrd : r ≤ d) :
    factorialMoment d (hypergeomMass E R d) r =
      (d.descFactorial r : ℝ) * (R.descFactorial r : ℝ) /
        (E.descFactorial r : ℝ) := by
  rw [factorialMoment_hypergeomMass E R d r hR hd hrR hrd]
  unfold explicitHypergeomFactorialMoment
  have hrE : r ≤ E := hrR.trans hR
  have hdr : d - r ≤ E - r := Nat.sub_le_sub_right hd r
  have hchooseE : (E.choose d : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hd
  have hdescE : (E.descFactorial r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hrE))
  have hcomb : E.choose d * d.choose r =
      E.choose r * (E - r).choose (d - r) :=
    Nat.choose_mul hrd
  have hnat : R.descFactorial r * (E - r).choose (d - r) *
        E.descFactorial r =
      (d.descFactorial r * R.descFactorial r) * E.choose d := by
    simp only [Nat.descFactorial_eq_factorial_mul_choose]
    calc
      r.factorial * R.choose r * (E - r).choose (d - r) *
          (r.factorial * E.choose r) =
          r.factorial ^ 2 * R.choose r *
            (E.choose r * (E - r).choose (d - r)) := by ring
      _ = (r.factorial * d.choose r * (r.factorial * R.choose r)) *
            E.choose d := by rw [← hcomb]; ring
  exact (div_eq_div_iff hchooseE hdescE).2 (by exact_mod_cast hnat)

def conditionalQueryRawMoment {n : ℕ} (M : ℕ) (G : Graph n)
    (j r : ℕ) : ℝ :=
  rawMoment (revealQuery (explore G j)).card
    (fun y => conditionalProbM n M
      (fun H => revealTrace H j = revealTrace G j)
      (fun H => (H ∩ revealQuery (explore G j)).card = y)) r

theorem conditionalQueryRawMoment_eq_hypergeom
    (hfinite : FiniteEnumerationStatement) {n M : ℕ}
    (hM : M ≤ capacity n) (G : Graph n) (j r : ℕ)
    (hpos : 0 < probM n M (fun H => revealTrace H j = revealTrace G j)) :
    conditionalQueryRawMoment M G j r =
      rawMoment (revealQuery (explore G j)).card
        (hypergeomMass
          (capacity n - (revealTrace G j).yes.card - (revealTrace G j).no.card)
          (M - (revealTrace G j).yes.card)
          (revealQuery (explore G j)).card) r := by
  unfold conditionalQueryRawMoment rawMoment weightedMoment
  apply Finset.sum_congr rfl
  intro y hy
  simp only
  rw [conditional_history_query_eq_hypergeom hfinite hM G j y hpos]

end

end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Asymptotics


/-!
# Hypergeometric moments without cardinality exceptions

The falling-factorial formula is valid even when there are fewer successes or
queries than the order of the moment.  This layer also records the exact
finite-population variance and the one-step density preservation identity.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_MomentBounds

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteHorizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Asymptotics
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Reveal
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Conditional
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

theorem factorialMoment_hypergeomMass_all (E R d r : ℕ)
    (hR : R ≤ E) (hd : d ≤ E) :
    factorialMoment d (hypergeomMass E R d) r =
      (d.descFactorial r : ℝ) * (R.descFactorial r : ℝ) /
        (E.descFactorial r : ℝ) := by
  by_cases hrd : r ≤ d
  · by_cases hrR : r ≤ R
    · exact factorialMoment_hypergeomMass_ratio E R d r hR hd hrR hrd
    · have hRlt : R < r := Nat.lt_of_not_ge hrR
      have hzero : factorialMoment d (hypergeomMass E R d) r = 0 := by
        unfold factorialMoment weightedMoment
        apply Finset.sum_eq_zero
        intro y hy
        by_cases hyr : y < r
        · dsimp only
          rw [fallingReal_natCast,
            Nat.descFactorial_eq_zero_iff_lt.mpr hyr]
          ring
        · have hRy : R < y := hRlt.trans_le (Nat.le_of_not_gt hyr)
          have hyd : y ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hy)
          simp [hypergeomMass, hR, hd, hyd,
            Nat.choose_eq_zero_of_lt hRy]
      rw [hzero, Nat.descFactorial_eq_zero_iff_lt.mpr hRlt]
      simp
  · have hdlt : d < r := Nat.lt_of_not_ge hrd
    have hzero : factorialMoment d (hypergeomMass E R d) r = 0 := by
      unfold factorialMoment weightedMoment
      apply Finset.sum_eq_zero
      intro y hy
      have hyr : y < r := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hy)).trans_lt hdlt
      dsimp only
      rw [fallingReal_natCast,
        Nat.descFactorial_eq_zero_iff_lt.mpr hyr]
      ring
    rw [hzero, Nat.descFactorial_eq_zero_iff_lt.mpr hdlt]
    simp

theorem rawMoment_hypergeomMass_one_all (E R d : ℕ)
    (hR : R ≤ E) (hd : d ≤ E) :
    rawMoment d (hypergeomMass E R d) 1 = (d : ℝ) * R / E := by
  rw [rawMoment_one, factorialMoment_hypergeomMass_all E R d 1 hR hd]
  simp

theorem rawMoment_hypergeomMass_two_all (E R d : ℕ)
    (hR : R ≤ E) (hd : d ≤ E) :
    rawMoment d (hypergeomMass E R d) 2 =
      (d.descFactorial 2 : ℝ) * (R.descFactorial 2 : ℝ) /
        (E.descFactorial 2 : ℝ) + (d : ℝ) * R / E := by
  rw [rawMoment_two,
    factorialMoment_hypergeomMass_all E R d 2 hR hd,
    factorialMoment_hypergeomMass_all E R d 1 hR hd]
  simp

theorem descFactorial_two_real (x : ℕ) :
    (x.descFactorial 2 : ℝ) = (x : ℝ) * ((x : ℝ) - 1) := by
  rw [← fallingReal_natCast, fallingReal_two]

def hypergeomMean (E R d : ℕ) : ℝ := (d : ℝ) * R / E

def hypergeomVariance (E R d : ℕ) : ℝ :=
  rawMoment d (hypergeomMass E R d) 2 - (hypergeomMean E R d) ^ 2

theorem hypergeomVariance_eq (E R d : ℕ)
    (hR : R ≤ E) (hd : d ≤ E) (hE : 2 ≤ E) :
    hypergeomVariance E R d =
      (d : ℝ) * ((R : ℝ) / E) * (1 - (R : ℝ) / E) *
        ((E - d : ℕ) : ℝ) / ((E : ℝ) - 1) := by
  have hE0 : (E : ℝ) ≠ 0 := by exact_mod_cast (by omega : E ≠ 0)
  have hE1 : (E : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ E := by exact_mod_cast hE
    linarith
  rw [hypergeomVariance, hypergeomMean,
    rawMoment_hypergeomMass_two_all E R d hR hd,
    descFactorial_two_real d, descFactorial_two_real R,
    descFactorial_two_real E, Nat.cast_sub hd]
  field_simp
  ring

theorem hypergeomVariance_nonneg_le_mean (E R d : ℕ)
    (hR : R ≤ E) (hd : d ≤ E) (hE : 2 ≤ E) :
    0 ≤ hypergeomVariance E R d ∧
      hypergeomVariance E R d ≤ hypergeomMean E R d := by
  rw [hypergeomVariance_eq E R d hR hd hE]
  have hE0 : (0 : ℝ) < E := by
    have : (2 : ℝ) ≤ E := by exact_mod_cast hE
    linarith
  have hE1 : (0 : ℝ) < (E : ℝ) - 1 := by
    have : (2 : ℝ) ≤ E := by exact_mod_cast hE
    linarith
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have hRE : (R : ℝ) ≤ E := by exact_mod_cast hR
  have hp0 : 0 ≤ (R : ℝ) / E := div_nonneg hR0 hE0.le
  have hp1 : (R : ℝ) / E ≤ 1 := (div_le_iff₀ hE0).mpr (by nlinarith)
  have hp' : 0 ≤ 1 - (R : ℝ) / E := by linarith
  have hp'' : 1 - (R : ℝ) / E ≤ 1 := by linarith
  have hdiff0 : (0 : ℝ) ≤ (E - d : ℕ) := Nat.cast_nonneg _
  constructor
  · positivity
  · by_cases hdz : d = 0
    · simp [hdz, hypergeomMean]
    · have hdiff1 : ((E - d : ℕ) : ℝ) ≤ (E : ℝ) - 1 := by
        have : E - d ≤ E - 1 := by omega
        have hc : ((E - d : ℕ) : ℝ) ≤ ((E - 1 : ℕ) : ℝ) := by
          exact_mod_cast this
        simpa [Nat.cast_sub (by omega : 1 ≤ E)] using! hc
      have hfrac : ((E - d : ℕ) : ℝ) / ((E : ℝ) - 1) ≤ 1 :=
        (div_le_iff₀ hE1).mpr (by nlinarith)
      calc
        (d : ℝ) * ((R : ℝ) / E) * (1 - (R : ℝ) / E) *
            ((E - d : ℕ) : ℝ) / ((E : ℝ) - 1) =
            ((d : ℝ) * ((R : ℝ) / E)) *
              (1 - (R : ℝ) / E) *
                (((E - d : ℕ) : ℝ) / ((E : ℝ) - 1)) := by ring
        _ ≤ ((d : ℝ) * ((R : ℝ) / E)) * 1 * 1 := by
          gcongr
        _ = hypergeomMean E R d := by
          unfold hypergeomMean
          ring

theorem conditionalQueryRawMoment_all
    (hfinite : FiniteEnumerationStatement) {n M : ℕ}
    (hM : M ≤ capacity n) (G : Graph n) (j r : ℕ)
    (hpos : 0 < probM n M (fun H => revealTrace H j = revealTrace G j)) :
    conditionalQueryRawMoment M G j r =
      rawMoment (revealQuery (explore G j)).card
        (hypergeomMass
          (capacity n - (revealTrace G j).yes.card - (revealTrace G j).no.card)
          (M - (revealTrace G j).yes.card)
          (revealQuery (explore G j)).card) r :=
  conditionalQueryRawMoment_eq_hypergeom hfinite hM G j r hpos

theorem conditionalQueryMean_all
    (hfinite : FiniteEnumerationStatement) {n M : ℕ}
    (hM : M ≤ capacity n) (G : Graph n) (j : ℕ)
    (hpos : 0 < probM n M (fun H => revealTrace H j = revealTrace G j))
    (hR : M - (revealTrace G j).yes.card ≤
      capacity n - (revealTrace G j).yes.card - (revealTrace G j).no.card)
    (hd : (revealQuery (explore G j)).card ≤
      capacity n - (revealTrace G j).yes.card - (revealTrace G j).no.card) :
    conditionalQueryRawMoment M G j 1 =
      (revealQuery (explore G j)).card * poolDensity M G j := by
  rw [conditionalQueryRawMoment_all hfinite hM G j 1 hpos,
    rawMoment_hypergeomMass_one_all _ _ _ hR hd]
  unfold poolDensity poolSuccessCount poolEdgeCount answeredCount
  rw [Finset.card_union_of_disjoint (revealTrace_yes_no_disjoint G j)]
  have hsub : capacity n - ((revealTrace G j).yes.card +
        (revealTrace G j).no.card) =
      capacity n - (revealTrace G j).yes.card -
        (revealTrace G j).no.card := by omega
  rw [hsub]
  ring

theorem conditionalQueryVariance_eq
    (hfinite : FiniteEnumerationStatement) {n M : ℕ}
    (hM : M ≤ capacity n) (G : Graph n) (j : ℕ)
    (hpos : 0 < probM n M (fun H => revealTrace H j = revealTrace G j))
    (hR : M - (revealTrace G j).yes.card ≤
      capacity n - (revealTrace G j).yes.card - (revealTrace G j).no.card)
    (hd : (revealQuery (explore G j)).card ≤
      capacity n - (revealTrace G j).yes.card - (revealTrace G j).no.card)
    (hE : 2 ≤ capacity n - (revealTrace G j).yes.card -
      (revealTrace G j).no.card) :
    let E := capacity n - (revealTrace G j).yes.card -
      (revealTrace G j).no.card
    let R := M - (revealTrace G j).yes.card
    let d := (revealQuery (explore G j)).card
    conditionalQueryRawMoment M G j 2 -
        (conditionalQueryRawMoment M G j 1) ^ 2 =
      (d : ℝ) * ((R : ℝ) / E) * (1 - (R : ℝ) / E) *
        ((E - d : ℕ) : ℝ) / ((E : ℝ) - 1) := by
  dsimp
  rw [conditionalQueryRawMoment_eq_hypergeom hfinite hM G j 2 hpos,
    conditionalQueryRawMoment_eq_hypergeom hfinite hM G j 1 hpos,
    rawMoment_hypergeomMass_one_all _ _ _ hR hd]
  exact hypergeomVariance_eq _ _ _ hR hd hE

end

end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_MomentBounds


/-!
# Finite pool admissibility and uniform query moments

The cardinality hypotheses in the hypergeometric moment identities follow
from every realized fixed-edge reveal trace.  The fourth-moment estimate is
uniform whenever the remaining pool is large and its query mean is bounded.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_PoolUniform

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Reveal
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Conditional
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteHorizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Asymptotics
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_MomentBounds
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

private theorem graph_card_le_capacity {n : ℕ} (H : Graph n) :
    H.card ≤ capacity n := by
  calc
    H.card ≤ (Finset.univ : Finset (Edge n)).card :=
      Finset.card_le_card (Finset.subset_univ H)
    _ = capacity n := by simp [card_edge]

theorem poolSuccessCount_le_poolEdgeCount {n M : ℕ}
    (G : Graph n) (j : ℕ) (hG : G.card = M) :
    poolSuccessCount M G j ≤ poolEdgeCount G j := by
  let yes := (revealTrace G j).yes
  let no := (revealTrace G j).no
  have hyes : yes.card ≤ M := by
    rw [← hG]
    exact Finset.card_le_card (revealTrace_yes_subset_graph G j)
  have hGN : Disjoint G no := (revealTrace_no_disjoint_graph G j).symm
  have hGNcap : M + no.card ≤ capacity n := by
    have hcard : (G ∪ no).card = G.card + no.card :=
      Finset.card_union_of_disjoint hGN
    rw [← hG, ← hcard]
    exact graph_card_le_capacity _
  dsimp [yes, no] at hyes hGNcap
  unfold poolSuccessCount poolEdgeCount answeredCount
  rw [Finset.card_union_of_disjoint (revealTrace_yes_no_disjoint G j)]
  omega

theorem queryCard_le_poolEdgeCount {n : ℕ} (G : Graph n) (j : ℕ) :
    (revealQuery (explore G j)).card ≤ poolEdgeCount G j := by
  have hdisj := (revealQuery_fresh G j).symm
  have hcard :
      (((revealTrace G j).yes ∪ (revealTrace G j).no) ∪
        revealQuery (explore G j)).card =
      answeredCount G j + (revealQuery (explore G j)).card := by
    unfold answeredCount
    exact Finset.card_union_of_disjoint hdisj
  have hcap := graph_card_le_capacity
    (((revealTrace G j).yes ∪ (revealTrace G j).no) ∪
      revealQuery (explore G j))
  unfold poolEdgeCount
  omega

theorem queryCount_le_poolSuccessCount {n M : ℕ}
    (G : Graph n) (j : ℕ) (hG : G.card = M) :
    queryCount G j ≤ poolSuccessCount M G j := by
  let yes := (revealTrace G j).yes
  let query := revealQuery (explore G j)
  have hdisj : Disjoint yes (G ∩ query) := by
    apply Finset.disjoint_left.mpr
    intro e heyes heinter
    exact Finset.disjoint_left.mp (revealQuery_fresh G j)
      (Finset.mem_inter.mp heinter).2 (Finset.mem_union_left _ heyes)
  have hsub : yes ∪ (G ∩ query) ⊆ G :=
    Finset.union_subset (revealTrace_yes_subset_graph G j)
      Finset.inter_subset_left
  have hcard : yes.card + queryCount G j ≤ M := by
    have heq : (yes ∪ (G ∩ query)).card =
        yes.card + queryCount G j := by
      unfold queryCount
      exact Finset.card_union_of_disjoint hdisj
    rw [← heq, ← hG]
    exact Finset.card_le_card hsub
  unfold poolSuccessCount
  dsimp [yes] at hcard
  omega

theorem poolEdgeCount_initial (n : ℕ) (G : Graph n) :
    poolEdgeCount G 0 = capacity n := by
  simp [poolEdgeCount, answeredCount, revealTrace_zero, initialReveal]

theorem poolSuccessCount_initial (n M : ℕ) (G : Graph n) :
    poolSuccessCount M G 0 = M := by
  simp [poolSuccessCount, revealTrace_zero, initialReveal]

theorem poolEdgeCount_eq_initial_sub_querySum {n : ℕ}
    (G : Graph n) (k : ℕ) :
    poolEdgeCount G k = capacity n -
      ∑ j ∈ Finset.range k, (revealQuery (explore G j)).card := by
  induction k with
  | zero => simp [poolEdgeCount_initial]
  | succ k ih =>
      rw [poolEdgeCount_succ, ih, Finset.sum_range_succ]
      omega

theorem poolDensity_update {n M : ℕ} (G : Graph n) (j : ℕ)
    (hG : G.card = M) :
    poolDensity M G (j + 1) =
      ((poolSuccessCount M G j : ℝ) - queryCount G j) /
        ((poolEdgeCount G j : ℝ) -
          (revealQuery (explore G j)).card) := by
  have hY := queryCount_le_poolSuccessCount G j hG
  have hd := queryCard_le_poolEdgeCount G j
  unfold poolDensity
  rw [poolSuccessCount_succ, poolEdgeCount_succ]
  rw [Nat.cast_sub hY, Nat.cast_sub hd]

theorem poolDensity_increment {n M : ℕ} (G : Graph n) (j : ℕ)
    (hG : G.card = M)
    (hstrict : (revealQuery (explore G j)).card < poolEdgeCount G j) :
    poolDensity M G (j + 1) - poolDensity M G j =
      ((revealQuery (explore G j)).card * poolDensity M G j -
        queryCount G j) /
      ((poolEdgeCount G j : ℝ) -
        (revealQuery (explore G j)).card) := by
  rw [poolDensity_update G j hG]
  have hE : (poolEdgeCount G j : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : poolEdgeCount G j ≠ 0)
  have hEd : (poolEdgeCount G j : ℝ) -
      (revealQuery (explore G j)).card ≠ 0 := by
    have hreal : ((revealQuery (explore G j)).card : ℝ) <
        poolEdgeCount G j := by exact_mod_cast hstrict
    linarith
  unfold poolDensity
  field_simp
  ring

/-- A falling-factorial query moment is bounded by a power of twice its
sampling mean while the remaining edge pool has at least eight edges. -/
theorem hypergeomFactorialMoment_le_meanPow
    (E R d r : ℕ) (hR : R ≤ E) (hd : d ≤ E)
    (hE : 8 ≤ E) (hr : r ≤ 4) :
    factorialMoment d (hypergeomMass E R d) r ≤
      (((d : ℝ) * R) / ((E : ℝ) / 2)) ^ r := by
  rw [factorialMoment_hypergeomMass_all E R d r hR hd]
  have hrE : r ≤ E := by omega
  have hEpos : (0 : ℝ) < E := by
    have : (8 : ℝ) ≤ E := by exact_mod_cast hE
    linarith
  have hhalf : (0 : ℝ) < (E : ℝ) / 2 := by positivity
  have hdenPos : (0 : ℝ) < (E.descFactorial r : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hrE
  have hnat : E ≤ 2 * (E + 1 - r) := by omega
  have hbase : (E : ℝ) / 2 ≤ ((E + 1 - r : ℕ) : ℝ) := by
    have hc : (E : ℝ) ≤ 2 * ((E + 1 - r : ℕ) : ℝ) := by
      exact_mod_cast hnat
    linarith
  have hden : ((E : ℝ) / 2) ^ r ≤ (E.descFactorial r : ℝ) := by
    calc
      ((E : ℝ) / 2) ^ r ≤ ((E + 1 - r : ℕ) : ℝ) ^ r := by gcongr
      _ ≤ (E.descFactorial r : ℝ) := by
        exact_mod_cast Nat.pow_sub_le_descFactorial E r
  have hdnum : (d.descFactorial r : ℝ) ≤ (d : ℝ) ^ r := by
    exact_mod_cast Nat.descFactorial_le_pow d r
  have hRnum : (R.descFactorial r : ℝ) ≤ (R : ℝ) ^ r := by
    exact_mod_cast Nat.descFactorial_le_pow R r
  have hnum : (d.descFactorial r : ℝ) * (R.descFactorial r : ℝ) ≤
      (d : ℝ) ^ r * (R : ℝ) ^ r := by gcongr
  have hupper : 0 ≤ (d : ℝ) ^ r * (R : ℝ) ^ r := by positivity
  have hlow : 0 ≤ ((E : ℝ) / 2) ^ r := by positivity
  have hratio :
      (d.descFactorial r : ℝ) * (R.descFactorial r : ℝ) /
          (E.descFactorial r : ℝ) ≤
        ((d : ℝ) ^ r * (R : ℝ) ^ r) / (((E : ℝ) / 2) ^ r) := by
    apply (div_le_div_iff₀ hdenPos (pow_pos hhalf r)).mpr
    have hfirst := mul_le_mul_of_nonneg_right hnum hlow
    have hsecond := mul_le_mul_of_nonneg_left hden hupper
    nlinarith
  calc
    (d.descFactorial r : ℝ) * (R.descFactorial r : ℝ) /
        (E.descFactorial r : ℝ) ≤
      ((d : ℝ) ^ r * (R : ℝ) ^ r) / (((E : ℝ) / 2) ^ r) := hratio
    _ = (((d : ℝ) * R) / ((E : ℝ) / 2)) ^ r := by
      simp only [div_pow, mul_pow]

theorem hypergeomRawMoment_four_le_polynomial
    (E R d : ℕ) (hR : R ≤ E) (hd : d ≤ E) (hE : 8 ≤ E) :
    let b := ((d : ℝ) * R) / ((E : ℝ) / 2)
    rawMoment d (hypergeomMass E R d) 4 ≤
      b ^ 4 + 6 * b ^ 3 + 7 * b ^ 2 + b := by
  dsimp
  rw [rawMoment_four]
  have h1 := hypergeomFactorialMoment_le_meanPow E R d 1 hR hd hE (by omega)
  have h2 := hypergeomFactorialMoment_le_meanPow E R d 2 hR hd hE (by omega)
  have h3 := hypergeomFactorialMoment_le_meanPow E R d 3 hR hd hE (by omega)
  have h4 := hypergeomFactorialMoment_le_meanPow E R d 4 hR hd hE (by omega)
  nlinarith [h1, h2, h3, h4]

theorem hypergeomRawMoment_four_le_constant
    (E R d : ℕ) (hR : R ≤ E) (hd : d ≤ E) (hE : 8 ≤ E)
    (K : ℝ)
    (hmean : ((d : ℝ) * R) / ((E : ℝ) / 2) ≤ K) :
    rawMoment d (hypergeomMass E R d) 4 ≤
      K ^ 4 + 6 * K ^ 3 + 7 * K ^ 2 + K := by
  let b := ((d : ℝ) * R) / ((E : ℝ) / 2)
  have hb0 : 0 ≤ b := by
    dsimp [b]
    positivity
  have hbK : b ≤ K := hmean
  have h2 : b ^ 2 ≤ K ^ 2 := by gcongr
  have h3 : b ^ 3 ≤ K ^ 3 := by gcongr
  have h4 : b ^ 4 ≤ K ^ 4 := by gcongr
  have hraw := hypergeomRawMoment_four_le_polynomial E R d hR hd hE
  change rawMoment d (hypergeomMass E R d) 4 ≤
    b ^ 4 + 6 * b ^ 3 + 7 * b ^ 2 + b at hraw
  nlinarith

theorem conditionalQueryRawMoment_four_le_constant
    (hfinite : FiniteEnumerationStatement) {n M : ℕ}
    (hM : M ≤ capacity n) (G : Graph n) (j : ℕ)
    (hpos : 0 < probM n M (fun H => revealTrace H j = revealTrace G j))
    (hR : poolSuccessCount M G j ≤ poolEdgeCount G j)
    (hd : (revealQuery (explore G j)).card ≤ poolEdgeCount G j)
    (hE : 8 ≤ poolEdgeCount G j) (K : ℝ)
    (hmean : ((revealQuery (explore G j)).card : ℝ) *
        poolSuccessCount M G j / ((poolEdgeCount G j : ℝ) / 2) ≤ K) :
    conditionalQueryRawMoment M G j 4 ≤
      K ^ 4 + 6 * K ^ 3 + 7 * K ^ 2 + K := by
  rw [conditionalQueryRawMoment_all hfinite hM G j 4 hpos]
  have hEeq : poolEdgeCount G j =
      capacity n - (revealTrace G j).yes.card -
        (revealTrace G j).no.card := by
    unfold poolEdgeCount answeredCount
    rw [Finset.card_union_of_disjoint (revealTrace_yes_no_disjoint G j)]
    omega
  have hReq : poolSuccessCount M G j =
      M - (revealTrace G j).yes.card := rfl
  have hdeq : (revealQuery (explore G j)).card =
      (revealQuery (explore G j)).card := rfl
  rw [hEeq] at hR hd hE hmean
  rw [hReq] at hR hmean
  exact hypergeomRawMoment_four_le_constant _ _ _ hR hd hE K hmean

end

end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_PoolUniform


/-!
# Query size and uniform finite-horizon estimates

The exact query size is expressed through processed and queued vertices. A
single deterministic budget then controls every realized pool, query mean,
conditional variance, and fourth moment on the horizon.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Horizon

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Pruefer
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Reveal
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteHorizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Asymptotics
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_MomentBounds
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_PoolUniform
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

private lemma edgeOf_eq_of_endpoints {n : ℕ} (v u : Fin n) (hvu : v ≠ u)
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

private lemma edgeOf_right_injective {n : ℕ} (v u w : Fin n)
    (hu : v ≠ u) (hw : v ≠ w)
    (heq : edgeOf v u hu = edgeOf v w hw) : u = w := by
  have h₁ := edgeOf_endpoints v u hu
  have h₂ := edgeOf_endpoints v w hw
  rw [heq] at h₁
  rcases h₁ with ⟨h₁a, h₁b⟩ | ⟨h₁a, h₁b⟩ <;>
    rcases h₂ with ⟨h₂a, h₂b⟩ | ⟨h₂a, h₂b⟩ <;> omega

/-- Every neutral vertex contributes exactly one incident query edge. -/
theorem incidentQuery_card_eq_neutral {n : ℕ} (v : Fin n)
    (discovered : Finset (Fin n)) (hv : v ∈ discovered) :
    (incidentQuery v discovered).card = n - discovered.card := by
  have hbij : ((Finset.univ : Finset (Fin n)) \ discovered).card =
      (incidentQuery v discovered).card := by
    apply Finset.card_bij
      (fun u hu => edgeOf v u (by
        have hnot : u ∉ discovered := (Finset.mem_sdiff.mp hu).2
        intro heq
        exact hnot (heq ▸ hv)))
    · intro u hu
      have hnot : u ∉ discovered := (Finset.mem_sdiff.mp hu).2
      rcases edgeOf_endpoints v u (by
        intro heq
        exact hnot (heq ▸ hv)) with h | h
      · exact (mem_incidentQuery_iff v discovered _).mpr
          (Or.inl ⟨h.1, by simpa [h.2] using! hnot⟩)
      · exact (mem_incidentQuery_iff v discovered _).mpr
          (Or.inr ⟨h.2, by simpa [h.1] using! hnot⟩)
    · intro u hu w hw heq
      exact edgeOf_right_injective v u w
        (by intro h; exact (Finset.mem_sdiff.mp hu).2 (h ▸ hv))
        (by intro h; exact (Finset.mem_sdiff.mp hw).2 (h ▸ hv)) heq
    · intro e he
      rcases (mem_incidentQuery_iff v discovered e).mp he with h | h
      · have hne : v ≠ e.val.2 := by
          intro heq
          exact (ne_of_lt e.property) (h.1.trans heq)
        refine ⟨e.val.2, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h.2⟩, ?_⟩
        exact edgeOf_eq_of_endpoints v e.val.2 hne e (Or.inl ⟨h.1, rfl⟩)
      · have hne : v ≠ e.val.1 := by
          intro heq
          exact (ne_of_lt e.property) (heq.symm.trans h.1.symm)
        refine ⟨e.val.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h.2⟩, ?_⟩
        exact edgeOf_eq_of_endpoints v e.val.1 hne e (Or.inr ⟨rfl, h.1⟩)
  rw [Finset.card_sdiff] at hbij
  simpa using! hbij.symm

/-- The finite BFS query size, including the one-vertex root correction. -/
theorem queryCard_exact {n : ℕ} (G : Graph n) (j : ℕ) (hj : j < n) :
    (revealQuery (explore G j)).card =
      n - j - (explore G j).queue.length -
        (if (explore G j).queue = [] then 1 else 0) := by
  have hp := processed_card_of_le G j (Nat.le_of_lt hj)
  have ha := processed_card_add_queue_length G j
  rw [hp] at ha
  rcases hstate : explore G j with ⟨seen, queue, z⟩
  simp only [hstate] at ha
  cases queue with
  | cons v rest =>
      have hv : v ∈ seen := by
        have hs := explore_queue_subset_seen G j
        rw [hstate] at hs
        exact hs (by simp)
      rw [revealQuery_queue_cons,
        incidentQuery_card_eq_neutral v seen hv]
      simp only [List.cons_ne_nil, ↓reduceIte]
      omega
  | nil =>
      have hseen : seen.card = j := by simpa using! ha.symm
      have hnonempty : ((Finset.univ : Finset (Fin n)) \ seen).Nonempty := by
        apply Finset.sdiff_nonempty_of_card_lt_card
        simpa [hseen] using! hj
      let v := ((Finset.univ : Finset (Fin n)) \ seen).min' hnonempty
      have hvnot : v ∉ seen :=
        (Finset.mem_sdiff.mp (Finset.min'_mem _ hnonempty)).2
      have hcard : (insert v seen).card = seen.card + 1 :=
        Finset.card_insert_of_notMem hvnot
      rw [revealQuery_queue_nil_of_nonempty seen z hnonempty]
      change (incidentQuery v (insert v seen)).card = _
      rw [incidentQuery_card_eq_neutral v (insert v seen) (Finset.mem_insert_self _ _)]
      simp only [List.length_nil, ↓reduceIte, Nat.sub_zero]
      omega

theorem queryCard_le_order {n : ℕ} (G : Graph n) (j : ℕ)
    (hj : j < n) : (revealQuery (explore G j)).card ≤ n := by
  rw [queryCard_exact G j hj]
  omega

theorem querySum_le_order_mul {n : ℕ} (G : Graph n) (j : ℕ)
    (hj : j ≤ n) :
    (∑ i ∈ Finset.range j, (revealQuery (explore G i)).card) ≤ j * n := by
  calc
    (∑ i ∈ Finset.range j, (revealQuery (explore G i)).card) ≤
        ∑ _i ∈ Finset.range j, n := by
          apply Finset.sum_le_sum
          intro i hi
          exact queryCard_le_order G i
            ((Finset.mem_range.mp hi).trans_le hj)
    _ = j * n := by simp

/-- A numerical budget sufficient for all graphs on a fixed horizon. -/
def HorizonBudget (n M J : ℕ) (K : ℝ) : Prop :=
  J ≤ n ∧ J * n + 8 ≤ capacity n ∧ 0 ≤ K ∧
    2 * (n : ℝ) * M ≤ K * ((capacity n - J * n : ℕ) : ℝ)

theorem poolEdgeCount_ge_horizon {n M J : ℕ} {K : ℝ}
    (G : Graph n) (j : ℕ) (hbudget : HorizonBudget n M J K)
    (hj : j ≤ J) : capacity n - J * n ≤ poolEdgeCount G j := by
  have hjN : j ≤ n := hj.trans hbudget.1
  have hsum := querySum_le_order_mul G j hjN
  have hmul : j * n ≤ J * n := Nat.mul_le_mul_right n hj
  rw [poolEdgeCount_eq_initial_sub_querySum]
  omega

theorem poolEdgeCount_ge_eight {n M J : ℕ} {K : ℝ}
    (G : Graph n) (j : ℕ) (hbudget : HorizonBudget n M J K)
    (hj : j ≤ J) : 8 ≤ poolEdgeCount G j := by
  have hlow := poolEdgeCount_ge_horizon G j hbudget hj
  dsimp [HorizonBudget] at hbudget
  omega

theorem horizon_halfMean_le {n M J : ℕ} {K : ℝ}
    (G : Graph n) (j : ℕ) (hG : G.card = M)
    (hbudget : HorizonBudget n M J K) (hj : j < J) :
    ((revealQuery (explore G j)).card : ℝ) * poolSuccessCount M G j /
      ((poolEdgeCount G j : ℝ) / 2) ≤ K := by
  let d := (revealQuery (explore G j)).card
  let R := poolSuccessCount M G j
  let E := poolEdgeCount G j
  let L := capacity n - J * n
  have hjN : j < n := hj.trans_le hbudget.1
  have hd : d ≤ n := queryCard_le_order G j hjN
  have hR : R ≤ M := by
    dsimp [R, poolSuccessCount]
    omega
  have hEL : L ≤ E := poolEdgeCount_ge_horizon G j hbudget hj.le
  have hL8 : 8 ≤ L := by
    dsimp [HorizonBudget] at hbudget
    dsimp [L]
    omega
  have hnum : (d : ℝ) * R ≤ (n : ℝ) * M := by
    have hd' : (d : ℝ) ≤ n := by exact_mod_cast hd
    have hR' : (R : ℝ) ≤ M := by exact_mod_cast hR
    gcongr
  have hEreal : (L : ℝ) ≤ E := by exact_mod_cast hEL
  have hscale : 2 * (n : ℝ) * M ≤ K * (L : ℝ) := hbudget.2.2.2
  have hK : 0 ≤ K := hbudget.2.2.1
  have hEpos : (0 : ℝ) < E := by
    have h8 : 8 ≤ E := poolEdgeCount_ge_eight G j hbudget hj.le
    have : (8 : ℝ) ≤ E := by exact_mod_cast h8
    linarith
  have hden : 0 < (E : ℝ) / 2 := by positivity
  apply (div_le_iff₀ hden).mpr
  have hKdiff : 0 ≤ K * ((E : ℝ) - L) :=
    mul_nonneg hK (sub_nonneg.mpr hEreal)
  dsimp [d, R, E] at *
  nlinarith

theorem horizon_conditional_mean_le {n M J : ℕ} {K : ℝ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (G : Graph n) (j : ℕ) (hG : G.card = M)
    (hbudget : HorizonBudget n M J K) (hj : j < J)
    (hpos : 0 < probM n M (fun H => revealTrace H j = revealTrace G j)) :
    conditionalQueryRawMoment M G j 1 ≤ K / 2 := by
  have hR := poolSuccessCount_le_poolEdgeCount G j hG
  have hd := queryCard_le_poolEdgeCount G j
  have hEeq : poolEdgeCount G j = capacity n -
      (revealTrace G j).yes.card - (revealTrace G j).no.card := by
    unfold poolEdgeCount answeredCount
    rw [Finset.card_union_of_disjoint (revealTrace_yes_no_disjoint G j)]
    omega
  have hR' : M - (revealTrace G j).yes.card ≤
      capacity n - (revealTrace G j).yes.card -
        (revealTrace G j).no.card := by
    rw [← hEeq]
    exact hR
  have hd' : (revealQuery (explore G j)).card ≤
      capacity n - (revealTrace G j).yes.card -
        (revealTrace G j).no.card := by
    rw [← hEeq]
    exact hd
  rw [conditionalQueryMean_all hfinite hM G j hpos hR' hd']
  have hhalf := horizon_halfMean_le G j hG hbudget hj
  unfold poolDensity at *
  have hE : (0 : ℝ) < poolEdgeCount G j := by
    have h8 := poolEdgeCount_ge_eight G j hbudget hj.le
    exact_mod_cast (by omega : 0 < poolEdgeCount G j)
  have hEne : (poolEdgeCount G j : ℝ) ≠ 0 := ne_of_gt hE
  field_simp at hhalf ⊢
  nlinarith

theorem horizon_conditional_variance_le {n M J : ℕ} {K : ℝ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (G : Graph n) (j : ℕ) (hG : G.card = M)
    (hbudget : HorizonBudget n M J K) (hj : j < J)
    (hpos : 0 < probM n M (fun H => revealTrace H j = revealTrace G j)) :
    0 ≤ conditionalQueryRawMoment M G j 2 -
      (conditionalQueryRawMoment M G j 1) ^ 2 ∧
    conditionalQueryRawMoment M G j 2 -
      (conditionalQueryRawMoment M G j 1) ^ 2 ≤ K / 2 := by
  let E := capacity n - (revealTrace G j).yes.card -
    (revealTrace G j).no.card
  let R := M - (revealTrace G j).yes.card
  let d := (revealQuery (explore G j)).card
  have hEeq : E = poolEdgeCount G j := by
    dsimp [E, poolEdgeCount, answeredCount]
    rw [Finset.card_union_of_disjoint (revealTrace_yes_no_disjoint G j)]
    omega
  have hR : R ≤ E := by
    rw [hEeq]
    exact poolSuccessCount_le_poolEdgeCount G j hG
  have hd : d ≤ E := by
    rw [hEeq]
    exact queryCard_le_poolEdgeCount G j
  have hE : 2 ≤ E := by
    rw [hEeq]
    have h8 := poolEdgeCount_ge_eight G j hbudget hj.le
    omega
  have hv := hypergeomVariance_nonneg_le_mean E R d hR hd hE
  have hfirst := horizon_conditional_mean_le hfinite hM G j hG hbudget hj hpos
  have hmean : conditionalQueryRawMoment M G j 1 = hypergeomMean E R d := by
    rw [conditionalQueryRawMoment_all hfinite hM G j 1 hpos,
      rawMoment_hypergeomMass_one_all E R d hR hd]
    rfl
  have hsecond : conditionalQueryRawMoment M G j 2 -
      (conditionalQueryRawMoment M G j 1) ^ 2 =
      hypergeomVariance E R d := by
    rw [conditionalQueryRawMoment_all hfinite hM G j 2 hpos,
      hmean]
    rfl
  rw [hsecond]
  exact ⟨hv.1, hv.2.trans (hmean ▸ hfirst)⟩

theorem horizon_conditional_fourth_le {n M J : ℕ} {K : ℝ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (G : Graph n) (j : ℕ) (hG : G.card = M)
    (hbudget : HorizonBudget n M J K) (hj : j < J)
    (hpos : 0 < probM n M (fun H => revealTrace H j = revealTrace G j)) :
    conditionalQueryRawMoment M G j 4 ≤
      K ^ 4 + 6 * K ^ 3 + 7 * K ^ 2 + K := by
  apply conditionalQueryRawMoment_four_le_constant hfinite hM G j hpos
    (poolSuccessCount_le_poolEdgeCount G j hG)
    (queryCard_le_poolEdgeCount G j)
    (poolEdgeCount_ge_eight G j hbudget hj.le) K
  exact horizon_halfMean_le G j hG hbudget hj

end

end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Horizon


/-!
# The critical window supplies one uniform horizon budget

The real power identities are kept separate from the finite probability
argument.  The budget is uniform in both the graph and the step.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_CriticalBudget

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Horizon
open Filter

noncomputable section

theorem n13_tendsto_atTop : Tendsto n13 atTop atTop := by
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))

theorem n23_mul_n13 (n : ℕ) (hn : 0 < n) :
    n23 n * n13 n = (n : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    n23 n * n13 n = (n : ℝ) ^ ((2 / 3 : ℝ) + (1 / 3 : ℝ)) := by
      exact (Real.rpow_add hn' _ _).symm
    _ = (n : ℝ) := by
      have hexp : (2 / 3 : ℝ) + (1 / 3 : ℝ) = 1 := by norm_num
      rw [hexp]
      simp

theorem n23_pos (n : ℕ) (hn : 0 < n) : 0 < n23 n := by
  unfold n23
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _

private theorem capacity_lower (n : ℕ) :
    n * (n - 1) ≤ 2 * capacity n + 1 := by
  rw [capacity, Nat.choose_two_right]
  omega

/-- A coarse deterministic numerical envelope; no probability enters here. -/
theorem horizonBudget_of_eighth {n M J : ℕ}
    (hn : 32 ≤ n) (hM : M ≤ n) (hJ : 8 * J ≤ n) :
    HorizonBudget n M J 8 := by
  have hJle : J ≤ n := by omega
  have hJn : 8 * (J * n) ≤ n * n := by
    nlinarith [Nat.mul_le_mul_right n hJ]
  have hMn : n * M ≤ n * n := Nat.mul_le_mul_left n hM
  have hN := capacity_lower n
  have hsubn : n - 1 + 1 = n := by omega
  have hnn : 32 * n ≤ n * n := Nat.mul_le_mul_right n hn
  have hbound : J * n + 8 ≤ capacity n := by
    nlinarith [hsubn]
  have hlast' : 2 * n * M + 8 * (J * n) ≤ 8 * capacity n := by
    nlinarith [hsubn]
  have hlast : 2 * n * M ≤ 8 * (capacity n - J * n) := by omega
  refine ⟨hJle, hbound, by norm_num, ?_⟩
  have hreal : (2 : ℝ) * n * M ≤
      8 * ((capacity n - J * n : ℕ) : ℝ) := by exact_mod_cast hlast
  simpa using! hreal

theorem eventually_eighth_horizon (T : ℝ) (hT : 0 ≤ T) :
    ∀ᶠ n : ℕ in atTop, 8 * ⌊T * n23 n⌋₊ ≤ n := by
  have hlarge := n13_tendsto_atTop.eventually_ge_atTop (8 * (T + 1))
  filter_upwards [hlarge, eventually_ge_atTop (1 : ℕ)] with n hn13 hn
  have hpow : n23 n * n13 n = n := n23_mul_n13 n hn
  have h23 : 0 ≤ n23 n := (n23_pos n hn).le
  have hfloor : (⌊T * n23 n⌋₊ : ℝ) ≤ T * n23 n :=
    Nat.floor_le (mul_nonneg hT h23)
  have hcast : (8 * ⌊T * n23 n⌋₊ : ℝ) ≤ n := by
    have hmul : n23 n * (8 * (T + 1)) ≤ n23 n * n13 n :=
      mul_le_mul_of_nonneg_left hn13 h23
    rw [hpow] at hmul
    nlinarith
  exact_mod_cast hcast

theorem eventually_edges_le_order (M : NatSeq) (lam : ℝ)
    (hcritical : criticalWindow M lam) :
    ∀ᶠ n : ℕ in atTop, M n ≤ n := by
  let C : ℝ := |lam| + 2
  have hClam : lam < C := by
    dsimp [C]
    have := le_abs_self lam
    linarith
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hratio := hcritical.2.eventually_le_const hClam
  have hlarge := n13_tendsto_atTop.eventually_ge_atTop C
  filter_upwards [hratio, hlarge, eventually_ge_atTop (1 : ℕ)] with n hx h13 hn
  have hpow : n23 n * n13 n = n := n23_mul_n13 n hn
  have h23 := n23_pos n hn
  have hx' : 2 * (M n : ℝ) - n ≤ C * n23 n := by
    have hr := (div_le_iff₀ h23).mp hx
    dsimp [C] at hr ⊢
    nlinarith
  have hCn : C * n23 n ≤ n := by
    have hh := mul_le_mul_of_nonneg_left h13 h23.le
    nlinarith [hpow]
  have hreal : (M n : ℝ) ≤ n := by nlinarith
  exact_mod_cast hreal

/-- On every fixed critical-window horizon, K=8 works for all realized graphs. -/
theorem eventually_horizonBudget (M : NatSeq) (lam T : ℝ)
    (hcritical : criticalWindow M lam) (hT : 0 ≤ T) :
    ∀ᶠ n : ℕ in atTop,
      HorizonBudget n (M n) ⌊T * n23 n⌋₊ 8 := by
  filter_upwards [eventually_edges_le_order M lam hcritical,
    eventually_eighth_horizon T hT, eventually_ge_atTop (32 : ℕ)]
    with n hM hJ hn
  exact horizonBudget_of_eighth hn hM hJ

end

end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_CriticalBudget
