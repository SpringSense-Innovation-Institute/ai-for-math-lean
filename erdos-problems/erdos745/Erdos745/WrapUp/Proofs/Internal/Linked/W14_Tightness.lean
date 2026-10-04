module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W14_Queue
public import Erdos745.WrapUp.Proofs.Internal.Linked.W14_Horizon
public import Erdos745.WrapUp.Proofs.Internal.Linked.W14_Base
public import Erdos745.WrapUp.Proofs.Internal.Linked.W14_Drift
public import Mathlib.MeasureTheory.Measure.TightNormed
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.MetricSpace.ProperSpace.Real

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


/-!
# Fourth moments of the centered BFS exploration

All expectations below are finite averages on the *same* fixed-edge support.
The fourth-moment recurrence conditions on the actual reveal-trace fibers.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FourthMoment

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteAtoms
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteMaximal
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_QueueControl
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_CriticalBudget
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Interpolation
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Reveal
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Horizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteHorizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_PoolMartingale
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Characteristic
open Filter
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false

private def rawFourthBound : ℝ := (8 : ℝ) ^ 4 + 6 * 8 ^ 3 + 7 * 8 ^ 2 + 8
private def centeredFourthBound : ℝ := 8 * (rawFourthBound + 4 ^ 4)
private def centeredThirdBound : ℝ := 1 + centeredFourthBound
private def intervalFourthBound : ℝ := 100 + 8 * centeredThirdBound + centeredFourthBound

private lemma bounds_nonneg :
    0 ≤ centeredFourthBound ∧ 0 ≤ centeredThirdBound ∧
      0 ≤ intervalFourthBound := by
  norm_num [centeredFourthBound, centeredThirdBound,
    intervalFourthBound, rawFourthBound]

private lemma centered_fourth_point (x m : ℝ) (hx : 0 ≤ x) (hm : 0 ≤ m) :
    |x - m| ^ 4 ≤ 8 * (x ^ 4 + m ^ 4) := by
  have htri : |x - m| ≤ x + m := by
    calc
      |x - m| ≤ |x| + |m| := abs_sub x m
      _ = x + m := by rw [abs_of_nonneg hx, abs_of_nonneg hm]
  have hpow := pow_le_pow_left₀ (abs_nonneg _) htri 4
  simpa only [show 2 ^ (4 - 1) = (8 : ℝ) by norm_num] using!
    hpow.trans (add_pow_le hx hm 4)

private lemma cube_le_fourth (x : ℝ) : |x| ^ 3 ≤ 1 + x ^ 4 := by
  by_cases h : |x| ≤ 1
  · have hh : |x| ^ 3 ≤ 1 := pow_le_one₀ (abs_nonneg _) h
    nlinarith [sq_nonneg (x ^ 2)]
  · have h1 : 1 ≤ |x| := le_of_not_ge h
    have hh : 0 ≤ |x| ^ 3 * (|x| - 1) :=
      mul_nonneg (pow_nonneg (abs_nonneg _) 3) (sub_nonneg.mpr h1)
    nlinarith [sq_abs x]

/- The third and fourth conditional moments are bounded on every positive
history atom. The trace-measurable mean is kept inside the fiber. -/
private theorem centered_atom_fourth_le {n M J : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (hbudget : HorizonBudget n M J 8) (G : Graph n) (j : ℕ)
    (hG : G.card = M) (hj : j < J) :
    ∑ H ∈ historyAtom M G j,
      (centeredPartial M H (j + 1) - centeredPartial M H j) ^ 4 ≤
        centeredFourthBound * ((historyAtom M G j).card : ℝ) := by
  let a := historyAtom M G j
  let m := queryMean M G j
  have hm0 : 0 ≤ m := by unfold m queryMean poolDensity; positivity
  have hm4 : m ≤ 4 := by
    have h := (historyAtom_horizon_moments hfinite hM G j hG hbudget hj).1
    have hmean : historyAverage M G j (fun H => (queryCount H j : ℝ)) = m := by
      have hz := historyAverage_centeredQuery_zero hfinite hM G j hG
      have hc := historyAverage_const G j hG m
      unfold historyAverage at hz hc ⊢
      have heq : ∑ H ∈ a, ((queryCount H j : ℝ) - m) =
          (∑ H ∈ a, (queryCount H j : ℝ)) - (a.card : ℝ) * m := by
        rw [Finset.sum_sub_distrib]
        simp
      change (∑ H ∈ a, ((queryCount H j : ℝ) - m)) / a.card = 0 at hz
      have ha : (a.card : ℝ) ≠ 0 := by
        exact_mod_cast Finset.card_ne_zero.mpr (historyAtom_nonempty G j hG)
      rw [heq] at hz
      have hz' := (div_eq_zero_iff).mp hz |>.resolve_right ha
      change (∑ H ∈ a, (queryCount H j : ℝ)) / a.card = m
      apply (div_eq_iff ha).mpr
      linarith
    rw [hmean] at h
    exact h
  have hraw := (historyAtom_horizon_moments hfinite hM G j hG hbudget hj).2.2.2
  have ha : (0 : ℝ) < a.card := by
    exact_mod_cast Finset.card_pos.mpr (historyAtom_nonempty G j hG)
  have hraw' : (∑ H ∈ a, (queryCount H j : ℝ) ^ 4) ≤
      rawFourthBound * (a.card : ℝ) := by
    apply (div_le_iff₀ ha).mp
    simpa [a, rawFourthBound, historyAverage] using! hraw
  have hpoint : ∀ H ∈ a,
      (centeredPartial M H (j + 1) - centeredPartial M H j) ^ 4 ≤
        8 * ((queryCount H j : ℝ) ^ 4 + 4 ^ 4) := by
    intro H hH
    have ht := (Finset.mem_filter.mp hH).2
    have hmean := queryMean_eq_of_trace (M := M) G H j ht
    have hD := centeredPartial_increment (M := M) H j
    dsimp [increment] at hD
    rw [hD, hmean]
    have hq : (0 : ℝ) ≤ queryCount H j := Nat.cast_nonneg _
    have hp := centered_fourth_point (queryCount H j : ℝ) m hq hm0
    have hp4 : m ^ 4 ≤ (4 : ℝ) ^ 4 := by gcongr
    have hpow : |(queryCount H j : ℝ) - m| ^ 4 =
        ((queryCount H j : ℝ) - m) ^ 4 := by
      calc
        _ = (|(queryCount H j : ℝ) - m| ^ 2) ^ 2 := by ring
        _ = (((queryCount H j : ℝ) - m) ^ 2) ^ 2 := by rw [sq_abs]
        _ = _ := by ring
    rw [hpow] at hp
    nlinarith [hp, hp4]
  have hs := Finset.sum_le_sum hpoint
  have hcalc : (∑ H ∈ a, 8 * ((queryCount H j : ℝ) ^ 4 + 4 ^ 4)) =
      8 * ((∑ H ∈ a, (queryCount H j : ℝ) ^ 4) +
        (a.card : ℝ) * 4 ^ 4) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
  rw [hcalc] at hs
  dsimp [centeredFourthBound]
  nlinarith [hraw']

private theorem centered_atom_third_le {n M J : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (hbudget : HorizonBudget n M J 8) (G : Graph n) (j : ℕ)
    (hG : G.card = M) (hj : j < J) :
    ∑ H ∈ historyAtom M G j,
      |centeredPartial M H (j + 1) - centeredPartial M H j| ^ 3 ≤
        centeredThirdBound * ((historyAtom M G j).card : ℝ) := by
  have hfour := centered_atom_fourth_le hfinite hM hbudget G j hG hj
  have hpoint : ∀ H ∈ historyAtom M G j,
      |centeredPartial M H (j + 1) - centeredPartial M H j| ^ 3 ≤
        1 + (centeredPartial M H (j + 1) - centeredPartial M H j) ^ 4 := by
    intro H hH
    exact cube_le_fourth _
  have hs := Finset.sum_le_sum hpoint
  have hcalc : (∑ H ∈ historyAtom M G j,
      ((1 : ℝ) + (centeredPartial M H (j + 1) - centeredPartial M H j) ^ 4)) =
      ((historyAtom M G j).card : ℝ) +
        (∑ H ∈ historyAtom M G j,
          (centeredPartial M H (j + 1) - centeredPartial M H j) ^ 4) := by
    rw [Finset.sum_add_distrib]
    simp
  rw [hcalc] at hs
  dsimp [centeredThirdBound]
  linarith

/- Regroup a finite sum by the observed trace. A nonnegative adapted
multiplier can be moved outside each conditional moment inequality. -/
private theorem fiber_weighted_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (h : α → β) (D F : α → ℝ) (c : ℝ)
    (hF0 : ∀ x ∈ s, 0 ≤ F x)
    (hF : ∀ x ∈ s, ∀ y ∈ s, h y = h x → F y = F x)
    (hD : ∀ x ∈ s,
      ∑ y ∈ s with h y = h x, D y ≤
        c * (((s.filter (fun y => h y = h x)).card : ℝ))) :
    ∑ x ∈ s, F x * D x ≤ c * ∑ x ∈ s, F x := by
  let u := s.image h
  have hmaps : ∀ x ∈ s, h x ∈ u := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hs : (∑ v ∈ u, ∑ y ∈ s with h y = v, F y * D y) ≤
      ∑ v ∈ u, ∑ y ∈ s with h y = v, c * F y := by
    apply Finset.sum_le_sum
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    have hf : (∑ y ∈ s with h y = h x, F y * D y) =
        F x * ∑ y ∈ s with h y = h x, D y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      rw [hF x hx y (Finset.mem_filter.mp hy).1
        (Finset.mem_filter.mp hy).2]
    have hr : (∑ y ∈ s with h y = h x, c * F y) =
        F x * (c * ((s.filter (fun y => h y = h x)).card : ℝ)) := by
      have hc : ∀ y ∈ s.filter (fun y => h y = h x), F y = F x := by
        intro y hy
        exact hF x hx y (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hy).2
      calc
        (∑ y ∈ s with h y = h x, c * F y) =
            ∑ _y ∈ s.filter (fun y => h y = h x), c * F x := by
              apply Finset.sum_congr rfl
              intro y hy
              rw [hc y hy]
        _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
    rw [hf, hr]
    exact mul_le_mul_of_nonneg_left (hD x hx) (hF0 x hx)
  calc
    (∑ x ∈ s, F x * D x) =
        ∑ v ∈ u, ∑ y ∈ s with h y = v, F y * D y :=
          (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ v ∈ u, ∑ y ∈ s with h y = v, c * F y := hs
    _ = c * ∑ y ∈ s, F y := by
      rw [Finset.sum_fiberwise_of_maps_to hmaps, ← Finset.mul_sum]

private theorem fiber_cross_zero {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (h : α → β) (D F : α → ℝ)
    (hD : ∀ x ∈ s, ∑ y ∈ s with h y = h x, D y = 0)
    (hF : ∀ x ∈ s, ∀ y ∈ s, h y = h x → F y = F x) :
    ∑ x ∈ s, F x * D x = 0 := by
  let u := s.image h
  have hmaps : ∀ x ∈ s, h x ∈ u := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun x => F x * D x)]
  apply Finset.sum_eq_zero
  intro v hv
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
  calc
    (∑ y ∈ s with h y = h x, F y * D y) =
        F x * (∑ y ∈ s with h y = h x, D y) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y hy
          rw [hF x hx y (Finset.mem_filter.mp hy).1
            (Finset.mem_filter.mp hy).2]
    _ = 0 := by rw [hD x hx]; ring

/-! ## The interval recurrence on the actual fixed-edge law -/

private def intervalSum {n : ℕ} (M : ℕ) (i j : ℕ) (G : Graph n) : ℝ :=
  centeredPartial M G j - centeredPartial M G i

private lemma intervalSum_self {n M : ℕ} (G : Graph n) (i : ℕ) :
    intervalSum M i i G = 0 := by simp [intervalSum]

private lemma intervalSum_succ {n M : ℕ} (G : Graph n) (i j : ℕ) :
    intervalSum M i (j + 1) G =
      intervalSum M i j G +
        (centeredPartial M G (j + 1) - centeredPartial M G j) := by
  unfold intervalSum
  ring

private lemma intervalSum_eq_of_trace {n M : ℕ} (G H : Graph n)
    {i j : ℕ} (hij : i ≤ j)
    (h : revealTrace H j = revealTrace G j) :
    intervalSum M i j H = intervalSum M i j G := by
  unfold intervalSum
  rw [centeredPartial_eq_of_trace G H j h,
    centeredPartial_eq_of_trace G H i (trace_eq_of_later G H hij h)]

private theorem centered_interval_moment_sums {n M J : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (hbudget : HorizonBudget n M J 8) (i j : ℕ)
    (hij : i ≤ j) (hj : j ≤ J) :
    (∑ G ∈ fixedGraphs n M, intervalSum M i j G ^ 2) ≤
        4 * ((j - i : ℕ) : ℝ) * ((fixedGraphs n M).card : ℝ) ∧
    (∑ G ∈ fixedGraphs n M, intervalSum M i j G ^ 4) ≤
        intervalFourthBound * ((j - i : ℕ) : ℝ) ^ 2 *
          ((fixedGraphs n M).card : ℝ) := by
  let s := fixedGraphs n M
  let X : ℕ → Graph n → ℝ := fun k G => intervalSum M i k G
  let D : ℕ → Graph n → ℝ := fun k G =>
    centeredPartial M G (k + 1) - centeredPartial M G k
  have hcard : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
  have hzero (k : ℕ) (hk : k < J) (G : Graph n) (hG : G ∈ s) :
      ∑ H ∈ s with revealTrace H k = revealTrace G k, D k H = 0 := by
    have hc : G.card = M := (Finset.mem_filter.mp hG).2
    simpa only [s, D, historyAtom, increment] using!
      centered_atom_zero hfinite hM G k hc
  have hsquare (k : ℕ) (hk : k < J) (G : Graph n) (hG : G ∈ s) :
      ∑ H ∈ s with revealTrace H k = revealTrace G k, (D k H) ^ 2 ≤
        4 * (((s.filter (fun H => revealTrace H k = revealTrace G k)).card : ℝ)) := by
    have hc : G.card = M := (Finset.mem_filter.mp hG).2
    simpa only [s, D, historyAtom, increment] using!
      centered_atom_square hfinite hM G k hc hbudget hk
  have hthird (k : ℕ) (hk : k < J) (G : Graph n) (hG : G ∈ s) :
      ∑ H ∈ s with revealTrace H k = revealTrace G k, |D k H| ^ 3 ≤
        centeredThirdBound *
          (((s.filter (fun H => revealTrace H k = revealTrace G k)).card : ℝ)) := by
    have hc : G.card = M := (Finset.mem_filter.mp hG).2
    simpa only [s, D, historyAtom] using!
      centered_atom_third_le hfinite hM hbudget G k hc hk
  have hfourth (k : ℕ) (hk : k < J) (G : Graph n) (hG : G ∈ s) :
      ∑ H ∈ s with revealTrace H k = revealTrace G k, (D k H) ^ 4 ≤
        centeredFourthBound *
          (((s.filter (fun H => revealTrace H k = revealTrace G k)).card : ℝ)) := by
    have hc : G.card = M := (Finset.mem_filter.mp hG).2
    simpa only [s, D, historyAtom] using!
      centered_atom_fourth_le hfinite hM hbudget G k hc hk
  have hadapt (k : ℕ) (hik : i ≤ k) (G H : Graph n)
      (hG : G ∈ s) (hH : H ∈ s)
      (heq : revealTrace H k = revealTrace G k) : X k H = X k G := by
    exact intervalSum_eq_of_trace G H hik heq
  have h2step (k : ℕ) (hik : i ≤ k) (hk : k < J) :
      (∑ G ∈ s, X (k + 1) G ^ 2) =
        (∑ G ∈ s, X k G ^ 2) + ∑ G ∈ s, (D k G) ^ 2 := by
    have hcross : (∑ G ∈ s, (2 * X k G) * D k G) = 0 := by
      apply fiber_cross_zero s (fun G => revealTrace G k) (D k)
        (fun G => 2 * X k G) (hzero k hk)
      intro G hG H hH heq
      rw [hadapt k hik G H hG hH heq]
    calc
      (∑ G ∈ s, X (k + 1) G ^ 2) =
          ∑ G ∈ s, (X k G ^ 2 + (D k G) ^ 2 +
            (2 * X k G) * D k G) := by
        apply Finset.sum_congr rfl
        intro G hG
        dsimp [X, D]
        rw [intervalSum_succ]
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hcross]
        ring
  have h2bound (k : ℕ) (hk : k < J) :
      (∑ G ∈ s, (D k G) ^ 2) ≤ 4 * (s.card : ℝ) := by
    have hh := fiber_weighted_le s (fun G => revealTrace G k)
      (fun G => (D k G) ^ 2) (fun _ => 1) 4
      (by intro G hG; norm_num)
      (by intro G hG H hH heq; rfl) (hsquare k hk)
    simpa using! hh
  have h4step (k : ℕ) (hik : i ≤ k) (hk : k < J) :
      (∑ G ∈ s, X (k + 1) G ^ 4) =
        (∑ G ∈ s, X k G ^ 4) +
          6 * (∑ G ∈ s, X k G ^ 2 * (D k G) ^ 2) +
          4 * (∑ G ∈ s, X k G * (D k G) ^ 3) +
          (∑ G ∈ s, (D k G) ^ 4) := by
    have hcross : (∑ G ∈ s, (4 * X k G ^ 3) * D k G) = 0 := by
      apply fiber_cross_zero s (fun G => revealTrace G k) (D k)
        (fun G => 4 * X k G ^ 3) (hzero k hk)
      intro G hG H hH heq
      rw [hadapt k hik G H hG hH heq]
    calc
      (∑ G ∈ s, X (k + 1) G ^ 4) =
          ∑ G ∈ s, (X k G ^ 4 +
            (4 * X k G ^ 3) * D k G +
            6 * (X k G ^ 2 * (D k G) ^ 2) +
            4 * (X k G * (D k G) ^ 3) +
            (D k G) ^ 4) := by
        apply Finset.sum_congr rfl
        intro G hG
        dsimp [X, D]
        rw [intervalSum_succ]
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [hcross]
        ring
  have h2weighted (k : ℕ) (hik : i ≤ k) (hk : k < J) :
      (∑ G ∈ s, X k G ^ 2 * (D k G) ^ 2) ≤
        4 * ∑ G ∈ s, X k G ^ 2 := by
    apply fiber_weighted_le s (fun G => revealTrace G k)
      (fun G => (D k G) ^ 2) (fun G => X k G ^ 2) 4
      (by intro G hG; positivity)
      (by
        intro G hG H hH heq
        change X k H ^ 2 = X k G ^ 2
        rw [hadapt k hik G H hG hH heq])
      (hsquare k hk)
  have h3weighted (k : ℕ) (hik : i ≤ k) (hk : k < J) :
      (∑ G ∈ s, |X k G| * |D k G| ^ 3) ≤
        centeredThirdBound * ∑ G ∈ s, |X k G| := by
    apply fiber_weighted_le s (fun G => revealTrace G k)
      (fun G => |D k G| ^ 3) (fun G => |X k G|) centeredThirdBound
      (by intro G hG; positivity)
      (by
        intro G hG H hH heq
        change |X k H| = |X k G|
        rw [hadapt k hik G H hG hH heq])
      (hthird k hk)
  have h4bound (k : ℕ) (hk : k < J) :
      (∑ G ∈ s, (D k G) ^ 4) ≤ centeredFourthBound * (s.card : ℝ) := by
    have hh := fiber_weighted_le s (fun G => revealTrace G k)
      (fun G => (D k G) ^ 4) (fun _ => 1) centeredFourthBound
      (by intro G hG; norm_num)
      (by intro G hG H hH heq; rfl) (hfourth k hk)
    simpa using! hh
  have hall : ∀ r : ℕ, i + r ≤ J →
      (∑ G ∈ s, X (i + r) G ^ 2) ≤
          4 * (r : ℝ) * (s.card : ℝ) ∧
      (∑ G ∈ s, X (i + r) G ^ 4) ≤
          intervalFourthBound * (r : ℝ) ^ 2 * (s.card : ℝ) := by
    intro r
    induction r with
    | zero =>
        intro hir
        simp [X, intervalSum_self]
    | succ r ih =>
        intro hir
        have hkr : i + r < J := by omega
        have hki : i ≤ i + r := by omega
        obtain ⟨h2old, h4old⟩ := ih (by omega)
        have h2new := h2step (i + r) hki hkr
        have h4new := h4step (i + r) hki hkr
        have hD2 := h2bound (i + r) hkr
        have hD4 := h4bound (i + r) hkr
        have hS2D2 := h2weighted (i + r) hki hkr
        have hSD3 := h3weighted (i + r) hki hkr
        have hSD3' : (∑ G ∈ s, X (i + r) G * (D (i + r) G) ^ 3) ≤
            centeredThirdBound * ∑ G ∈ s, |X (i + r) G| := by
          calc
            _ ≤ ∑ G ∈ s, |X (i + r) G| * |D (i + r) G| ^ 3 := by
              apply Finset.sum_le_sum
              intro G hG
              calc
                _ ≤ |X (i + r) G * (D (i + r) G) ^ 3| := le_abs_self _
                _ = _ := by rw [abs_mul, abs_pow]
            _ ≤ _ := hSD3
        have hSabs : (∑ G ∈ s, |X (i + r) G|) ≤
            ((∑ G ∈ s, X (i + r) G ^ 2) + (s.card : ℝ)) / 2 := by
          have hp : ∀ G ∈ s, |X (i + r) G| ≤
              (X (i + r) G ^ 2 + 1) / 2 := by
            intro G hG
            nlinarith [sq_nonneg (|X (i + r) G| - 1), sq_abs (X (i + r) G)]
          have hs := Finset.sum_le_sum hp
          have heq : (∑ G ∈ s, (X (i + r) G ^ 2 + 1) / 2) =
              ((∑ G ∈ s, X (i + r) G ^ 2) + (s.card : ℝ)) / 2 := by
            rw [← Finset.sum_div, Finset.sum_add_distrib]
            simp
          rw [heq] at hs
          exact hs
        have hnonneg : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
        have hC3 : 0 ≤ centeredThirdBound := bounds_nonneg.2.1
        have hC4 : 0 ≤ centeredFourthBound := bounds_nonneg.1
        have hC : 0 ≤ intervalFourthBound := bounds_nonneg.2.2
        have hsq : (∑ G ∈ s, X (i + r) G ^ 2) ≥ 0 :=
          Finset.sum_nonneg (fun G hG => sq_nonneg _)
        have h2goal : (∑ G ∈ s, X (i + (r + 1)) G ^ 2) ≤
            4 * ((r + 1 : ℕ) : ℝ) * (s.card : ℝ) := by
          convert h2new ▸ (add_le_add h2old hD2) using 1 <;> push_cast <;> ring
        refine ⟨h2goal, ?_⟩
        have hthird1 := mul_le_mul_of_nonneg_left hSabs hC3
        have hsecond1 := mul_le_mul_of_nonneg_left hS2D2 (by norm_num : (0 : ℝ) ≤ 6)
        have hthird2 := mul_le_mul_of_nonneg_left hSD3' (by norm_num : (0 : ℝ) ≤ 4)
        have hprod : (0 : ℝ) ≤ (s.card : ℝ) := hcard
        have hrprod : 0 ≤ (r : ℝ) * (s.card : ℝ) :=
          mul_nonneg hnonneg hprod
        have h4target :
          (∑ G ∈ s, X ((i + r) + 1) G ^ 4) ≤
            intervalFourthBound * ((r + 1 : ℕ) : ℝ) ^ 2 * (s.card : ℝ) := by
          norm_num [intervalFourthBound, centeredThirdBound,
            centeredFourthBound, rawFourthBound] at h4old hD4 hthird1 hthird2 ⊢
          push_cast at h4new ⊢
          nlinarith [h4new, h4old, hsecond1, hthird1, hthird2,
            h2old, hD4, hrprod]
        simpa only [Nat.add_assoc] using! h4target
  have hresult := hall (j - i) (by omega)
  have heq : i + (j - i) = j := by omega
  simpa only [s, X, heq] using! hresult

/-- Fourth moment of a centered BFS martingale interval, with the actual
fixed-edge law and no independent-edge replacement. -/
theorem centered_interval_fourth {n M J : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (hbudget : HorizonBudget n M J 8) (i j : ℕ)
    (hij : i ≤ j) (hj : j ≤ J) :
    expectM n M (fun G => |centeredPartial M G j - centeredPartial M G i| ^ 4) ≤
      intervalFourthBound * ((j - i : ℕ) : ℝ) ^ 2 := by
  have hcard : (0 : ℝ) < ((fixedGraphs n M).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (fixedGraphs_nonempty hM)
  have hsum := (centered_interval_moment_sums hfinite hM hbudget i j hij hj).2
  have heq (G : Graph n) :
      |centeredPartial M G j - centeredPartial M G i| ^ 4 =
        intervalSum M i j G ^ 4 := by
    dsimp [intervalSum]
    calc
      _ = (|centeredPartial M G j - centeredPartial M G i| ^ 2) ^ 2 := by ring
      _ = ((centeredPartial M G j - centeredPartial M G i) ^ 2) ^ 2 := by rw [sq_abs]
      _ = _ := by ring
  unfold expectM
  simp_rw [heq]
  exact (div_le_iff₀ hcard).mpr (by nlinarith [hsum])

/-! ## Both fractional mesh cells -/

def centeredPolygon {n : ℕ} (M : ℕ) (G : Graph n) (t : NNReal) : ℝ :=
  linearInterpolation (centeredPartial M G) (t * explorationScale n) / n13 n

private lemma centeredPolygon_apply {n M : ℕ} (G : Graph n) (t : NNReal) :
    centeredPolygon M G t =
      (centeredPartial M G (meshIndex n (t : ℝ)) +
        ((t : ℝ) * n23 n - (meshIndex n (t : ℝ) : ℝ)) *
          (centeredPartial M G (meshIndex n (t : ℝ) + 1) -
            centeredPartial M G (meshIndex n (t : ℝ)))) / n13 n := by
  unfold centeredPolygon linearInterpolation meshIndex
  simp only [NNReal.coe_mul, explorationScale_coe]
  ring

private theorem expectM_mono {n M : ℕ} (f g : Graph n → ℝ)
    (h : ∀ G ∈ fixedGraphs n M, f G ≤ g G) :
    expectM n M f ≤ expectM n M g := by
  unfold expectM
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg _)

private theorem expectM_add {n M : ℕ} (f g : Graph n → ℝ) :
    expectM n M (fun G => f G + g G) =
      expectM n M f + expectM n M g := by
  unfold expectM
  rw [Finset.sum_add_distrib, add_div]

private theorem expectM_const_mul {n M : ℕ} (c : ℝ) (f : Graph n → ℝ) :
    expectM n M (fun G => c * f G) = c * expectM n M f := by
  unfold expectM
  rw [← Finset.mul_sum]
  ring

private theorem scaled_interval_fourth {n M J : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (hbudget : HorizonBudget n M J 8) (hn : 0 < n)
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ J) (c Δ : ℝ)
    (hfactor : c ^ 4 / n13 n ^ 4 * ((j - i : ℕ) : ℝ) ^ 2 ≤ Δ ^ 2) :
    expectM n M (fun G =>
      (c * (centeredPartial M G j - centeredPartial M G i) / n13 n) ^ 4) ≤
      intervalFourthBound * Δ ^ 2 := by
  have hb : 0 < n13 n := by
    unfold n13
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hmain := centered_interval_fourth hfinite hM hbudget i j hij hj
  have hcoeff : 0 ≤ c ^ 4 / n13 n ^ 4 := by positivity
  have hC : 0 ≤ intervalFourthBound := bounds_nonneg.2.2
  have hpoint (G : Graph n) :
      (c * (centeredPartial M G j - centeredPartial M G i) / n13 n) ^ 4 =
        (c ^ 4 / n13 n ^ 4) *
          |centeredPartial M G j - centeredPartial M G i| ^ 4 := by
    have habs : |centeredPartial M G j - centeredPartial M G i| ^ 4 =
        (centeredPartial M G j - centeredPartial M G i) ^ 4 := by
      calc
        _ = (|centeredPartial M G j - centeredPartial M G i| ^ 2) ^ 2 := by ring
        _ = ((centeredPartial M G j - centeredPartial M G i) ^ 2) ^ 2 := by
          rw [sq_abs]
        _ = _ := by ring
    rw [habs]
    ring
  simp_rw [hpoint, expectM_const_mul]
  calc
    _ ≤ (c ^ 4 / n13 n ^ 4) *
        (intervalFourthBound * ((j - i : ℕ) : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hmain hcoeff
    _ ≤ intervalFourthBound * Δ ^ 2 := by
      have hh := mul_le_mul_of_nonneg_left hfactor hC
      nlinarith

private lemma partial_coeff_bound (b c Δ : ℝ) (hb : 0 < b)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hcd : c ≤ b ^ 2 * Δ) :
    c ^ 4 / b ^ 4 ≤ Δ ^ 2 := by
  have hcsq : c ^ 2 ≤ 1 := by nlinarith [sq_nonneg (c - 1)]
  have hΔ : 0 ≤ b ^ 2 * Δ := le_trans hc0 hcd
  have hcsq2 : c ^ 2 ≤ (b ^ 2 * Δ) ^ 2 := by gcongr
  have h4 : c ^ 4 ≤ b ^ 4 * Δ ^ 2 := by
    calc
      c ^ 4 = c ^ 2 * c ^ 2 := by ring
      _ ≤ 1 * c ^ 2 := mul_le_mul_of_nonneg_right hcsq (sq_nonneg c)
      _ ≤ (b ^ 2 * Δ) ^ 2 := by simpa using! hcsq2
      _ = b ^ 4 * Δ ^ 2 := by ring
  exact (div_le_iff₀ (pow_pos hb 4)).mpr (by nlinarith)

private lemma interval_coeff_bound (b k Δ : ℝ) (hb : 0 < b)
    (hk : 0 ≤ k) (hkd : k ≤ b ^ 2 * Δ) :
    (1 : ℝ) ^ 4 / b ^ 4 * k ^ 2 ≤ Δ ^ 2 := by
  have hΔ : 0 ≤ b ^ 2 * Δ := le_trans hk hkd
  have hsq : k ^ 2 ≤ (b ^ 2 * Δ) ^ 2 := by gcongr
  have hb4 : 0 < b ^ 4 := pow_pos hb _
  have hh : k ^ 2 / b ^ 4 ≤ Δ ^ 2 :=
    (div_le_iff₀ hb4).mpr (by nlinarith [hsq])
  convert hh using 1 <;> ring

private lemma three_sum_fourth (x y z : ℝ) :
    (x + y + z) ^ 4 ≤ 64 * (x ^ 4 + y ^ 4 + z ^ 4) := by
  have hxy : |x + y| ≤ |x| + |y| := abs_add_le x y
  have hxyz : |x + y + z| ≤ |x + y| + |z| := abs_add_le (x + y) z
  have hp1 := pow_le_pow_left₀ (abs_nonneg _) hxy 4
  have hp2 := pow_le_pow_left₀ (abs_nonneg _) hxyz 4
  have hp3 := add_pow_le (abs_nonneg x) (abs_nonneg y) 4
  have hp4 := add_pow_le (add_nonneg (abs_nonneg x) (abs_nonneg y))
    (abs_nonneg z) 4
  have hadd : |x + y| + |z| ≤ (|x| + |y|) + |z| := by linarith [hxy]
  have hp5 := pow_le_pow_left₀ (add_nonneg (abs_nonneg (x + y))
    (abs_nonneg z)) hadd 4
  have hfour (w : ℝ) : |w| ^ 4 = w ^ 4 := by
    calc
      _ = (|w| ^ 2) ^ 2 := by ring
      _ = (w ^ 2) ^ 2 := by rw [sq_abs]
      _ = _ := by ring
  calc
    (x + y + z) ^ 4 = |x + y + z| ^ 4 := (hfour _).symm
    _ ≤ (|x + y| + |z|) ^ 4 := hp2
    _ ≤ (|x| + |y| + |z|) ^ 4 := hp5
    _ ≤ 8 * ((|x| + |y|) ^ 4 + |z| ^ 4) := by
      norm_num at hp4 ⊢
      exact hp4
    _ ≤ 8 * (8 * (|x| ^ 4 + |y| ^ 4) + |z| ^ 4) := by
      gcongr
      norm_num at hp3 ⊢
      exact hp3
    _ ≤ 64 * (|x| ^ 4 + |y| ^ 4 + |z| ^ 4) := by
      nlinarith [pow_nonneg (abs_nonneg z) 4]
    _ = _ := by rw [hfour x, hfour y, hfour z]

/-- The interpolation of the centered BFS martingale has the Brownian fourth
increment scale. Both end cells, including the adjacent-cell case with no
interior mesh points, are included. -/
theorem finite_centeredPolygon_fourth {n M J : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (hbudget : HorizonBudget n M J 8) (hn : 0 < n)
    (s t : NNReal) (hst : s ≤ t)
    (hJ : meshIndex n (t : ℝ) + 1 ≤ J) :
    expectM n M (fun G => |centeredPolygon M G t - centeredPolygon M G s| ^ 4) ≤
      (192 * intervalFourthBound) * ((t : ℝ) - (s : ℝ)) ^ 2 := by
  let a := n23 n
  let b := n13 n
  let u := (s : ℝ) * a
  let v := (t : ℝ) * a
  let p := meshIndex n (s : ℝ)
  let q := meshIndex n (t : ℝ)
  let Δ := (t : ℝ) - (s : ℝ)
  have hb : 0 < b := by
    dsimp [b, n13]
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have ha : 0 < a := n23_pos n hn
  have hab : a = b ^ 2 := n23_eq_n13_square n hn
  have hΔ : 0 ≤ Δ := by
    dsimp [Δ]
    exact sub_nonneg.mpr (by exact_mod_cast hst)
  have huv : v - u = b ^ 2 * Δ := by dsimp [v, u, Δ]; rw [← hab]; ring
  have hu : (p : ℝ) ≤ u ∧ u < (p : ℝ) + 1 := by
    dsimp [p, u, a, meshIndex]
    exact ⟨Nat.floor_le (by positivity), Nat.lt_floor_add_one _⟩
  have hv : (q : ℝ) ≤ v ∧ v < (q : ℝ) + 1 := by
    dsimp [q, v, a, meshIndex]
    exact ⟨Nat.floor_le (by positivity), Nat.lt_floor_add_one _⟩
  have hpq : p ≤ q := by
    dsimp [p, q, meshIndex]
    exact Nat.floor_mono (mul_le_mul_of_nonneg_right
      (by exact_mod_cast hst) ha.le)
  have hqJ : q + 1 ≤ J := hJ
  have hpJ : p + 1 ≤ J := by omega
  have hpoly (G : Graph n) (x : NNReal) :
      centeredPolygon M G x =
        (centeredPartial M G (meshIndex n (x : ℝ)) +
          ((x : ℝ) * a - (meshIndex n (x : ℝ) : ℝ)) *
            (centeredPartial M G (meshIndex n (x : ℝ) + 1) -
              centeredPartial M G (meshIndex n (x : ℝ)))) / b := by
    simpa only [a, b] using! centeredPolygon_apply G x
  by_cases heq : p = q
  · have hc0 : 0 ≤ v - u := by rw [huv]; positivity
    have hc1 : v - u ≤ 1 := by
      have hpqreal : (p : ℝ) = q := by exact_mod_cast heq
      linarith
    have hcoef := partial_coeff_bound b (v - u) Δ hb hc0 hc1
      (by rw [huv])
    have hfac : (v - u) ^ 4 / b ^ 4 * ((p + 1 - p : ℕ) : ℝ) ^ 2 ≤ Δ ^ 2 := by
      simpa using! hcoef
    have hs := scaled_interval_fourth hfinite hM hbudget hn
      p (p + 1) (by omega) hpJ (v - u) Δ hfac
    have heval (G : Graph n) :
        centeredPolygon M G t - centeredPolygon M G s =
          (v - u) * (centeredPartial M G (p + 1) -
            centeredPartial M G p) / b := by
      rw [hpoly G t, hpoly G s]
      simp only [show meshIndex n (t : ℝ) = q by rfl,
        show meshIndex n (s : ℝ) = p by rfl, ← heq]
      dsimp [v, u]
      ring
    have habs (G : Graph n) :
        |centeredPolygon M G t - centeredPolygon M G s| ^ 4 =
          (centeredPolygon M G t - centeredPolygon M G s) ^ 4 := by
      nlinarith [sq_abs (centeredPolygon M G t - centeredPolygon M G s)]
    calc
      _ = expectM n M (fun G =>
          ((v - u) * (centeredPartial M G (p + 1) -
            centeredPartial M G p) / b) ^ 4) := by
            congr 1
            funext G
            rw [habs, heval]
      _ ≤ intervalFourthBound * Δ ^ 2 := by simpa only [b] using! hs
      _ ≤ (192 * intervalFourthBound) * Δ ^ 2 := by
        have hC : 0 ≤ intervalFourthBound := bounds_nonneg.2.2
        have hd : 0 ≤ Δ ^ 2 := sq_nonneg Δ
        nlinarith [mul_nonneg hC hd]
  · have hpqlt : p < q := lt_of_le_of_ne hpq heq
    have hpq1 : p + 1 ≤ q := by omega
    let c₁ : ℝ := (p : ℝ) + 1 - u
    let c₃ : ℝ := v - (q : ℝ)
    let k : ℝ := ((q - (p + 1) : ℕ) : ℝ)
    have hc₁0 : 0 ≤ c₁ := by
      dsimp [c₁]
      linarith [hu.2]
    have hc₁1 : c₁ ≤ 1 := by dsimp [c₁]; linarith [hu.1]
    have hc₃0 : 0 ≤ c₃ := by dsimp [c₃]; linarith [hv.1]
    have hc₃1 : c₃ ≤ 1 := by dsimp [c₃]; linarith [hv.2]
    have hqcast : (p : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hpq1
    have hc₁d : c₁ ≤ b ^ 2 * Δ := by
      dsimp [c₁]
      rw [← huv]
      linarith [hv.1]
    have hc₃d : c₃ ≤ b ^ 2 * Δ := by
      dsimp [c₃]
      rw [← huv]
      linarith [hu.2]
    have hk0 : 0 ≤ k := by dsimp [k]; positivity
    have hkcast : k = (q : ℝ) - ((p : ℝ) + 1) := by
      dsimp [k]
      have hh : p + 1 ≤ q := hpq1
      rw [Nat.cast_sub hh]
      push_cast
      ring
    have hkd : k ≤ b ^ 2 * Δ := by
      rw [hkcast, ← huv]
      linarith [hu.2, hv.1]
    have hfirst : c₁ ^ 4 / b ^ 4 * ((p + 1 - p : ℕ) : ℝ) ^ 2 ≤ Δ ^ 2 := by
      simpa using! partial_coeff_bound b c₁ Δ hb hc₁0 hc₁1 hc₁d
    have hlast : c₃ ^ 4 / b ^ 4 * ((q + 1 - q : ℕ) : ℝ) ^ 2 ≤ Δ ^ 2 := by
      simpa using! partial_coeff_bound b c₃ Δ hb hc₃0 hc₃1 hc₃d
    have hmiddle : (1 : ℝ) ^ 4 / b ^ 4 *
        ((q - (p + 1) : ℕ) : ℝ) ^ 2 ≤ Δ ^ 2 := by
      exact interval_coeff_bound b k Δ hb hk0 hkd
    have hbound₁ := scaled_interval_fourth hfinite hM hbudget hn
      p (p + 1) (by omega) hpJ c₁ Δ hfirst
    have hbound₂ := scaled_interval_fourth hfinite hM hbudget hn
      (p + 1) q hpq1 (by omega) 1 Δ hmiddle
    have hbound₃ := scaled_interval_fourth hfinite hM hbudget hn
      q (q + 1) (by omega) hqJ c₃ Δ hlast
    let X : Graph n → ℝ := fun G =>
      c₁ * (centeredPartial M G (p + 1) - centeredPartial M G p) / b
    let Y : Graph n → ℝ := fun G =>
      (centeredPartial M G q - centeredPartial M G (p + 1)) / b
    let Z : Graph n → ℝ := fun G =>
      c₃ * (centeredPartial M G (q + 1) - centeredPartial M G q) / b
    have heval (G : Graph n) :
        centeredPolygon M G t - centeredPolygon M G s = X G + Y G + Z G := by
      rw [hpoly G t, hpoly G s]
      dsimp [X, Y, Z, c₁, c₃]
      simp only [show meshIndex n (t : ℝ) = q by rfl,
        show meshIndex n (s : ℝ) = p by rfl]
      dsimp [v, u]
      ring
    have hpoint (G : Graph n) :
        |centeredPolygon M G t - centeredPolygon M G s| ^ 4 ≤
          64 * (X G ^ 4 + Y G ^ 4 + Z G ^ 4) := by
      rw [heval]
      have habs : |X G + Y G + Z G| ^ 4 = (X G + Y G + Z G) ^ 4 := by
        nlinarith [sq_abs (X G + Y G + Z G)]
      rw [habs]
      exact three_sum_fourth _ _ _
    have hmono := expectM_mono (M := M)
      (fun G => |centeredPolygon M G t - centeredPolygon M G s| ^ 4)
      (fun G => 64 * (X G ^ 4 + Y G ^ 4 + Z G ^ 4))
      (fun G hG => hpoint G)
    have heqsum : expectM n M
        (fun G => 64 * (X G ^ 4 + Y G ^ 4 + Z G ^ 4)) =
          64 * (expectM n M (fun G => X G ^ 4) +
            expectM n M (fun G => Y G ^ 4) +
            expectM n M (fun G => Z G ^ 4)) := by
      rw [expectM_const_mul, expectM_add, expectM_add]
    rw [heqsum] at hmono
    have hC : 0 ≤ intervalFourthBound := bounds_nonneg.2.2
    have hΔ2 : 0 ≤ Δ ^ 2 := sq_nonneg _
    have hb1 : expectM n M (fun G => X G ^ 4) ≤
        intervalFourthBound * Δ ^ 2 := hbound₁
    have hb2 : expectM n M (fun G => Y G ^ 4) ≤
        intervalFourthBound * Δ ^ 2 := by simpa only [Y, one_mul] using! hbound₂
    have hb3 : expectM n M (fun G => Z G ^ 4) ≤
        intervalFourthBound * Δ ^ 2 := hbound₃
    dsimp [Δ] at *
    nlinarith [hmono, hb1, hb2, hb3]

/-- Uniform fourth increments on each fixed compact time window for the
actual critical fixed-edge law. The conclusion is eventual because early
inadmissible edge counts do not define probability laws. -/
theorem critical_centeredPolygon_fourth
    (hfinite : FiniteEnumerationStatement) (M : NatSeq) (lam T : ℝ)
    (hcritical : criticalWindow M lam) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ s t : NNReal, s ≤ t → (t : ℝ) ≤ T →
        expectM n (M n) (fun G =>
          |linearInterpolation (centeredPartial (M n) G)
              (t * explorationScale n) / n13 n -
            linearInterpolation (centeredPartial (M n) G)
              (s * explorationScale n) / n13 n| ^ 4) ≤
          C * ((t : ℝ) - (s : ℝ)) ^ 2 := by
  let H := T + 1
  have hH : 0 ≤ H := by dsimp [H]; linarith
  refine ⟨192 * intervalFourthBound, ?_, ?_⟩
  · have hC : 0 < intervalFourthBound := by
      unfold intervalFourthBound centeredThirdBound centeredFourthBound rawFourthBound
      norm_num
    positivity
  filter_upwards [hcritical.1,
    eventually_horizonBudget M lam H hcritical hH,
    n13_tendsto_atTop.eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (1 : ℕ)] with n hM hbudget hb hn
  have hn' : 0 < n := by omega
  have ha : 1 ≤ n23 n := by
    rw [n23_eq_n13_square n hn']
    nlinarith [sq_nonneg (n13 n - 1)]
  intro s t hst ht
  have hguard : meshIndex n (t : ℝ) + 1 ≤ meshIndex n H := by
    have ha0 : 0 < n23 n := n23_pos n hn'
    have hx : 0 ≤ (t : ℝ) * n23 n := by positivity
    have hfloor : (meshIndex n (t : ℝ) : ℝ) ≤
        (t : ℝ) * n23 n := by
      exact Nat.floor_le hx
    have hle : ((meshIndex n (t : ℝ) + 1 : ℕ) : ℝ) ≤
        H * n23 n := by
      dsimp [H]
      push_cast
      nlinarith
    exact Nat.le_floor hle
  simpa only [centeredPolygon] using!
    finite_centeredPolygon_fourth hfinite hM hbudget hn' s t hst hguard

end

end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FourthMoment


/-!
# All-index exploration vector laws and their tightness

The exceptional indices use the admissible edge count `min (M n) (capacity n)`.
At every index the law is the finite fixed-edge exploration law for that count;
under a critical window it agrees eventually with the law for `M n` itself.
The centered mesh vectors have uniformly bounded second moments, by the
positive-history-atom martingale square estimate.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_VectorTightness

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteHorizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Horizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Reveal
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteAtoms
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteMaximal
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_QueueControl
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_CriticalBudget
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteLaw
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Characteristic
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Interpolation
open MeasureTheory Filter WithLp
open scoped BigOperators Topology ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable
local instance graphMeasurableSpace (n : ℕ) : MeasurableSpace (Graph n) := ⊤
local instance : MeasurableSpace BrownianPath := borel BrownianPath
local instance : BorelSpace BrownianPath := ⟨rfl⟩
set_option maxHeartbeats 1000000

def admissibleEdges (M : NatSeq) (n : ℕ) : ℕ := min (M n) (capacity n)

theorem admissibleEdges_le (M : NatSeq) (n : ℕ) :
    admissibleEdges M n ≤ capacity n := Nat.min_le_right _ _

theorem admissibleEdges_eq_of_le (M : NatSeq) (n : ℕ)
    (hM : M n ≤ capacity n) : admissibleEdges M n = M n :=
  Nat.min_eq_left hM

def allPathLaw (M : NatSeq) (n : ℕ) : PathLaw :=
  explorationPathMeasure n (admissibleEdges M n) (admissibleEdges_le M n)

instance allPathLaw_probability (M : NatSeq) (n : ℕ) :
    IsProbabilityMeasure (allPathLaw M n) := by
  unfold allPathLaw
  infer_instance

def centeredMeshVector {m : ℕ} (M : ℕ) (n : ℕ)
    (t : Fin m → NNReal) (G : Graph n) : EuclideanSpace ℝ (Fin m) :=
  toLp 2 (fun i => centeredPartial M G (meshIndex n (t i : ℝ)) / n13 n)

private theorem meshIndex_mono {n : ℕ} {s t : ℝ} (hst : s ≤ t) :
    meshIndex n s ≤ meshIndex n t := by
  unfold meshIndex
  apply Nat.floor_mono
  exact mul_le_mul_of_nonneg_right hst
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)

@[simp] theorem centeredMeshVector_apply {m n M : ℕ}
    (t : Fin m → NNReal) (G : Graph n) (i : Fin m) :
    centeredMeshVector M n t G i =
      centeredPartial M G (meshIndex n (t i : ℝ)) / n13 n := rfl

/-- A probability measure for every `n`, including indices where `M n` is
inadmissible. Its support consists of genuine fixed-edge BFS vectors. -/
def centeredVectorLaw {m : ℕ} (M : NatSeq) (t : Fin m → NNReal)
    (n : ℕ) : ProbabilityMeasure (EuclideanSpace ℝ (Fin m)) :=
  ⟨Measure.map (centeredMeshVector (admissibleEdges M n) n t)
      (fixedMeasure n (admissibleEdges M n) (admissibleEdges_le M n)),
    Measure.isProbabilityMeasure_map
      (measurable_from_fixed_graphs
        (centeredMeshVector (admissibleEdges M n) n t)).aemeasurable⟩

theorem centeredVectorLaw_eq_actual {m : ℕ} (M : NatSeq)
    (t : Fin m → NNReal) (n : ℕ) (hM : M n ≤ capacity n) :
    (centeredVectorLaw M t n : Measure (EuclideanSpace ℝ (Fin m))) =
      Measure.map (centeredMeshVector (M n) n t)
        (fixedMeasure n (M n) hM) := by
  simp [centeredVectorLaw, admissibleEdges_eq_of_le M n hM]

theorem centeredVectorLaw_apply_toReal {m : ℕ} (M : NatSeq)
    (t : Fin m → NNReal) (n : ℕ)
    (A : EuclideanSpace ℝ (Fin m) → Prop)
    (hA : MeasurableSet {x | A x}) :
    ((centeredVectorLaw M t n : Measure (EuclideanSpace ℝ (Fin m)))
      {x | A x}).toReal =
      probM n (admissibleEdges M n)
        (fun G => A (centeredMeshVector (admissibleEdges M n) n t G)) := by
  change ((Measure.map (centeredMeshVector (admissibleEdges M n) n t)
    (fixedMeasure n (admissibleEdges M n) (admissibleEdges_le M n)))
      {x | A x}).toReal = _
  rw [Measure.map_apply_of_aemeasurable
    (measurable_from_fixed_graphs
      (centeredMeshVector (admissibleEdges M n) n t)).aemeasurable hA]
  exact fixedMeasure_apply_toReal n _ (admissibleEdges_le M n) _

theorem centeredVectorLaw_integral {m : ℕ} (M : NatSeq)
    (t : Fin m → NNReal) (n : ℕ)
    (F : EuclideanSpace ℝ (Fin m) → ℝ) (hF : Continuous F) :
    ∫ x, F x ∂(centeredVectorLaw M t n : Measure _) =
      expectM n (admissibleEdges M n)
        (fun G => F (centeredMeshVector (admissibleEdges M n) n t G)) := by
  change ∫ x, F x ∂Measure.map
      (centeredMeshVector (admissibleEdges M n) n t)
      (fixedMeasure n (admissibleEdges M n) (admissibleEdges_le M n)) = _
  rw [MeasureTheory.integral_map
    (measurable_from_fixed_graphs
      (centeredMeshVector (admissibleEdges M n) n t)).aemeasurable
      hF.aestronglyMeasurable]
  exact integral_fixedMeasure n _ (admissibleEdges_le M n) _

/-- Finite fiber cancellation for an adapted factor. -/
private theorem fiber_cross_zero {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (h : α → β) (D F : α → ℝ)
    (hD : ∀ x ∈ s, ∑ y ∈ s with h y = h x, D y = 0)
    (hF : ∀ x ∈ s, ∀ y ∈ s, h y = h x → F y = F x) :
    ∑ x ∈ s, F x * D x = 0 := by
  let u := s.image h
  have hmaps : ∀ x ∈ s, h x ∈ u := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun x => F x * D x)]
  apply Finset.sum_eq_zero
  intro v hv
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
  calc
    (∑ y ∈ s with h y = h x, F y * D y) =
        F x * (∑ y ∈ s with h y = h x, D y) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y hy
          rw [hF x hx y (Finset.mem_filter.mp hy).1
            (Finset.mem_filter.mp hy).2]
    _ = 0 := by rw [hD x hx]; ring

/-- The conditional second-moment estimate summed over every realized atom. -/
private theorem fiber_square_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (h : α → β) (D : α → ℝ) (c : ℝ)
    (hD : ∀ x ∈ s,
      ∑ y ∈ s with h y = h x, (D y) ^ 2 ≤
        c * (((s.filter (fun y => h y = h x)).card : ℝ))) :
    ∑ x ∈ s, (D x) ^ 2 ≤ c * (s.card : ℝ) := by
  let u := s.image h
  have hmaps : ∀ x ∈ s, h x ∈ u := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hsum : ∑ v ∈ u, ∑ y ∈ s with h y = v, (D y) ^ 2 ≤
      ∑ v ∈ u, c * (((s.filter (fun y => h y = v)).card : ℝ)) := by
    apply Finset.sum_le_sum
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    exact hD x hx
  have hcard : ∑ v ∈ u, (s.filter (fun y => h y = v)).card = s.card := by
    calc
      (∑ v ∈ u, (s.filter (fun y => h y = v)).card) =
          ∑ v ∈ u, ∑ y ∈ s with h y = v, (1 : ℕ) := by simp
      _ = ∑ y ∈ s, (1 : ℕ) := Finset.sum_fiberwise_of_maps_to hmaps _
      _ = s.card := by simp
  calc
    (∑ x ∈ s, (D x) ^ 2) =
        ∑ v ∈ u, ∑ y ∈ s with h y = v, (D y) ^ 2 :=
          (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ v ∈ u, c * (((s.filter (fun y => h y = v)).card : ℝ)) := hsum
    _ = c * (s.card : ℝ) := by
      rw [← Finset.mul_sum]
      norm_cast
      rw [hcard]

/-- The centered partial sum has its sharp finite second-moment bound. -/
theorem centeredPartial_square_sum_le {n M J : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (hbudget : HorizonBudget n M J 8) (k : ℕ) (hk : k ≤ J) :
    (∑ G ∈ fixedGraphs n M, centeredPartial M G k ^ 2) ≤
      4 * (k : ℝ) * ((fixedGraphs n M).card : ℝ) := by
  let s := fixedGraphs n M
  let X : ℕ → Graph n → ℝ := fun j G => centeredPartial M G j
  have hstep (j : ℕ) (hj : j < J) :
      (∑ G ∈ s, X (j + 1) G ^ 2) =
        (∑ G ∈ s, X j G ^ 2) +
          (∑ G ∈ s, (increment X j G) ^ 2) := by
    have hcross : (∑ G ∈ s, (2 * X j G) * increment X j G) = 0 := by
      apply fiber_cross_zero s (fun G => revealTrace G j)
        (increment X j) (fun G => 2 * X j G)
      · intro G hG
        have hc : G.card = M := (Finset.mem_filter.mp hG).2
        simpa only [atom, historyAtom, s, X] using!
          centered_atom_zero hfinite hM G j hc
      · intro G hG H hH heq
        simpa only [X] using! congrArg (fun v : ℝ => 2 * v)
          (centeredPartial_eq_of_trace G H j heq)
    calc
      (∑ G ∈ s, X (j + 1) G ^ 2) =
          ∑ G ∈ s, (X j G ^ 2 + (increment X j G) ^ 2 +
            (2 * X j G) * increment X j G) := by
              apply Finset.sum_congr rfl
              intro G hG
              unfold increment
              ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hcross]
        ring
  have hsquare (j : ℕ) (hj : j < J) :
      (∑ G ∈ s, (increment X j G) ^ 2) ≤
        4 * (s.card : ℝ) := by
    apply fiber_square_le s (fun G => revealTrace G j) (increment X j) 4
    intro G hG
    have hc : G.card = M := (Finset.mem_filter.mp hG).2
    simpa only [atom, historyAtom, s, X] using!
      centered_atom_square hfinite hM G j hc hbudget hj
  have hall : ∀ k ≤ J, (∑ G ∈ s, X k G ^ 2) ≤
      4 * (k : ℝ) * (s.card : ℝ) := by
    intro r hr
    induction r with
    | zero => simp [X, centeredPartial_zero]
    | succ r ih =>
        have hr' : r < J := by omega
        have hprior := ih (Nat.le_of_lt hr')
        rw [hstep r hr']
        have hs := hsquare r hr'
        push_cast
        nlinarith
  simpa only [s, X] using! hall k hk

theorem centeredMeshVector_second_moment {m n M J : ℕ}
    (hfinite : FiniteEnumerationStatement) (hM : M ≤ capacity n)
    (hbudget : HorizonBudget n M J 8) (hn : 0 < n)
    (t : Fin m → NNReal)
    (ht : ∀ i, meshIndex n (t i : ℝ) ≤ J) :
    expectM n M (fun G => ‖centeredMeshVector M n t G‖ ^ 2) ≤
      4 * (m : ℝ) * (J : ℝ) / n13 n ^ 2 := by
  have hb : 0 < n13 n := by
    unfold n13
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hcard : (0 : ℝ) < ((fixedGraphs n M).card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr (fixedGraphs_nonempty hM))
  have hsum (i : Fin m) :
      (∑ G ∈ fixedGraphs n M,
        (centeredPartial M G (meshIndex n (t i : ℝ)) / n13 n) ^ 2) ≤
        4 * (J : ℝ) * ((fixedGraphs n M).card : ℝ) / n13 n ^ 2 := by
    have hs := centeredPartial_square_sum_le hfinite hM hbudget _ (ht i)
    have hk : (meshIndex n (t i : ℝ) : ℝ) ≤ J := by exact_mod_cast ht i
    have heq : ∀ G : Graph n,
        (centeredPartial M G (meshIndex n (t i : ℝ)) / n13 n) ^ 2 =
          centeredPartial M G (meshIndex n (t i : ℝ)) ^ 2 / n13 n ^ 2 := by
      intro G
      ring
    simp_rw [heq]
    rw [← Finset.sum_div]
    apply div_le_div_of_nonneg_right (by
      have hfac := mul_le_mul_of_nonneg_right hk
        (by positivity : 0 ≤ 4 * ((fixedGraphs n M).card : ℝ))
      nlinarith [hs, hfac]) (sq_nonneg _)
  unfold expectM
  have hrewrite : ∀ G : Graph n,
      ‖centeredMeshVector M n t G‖ ^ 2 =
        ∑ i : Fin m,
          (centeredPartial M G (meshIndex n (t i : ℝ)) / n13 n) ^ 2 := by
    intro G
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.norm_eq_abs, centeredMeshVector_apply, sq_abs]
  simp_rw [hrewrite]
  conv_lhs => rw [Finset.sum_comm]
  have hbound :
      (∑ i : Fin m, ∑ G ∈ fixedGraphs n M,
        (centeredPartial M G (meshIndex n (t i : ℝ)) / n13 n) ^ 2) ≤
      ∑ _i : Fin m,
        4 * (J : ℝ) * ((fixedGraphs n M).card : ℝ) / n13 n ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    exact hsum i
  have heq : (∑ _i : Fin m,
      4 * (J : ℝ) * ((fixedGraphs n M).card : ℝ) / n13 n ^ 2) =
      4 * (m : ℝ) * (J : ℝ) / n13 n ^ 2 *
        ((fixedGraphs n M).card : ℝ) := by simp; ring
  rw [heq] at hbound
  exact (div_le_iff₀ hcard).mpr hbound

/-- The vector's second moment is eventually bounded at the correct critical
scale under the actual `M n` fixed-edge law. -/
theorem eventually_centeredVector_second_moment {m : ℕ}
    (hfinite : FiniteEnumerationStatement) (M : NatSeq) (lam T : ℝ)
    (hcritical : criticalWindow M lam) (hT : 0 ≤ T)
    (t : Fin m → NNReal) (ht : ∀ i, (t i : ℝ) ≤ T) :
    ∀ᶠ n : ℕ in atTop,
      expectM n (M n)
        (fun G => ‖centeredMeshVector (M n) n t G‖ ^ 2) ≤
          4 * (m : ℝ) * T := by
  filter_upwards [hcritical.1,
    eventually_horizonBudget M lam T hcritical hT,
    eventually_ge_atTop (1 : ℕ)] with n hM hbudget hn
  let J := meshIndex n T
  have hmesh (i : Fin m) : meshIndex n (t i : ℝ) ≤ J :=
    meshIndex_mono (ht i)
  have hs := centeredMeshVector_second_moment hfinite hM hbudget hn t hmesh
  have ha : 0 < n23 n := n23_pos n hn
  have hab : n23 n = n13 n ^ 2 := n23_eq_n13_square n hn
  have hfloor : (J : ℝ) ≤ T * n23 n :=
    Nat.floor_le (mul_nonneg hT ha.le)
  have hratio : (J : ℝ) / n13 n ^ 2 ≤ T := by
    rw [hab] at hfloor
    have hb : 0 < n13 n := by
      unfold n13
      exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
    exact (div_le_iff₀ (sq_pos_of_pos hb)).mpr hfloor
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 4 * (m : ℝ))
  have hres : 4 * (m : ℝ) * (J : ℝ) / n13 n ^ 2 ≤ 4 * (m : ℝ) * T := by
    calc
      _ = 4 * (m : ℝ) * ((J : ℝ) / n13 n ^ 2) := by ring
      _ ≤ 4 * (m : ℝ) * T := hmul
  exact hs.trans hres

/-- The finitely many exceptional indices can be absorbed into one global
second-moment constant for the all-index probability laws. -/
theorem centeredVectorLaw_uniform_second_moment {m : ℕ}
    (hfinite : FiniteEnumerationStatement) (M : NatSeq) (lam T : ℝ)
    (hcritical : criticalWindow M lam) (hT : 0 ≤ T)
    (t : Fin m → NNReal) (ht : ∀ i, (t i : ℝ) ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ∫ x, ‖x‖ ^ 2 ∂((centeredVectorLaw M t n :
        ProbabilityMeasure (EuclideanSpace ℝ (Fin m))) :
          Measure (EuclideanSpace ℝ (Fin m))) ≤ C := by
  let a : ℕ → ℝ := fun n =>
    ∫ x, ‖x‖ ^ 2 ∂((centeredVectorLaw M t n :
      ProbabilityMeasure (EuclideanSpace ℝ (Fin m))) :
        Measure (EuclideanSpace ℝ (Fin m)))
  have hevent : ∀ᶠ n : ℕ in atTop, a n ≤ 4 * (m : ℝ) * T := by
    filter_upwards [hcritical.1,
      eventually_centeredVector_second_moment hfinite M lam T hcritical hT t ht]
      with n hM hbound
    have heq : a n = expectM n (M n)
        (fun G => ‖centeredMeshVector (M n) n t G‖ ^ 2) := by
      dsimp [a]
      rw [centeredVectorLaw_integral M t n
        (fun x => ‖x‖ ^ 2) (by fun_prop), admissibleEdges_eq_of_le M n hM]
    rw [heq]
    exact hbound
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  let C : ℝ := 4 * (m : ℝ) * T +
    ∑ k ∈ Finset.range N, |a k| + 1
  have hC : 0 ≤ C := by
    dsimp [C]
    have hsum : 0 ≤ ∑ k ∈ Finset.range N, |a k| :=
      Finset.sum_nonneg (fun k hk => abs_nonneg _)
    positivity
  refine ⟨C, hC, ?_⟩
  intro n
  by_cases hn : n < N
  · have hterm : |a n| ≤ ∑ k ∈ Finset.range N, |a k| :=
      Finset.single_le_sum (s := Finset.range N) (f := fun k => |a k|)
        (fun k hk => abs_nonneg _) (Finset.mem_range.mpr hn)
    have hreal : (0 : ℝ) ≤ 4 * (m : ℝ) * T := by positivity
    exact le_trans (le_abs_self (a n)) (by dsimp [C]; linarith)
  · have hh := hN n (le_of_not_gt hn)
    have hsum : 0 ≤ ∑ k ∈ Finset.range N, |a k| :=
      Finset.sum_nonneg (fun k hk => abs_nonneg _)
    dsimp [C]
    linarith

/-- Uniform tightness of the all-index centered mesh-vector laws. -/
theorem centeredVectorLaw_tight {m : ℕ}
    (hfinite : FiniteEnumerationStatement) (M : NatSeq) (lam T : ℝ)
    (hcritical : criticalWindow M lam) (hT : 0 ≤ T)
    (t : Fin m → NNReal) (ht : ∀ i, (t i : ℝ) ≤ T) :
    IsTightMeasureSet
      {((centeredVectorLaw M t n : ProbabilityMeasure
          (EuclideanSpace ℝ (Fin m))) :
          Measure (EuclideanSpace ℝ (Fin m))) | n : ℕ} := by
  obtain ⟨C, hC, hmoment⟩ :=
    centeredVectorLaw_uniform_second_moment hfinite M lam T hcritical hT t ht
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, hδ0, hδPos, hδε⟩ := (ENNReal.lt_iff_exists_real_btwn).1 hε
  have hδ : 0 < δ := ENNReal.ofReal_pos.mp hδPos
  let R : ℝ := C / δ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hRbound : C / R ^ 2 < δ := by
    dsimp [R]
    have hden : 0 < δ := hδ
    have hcore : C < δ * (C / δ + 1) ^ 2 := by
      have hd : C / δ ≥ 0 := div_nonneg hC hδ.le
      have hh : C / δ * δ = C := by field_simp
      nlinarith [sq_nonneg (C / δ)]
    exact (div_lt_iff₀ (by positivity : 0 < (C / δ + 1) ^ 2)).mpr
      (by nlinarith [hcore])
  let K : Set (EuclideanSpace ℝ (Fin m)) := Metric.closedBall 0 R
  refine ⟨K, isCompact_closedBall 0 R, ?_⟩
  intro μ hμ
  obtain ⟨n, rfl⟩ := hμ
  let μ : Measure (EuclideanSpace ℝ (Fin m)) := centeredVectorLaw M t n
  have hcard : (0 : ℝ) < ((fixedGraphs n (admissibleEdges M n)).card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr
      (fixedGraphs_nonempty (admissibleEdges_le M n)))
  let f : Graph n → ℝ := fun G =>
    ‖centeredMeshVector (admissibleEdges M n) n t G‖ ^ 2
  let bad : Graph n → Prop := fun G =>
    centeredMeshVector (admissibleEdges M n) n t G ∈ Kᶜ
  have hpoint : ∀ G ∈ fixedGraphs n (admissibleEdges M n),
      R ^ 2 * (if bad G then (1 : ℝ) else 0) ≤ f G := by
    intro G hG
    by_cases hb : bad G
    · simp only [if_pos hb, mul_one]
      have hx : R < ‖centeredMeshVector (admissibleEdges M n) n t G‖ := by
        simpa [bad, K, Metric.mem_closedBall, dist_zero_right] using! hb
      exact (sq_le_sq₀ hR.le (norm_nonneg _)).mpr hx.le
    · simp only [if_neg hb, mul_zero]
      exact sq_nonneg _
  have hsum := Finset.sum_le_sum hpoint
  have hcount : (∑ G ∈ fixedGraphs n (admissibleEdges M n),
      if bad G then (1 : ℝ) else 0) =
      (((fixedGraphs n (admissibleEdges M n)).filter bad).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  have hfinite : R ^ 2 *
      (((fixedGraphs n (admissibleEdges M n)).filter bad).card : ℝ) ≤
      (fixedGraphs n (admissibleEdges M n)).sum f := by
    simpa only [← Finset.mul_sum, hcount] using! hsum
  have hbound : μ.real Kᶜ ≤ C / R ^ 2 := by
    have hh : (fixedGraphs n (admissibleEdges M n)).sum f /
        ((fixedGraphs n (admissibleEdges M n)).card : ℝ) ≤ C := by
      simpa only [f, centeredVectorLaw_integral M t n
        (fun x => ‖x‖ ^ 2) (by fun_prop)] using! hmoment n
    have hprob : μ.real Kᶜ =
        (((fixedGraphs n (admissibleEdges M n)).filter bad).card : ℝ) /
          ((fixedGraphs n (admissibleEdges M n)).card : ℝ) := by
      change (μ Kᶜ).toReal = _
      rw [show Kᶜ = {x : EuclideanSpace ℝ (Fin m) | x ∈ Kᶜ} by rfl,
        centeredVectorLaw_apply_toReal M t n
          (fun x => x ∈ Kᶜ)
          (show MeasurableSet {x : EuclideanSpace ℝ (Fin m) | x ∈ Kᶜ} from
            Metric.isClosed_closedBall.measurableSet.compl)]
      simp only [probM, bad]
      congr 1
      congr 1
      congr 1
      ext G
      simp
    rw [hprob]
    have hnum : R ^ 2 *
        (((fixedGraphs n (admissibleEdges M n)).filter bad).card : ℝ) ≤
        C * ((fixedGraphs n (admissibleEdges M n)).card : ℝ) := by
      have hcross := (div_le_iff₀ hcard).mp hh
      nlinarith [hfinite, hcross]
    exact (div_le_div_iff₀ hcard (sq_pos_of_pos hR)).mpr
      (by nlinarith [hnum])
  have hμfinite : μ Kᶜ ≠ ∞ := measure_ne_top _ _
  calc
    μ Kᶜ = ENNReal.ofReal (μ.real Kᶜ) :=
      (ofReal_measureReal hμfinite).symm
    _ ≤ ENNReal.ofReal (C / R ^ 2) := ENNReal.ofReal_le_ofReal hbound
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hRbound.le
    _ ≤ ε := hδε.le

end

end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_VectorTightness


/-!
# Dyadic compactness for the centered exploration polygon

The estimates in this file use one fixed-edge graph at a time.  The rational
geometric ratio `7/8` is stronger than the exponent `1/8` required for the
dyadic modulus: `(7/8)^8 < 1/2`.  It makes both the Markov series and the
deterministic chaining series ordinary geometric sums.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_DyadicCompact

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Reveal
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteHorizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FourthMoment
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_QueueControl
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Interpolation
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteLaw
open Filter MeasureTheory
open scoped BigOperators Topology BoundedContinuousFunction

noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

private def q : ℝ := 7 / 8
private def r : ℝ := 2048 / 2401

private theorem q_bounds : 0 < q ∧ q < 1 := by norm_num [q]
private theorem r_bounds : 0 < r ∧ r < 1 := by norm_num [r]

private theorem q_relation : (2 : ℝ) * q ^ 4 * r = 1 := by
  norm_num [q, r]

private theorem geometric_sum (N : ℕ) :
    (∑ m ∈ Finset.range N, r ^ m) ≤ (1 - r)⁻¹ := by
  have hr := r_bounds
  have hs : ∀ N : ℕ,
      (∑ m ∈ Finset.range N, r ^ m) * (1 - r) = 1 - r ^ N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ]
        calc
          ((∑ m ∈ Finset.range N, r ^ m) + r ^ N) * (1 - r) =
              (1 - r ^ N) + r ^ N * (1 - r) := by rw [← ih]; ring
          _ = 1 - r ^ (N + 1) := by rw [pow_succ]; ring
  have hnonneg : 0 ≤ r ^ N := pow_nonneg hr.1.le N
  have hpos : 0 < 1 - r := sub_pos.mpr hr.2
  have hh : (∑ m ∈ Finset.range N, r ^ m) ≤ 1 / (1 - r) := by
    apply (le_div_iff₀ hpos).mpr
    rw [hs]
    linarith
  simpa only [one_div] using! hh

/- The finite support lets us replace the countable union of bad dyadic
events by one sufficiently large finite union, before taking cardinalities. -/
private theorem finite_support_union {α : Type*} [DecidableEq α]
    (S : Finset α) (P : ℕ → α → Prop) :
    ∃ N : ℕ, ∀ x ∈ S, (∃ m, P m x) ↔ ∃ m < N, P m x := by
  classical
  let witness (x : α) : ℕ :=
    if h : ∃ m, P m x then Nat.find h else 0
  let N := S.sup (fun x => witness x + 1)
  refine ⟨N, ?_⟩
  intro x hx
  constructor
  · intro h
    refine ⟨witness x, ?_, ?_⟩
    · have hle : witness x + 1 ≤ N := Finset.le_sup (f := fun x => witness x + 1) hx
      omega
    · dsimp [witness]
      rw [dif_pos h]
      exact Nat.find_spec h
  · rintro ⟨m, hm, hp⟩
    exact ⟨m, hp⟩

private theorem finite_union_probability {n M : ℕ} (hM : M ≤ capacity n)
    {ι : Type*} [Fintype ι] (P : ι → Graph n → Prop) :
    probM n M (fun G => ∃ i, P i G) ≤ ∑ i, probM n M (P i) := by
  classical
  let S := fixedGraphs n M
  have hcard : (0 : ℝ) < (S.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr (fixedGraphs_nonempty hM))
  have hfilter : S.filter (fun G => ∃ i, P i G) =
      Finset.univ.biUnion (fun i : ι => S.filter (P i)) := by
    ext G
    simp [S]
  have hcount :
      (S.filter (fun G => ∃ i, P i G)).card ≤
        ∑ i : ι, (S.filter (P i)).card := by
    rw [hfilter]
    exact Finset.card_biUnion_le
  have hreal : (((S.filter (fun G => ∃ i, P i G)).card : ℝ)) ≤
      ∑ i : ι, ((S.filter (P i)).card : ℝ) := by
    exact_mod_cast hcount
  unfold probM
  simp only [← Finset.sum_div]
  convert div_le_div_of_nonneg_right hreal hcard.le using 1
  · congr 1
    congr 1
    congr 1
    ext G
    simp [S]

private theorem finite_markov {n M : ℕ} (hM : M ≤ capacity n)
    (Y : Graph n → ℝ) (a : ℝ) (ha : 0 < a) :
    probM n M (fun G => a ≤ |Y G|) ≤
      expectM n M (fun G => |Y G| ^ 4) / a ^ 4 := by
  let S := fixedGraphs n M
  have hcard : (0 : ℝ) < (S.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr (fixedGraphs_nonempty hM))
  have hpoint : ∀ G ∈ S,
      a ^ 4 * (if a ≤ |Y G| then (1 : ℝ) else 0) ≤ |Y G| ^ 4 := by
    intro G hG
    by_cases h : a ≤ |Y G|
    · simp only [if_pos h, mul_one]
      exact pow_le_pow_left₀ ha.le h 4
    · simp only [if_neg h, mul_zero]
      positivity
  have hsum := Finset.sum_le_sum hpoint
  have hcount : (∑ G ∈ S, if a ≤ |Y G| then (1 : ℝ) else 0) =
      (((S.filter (fun G => a ≤ |Y G|)).card : ℝ)) := by
    rw [← Finset.sum_filter]
    simp
  have hnum : a ^ 4 * (((S.filter (fun G => a ≤ |Y G|)).card : ℝ)) ≤
      S.sum (fun G => |Y G| ^ 4) := by
    simpa only [← Finset.mul_sum, hcount] using! hsum
  unfold probM expectM
  have hmain : (((S.filter (fun G => a ≤ |Y G|)).card : ℝ) / S.card) * a ^ 4 ≤
      S.sum (fun G => |Y G| ^ 4) / S.card := by
    calc
      _ = (a ^ 4 * ((S.filter (fun G => a ≤ |Y G|)).card : ℝ)) / S.card := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hnum hcard.le
  have hfinal := (le_div_iff₀ (pow_pos ha 4)).mpr hmain
  simpa only [S] using! hfinal

private theorem probM_complement {n M : ℕ} (hM : M ≤ capacity n)
    (P : Graph n → Prop) :
    probM n M P + probM n M (fun G => ¬ P G) = 1 := by
  classical
  unfold probM
  rw [← add_div, ← Nat.cast_add]
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := fixedGraphs n M) P
  have hcard : ((fixedGraphs n M).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr (fixedGraphs_nonempty hM))
  convert (div_self hcard) using 1
  congr 1
  norm_cast
  convert hpartition using 1
  congr 2
  ext G
  simp

private theorem probM_monotone {n M : ℕ} (P Q : Graph n → Prop)
    (h : ∀ G, P G → Q G) : probM n M P ≤ probM n M Q := by
  classical
  unfold probM
  have hs : (fixedGraphs n M).filter P ⊆ (fixedGraphs n M).filter Q := by
    intro G hG
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hG).1, h G (Finset.mem_filter.mp hG).2⟩
  have hc : (((fixedGraphs n M).filter P).card : ℝ) ≤
      (((fixedGraphs n M).filter Q).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hs
  exact div_le_div_of_nonneg_right hc (Nat.cast_nonneg _)

/- Dyadic points are expressed in nonnegative real time, so they are valid
inputs both to the concrete polygon and to B06's fourth-moment theorem. -/
private def grid (T : NNReal) (m k : ℕ) : NNReal :=
  T * (k : NNReal) / (2 : NNReal) ^ m

private theorem grid_zero (T : NNReal) (m : ℕ) : grid T m 0 = 0 := by
  simp [grid]

private theorem grid_end (T : NNReal) (m : ℕ) : grid T m (2 ^ m) = T := by
  simp [grid]

private theorem grid_step (T : NNReal) (m k : ℕ) :
    ((grid T m (k + 1) : NNReal) : ℝ) - (grid T m k : ℝ) =
      (T : ℝ) / (2 : ℝ) ^ m := by
  simp only [grid, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast,
    NNReal.coe_pow, NNReal.coe_ofNat]
  push_cast
  have hpow : (0 : ℝ) < 2 ^ m := pow_pos (by norm_num) _
  field_simp
  ring

private theorem grid_mono (T : NNReal) (m : ℕ) {k l : ℕ}
    (hkl : k ≤ l) : grid T m k ≤ grid T m l := by
  unfold grid
  gcongr

private theorem grid_le_end (T : NNReal) (m : ℕ) {k : ℕ}
    (hk : k ≤ 2 ^ m) : grid T m k ≤ T := by
  simpa only [grid_end] using! grid_mono T m hk

private def edgeBad {n : ℕ} (M : ℕ) (T : NNReal) (R : ℝ)
    (m k : ℕ) (G : Graph n) : Prop :=
  R * q ^ m ≤
    |centeredPolygon M G (grid T m (k + 1)) -
      centeredPolygon M G (grid T m k)|

private def someBad {n : ℕ} (M : ℕ) (T : NNReal) (R : ℝ)
    (G : Graph n) : Prop :=
  ∃ m k : ℕ, k < 2 ^ m ∧ edgeBad M T R m k G

private theorem edge_bad_probability {n M : ℕ}
    (hM : M ≤ capacity n) (T : NNReal) (C R : ℝ)
    (hC : ∀ s t : NNReal, s ≤ t → (t : ℝ) ≤ T →
      expectM n M (fun G =>
        |centeredPolygon M G t - centeredPolygon M G s| ^ 4) ≤
          C * ((t : ℝ) - (s : ℝ)) ^ 2)
    (hR : 0 < R) (m k : ℕ) (hk : k < 2 ^ m) :
    probM n M (edgeBad M T R m k) ≤
      (C * (T : ℝ) ^ 2 / R ^ 4) * r ^ m / (2 : ℝ) ^ m := by
  let s := grid T m k
  let t := grid T m (k + 1)
  have hq : 0 < q := q_bounds.1
  have ha : 0 < R * q ^ m := mul_pos hR (pow_pos hq _)
  have hst : s ≤ t := grid_mono T m (by omega)
  have htT : (t : ℝ) ≤ T := by
    exact_mod_cast grid_le_end T m (by omega : k + 1 ≤ 2 ^ m)
  have hfour := hC s t hst htT
  have hmark := finite_markov hM
    (fun G => centeredPolygon M G t - centeredPolygon M G s)
    (R * q ^ m) ha
  have hstep := grid_step T m k
  have hpow : (0 : ℝ) < 2 ^ m := pow_pos (by norm_num) _
  have hrel : (2 : ℝ) ^ m * (q ^ m) ^ 4 * r ^ m = 1 := by
    calc
      (2 : ℝ) ^ m * (q ^ m) ^ 4 * r ^ m =
          (2 * q ^ 4 * r) ^ m := by ring
      _ = 1 := by rw [q_relation]; simp
  calc
    probM n M (edgeBad M T R m k) ≤
        expectM n M (fun G => |centeredPolygon M G t -
          centeredPolygon M G s| ^ 4) / (R * q ^ m) ^ 4 := hmark
    _ ≤ (C * ((t : ℝ) - (s : ℝ)) ^ 2) / (R * q ^ m) ^ 4 := by
      exact div_le_div_of_nonneg_right hfour (pow_nonneg ha.le _)
    _ = (C * (T : ℝ) ^ 2 / R ^ 4) * r ^ m / (2 : ℝ) ^ m := by
      rw [hstep]
      have hR4 : R ^ 4 ≠ 0 := ne_of_gt (pow_pos hR 4)
      have hq4 : (q ^ m) ^ 4 ≠ 0 := ne_of_gt (pow_pos (pow_pos hq m) 4)
      field_simp
      calc
        C * (T : ℝ) ^ 2 = C * (T : ℝ) ^ 2 * 1 := by ring
        _ = C * (T : ℝ) ^ 2 *
            ((2 : ℝ) ^ m * (q ^ m) ^ 4 * r ^ m) := by rw [hrel]
        _ = _ := by ring

private theorem finite_level_bad_probability {n M : ℕ}
    (hM : M ≤ capacity n) (T : NNReal) (C R : ℝ)
    (hC : ∀ s t : NNReal, s ≤ t → (t : ℝ) ≤ T →
      expectM n M (fun G =>
        |centeredPolygon M G t - centeredPolygon M G s| ^ 4) ≤
          C * ((t : ℝ) - (s : ℝ)) ^ 2)
    (hR : 0 < R) (m : ℕ) :
    probM n M (fun G => ∃ k < 2 ^ m, edgeBad M T R m k G) ≤
      (C * (T : ℝ) ^ 2 / R ^ 4) * r ^ m := by
  have hu := finite_union_probability hM
    (P := fun k : Fin (2 ^ m) => fun G => edgeBad M T R m k G)
  have hsum :
      (∑ k : Fin (2 ^ m), probM n M (edgeBad M T R m k)) ≤
        ∑ _k : Fin (2 ^ m),
          (C * (T : ℝ) ^ 2 / R ^ 4) * r ^ m / (2 : ℝ) ^ m := by
    apply Finset.sum_le_sum
    intro k hk
    exact edge_bad_probability hM T C R hC hR m k k.isLt
  have hcount : (∑ _k : Fin (2 ^ m),
      (C * (T : ℝ) ^ 2 / R ^ 4) * r ^ m / (2 : ℝ) ^ m) =
      (C * (T : ℝ) ^ 2 / R ^ 4) * r ^ m := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have hpow : (0 : ℝ) < 2 ^ m := pow_pos (by norm_num) _
    simp only [nsmul_eq_mul]
    push_cast
    field_simp
  have heq : (fun G : Graph n => ∃ k < 2 ^ m, edgeBad M T R m k G) =
      (fun G : Graph n => ∃ k : Fin (2 ^ m), edgeBad M T R m k G) := by
    funext G
    apply propext
    constructor
    · rintro ⟨k, hk, hbad⟩
      exact ⟨⟨k, hk⟩, hbad⟩
    · rintro ⟨k, hbad⟩
      exact ⟨k, k.isLt, hbad⟩
  rw [heq]
  exact hu.trans (hsum.trans hcount.le)

private theorem bad_probability {n M : ℕ}
    (hM : M ≤ capacity n) (T : NNReal) (C R : ℝ) (hCpos : 0 ≤ C)
    (hC : ∀ s t : NNReal, s ≤ t → (t : ℝ) ≤ T →
      expectM n M (fun G =>
        |centeredPolygon M G t - centeredPolygon M G s| ^ 4) ≤
          C * ((t : ℝ) - (s : ℝ)) ^ 2)
    (hR : 0 < R) :
    probM n M (someBad M T R) ≤
      (C * (T : ℝ) ^ 2 / R ^ 4) * (1 - r)⁻¹ := by
  let S := fixedGraphs n M
  obtain ⟨N, hN⟩ := finite_support_union S
    (fun m G => ∃ k < 2 ^ m, edgeBad M T R m k G)
  have heq : (S.filter (someBad M T R)) =
      S.filter (fun G => ∃ m < N, ∃ k < 2 ^ m, edgeBad M T R m k G) := by
    ext G
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hG, hbad⟩
      exact ⟨hG, (hN G hG).mp (by simpa [someBad] using! hbad)⟩
    · rintro ⟨hG, hbad⟩
      exact ⟨hG, by
        simpa [someBad] using! (hN G hG).mpr hbad⟩
  have hfinite := finite_union_probability hM
    (P := fun m : Fin N =>
      fun G : Graph n => ∃ k < 2 ^ (m : ℕ), edgeBad M T R m k G)
  have hsum :
      (∑ m : Fin N, probM n M
        (fun G => ∃ k < 2 ^ (m : ℕ), edgeBad M T R m k G)) ≤
      ∑ m : Fin N, (C * (T : ℝ) ^ 2 / R ^ 4) * r ^ (m : ℕ) := by
    apply Finset.sum_le_sum
    intro m hm
    exact finite_level_bad_probability hM T C R hC hR m
  have hgeo : (∑ m : Fin N, r ^ (m : ℕ)) ≤ (1 - r)⁻¹ := by
    simpa only [Fin.sum_univ_eq_sum_range] using! geometric_sum N
  have hfactor : 0 ≤ C * (T : ℝ) ^ 2 / R ^ 4 := by
    positivity
  have hmain := mul_le_mul_of_nonneg_left hgeo hfactor
  unfold probM
  rw [heq]
  have hevent : (fun G : Graph n => ∃ m < N, ∃ k < 2 ^ m,
      edgeBad M T R m k G) =
      (fun G : Graph n => ∃ i : Fin N, ∃ k < 2 ^ (i : ℕ),
        edgeBad M T R i k G) := by
    funext G
    apply propext
    constructor
    · rintro ⟨m, hm, hbad⟩
      exact ⟨⟨m, hm⟩, hbad⟩
    · rintro ⟨i, hbad⟩
      exact ⟨i, i.isLt, hbad⟩
  have hconvert :
      (((S.filter (fun G => ∃ m < N, ∃ k < 2 ^ m,
          edgeBad M T R m k G)).card : ℝ)) / S.card ≤
      ∑ m : Fin N, probM n M
        (fun G => ∃ k < 2 ^ (m : ℕ), edgeBad M T R m k G) := by
    have hfilter : S.filter (fun G => ∃ m < N, ∃ k < 2 ^ m,
        edgeBad M T R m k G) =
        S.filter (fun G => ∃ i : Fin N, ∃ k < 2 ^ (i : ℕ),
          edgeBad M T R i k G) := by
      ext G
      simp only [Finset.mem_filter, and_congr_right_iff]
      intro hG
      exact congrFun hevent G ▸ Iff.rfl
    rw [hfilter]
    convert hfinite using 1
    · congr 1
      congr 1
      congr 1
      ext G
      simp [S]
  calc
    (((S.filter (fun G => ∃ m < N, ∃ k < 2 ^ m,
        edgeBad M T R m k G)).card : ℝ)) / S.card ≤
        ∑ m : Fin N, probM n M
          (fun G => ∃ k < 2 ^ (m : ℕ), edgeBad M T R m k G) := hconvert
    _ ≤ ∑ m : Fin N, (C * (T : ℝ) ^ 2 / R ^ 4) * r ^ (m : ℕ) := hsum
    _ = (C * (T : ℝ) ^ 2 / R ^ 4) *
          (∑ m : Fin N, r ^ (m : ℕ)) := by rw [Finset.mul_sum]
    _ ≤ (C * (T : ℝ) ^ 2 / R ^ 4) * (1 - r)⁻¹ := hmain

/-! The following deterministic argument is independent of probability.
`snap` is the left endpoint of the dyadic cell containing a time.  Each
successive snap is either unchanged or advances by one half-cell. -/

private def snapIndex (T x : NNReal) (m : ℕ) : ℕ :=
  ⌊(x : ℝ) * (2 : ℝ) ^ m / (T : ℝ)⌋₊

private def snap (T x : NNReal) (m : ℕ) : NNReal :=
  grid T m (snapIndex T x m)

private theorem snapIndex_bounds (T x : NNReal) (hT : 0 < T)
    (hx : x ≤ T) (m : ℕ) :
    (snapIndex T x m : ℝ) ≤ (x : ℝ) * 2 ^ m / (T : ℝ) ∧
    (x : ℝ) * 2 ^ m / (T : ℝ) < snapIndex T x m + 1 ∧
    snapIndex T x m ≤ 2 ^ m := by
  have hTr : (0 : ℝ) < T := NNReal.coe_pos.mpr hT
  have hpow : (0 : ℝ) < 2 ^ m := pow_pos (by norm_num) _
  have hz : 0 ≤ (x : ℝ) * 2 ^ m / (T : ℝ) := by positivity
  have hlo := Nat.floor_le hz
  have hhi := Nat.lt_floor_add_one ((x : ℝ) * 2 ^ m / (T : ℝ))
  have hle : (x : ℝ) * 2 ^ m / (T : ℝ) ≤ (2 : ℝ) ^ m := by
    have hxr : (x : ℝ) ≤ T := NNReal.coe_le_coe.mpr hx
    apply (div_le_iff₀ hTr).mpr
    nlinarith [mul_le_mul_of_nonneg_right hxr hpow.le]
  have hfloor : snapIndex T x m ≤ 2 ^ m := by
    have hh := Nat.floor_mono hle
    have hnat : (⌊(2 : ℝ) ^ m⌋₊ : ℕ) = 2 ^ m := by
      norm_cast
      rw [Nat.floor_natCast]
    simpa [snapIndex, hnat] using! hh
  exact ⟨hlo, hhi, hfloor⟩

private theorem snapIndex_child (T x : NNReal) (hT : 0 < T)
    (hx : x ≤ T) (m : ℕ) :
    2 * snapIndex T x m ≤ snapIndex T x (m + 1) ∧
      snapIndex T x (m + 1) ≤ 2 * snapIndex T x m + 1 := by
  have hm := snapIndex_bounds T x hT hx m
  have hm' := snapIndex_bounds T x hT hx (m + 1)
  have hz : (x : ℝ) * 2 ^ (m + 1) / (T : ℝ) =
      2 * ((x : ℝ) * 2 ^ m / (T : ℝ)) := by rw [pow_succ]; ring
  rw [hz] at hm'
  have hlo : (2 * snapIndex T x m : ℝ) ≤
      (snapIndex T x (m + 1) : ℝ) := by
    have hh := hm.1
    have hn := hm'.2.1
    by_contra h
    have hnat0 : snapIndex T x (m + 1) < 2 * snapIndex T x m := by
      exact_mod_cast (lt_of_not_ge h)
    have hnat : snapIndex T x (m + 1) + 1 ≤ 2 * snapIndex T x m := by omega
    have hnatR : (snapIndex T x (m + 1) : ℝ) + 1 ≤
        2 * snapIndex T x m := by exact_mod_cast hnat
    linarith
  have hhi : (snapIndex T x (m + 1) : ℝ) ≤
      2 * snapIndex T x m + 1 := by
    have hh := hm.2.1
    have hn := hm'.1
    by_contra h
    have hnat0 : 2 * snapIndex T x m + 1 < snapIndex T x (m + 1) := by
      exact_mod_cast (lt_of_not_ge h)
    have hnat : 2 * snapIndex T x m + 2 ≤ snapIndex T x (m + 1) := by omega
    have hnatR : 2 * (snapIndex T x m : ℝ) + 2 ≤
        snapIndex T x (m + 1) := by exact_mod_cast hnat
    linarith
  exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩

private theorem grid_double (T : NNReal) (m k : ℕ) :
    grid T (m + 1) (2 * k) = grid T m k := by
  apply NNReal.coe_injective
  simp only [grid, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast,
    NNReal.coe_pow, NNReal.coe_ofNat, pow_succ]
  push_cast
  ring

private theorem snap_step_bound (T x : NNReal) (hT : 0 < T)
    (hx : x ≤ T) (f : NNReal → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hgood : ∀ m k, k < 2 ^ m →
      |f (grid T m (k + 1)) - f (grid T m k)| ≤ R * q ^ m)
    (m : ℕ) :
    |f (snap T x (m + 1)) - f (snap T x m)| ≤ R * q ^ (m + 1) := by
  let k := snapIndex T x m
  have hchild := snapIndex_child T x hT hx m
  have hk := (snapIndex_bounds T x hT hx m).2.2
  have hchildEq : snapIndex T x (m + 1) = 2 * k ∨
      snapIndex T x (m + 1) = 2 * k + 1 := by omega
  rcases hchildEq with heq | heq
  · have hsame : snap T x (m + 1) = snap T x m := by
      simp [snap, heq, grid_double, k]
    rw [hsame, sub_self, abs_zero]
    exact mul_nonneg hR (pow_nonneg q_bounds.1.le _)
  · have hk' : 2 * k < 2 ^ (m + 1) := by
      have hb := (snapIndex_bounds T x hT hx (m + 1)).2.2
      omega
    simpa only [snap, heq, grid_double] using!
      hgood (m + 1) (2 * k) hk'

private theorem snap_error (T x : NNReal) (hT : 0 < T)
    (hx : x ≤ T) (m : ℕ) :
    0 ≤ (x : ℝ) - (snap T x m : ℝ) ∧
      (x : ℝ) - (snap T x m : ℝ) ≤ (T : ℝ) / 2 ^ m := by
  have h := snapIndex_bounds T x hT hx m
  have hTr : (0 : ℝ) < T := NNReal.coe_pos.mpr hT
  have hpow : (0 : ℝ) < 2 ^ m := pow_pos (by norm_num) _
  simp only [snap, grid, NNReal.coe_div, NNReal.coe_mul,
    NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat]
  constructor
  · have hh := h.1
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hpow).mpr
    have hh' := (le_div_iff₀ hTr).mp hh
    nlinarith
  · have hh := h.2.1
    apply (sub_le_iff_le_add).mpr
    have hh' := (div_lt_iff₀ hTr).mp hh
    calc
      (x : ℝ) ≤ (T : ℝ) * (snapIndex T x m + 1) / 2 ^ m := by
        apply (le_div_iff₀ hpow).mpr
        nlinarith
      _ = (T : ℝ) / 2 ^ m +
          (T : ℝ) * (snapIndex T x m : ℝ) / 2 ^ m := by ring

private theorem snap_tendsto (T x : NNReal) (hT : 0 < T)
    (hx : x ≤ T) : Tendsto (snap T x) atTop (𝓝 x) := by
  have hpow : Tendsto (fun m : ℕ => ((2 : ℝ) ^ m)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hzero : Tendsto (fun m : ℕ => (T : ℝ) / 2 ^ m) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using!
      tendsto_const_nhds.mul hpow
  apply NNReal.tendsto_coe.mp
  have hdiff : Tendsto (fun m : ℕ =>
      (x : ℝ) - (snap T x m : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero
    · exact fun m => (snap_error T x hT hx m).1
    · exact fun m => (snap_error T x hT hx m).2
    · exact hzero
  have hsum : Tendsto (fun m : ℕ => (x : ℝ) -
      ((x : ℝ) - (snap T x m : ℝ))) atTop (𝓝 ((x : ℝ) - 0)) :=
    tendsto_const_nhds.sub hdiff
  have heq : (fun m : ℕ => (x : ℝ) -
      ((x : ℝ) - (snap T x m : ℝ))) =
      (fun m : ℕ => (snap T x m : ℝ)) := by
    funext m
    ring
  simpa only [heq, sub_zero] using! hsum

private theorem snap_tail_bound (T x : NNReal) (hT : 0 < T)
    (hx : x ≤ T) (f : NNReal → ℝ) (hf : Continuous f)
    (R : ℝ) (hR : 0 ≤ R)
    (hgood : ∀ m k, k < 2 ^ m →
      |f (grid T m (k + 1)) - f (grid T m k)| ≤ R * q ^ m)
    (m : ℕ) :
    |f x - f (snap T x m)| ≤ 7 * R * q ^ m := by
  have hfinite (l : ℕ) (hml : m ≤ l) :
      |f (snap T x l) - f (snap T x m)| ≤
        7 * R * (q ^ m - q ^ l) := by
    induction l, hml using Nat.le_induction with
    | base => simp
    | succ l hml ih =>
      have hstep := snap_step_bound T x hT hx f R hR hgood l
      have htri : |f (snap T x (l + 1)) - f (snap T x m)| ≤
          |f (snap T x (l + 1)) - f (snap T x l)| +
            |f (snap T x l) - f (snap T x m)| := by
        exact abs_sub_le _ _ _
      have hq : q ^ (l + 1) = 7 * (q ^ l - q ^ (l + 1)) := by
        rw [pow_succ]
        dsimp [q]
        ring
      calc
        |f (snap T x (l + 1)) - f (snap T x m)| ≤
            |f (snap T x (l + 1)) - f (snap T x l)| +
              |f (snap T x l) - f (snap T x m)| := htri
        _ ≤ R * q ^ (l + 1) + 7 * R * (q ^ m - q ^ l) :=
          add_le_add hstep ih
        _ = 7 * R * (q ^ m - q ^ (l + 1)) := by
          calc
            _ = R * (7 * (q ^ l - q ^ (l + 1))) +
                7 * R * (q ^ m - q ^ l) := by rw [← hq]
            _ = _ := by ring
  have hlim : Tendsto (fun l =>
      |f (snap T x l) - f (snap T x m)|) atTop
      (𝓝 |f x - f (snap T x m)|) := by
    exact (((hf.tendsto x).comp (snap_tendsto T x hT hx)).sub_const _).abs
  have hqzero : Tendsto (fun l : ℕ => q ^ l) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one q_bounds.1.le q_bounds.2
  have hrhs : Tendsto (fun l : ℕ => 7 * R * (q ^ m - q ^ l))
      atTop (𝓝 (7 * R * q ^ m)) := by
    convert tendsto_const_nhds.mul (tendsto_const_nhds.sub hqzero) using 1
    congr 1
    ring
  exact le_of_tendsto_of_tendsto hlim hrhs
    (by filter_upwards [eventually_ge_atTop m] with l hml
        exact hfinite l hml)

private theorem snap_neighbor (T x y : NNReal) (hT : 0 < T)
    (hx : x ≤ T) (hy : y ≤ T) (hxy : x ≤ y) (m : ℕ)
    (hd : (y : ℝ) - (x : ℝ) ≤ (T : ℝ) / 2 ^ m) :
    snapIndex T x m ≤ snapIndex T y m ∧
      snapIndex T y m ≤ snapIndex T x m + 1 := by
  have hTr : (0 : ℝ) < T := NNReal.coe_pos.mpr hT
  have hpow : (0 : ℝ) < 2 ^ m := pow_pos (by norm_num) _
  have hi := snapIndex_bounds T x hT hx m
  have hj := snapIndex_bounds T y hT hy m
  have hscaled : (y : ℝ) * 2 ^ m / (T : ℝ) -
      (x : ℝ) * 2 ^ m / (T : ℝ) ≤ 1 := by
    have hh := (mul_le_mul_of_nonneg_right hd hpow.le)
    have hcancel : (T : ℝ) / 2 ^ m * 2 ^ m = T := by field_simp
    rw [hcancel] at hh
    calc
      (y : ℝ) * 2 ^ m / (T : ℝ) -
          (x : ℝ) * 2 ^ m / (T : ℝ) =
          ((y : ℝ) - (x : ℝ)) * 2 ^ m / (T : ℝ) := by ring
      _ ≤ 1 := (div_le_iff₀ hTr).mpr (by simpa using! hh)
  have hmon : snapIndex T x m ≤ snapIndex T y m := by
    unfold snapIndex
    apply Nat.floor_mono
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr hxy) hpow.le)
      hTr.le
  have hnear : snapIndex T y m ≤ snapIndex T x m + 1 := by
    by_contra hh
    have hnat : snapIndex T x m + 2 ≤ snapIndex T y m := by omega
    have hreal : (snapIndex T x m : ℝ) + 2 ≤ snapIndex T y m := by
      exact_mod_cast hnat
    linarith
  exact ⟨hmon, hnear⟩

private theorem dyadic_modulus (T : NNReal) (hT : 0 < T)
    (f : NNReal → ℝ) (hf : Continuous f) (R : ℝ) (hR : 0 ≤ R)
    (hgood : ∀ m k, k < 2 ^ m →
      |f (grid T m (k + 1)) - f (grid T m k)| ≤ R * q ^ m)
    (x y : NNReal) (hx : x ≤ T) (hy : y ≤ T) (m : ℕ)
    (hnear : |(x : ℝ) - (y : ℝ)| ≤ (T : ℝ) / 2 ^ m) :
    |f x - f y| ≤ 15 * R * q ^ m := by
  wlog hxy : x ≤ y generalizing x y
  · have hyx : y ≤ x := le_of_not_ge hxy
    simpa only [abs_sub_comm] using!
      this y x hy hx (by simpa only [abs_sub_comm] using! hnear) hyx
  have hidx := snap_neighbor T x y hT hx hy hxy m
    (by simpa [abs_of_nonpos (sub_nonpos.mpr (NNReal.coe_le_coe.mpr hxy))] using! hnear)
  have hgrid : |f (snap T x m) - f (snap T y m)| ≤ R * q ^ m := by
    rcases (by omega : snapIndex T y m = snapIndex T x m ∨
      snapIndex T y m = snapIndex T x m + 1) with heq | heq
    · have hsame : snap T x m = snap T y m := by simp [snap, heq]
      rw [hsame, sub_self, abs_zero]
      exact mul_nonneg hR (pow_nonneg q_bounds.1.le _)
    · have hk : snapIndex T x m < 2 ^ m := by
        have hh := (snapIndex_bounds T y hT hy m).2.2
        omega
      simpa only [snap, heq, abs_sub_comm] using!
        hgood m (snapIndex T x m) hk
  have hxerr := snap_tail_bound T x hT hx f hf R hR hgood m
  have hyerr := snap_tail_bound T y hT hy f hf R hR hgood m
  have htri : |f x - f y| ≤ |f x - f (snap T x m)| +
      |f (snap T x m) - f (snap T y m)| +
        |f (snap T y m) - f y| := by
    calc
      |f x - f y| ≤ |f x - f (snap T x m)| +
          |f (snap T x m) - f y| := abs_sub_le _ _ _
      _ ≤ _ := by
        have hh := abs_sub_le (f (snap T x m)) (f (snap T y m)) (f y)
        linarith
  nlinarith [htri, hxerr, hgrid, hyerr, abs_sub_comm (f (snap T y m)) (f y)]

/-- The dyadic chain has at least the requested exponent `1/8`: its
eighth-power modulus decreases by one factor of `2` per grid level. -/
private theorem dyadic_range (T : NNReal) (hT : 0 < T)
    (f : NNReal → ℝ) (hf : Continuous f) (R : ℝ) (hR : 0 ≤ R)
    (hzero : f 0 = 0)
    (hgood : ∀ m k, k < 2 ^ m →
      |f (grid T m (k + 1)) - f (grid T m k)| ≤ R * q ^ m)
    (x : NNReal) (hx : x ≤ T) : |f x| ≤ 8 * R := by
  have herr := snap_tail_bound T x hT hx f hf R hR hgood 0
  have hidx := (snapIndex_bounds T x hT hx 0).2.2
  have hroot : |f (snap T x 0)| ≤ R := by
    have hidx' : snapIndex T x 0 = 0 ∨ snapIndex T x 0 = 1 := by
      simp only [pow_zero] at hidx
      omega
    rcases hidx' with h | h
    · simpa [snap, h, grid_zero, hzero] using! hR
    · simpa [snap, h, grid_zero, grid_end, hzero, q] using! hgood 0 0 (by norm_num)
  have hh := abs_add_le (f x - f (snap T x 0)) (f (snap T x 0))
  have heq : f x - f (snap T x 0) + f (snap T x 0) = f x := by ring
  rw [heq] at hh
  simpa using! hh.trans (by nlinarith [herr, hroot])

abbrev Window (T : NNReal) := {t : NNReal // t ∈ Set.Icc 0 T}

private instance windowCompact (T : NNReal) : CompactSpace (Window T) :=
  isCompact_iff_compactSpace.mp (by
    have hcompact : IsCompact (Metric.closedBall (0 : NNReal) (T : ℝ)) :=
      isCompact_closedBall _ _
    apply IsCompact.of_isClosed_subset hcompact isClosed_Icc
    intro x hx
    simpa [Metric.mem_closedBall, dist_nndist, NNReal.nndist_zero_eq_val']
      using! hx.2)

private def windowGrid (T : NNReal) (m k : ℕ) (hk : k ≤ 2 ^ m) : Window T :=
  ⟨grid T m k, ⟨zero_le, grid_le_end T m hk⟩⟩

private def Good (T : NNReal) (R : ℝ) :
    Set (Window T →ᵇ ℝ) :=
  {f | f ⟨0, by simp⟩ = 0 ∧
    ∀ m k (hk : k < 2 ^ m),
      |f (windowGrid T m (k + 1) (by omega)) -
        f (windowGrid T m k hk.le)| ≤ R * q ^ m}

private theorem good_range (T : NNReal) (hT : 0 < T)
    (R : ℝ) (hR : 0 ≤ R) (f : Window T →ᵇ ℝ)
    (hf : f ∈ Good T R) (x : Window T) :
    |f x| ≤ 8 * R := by
  let g : NNReal → ℝ := fun t => f ⟨min t T, ⟨zero_le, min_le_right _ _⟩⟩
  have hgcont : Continuous g := by fun_prop
  have hggood : ∀ m k, k < 2 ^ m →
      |g (grid T m (k + 1)) - g (grid T m k)| ≤ R * q ^ m := by
    intro m k hk
    have hk1 := grid_le_end T m (by omega : k + 1 ≤ 2 ^ m)
    have hk0 := grid_le_end T m hk.le
    have heq1 : (⟨min (grid T m (k + 1)) T,
        ⟨zero_le, min_le_right _ _⟩⟩ : Window T) =
        windowGrid T m (k + 1) (by omega) := by
      apply Subtype.ext
      exact min_eq_left hk1
    have heq0 : (⟨min (grid T m k) T,
        ⟨zero_le, min_le_right _ _⟩⟩ : Window T) =
        windowGrid T m k hk.le := by
      apply Subtype.ext
      exact min_eq_left hk0
    simpa only [g, heq1, heq0] using! hf.2 m k hk
  have hgzero : g 0 = 0 := by
    have heq0 : (⟨min 0 T, ⟨zero_le, min_le_right _ _⟩⟩ : Window T) =
        ⟨0, ⟨zero_le, zero_le⟩⟩ := by
          apply Subtype.ext
          exact min_eq_left (zero_le)
    simpa only [g, heq0] using! hf.1
  have hx := x.property.2
  have heq : g x.1 = f x := by
    change f ⟨min x.1 T, _⟩ = f x
    congr 1
    apply Subtype.ext
    exact min_eq_left hx
  rw [← heq]
  exact dyadic_range T hT g hgcont R hR hgzero hggood x hx

private theorem good_equicontinuous (T : NNReal) (hT : 0 < T)
    (R : ℝ) (hR : 0 ≤ R) :
    Equicontinuous ((↑) : Good T R → Window T → ℝ) := by
  apply (Metric.uniformEquicontinuous_iff.mpr ?_).equicontinuous
  intro ε hε
  have hqzero : Tendsto (fun m : ℕ => 15 * R * q ^ m) atTop (𝓝 0) := by
    simpa only [mul_zero] using!
      tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one q_bounds.1.le q_bounds.2)
  obtain ⟨m, hm⟩ := (hqzero.eventually_lt_const hε).exists
  let δ : ℝ := (T : ℝ) / 2 ^ m
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy f
  have hmod : |(f.1 x) - (f.1 y)| ≤ 15 * R * q ^ m := by
    let g : NNReal → ℝ := fun t => f.1 ⟨min t T, ⟨zero_le, min_le_right _ _⟩⟩
    have hgcont : Continuous g := by fun_prop
    have hggood : ∀ m k, k < 2 ^ m →
        |g (grid T m (k + 1)) - g (grid T m k)| ≤ R * q ^ m := by
      intro m k hk
      have hk1 := grid_le_end T m (by omega : k + 1 ≤ 2 ^ m)
      have hk0 := grid_le_end T m hk.le
      have heq1 : (⟨min (grid T m (k + 1)) T,
          ⟨zero_le, min_le_right _ _⟩⟩ : Window T) =
          windowGrid T m (k + 1) (by omega) := by
        apply Subtype.ext
        exact min_eq_left hk1
      have heq0 : (⟨min (grid T m k) T,
          ⟨zero_le, min_le_right _ _⟩⟩ : Window T) =
          windowGrid T m k hk.le := by
        apply Subtype.ext
        exact min_eq_left hk0
      simpa only [g, heq1, heq0] using! f.property.2 m k hk
    have hx : (x : NNReal) ≤ T := x.property.2
    have hy : (y : NNReal) ≤ T := y.property.2
    have heqx : g x.1 = f.1 x := by
      change f.1 ⟨min x.1 T, _⟩ = f.1 x
      congr 1
      apply Subtype.ext
      exact min_eq_left hx
    have heqy : g y.1 = f.1 y := by
      change f.1 ⟨min y.1 T, _⟩ = f.1 y
      congr 1
      apply Subtype.ext
      exact min_eq_left hy
    rw [← heqx, ← heqy]
    apply dyadic_modulus T hT g hgcont R hR hggood x y hx hy m
    have hxy' : |((x : NNReal) : ℝ) - (y : ℝ)| < δ := by
      simpa only [δ, Real.dist_eq, Subtype.dist_eq] using! hxy
    exact hxy'.le
  calc
    dist (f.1 x) (f.1 y) = |f.1 x - f.1 y| := Real.dist_eq _ _
    _ ≤ 15 * R * q ^ m := hmod
    _ < ε := hm

private theorem good_compact (T : NNReal) (hT : 0 < T)
    (R : ℝ) (hR : 0 ≤ R) : IsCompact (closure (Good T R)) := by
  apply BoundedContinuousFunction.arzela_ascoli
    (s := Set.Icc (-(8 * R)) (8 * R))
  · exact isCompact_Icc
  · intro f x hf
    have hh := good_range T hT R hR f hf x
    exact abs_le.mp hh
  · exact good_equicontinuous T hT R hR

private theorem centeredPartial_stationary {n M : ℕ} (G : Graph n) :
    ∀ k, n ≤ k → centeredPartial M G k = centeredPartial M G n := by
  have hquery (j : ℕ) (hj : n ≤ j) :
      revealQuery (explore G j) = ∅ := by
    rw [explore_eq_at_order_of_le G hj]
    have hq := queue_at_order_eq_nil G
    have hs := seen_at_order_eq_univ G
    rcases hstate : explore G n with ⟨seen, queue, z⟩
    simp only [hstate] at hq
    simp only [hstate] at hs
    subst queue
    subst seen
    simp [revealQuery, selectRoot]
  have hzero (j : ℕ) (hj : n ≤ j) :
      (queryCount G j : ℝ) - queryMean M G j = 0 := by
    simp [queryCount, queryMean, hquery j hj]
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
      rw [centeredPartial, Finset.sum_range_succ]
      change centeredPartial M G k +
        ((queryCount G k : ℝ) - queryMean M G k) = _
      rw [hzero k hk, add_zero, ih]

theorem centeredPolygon_continuous {n M : ℕ} (G : Graph n) :
    Continuous (centeredPolygon M G) := by
  unfold centeredPolygon
  exact ((continuous_linearInterpolation_of_stationary
    (centeredPartial M G) n (centeredPartial_stationary G)).comp
      (continuous_id.mul continuous_const)).div_const _

@[simp] theorem centeredPolygon_zero {n M : ℕ} (G : Graph n) :
    centeredPolygon M G 0 = 0 := by
  simp [centeredPolygon, linearInterpolation, centeredPartial_zero]

/-- The actual centered polygon restricted to one compact time window. -/
def centeredRestriction {n : ℕ} (M : ℕ) (G : Graph n)
    (T : NNReal) : C(Window T, ℝ) :=
  ⟨fun x => centeredPolygon M G x, (centeredPolygon_continuous G).comp continuous_subtype_val⟩

private theorem good_compact_zero (R : ℝ) (hR : 0 ≤ R) :
    IsCompact (closure (Good 0 R)) := by
  have hsub : ∀ f : Window 0 →ᵇ ℝ, f ∈ Good 0 R → f = 0 := by
    intro f hf
    ext x
    have hx : x = (⟨0, by simp⟩ : Window 0) := by
      apply Subtype.ext
      exact le_zero_iff.mp x.property.2
    simpa [hx] using! hf.1
  have hgood : Good 0 R = {0} := by
    ext f
    constructor
    · intro hf
      simp [hsub f hf]
    · intro hf
      have hf0 : f = 0 := Set.mem_singleton_iff.mp hf
      subst f
      constructor
      · simp
      · intro m k hk
        simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply,
          sub_self, abs_zero]
        exact mul_nonneg hR (pow_nonneg q_bounds.1.le _)
  rw [hgood, closure_singleton]
  exact isCompact_singleton

private theorem good_compact_all (T : NNReal) (R : ℝ) (hR : 0 ≤ R) :
    IsCompact (closure (Good T R)) := by
  by_cases hT : 0 < T
  · exact good_compact T hT R hR
  · have hzero : T = 0 := le_antisymm (le_of_not_gt hT) (zero_le)
    subst T
    exact good_compact_zero R hR

private theorem actual_restriction_good {n M : ℕ}
    (T : NNReal) (R : ℝ) (G : Graph n)
    (hgood : ¬ someBad M T R G) :
    ContinuousMap.equivBoundedOfCompact (Window T) ℝ
      (centeredRestriction M G T) ∈ Good T R := by
  constructor
  · simp [centeredRestriction]
  · intro m k hk
    have hnot : ¬ edgeBad M T R m k G := by
      intro hb
      exact hgood ⟨m, k, hk, hb⟩
    have hqpos : 0 ≤ q ^ m := pow_nonneg q_bounds.1.le _
    have hb : |centeredPolygon M G (grid T m (k + 1)) -
        centeredPolygon M G (grid T m k)| < R * q ^ m :=
      lt_of_not_ge hnot
    simpa only [ContinuousMap.equivBoundedOfCompact_apply,
      centeredRestriction, windowGrid] using! hb.le

/-- One compact restriction family captures the centered martingale polygon
on the actual fixed-edge law with arbitrarily high eventual probability. -/
theorem critical_centeredRestriction_compact
    (hfinite : FiniteEnumerationStatement) (M : NatSeq) (lam T ε : ℝ)
    (hcritical : criticalWindow M lam) (hT : 0 ≤ T) (hε : 0 < ε) :
    ∃ K : Set (C(Window ⟨T, hT⟩, ℝ)), IsCompact K ∧
      ∀ᶠ n : ℕ in atTop,
        probM n (M n) (fun G => centeredRestriction (M n) G ⟨T, hT⟩ ∈ K)
          ≥ 1 - ε := by
  let T₀ : NNReal := NNReal.mk (T) (hT)
  obtain ⟨C, hC, hmoment⟩ :=
    critical_centeredPolygon_fourth hfinite M lam T hcritical hT
  have hrpos : 0 < 1 - r := sub_pos.mpr r_bounds.2
  let R : ℝ := 1 + C * T ^ 2 / (ε * (1 - r))
  have hR : 0 < R := by dsimp [R]; positivity
  have hbudget : (C * T ^ 2 / R ^ 4) * (1 - r)⁻¹ ≤ ε := by
    have hden : 0 < ε * (1 - r) := mul_pos hε hrpos
    have hbase : C * T ^ 2 ≤ ε * (1 - r) * R := by
      dsimp [R]
      have hh : (C * T ^ 2 / (ε * (1 - r))) * (ε * (1 - r)) =
          C * T ^ 2 := by field_simp
      nlinarith
    have hR1 : 1 ≤ R := by
      change 1 ≤ 1 + C * T ^ 2 / (ε * (1 - r))
      exact le_add_of_nonneg_right (div_nonneg
        (mul_nonneg hC.le (sq_nonneg T)) hden.le)
    have hR4 : R ≤ R ^ 4 := by
      calc
        R = R * 1 := by ring
        _ ≤ R * R ^ 3 := mul_le_mul_of_nonneg_left
          (one_le_pow₀ hR1) hR.le
        _ = R ^ 4 := by ring
    have hmain : C * T ^ 2 ≤ ε * (1 - r) * R ^ 4 := by
      exact hbase.trans (mul_le_mul_of_nonneg_left hR4
        (mul_nonneg hε.le hrpos.le))
    calc
      (C * T ^ 2 / R ^ 4) * (1 - r)⁻¹ =
          C * T ^ 2 / (R ^ 4 * (1 - r)) := by
            simp only [div_eq_mul_inv, mul_inv_rev]
            ring
      _ ≤ ε := (div_le_iff₀ (mul_pos (pow_pos hR 4) hrpos)).mpr
          (by nlinarith [hmain])
  let A := Good T₀ R
  let e := ContinuousMap.isometryEquivBoundedOfCompact (Window T₀) ℝ
  let K : Set (C(Window T₀, ℝ)) := e.symm '' closure A
  have hAcompact : IsCompact (closure A) :=
    good_compact_all T₀ R hR.le
  have hK : IsCompact K := hAcompact.image e.symm.continuous
  refine ⟨K, hK, ?_⟩
  filter_upwards [hcritical.1, hmoment] with n hM hfour
  have hbad := bad_probability hM T₀ C R hC.le
    (by simpa only [T₀, centeredPolygon] using! hfour) hR
  have hgood_prob : probM n (M n) (fun G => ¬ someBad (M n) T₀ R G) ≥ 1 - ε := by
    have hsum := probM_complement hM (someBad (M n) T₀ R)
    linarith [hbad.trans hbudget]
  have hmono : probM n (M n)
      (fun G => ¬ someBad (M n) T₀ R G) ≤
      probM n (M n) (fun G => centeredRestriction (M n) G T₀ ∈ K) := by
    apply probM_monotone
    intro G hG
    have hg := actual_restriction_good T₀ R G hG
    exact ⟨e (centeredRestriction (M n) G T₀),
      subset_closure hg, e.symm_apply_apply _⟩
  exact le_trans hgood_prob hmono

end

end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_DyadicCompact


/-!
# Compact predictable-drift restrictions

The predictable polygon is controlled on one actual fixed-edge graph.  Queue
and pool events give a uniform bound on its affine slopes, and Ascoli turns
the resulting zero-start Lipschitz family into a compact window set.
-/

namespace Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_DriftCompact

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W01_ENUM_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Finite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Reveal
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_FiniteHorizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Horizon
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_CriticalBudget
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_PoolConcentration
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_QueueControl
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_DriftFinite
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Drift
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_Interpolation
open Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_DyadicCompact
open Filter
open scoped BigOperators Topology BoundedContinuousFunction

noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

private instance windowCompact (T : NNReal) : CompactSpace (Window T) :=
  isCompact_iff_compactSpace.mp (by
    have hcompact : IsCompact (Metric.closedBall (0 : NNReal) (T : ℝ)) :=
      isCompact_closedBall _ _
    apply IsCompact.of_isClosed_subset hcompact isClosed_Icc
    intro x hx
    simpa [Metric.mem_closedBall, dist_nndist, NNReal.nndist_zero_eq_val']
      using! hx.2)

private theorem step_span (z : ℕ → ℝ) (L : ℝ)
    (hz : ∀ j, |z (j + 1) - z j| ≤ L) (j k : ℕ) (hjk : j ≤ k) :
    |z k - z j| ≤ L * ((k : ℝ) - j) := by
  induction k, hjk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
      have ht := abs_add_le (z (k + 1) - z k) (z k - z j)
      have hs := hz k
      have hreal : (j : ℝ) ≤ k := by exact_mod_cast hk
      have hcalc : z (k + 1) - z j =
          (z (k + 1) - z k) + (z k - z j) := by ring
      rw [hcalc]
      calc
        _ ≤ |z (k + 1) - z k| + |z k - z j| := ht
        _ ≤ L + L * ((k : ℝ) - j) := add_le_add hs ih
        _ = L * (((k + 1 : ℕ) : ℝ) - j) := by push_cast; ring

private theorem interpolation_lipschitz (z : ℕ → ℝ) (L : ℝ)
    (hz : ∀ j, |z (j + 1) - z j| ≤ L)
    (x y : NNReal) (hxy : x ≤ y) :
    |linearInterpolation z y - linearInterpolation z x| ≤
      L * ((y : ℝ) - x) := by
  let j := ⌊(x : ℝ)⌋₊
  let k := ⌊(y : ℝ)⌋₊
  have hxyR : (x : ℝ) ≤ y := by exact_mod_cast hxy
  have hjx : (j : ℝ) ≤ x := Nat.floor_le (by positivity)
  have hxj : (x : ℝ) < j + 1 := Nat.lt_floor_add_one _
  have hky : (k : ℝ) ≤ y := Nat.floor_le (by positivity)
  have hyk : (y : ℝ) < k + 1 := Nat.lt_floor_add_one _
  have hjk : j ≤ k := by
    apply Nat.le_floor
    exact hjx.trans hxyR
  have hform (u : NNReal) :
      linearInterpolation z u =
        z ⌊(u : ℝ)⌋₊ +
          ((u : ℝ) - ⌊(u : ℝ)⌋₊) *
            (z (⌊(u : ℝ)⌋₊ + 1) - z ⌊(u : ℝ)⌋₊) := by
    unfold linearInterpolation
    simp only
    ring
  rw [hform x, hform y]
  change |(z k + ((y : ℝ) - k) * (z (k + 1) - z k)) -
    (z j + ((x : ℝ) - j) * (z (j + 1) - z j))| ≤ L * ((y : ℝ) - x)
  by_cases heq : j = k
  · subst k
    rw [← heq]
    have he :
        (z j + ((y : ℝ) - j) * (z (j + 1) - z j)) -
          (z j + ((x : ℝ) - j) * (z (j + 1) - z j)) =
          ((y : ℝ) - x) * (z (j + 1) - z j) := by ring
    rw [he, abs_mul, abs_of_nonneg (sub_nonneg.mpr hxyR)]
    calc
      _ ≤ ((y : ℝ) - x) * L :=
        mul_le_mul_of_nonneg_left (hz j) (sub_nonneg.mpr hxyR)
      _ = L * ((y : ℝ) - x) := by ring
  · have hjk' : j + 1 ≤ k := by omega
    have hjkR : ((j + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hjk'
    have hu : 0 ≤ ((j + 1 : ℕ) : ℝ) - x := by
      push_cast
      linarith
    have hv : 0 ≤ (k : ℝ) - (j + 1) := by
      push_cast at hjkR
      exact sub_nonneg.mpr hjkR
    have hw : 0 ≤ (y : ℝ) - k := sub_nonneg.mpr hky
    have hmid := step_span z L hz (j + 1) k hjk'
    have hdecomp :
        (z k + ((y : ℝ) - k) * (z (k + 1) - z k)) -
          (z j + ((x : ℝ) - j) * (z (j + 1) - z j)) =
          (((j + 1 : ℕ) : ℝ) - x) * (z (j + 1) - z j) +
            (z k - z (j + 1)) +
            ((y : ℝ) - k) * (z (k + 1) - z k) := by
      push_cast
      ring
    rw [hdecomp]
    calc
      _ ≤ |(((j + 1 : ℕ) : ℝ) - x) * (z (j + 1) - z j)| +
          |z k - z (j + 1)| +
          |((y : ℝ) - k) * (z (k + 1) - z k)| := by
            have htri1 := abs_add_le
              ((((j + 1 : ℕ) : ℝ) - x) * (z (j + 1) - z j) +
                (z k - z (j + 1)))
              (((y : ℝ) - k) * (z (k + 1) - z k))
            have htri2 := abs_add_le
              ((((j + 1 : ℕ) : ℝ) - x) * (z (j + 1) - z j))
              (z k - z (j + 1))
            linarith
      _ ≤ ((((j + 1 : ℕ) : ℝ) - x) * L) +
          L * ((k : ℝ) - (j + 1)) + ((y : ℝ) - k) * L := by
            rw [abs_mul, abs_mul, abs_of_nonneg hu, abs_of_nonneg hw]
            gcongr
            · exact hz j
            · simpa only [Nat.cast_add, Nat.cast_one] using! hmid
            · exact hz k
      _ = L * ((y : ℝ) - x) := by push_cast; ring

private theorem probM_complement {n M : ℕ} (hM : M ≤ capacity n)
    (P : Graph n → Prop) :
    probM n M P + probM n M (fun G => ¬ P G) = 1 := by
  classical
  unfold probM
  rw [← add_div, ← Nat.cast_add]
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := fixedGraphs n M) P
  have hcard : ((fixedGraphs n M).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr (fixedGraphs_nonempty hM))
  convert (div_self hcard) using 1
  congr 1
  norm_cast
  convert hpartition using 1
  congr 2
  ext G
  simp

private theorem probM_mono {n M : ℕ} (P Q : Graph n → Prop)
    (h : ∀ G, P G → Q G) : probM n M P ≤ probM n M Q := by
  classical
  unfold probM
  have hs : (fixedGraphs n M).filter P ⊆ (fixedGraphs n M).filter Q := by
    intro G hG
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hG).1, h G (Finset.mem_filter.mp hG).2⟩
  have hc : (((fixedGraphs n M).filter P).card : ℝ) ≤
      (((fixedGraphs n M).filter Q).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hs
  exact div_le_div_of_nonneg_right hc (Nat.cast_nonneg _)

private theorem probM_union {n M : ℕ} (P Q : Graph n → Prop) :
    probM n M (fun G => P G ∨ Q G) ≤ probM n M P + probM n M Q := by
  classical
  unfold probM
  have hs : (fixedGraphs n M).filter (fun G => P G ∨ Q G) =
      (fixedGraphs n M).filter P ∪ (fixedGraphs n M).filter Q := by
    ext G
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  have hc := Finset.card_union_le
    ((fixedGraphs n M).filter P) ((fixedGraphs n M).filter Q)
  have hr : (((fixedGraphs n M).filter P ∪
        (fixedGraphs n M).filter Q).card : ℝ) ≤
      ((fixedGraphs n M).filter P).card +
        ((fixedGraphs n M).filter Q).card := by exact_mod_cast hc
  have hr' : (((fixedGraphs n M).filter (fun G => P G ∨ Q G)).card : ℝ) ≤
      ((fixedGraphs n M).filter P).card +
        ((fixedGraphs n M).filter Q).card := by
    rw [hs]
    exact hr
  rw [← add_div]
  convert div_le_div_of_nonneg_right hr' (Nat.cast_nonneg _) using 1
  congr 1
  congr 1
  congr 1
  ext G
  simp

private theorem predictable_zero {n M : ℕ} (G : Graph n) :
    predictablePartial M G 0 = 0 := by simp [predictablePartial]

private def clippedPredictable {n : ℕ} (M : ℕ) (G : Graph n)
    (J : ℕ) (j : ℕ) : ℝ := predictablePartial M G (min j J)

private theorem clipped_step {n M J : ℕ} (G : Graph n)
    (L : ℝ) (hL : 0 ≤ L)
    (h : ∀ j < J, |predictablePartial M G (j + 1) -
      predictablePartial M G j| ≤ L) (j : ℕ) :
    |clippedPredictable M G J (j + 1) - clippedPredictable M G J j| ≤ L := by
  by_cases hj : j < J
  · simpa [clippedPredictable, Nat.min_eq_left (by omega : j + 1 ≤ J),
      Nat.min_eq_left hj.le] using! h j hj
  · have hj' : J ≤ j := by omega
    simp [clippedPredictable, Nat.min_eq_right hj',
      Nat.min_eq_right (by omega : J ≤ j + 1), hL]

private theorem clipped_stationary {n M J : ℕ} (G : Graph n) :
    ∀ j, J ≤ j → clippedPredictable M G J j =
      clippedPredictable M G J J := by
  intro j hj
  simp [clippedPredictable, Nat.min_eq_right hj]

/-- The actual predictable polygon restricted to a fixed compact window.
The clamping beyond its guarded endpoint supplies a global continuous map. -/
def polygonalDriftRestriction {n : ℕ} (M : ℕ) (G : Graph n)
    (T : NNReal) : C(Window T, ℝ) := by
  let J := ⌊((T : ℝ) + 1) * n23 n⌋₊
  let f : NNReal → ℝ := fun t =>
    linearInterpolation (clippedPredictable M G J)
      (t * explorationScale n) / n13 n
  have hf : Continuous f :=
    ((continuous_linearInterpolation_of_stationary
      (clippedPredictable M G J) J (clipped_stationary G)).comp
        (continuous_id.mul continuous_const)).div_const _
  exact ⟨fun t => f t, hf.comp continuous_subtype_val⟩

/-- The restriction is pointwise the actual predictable polygon on the window. -/
theorem polygonalDriftRestriction_apply {n M : ℕ} (G : Graph n)
    (T : NNReal) (ha : 1 ≤ n23 n) (x : Window T) :
    polygonalDriftRestriction M G T x = polygonalDrift M G x := by
  let J := ⌊((T : ℝ) + 1) * n23 n⌋₊
  have hguard := horizon_endpoint_guard n (T : ℝ) x.1
    (NNReal.coe_nonneg _) x.property.2 ha
  have hj : ⌊((x : NNReal) : ℝ) * n23 n⌋₊ ≤ J := by
    simpa only [J] using! (hguard.1.trans (by
      apply Nat.le_floor
      have ha0 : 0 ≤ n23 n := by linarith
      have hx : (T : ℝ) * n23 n ≤ ((T : ℝ) + 1) * n23 n := by
        nlinarith
      exact (Nat.floor_le (mul_nonneg (NNReal.coe_nonneg _) ha0)).trans hx))
  have hj1 : ⌊((x : NNReal) : ℝ) * n23 n⌋₊ + 1 ≤ J := by
    simpa only [J] using! hguard.2
  change linearInterpolation (clippedPredictable M G J)
      (x.1 * explorationScale n) / n13 n = polygonalDrift M G x
  simp only [clippedPredictable, linearInterpolation,
    polygonalDrift, explorationScale_coe, NNReal.coe_mul]
  rw [Nat.min_eq_left hj, Nat.min_eq_left hj1]

private theorem driftRestriction_zero {n M : ℕ} (G : Graph n)
    (T : NNReal) :
    polygonalDriftRestriction M G T ⟨0, by simp⟩ = 0 := by
  simp [polygonalDriftRestriction, clippedPredictable, linearInterpolation,
    predictable_zero]

private theorem driftRestriction_lipschitz {n M : ℕ} (G : Graph n)
    (T : NNReal) (L : ℝ) (hL : 0 ≤ L)
    (hb : 0 < n13 n) (ha : n23 n = n13 n ^ 2)
    (hstep : ∀ j < ⌊((T : ℝ) + 1) * n23 n⌋₊,
      |n13 n * (queryMean M G j - 1)| ≤ L) :
    ∀ x y : Window T,
      |polygonalDriftRestriction M G T x - polygonalDriftRestriction M G T y| ≤
        L * |((x : NNReal) : ℝ) - (y : ℝ)| := by
  intro x y
  wlog hxy : x ≤ y generalizing x y
  · have hyx : y ≤ x := le_of_not_ge hxy
    simpa only [abs_sub_comm] using! this y x hyx
  let J := ⌊((T : ℝ) + 1) * n23 n⌋₊
  let z := clippedPredictable M G J
  have hz (j : ℕ) : |z (j + 1) - z j| ≤ L / n13 n := by
    have hj := clipped_step G (L / n13 n)
      (div_nonneg hL hb.le) (by
        intro k hk
        have hs : predictablePartial M G (k + 1) -
            predictablePartial M G k = queryMean M G k - 1 := by
          rw [predictablePartial, Finset.sum_range_succ, predictablePartial]
          ring
        rw [hs]
        have hsk := hstep k (by simpa [J] using! hk)
        exact (le_div_iff₀ hb).mpr (by
          simpa only [abs_mul, abs_of_pos hb, mul_comm] using! hsk)) j
    exact hj
  have hscale : (x : NNReal) * explorationScale n ≤
      (y : NNReal) * explorationScale n := by gcongr
  have hlin := interpolation_lipschitz z (L / n13 n) hz
    (x.1 * explorationScale n) (y.1 * explorationScale n) hscale
  have hcoe : (((y : NNReal) * explorationScale n : NNReal) : ℝ) -
      (((x : NNReal) * explorationScale n : NNReal) : ℝ) =
        ((y : ℝ) - (x : ℝ)) * n23 n := by
    simp only [NNReal.coe_mul, explorationScale_coe]
    ring
  change |linearInterpolation z (x.1 * explorationScale n) / n13 n -
      linearInterpolation z (y.1 * explorationScale n) / n13 n| ≤ _
  rw [abs_sub_comm]
  change |linearInterpolation z (y.1 * explorationScale n) / n13 n -
      linearInterpolation z (x.1 * explorationScale n) / n13 n| ≤ _
  rw [← sub_div, abs_div, abs_of_pos hb]
  have hxyR : ((x : NNReal) : ℝ) ≤ (y : ℝ) := by exact_mod_cast hxy
  rw [abs_of_nonpos (sub_nonpos.mpr hxyR)]
  have hneg : -(((x : NNReal) : ℝ) - (y : ℝ)) =
      ((y : NNReal) : ℝ) - (x : ℝ) := by ring
  rw [hneg]
  rw [hcoe] at hlin
  apply (div_le_iff₀ hb).mpr
  calc
    |linearInterpolation z (y.1 * explorationScale n) -
        linearInterpolation z (x.1 * explorationScale n)| ≤
        (L / n13 n) * (((y : ℝ) - x) * n23 n) := hlin
    _ = L * ((y : ℝ) - x) * n13 n := by rw [ha]; field_simp

private def DriftGood (T : NNReal) (L : ℝ) :
    Set (Window T →ᵇ ℝ) :=
  {f | f ⟨0, by simp⟩ = 0 ∧
    ∀ x y : Window T,
      |f x - f y| ≤ L * |((x : NNReal) : ℝ) - (y : ℝ)|}

private theorem driftGood_compact (T : NNReal) (L : ℝ) (hL : 0 ≤ L) :
    IsCompact (closure (DriftGood T L)) := by
  have hcompact : CompactSpace (Window T) := inferInstance
  apply BoundedContinuousFunction.arzela_ascoli
    (s := Set.Icc (-(L * (T : ℝ))) (L * (T : ℝ)))
  · exact isCompact_Icc
  · intro f x hf
    have h0 := hf.1
    have h := hf.2 x ⟨0, by simp⟩
    simp only [h0, sub_zero, NNReal.coe_zero, sub_zero,
      abs_of_nonneg (NNReal.coe_nonneg _)] at h
    have hx : ((x : NNReal) : ℝ) ≤ T := by exact_mod_cast x.property.2
    exact abs_le.mp (h.trans (mul_le_mul_of_nonneg_left hx hL))
  · apply (Metric.uniformEquicontinuous_iff.mpr ?_).equicontinuous
    intro ε hε
    let δ := ε / (L + 1)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    refine ⟨δ, hδ, ?_⟩
    intro x y hxy f
    have h := f.property.2 x y
    have hdist : dist x y =
        |((x : NNReal) : ℝ) - (y : ℝ)| := by
      simp only [Subtype.dist_eq, NNReal.dist_eq]
    have hδ' : L * δ < ε := by
      dsimp [δ]
      have hden : 0 < L + 1 := by linarith
      calc
        L * (ε / (L + 1)) = L * ε / (L + 1) := by ring
        _ < ε := (div_lt_iff₀ hden).mpr (by nlinarith)
    rw [hdist] at hxy
    exact (h.trans_lt
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hxy.le hL) hδ'))

private theorem good_restriction {n M : ℕ} (G : Graph n)
    (T : NNReal) (L : ℝ) (hL : 0 ≤ L)
    (hb : 0 < n13 n) (ha : n23 n = n13 n ^ 2)
    (hstep : ∀ j < ⌊((T : ℝ) + 1) * n23 n⌋₊,
      |n13 n * (queryMean M G j - 1)| ≤ L) :
    ContinuousMap.equivBoundedOfCompact (Window T) ℝ
      (polygonalDriftRestriction M G T) ∈ DriftGood T L := by
  constructor
  · simp [driftRestriction_zero]
  · intro x y
    simpa only [ContinuousMap.equivBoundedOfCompact_apply] using!
      driftRestriction_lipschitz G T L hL hb ha hstep x y

/- The real-variable calculation keeps the corrected initial density as
`n*p-1`; the exact equality `n=b³` is used only after that correction. -/
private theorem slope_numeric (n b p d j q root delta H K A : ℝ)
    (hb : 1 ≤ b) (hn : n = b ^ 3) (hp : 0 ≤ p)
    (hnp : n * p ≤ 2) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hd : 0 ≤ d) (hbal : d + j + q + root = n)
    (hj : 0 ≤ j ∧ j ≤ H * b ^ 2)
    (hq : 0 ≤ q ∧ q ≤ K * b)
    (hr : 0 ≤ root ∧ root ≤ 1)
    (hdelta : |delta| ≤ 1 / b ^ 4)
    (hinit : |b * (n * p - 1)| ≤ A) :
    |b * (d * (p + delta) - 1)| ≤ A + 2 * H + 2 * K + 5 := by
  have hb0 : 0 < b := by linarith
  have hnp0 : 0 ≤ n * p := by rw [hn]; positivity
  have hb2 : b ^ 2 * p ≤ 2 := by
    have hbb : b ^ 2 ≤ b ^ 3 := by
      calc
        b ^ 2 = b ^ 2 * 1 := by ring
        _ ≤ b ^ 2 * b := mul_le_mul_of_nonneg_left hb (sq_nonneg b)
        _ = b ^ 3 := by ring
    calc
      b ^ 2 * p ≤ b ^ 3 * p := mul_le_mul_of_nonneg_right hbb hp
      _ = n * p := by rw [hn]
      _ ≤ 2 := hnp
  have hb1 : b * p ≤ 2 := by
    have hbb : b ≤ b ^ 2 := by nlinarith [sq_nonneg (b - 1)]
    exact (mul_le_mul_of_nonneg_right hbb hp).trans hb2
  have hjp : b * j * p ≤ 2 * H := by
    calc
      b * j * p = j * (b * p) := by ring
      _ ≤ (H * b ^ 2) * (b * p) :=
        mul_le_mul_of_nonneg_right hj.2 (mul_nonneg hb0.le hp)
      _ = H * (n * p) := by rw [hn]; ring
      _ ≤ H * 2 := mul_le_mul_of_nonneg_left hnp hH
      _ = 2 * H := by ring
  have hqp : b * q * p ≤ 2 * K := by
    calc
      b * q * p = q * (b * p) := by ring
      _ ≤ (K * b) * (b * p) :=
        mul_le_mul_of_nonneg_right hq.2 (mul_nonneg hb0.le hp)
      _ = K * (b ^ 2 * p) := by ring
      _ ≤ K * 2 := mul_le_mul_of_nonneg_left hb2 hK
      _ = 2 * K := by ring
  have hrp : b * root * p ≤ 2 := by
    calc
      b * root * p = root * (b * p) := by ring
      _ ≤ 1 * (b * p) :=
        mul_le_mul_of_nonneg_right hr.2 (mul_nonneg hb0.le hp)
      _ ≤ 2 := by simpa using! hb1
  have hdle : d ≤ n := by linarith
  have hdp : |b * d * delta| ≤ 1 := by
    have hn0 : 0 ≤ n := by rw [hn]; positivity
    have hpow : 0 < b ^ 4 := pow_pos hb0 _
    rw [abs_mul, abs_mul, abs_of_pos hb0, abs_of_nonneg hd]
    calc
      b * d * |delta| ≤ b * n * |delta| := by
        gcongr
      _ ≤ b * n * (1 / b ^ 4) :=
        mul_le_mul_of_nonneg_left hdelta (mul_nonneg hb0.le hn0)
      _ = 1 := by rw [hn]; field_simp
  have hjp0 : 0 ≤ b * j * p :=
    mul_nonneg (mul_nonneg hb0.le hj.1) hp
  have hqp0 : 0 ≤ b * q * p :=
    mul_nonneg (mul_nonneg hb0.le hq.1) hp
  have hrp0 : 0 ≤ b * root * p :=
    mul_nonneg (mul_nonneg hb0.le hr.1) hp
  have heq : b * (d * (p + delta) - 1) =
      b * (n * p - 1) - b * j * p - b * q * p -
        b * root * p + b * d * delta := by
    calc
      _ = b * ((d + j + q + root) * p - 1) -
            b * j * p - b * q * p - b * root * p +
              b * d * delta := by ring
      _ = _ := by rw [hbal]
  rw [heq]
  have hi := abs_le.mp hinit
  have he := abs_le.mp hdp
  apply abs_le.mpr
  constructor <;> nlinarith

private def queueBad {n : ℕ} (H K : ℝ) (G : Graph n) : Prop :=
  ∃ j ≤ ⌊H * n23 n⌋₊,
    K * n13 n < ((explore G j).queue.length : ℝ)

private def poolBad {n : ℕ} (M : ℕ) (H : ℝ) (G : Graph n) : Prop :=
  ∃ j ≤ ⌊H * n23 n⌋₊,
    1 / (n13 n) ^ 4 ≤
      |poolDensity M G j - poolDensity M G 0|

private theorem slope_on_good {n M : ℕ} (G : Graph n)
    (H K A : ℝ) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hn : 2 ≤ n) (hb : 1 ≤ n13 n)
    (hJ : ⌊H * n23 n⌋₊ ≤ n)
    (hinit : |n13 n *
      ((n : ℝ) * ((M : ℝ) / (capacity n : ℝ)) - 1)| ≤ A)
    (hnp : (n : ℝ) * ((M : ℝ) / (capacity n : ℝ)) ≤ 2)
    (hq : ¬ queueBad H K G) (hp : ¬ poolBad M H G) :
    ∀ j < ⌊H * n23 n⌋₊,
      |n13 n * (queryMean M G j - 1)| ≤
        A + 2 * H + 2 * K + 5 := by
  intro j hj
  let b := n13 n
  let p := poolDensity M G 0
  let d : ℝ := (revealQuery (explore G j)).card
  let q : ℝ := (explore G j).queue.length
  let rt := rootIndicator G j
  let delta := poolDensity M G j - p
  have hn0 : 0 < n := by omega
  have hcube : (n : ℝ) = b ^ 3 := by
    simpa only [b] using! (n13_cube n hn0).symm
  have hsq : n23 n = b ^ 2 := by
    simpa only [b] using! n23_eq_n13_square n hn0
  have hjn : j < n := lt_of_lt_of_le hj hJ
  have hbalance := queryCard_balance G j hjn
  have hrt : 0 ≤ rt ∧ rt ≤ 1 := by
    unfold rt rootIndicator
    split_ifs <;> norm_num
  have hp0 : 0 ≤ p := by
    dsimp [p]
    rw [initial_pool_density]
    positivity
  have hnp' : (n : ℝ) * p ≤ 2 := by
    simpa [p, initial_pool_density] using! hnp
  have hinit' : |b * ((n : ℝ) * p - 1)| ≤ A := by
    simpa [b, p, initial_pool_density] using! hinit
  have hjmax : (j : ℝ) ≤ H * b ^ 2 := by
    have hjfloor : (j : ℝ) ≤ (⌊H * n23 n⌋₊ : ℝ) := by exact_mod_cast hj.le
    have hfloor := Nat.floor_le (mul_nonneg hH (n23_pos n hn0).le)
    simpa only [hsq] using! hjfloor.trans hfloor
  have hqmax : q ≤ K * b := by
    have hnot : ¬ K * n13 n < ((explore G j).queue.length : ℝ) := by
      intro hbad
      exact hq ⟨j, hj.le, hbad⟩
    exact le_of_not_gt hnot
  have hdelta : |delta| ≤ 1 / b ^ 4 := by
    have hnot : ¬ 1 / (n13 n) ^ 4 ≤
        |poolDensity M G j - poolDensity M G 0| := by
      intro hbad
      exact hp ⟨j, hj.le, hbad⟩
    exact (lt_of_not_ge hnot).le
  have hs := slope_numeric (n : ℝ) b p d (j : ℝ) q rt delta
    H K A hb hcube hp0 hnp' hH hK (by positivity)
    (by simpa [d, q, rt] using! hbalance)
    ⟨by positivity, hjmax⟩ ⟨by positivity, hqmax⟩
    hrt hdelta hinit'
  have heq : queryMean M G j - 1 = d * (p + delta) - 1 := by
    simp [queryMean, d, p, delta]
  simpa only [b, heq] using! hs

/-- One compact zero-start Lipschitz family captures the actual predictable
drift polygon on `[0,T]` with arbitrarily high eventual fixed-edge mass. -/
theorem critical_polygonalDriftRestriction_compact
    (hfinite : FiniteEnumerationStatement) (M : NatSeq) (lam T ε : ℝ)
    (hcritical : criticalWindow M lam) (hT : 0 ≤ T) (hε : 0 < ε) :
    ∃ K : Set (C(Window ⟨T, hT⟩, ℝ)), IsCompact K ∧
      ∀ᶠ n : ℕ in atTop,
        probM n (M n)
          (fun G => polygonalDriftRestriction (M n) G ⟨T, hT⟩ ∈ K)
            ≥ 1 - ε := by
  let T₀ : NNReal := NNReal.mk (T) (hT)
  let H : ℝ := T + 1
  have hH : 0 ≤ H := by dsimp [H]; linarith
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨Q, hQ, hqueue⟩ :=
    critical_queue_tight hfinite M lam H (ε / 2) hcritical hH hε2
  have hpool :=
    (critical_poolDensity_concentration hfinite M lam H 1
      hcritical hH (by norm_num)).eventually_le_const hε2
  have hinitlim := critical_initial_drift_tendsto M lam hcritical
  have hinitdev : Tendsto (fun n =>
      |n13 n * ((n : ℝ) * ((M n : ℝ) / (capacity n : ℝ)) - 1) - lam|)
      atTop (𝓝 0) := by
    simpa using! (hinitlim.sub (tendsto_const_nhds (x := lam))).abs
  have hinit := hinitdev.eventually_le_const (by norm_num : (0 : ℝ) < 1)
  have hnp := (critical_initial_density_tendsto_one M lam hcritical).eventually_le_const
    (by norm_num : (1 : ℝ) < 2)
  have hb := n13_tendsto_atTop.eventually_ge_atTop (1 : ℝ)
  have hbudget := eventually_horizonBudget M lam H hcritical hH
  let L : ℝ := |lam| + 1 + 2 * H + 2 * Q + 5
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let A := DriftGood T₀ L
  let e := ContinuousMap.isometryEquivBoundedOfCompact (Window T₀) ℝ
  let K : Set (C(Window T₀, ℝ)) := e.symm '' closure A
  have hcompact : IsCompact K :=
    (driftGood_compact T₀ L hL).image e.symm.continuous
  refine ⟨K, hcompact, ?_⟩
  filter_upwards [hcritical.1, hqueue, hpool, hinit, hnp, hb,
    hbudget, eventually_ge_atTop (32 : ℕ)] with
    n hM hqprob hpprob hinit' hnp' hb' hbudget' hn
  have hn0 : 0 < n := by omega
  have hb0 : 0 < n13 n := by linarith
  have ha : n23 n = n13 n ^ 2 := n23_eq_n13_square n hn0
  have ha1 : 1 ≤ n23 n := by rw [ha]; nlinarith [sq_nonneg (n13 n - 1)]
  have hinitBound :
      |n13 n * ((n : ℝ) * ((M n : ℝ) / (capacity n : ℝ)) - 1)| ≤
        |lam| + 1 := by
    have hsplit := abs_add_le
      (n13 n * ((n : ℝ) * ((M n : ℝ) / (capacity n : ℝ)) - 1) - lam) lam
    have heq : n13 n * ((n : ℝ) * ((M n : ℝ) / (capacity n : ℝ)) - 1) -
        lam + lam = n13 n * ((n : ℝ) * ((M n : ℝ) / (capacity n : ℝ)) - 1) := by ring
    rw [heq] at hsplit
    linarith
  let Pq : Graph n → Prop := queueBad H Q
  let Pp : Graph n → Prop := poolBad (M n) H
  let Good : Graph n → Prop := fun G => ¬ Pq G ∧ ¬ Pp G
  have hbad : probM n (M n) (fun G => ¬ Good G) ≤ ε := by
    have hform : (fun G : Graph n => ¬ Good G) =
        (fun G => Pq G ∨ Pp G) := by
      funext G
      apply propext
      simp only [Good, not_and_or, not_not]
    rw [hform]
    calc
      probM n (M n) (fun G => Pq G ∨ Pp G) ≤
          probM n (M n) Pq + probM n (M n) Pp :=
        probM_union Pq Pp
      _ ≤ ε / 2 + ε / 2 := add_le_add
        (by simpa only [Pq, queueBad] using! hqprob)
        (by simpa only [Pp, poolBad] using! hpprob)
      _ = ε := by ring
  have hgood : 1 - ε ≤ probM n (M n) Good := by
    have hcomp := probM_complement hM Good
    linarith
  have hsubset : ∀ G : Graph n, Good G →
      polygonalDriftRestriction (M n) G T₀ ∈ K := by
    intro G hG
    have hslope := slope_on_good G H Q (|lam| + 1) hH hQ.le
      (by omega : 2 ≤ n) hb' hbudget'.1 hinitBound hnp' hG.1 hG.2
    have hmem : e (polygonalDriftRestriction (M n) G T₀) ∈ A := by
      simpa only [A, e, L, T₀] using!
        good_restriction G T₀ L hL hb0 ha (by
          simpa only [H, T₀, L] using! hslope)
    exact ⟨e (polygonalDriftRestriction (M n) G T₀),
      subset_closure hmem, e.symm_apply_apply _⟩
  exact hgood.trans (probM_mono Good
    (fun G => polygonalDriftRestriction (M n) G T₀ ∈ K) hsubset)

end

end Erdos745.WrapUp.Proofs.Internal.W14_EXPLORATION_DriftCompact
