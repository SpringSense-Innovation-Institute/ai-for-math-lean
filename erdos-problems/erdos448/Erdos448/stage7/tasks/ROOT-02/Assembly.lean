module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-02».AllU
public import Erdos448.stage7.tasks.«ROOT-02».RoughDensity

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT02.Assembly

open Filter Finset Set
open scoped BigOperators Topology
open Erdos448.Stage4
open Erdos448.Stage4.Contracts

noncomputable section

lemma roughIndicator_eq_one_iff (n : ℕ) (s : ℝ) :
    roughIndicator n s = 1 ↔ IsRough n s := by
  classical
  simp [roughIndicator]

lemma roughTau_pos (n : PosNat) (s : ℝ) : 0 < roughTau n s := by
  have hone : roughIndicator 1 s = 1 := by
    rw [roughIndicator_eq_one_iff]
    intro p hp hp1
    have : p = 1 := Nat.dvd_one.mp hp1
    subst p
    exact (Nat.not_prime_one hp).elim
  have hmem : 1 ∈ divisorSet n := by
    simp [divisorSet, n.2.ne']
  unfold roughTau
  have hle : roughIndicator 1 s ≤ ∑ d ∈ divisorSet n, roughIndicator d s :=
    Finset.single_le_sum (s := divisorSet n)
      (f := fun d => roughIndicator d s) (fun d hd => Nat.zero_le _) hmem
  omega

lemma positiveNatsBelow_natCast (N : ℕ) :
    positiveNatsBelow (N : ℝ) = (Finset.range N).filter fun n => 0 < n := by
  ext n
  simp only [positiveNatsBelow, Finset.mem_filter, Finset.mem_range, Nat.ceil_natCast]
  norm_cast
  tauto

@[expose] def selectedSet (q : GoodParameters) (theta : ℝ) : Set ℕ :=
  {n | ∃ hn : 0 < n,
    roughIndicator n theta = 1 ∧
      (badDivisorCount q ⟨n, hn⟩ : ℝ) ≤
        (1 / 10 : ℝ) * roughTau ⟨n, hn⟩ q.sigma}

@[expose] def rejectedSet (q : GoodParameters) (theta : ℝ) : Set ℕ :=
  roughNumberSet theta \ selectedSet q theta

lemma good_bad_partition (q : Lemma4Parameters) (n : PosNat) :
    lemma4GoodDivisorMass q n +
      badDivisorCount q.toGoodParameters n = roughTau n q.sigma := by
  classical
  unfold lemma4GoodDivisorMass badDivisorCount roughTau
  rw [Finset.card_eq_sum_ones]
  rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : 0 < d := by
    have hdvd : d ∣ n.1 := by
      simpa [divisorSet, n.2.ne'] using hd
    exact Nat.pos_of_dvd_of_pos hdvd n.2
  simp only [goodIndicator, dif_pos n.2, dif_pos hdpos]
  by_cases hr : roughIndicator d q.sigma = 1
  · by_cases hg : Good q.toGoodParameters n ⟨d, hdpos⟩
    · simp [hr, hg]
    · simp [hr, hg]
  · have hr0 : roughIndicator d q.sigma = 0 := by
      unfold roughIndicator at hr ⊢
      split_ifs <;> simp_all
    simp [hr0]

lemma tenth_rejected_prefix_le_badMass
    (q : GoodParameters) (theta : ℝ) (N : ℕ) :
    (1 / 10 : ℝ) * prefixCount (rejectedSet q theta) N ≤
      badDivisorMass q theta (N : ℝ) := by
  classical
  let D := (Finset.range N).filter fun n => 0 < n
  have hcount : (prefixCount (rejectedSet q theta) N : ℝ) =
      ∑ n ∈ D, if n ∈ rejectedSet q theta then (1 : ℝ) else 0 := by
    simp [prefixCount, D, Finset.filter_filter]
  rw [hcount]
  rw [Finset.mul_sum]
  unfold badDivisorMass
  rw [positiveNatsBelow_natCast]
  change (∑ n ∈ D,
      (1 / 10 : ℝ) * if n ∈ rejectedSet q theta then 1 else 0) ≤ _
  apply Finset.sum_le_sum
  intro n hnD
  have hn : 0 < n := (Finset.mem_filter.mp hnD).2
  rw [dif_pos hn]
  by_cases hrej : n ∈ rejectedSet q theta
  · simp only [hrej, if_true, mul_one]
    have hrough : roughIndicator n theta = 1 := by
      rw [roughIndicator_eq_one_iff]
      exact hrej.1.2
    have hlarge :
        (1 / 10 : ℝ) * roughTau ⟨n, hn⟩ q.sigma <
          badDivisorCount q ⟨n, hn⟩ := by
      apply lt_of_not_ge
      intro hle
      apply hrej.2
      exact ⟨hn, hrough, hle⟩
    rw [hrough]
    norm_num only [Nat.cast_one]
    have htau : (0 : ℝ) < roughTau ⟨n, hn⟩ q.sigma := by
      exact_mod_cast roughTau_pos ⟨n, hn⟩ q.sigma
    calc
      (1 / 10 : ℝ) ≤
          (badDivisorCount q ⟨n, hn⟩ : ℝ) /
            roughTau ⟨n, hn⟩ q.sigma := (le_div_iff₀ htau).2 hlarge.le
      _ = (1 : ℝ) / roughTau ⟨n, hn⟩ q.sigma *
          badDivisorCount q ⟨n, hn⟩ := by ring
  · simp only [hrej, if_false, mul_zero]
    positivity

lemma prefixDensity_le_one (A : Set ℕ) (N : ℕ) :
    prefixDensity A N ≤ 1 := by
  classical
  by_cases hN : N = 0
  · subst N
    simp [prefixDensity, prefixCount]
  · have hNpos : (0 : ℝ) < N := by
      exact_mod_cast Nat.pos_of_ne_zero hN
    have hcard :
        ((Finset.range N).filter fun n => 0 < n ∧ n ∈ A).card ≤ N := by
      simpa using
        Finset.card_filter_le (Finset.range N) (fun n => 0 < n ∧ n ∈ A)
    unfold prefixDensity prefixCount
    rw [div_le_iff₀ hNpos]
    norm_num
    exact_mod_cast hcard

lemma prefixCount_selected_add_rejected
    (q : GoodParameters) (theta : ℝ) (N : ℕ) :
    prefixCount (selectedSet q theta) N +
        prefixCount (rejectedSet q theta) N =
      prefixCount (roughNumberSet theta) N := by
  classical
  let R := (Finset.range N).filter fun n => 0 < n ∧ n ∈ roughNumberSet theta
  let S := (Finset.range N).filter fun n => 0 < n ∧ n ∈ selectedSet q theta
  have hS : S ⊆ R := by
    intro n hn
    simp only [S, R, Finset.mem_filter, Finset.mem_range] at hn ⊢
    rcases hn with ⟨hnN, hnpos, hnsel⟩
    rcases hnsel with ⟨hnpos', hrough, hbad⟩
    exact ⟨hnN, hnpos, hnpos', (roughIndicator_eq_one_iff n theta).mp hrough⟩
  have hrej :
      ((Finset.range N).filter fun n => 0 < n ∧ n ∈ rejectedSet q theta) =
        R \ S := by
    ext n
    simp only [R, S, Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff]
    simp [rejectedSet]
    tauto
  unfold prefixCount
  change S.card +
      ((Finset.range N).filter fun n => 0 < n ∧ n ∈ rejectedSet q theta).card =
    R.card
  rw [hrej]
  simpa [Nat.add_comm] using Finset.card_sdiff_add_card_eq_card hS

lemma prefixDensity_selected_add_rejected
    (q : GoodParameters) (theta : ℝ) (N : ℕ) :
    prefixDensity (selectedSet q theta) N +
        prefixDensity (rejectedSet q theta) N =
      prefixDensity (roughNumberSet theta) N := by
  unfold prefixDensity
  rw [← add_div]
  congr 1
  exact_mod_cast prefixCount_selected_add_rejected q theta N

theorem p020
    (hEXT : EXT001Statement) (h007 : P007Statement) (h008 : P008Statement.{0}) :
    P020Statement := by
  intro epsilon hepsilon hepsilon_le
  rcases Erdos448.Stage7.ROOT02.AllU.p018 hEXT h007 h008
      epsilon hepsilon hepsilon_le with ⟨allU⟩
  refine ⟨{
    Cgrid := allU.Cgrid
    Cgrid_pos := allU.Cgrid_pos
    Xi0 := allU.Xi0
    Xi0_gt_one := allU.Xi0_gt_one
    grid_bound := allU.grid_bound
    threshold_spec := allU.threshold_spec
    witness := ?_
  }⟩
  intro xi sigma theta hxi htheta hsigma
  let q : Lemma4Parameters :=
    makeLemma4Parameters epsilon hepsilon hepsilon_le xi
      (lt_of_lt_of_le allU.Xi0_gt_one hxi) sigma theta htheta hsigma
  let A : Set ℕ := selectedSet q.toGoodParameters theta
  let decay : ℝ := (Real.log xi).rpow (-(9 / 10) * epsilon ^ 2)
  let rejectedBound : ℝ := decay * roughDensity theta
  have hdecay :
      (Real.log xi).rpow (-0.9 * epsilon ^ 2) = decay := by
    congr 1
    norm_num [decay]
  have hroughDensity := Erdos448.Stage7.ROOT02.RoughDensity.p019 theta htheta
  have hrejected : ∀ᶠ N : ℕ in atTop,
      prefixDensity (rejectedSet q.toGoodParameters theta) N ≤ rejectedBound := by
    filter_upwards
      [tendsto_natCast_atTop_atTop.eventually_gt_atTop (gridU0 xi sigma),
        eventually_gt_atTop 0] with N hU hN
    have hmass := allU.all_u_bound xi sigma theta (N : ℝ)
      hxi htheta hsigma hU
    have htenth := tenth_rejected_prefix_le_badMass q.toGoodParameters theta N
    have hcombined :
        (1 / 10 : ℝ) * prefixCount (rejectedSet q.toGoodParameters theta) N ≤
          (1 / 10 : ℝ) * (N : ℝ) * roughDensity theta * decay := by
      calc
        (1 / 10 : ℝ) * prefixCount (rejectedSet q.toGoodParameters theta) N ≤
            badDivisorMass q.toGoodParameters theta (N : ℝ) := htenth
        _ ≤ (1 / 10 : ℝ) * (N : ℝ) * roughDensity theta *
            (Real.log xi).rpow (-0.9 * epsilon ^ 2) := by
              simpa [q, makeLemma4Parameters, makeGoodParameters] using hmass
        _ = (1 / 10 : ℝ) * (N : ℝ) * roughDensity theta * decay := by
              rw [hdecay]
    unfold prefixDensity
    rw [div_le_iff₀ (by exact_mod_cast hN : (0 : ℝ) < N)]
    dsimp [rejectedBound]
    nlinarith
  refine ⟨A, ?_⟩
  unfold L4Spec
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    change n ∈ selectedSet q.toGoodParameters theta at hn
    rcases hn with ⟨hnpos, hrough, hbad⟩
    exact ⟨hnpos, hrough⟩
  · unfold LowerDensityAtLeast lowerDensity
    change (1 - decay) * roughDensity theta ≤
      Filter.liminf (prefixDensity A) atTop
    apply le_of_forall_lt
    intro z hz
    let target : ℝ := (1 - decay) * roughDensity theta
    let w : ℝ := (z + target) / 2
    have hzw : z < w := by
      dsimp [w, target]
      nlinarith [hz]
    have hwtarget : w < target := by
      dsimp [w, target]
      nlinarith [hz]
    have hsum : target + rejectedBound = roughDensity theta := by
      dsimp [target, rejectedBound]
      ring
    have hwrho : w + rejectedBound < roughDensity theta := by
      rw [← hsum]
      linarith
    have hroughEventually : ∀ᶠ N : ℕ in atTop,
        w + rejectedBound < prefixDensity (roughNumberSet theta) N :=
      hroughDensity.eventually_const_lt hwrho
    have hlowerEventually : ∀ᶠ N : ℕ in atTop,
        w ≤ prefixDensity A N := by
      filter_upwards [hroughEventually, hrejected] with N hroughN hrejectedN
      have hpartition :=
        prefixDensity_selected_add_rejected q.toGoodParameters theta N
      change prefixDensity (selectedSet q.toGoodParameters theta) N +
          prefixDensity (rejectedSet q.toGoodParameters theta) N =
        prefixDensity (roughNumberSet theta) N at hpartition
      change w ≤ prefixDensity (selectedSet q.toGoodParameters theta) N
      linarith
    have hcobounded :
        IsCoboundedUnder (· ≥ ·) atTop (prefixDensity A) :=
      isCoboundedUnder_ge_of_le atTop (prefixDensity_le_one A)
    have hwliminf : w ≤ Filter.liminf (prefixDensity A) atTop :=
      Filter.le_liminf_of_le hcobounded hlowerEventually
    exact hzw.trans_le hwliminf
  · intro n hnA hn
    change n ∈ selectedSet q.toGoodParameters theta at hnA
    rcases hnA with ⟨hnpos, hrough, hbad⟩
    have hbad' :
        (badDivisorCount q.toGoodParameters ⟨n, hn⟩ : ℝ) ≤
          (1 / 10 : ℝ) * roughTau ⟨n, hn⟩ q.sigma := by
      simpa only using hbad
    have hpartition := good_bad_partition q ⟨n, hn⟩
    have hpartitionReal := congrArg (fun m : ℕ => (m : ℝ)) hpartition
    push_cast at hpartitionReal
    nlinarith

end

end Erdos448.Stage7.ROOT02.Assembly
