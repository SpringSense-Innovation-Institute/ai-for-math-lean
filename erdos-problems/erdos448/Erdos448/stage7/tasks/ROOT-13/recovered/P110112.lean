module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage6.TaskContracts

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT13.Recovered.P110112

open Filter Finset Set
open scoped BigOperators Topology

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Erdos448.Stage6.TaskContracts

noncomputable section

@[expose] def twoParameters
    (epsilonInt xi : ℝ) (he0 : 0 < epsilonInt)
    (he1 : epsilonInt ≤ 1 / 10) (hxi : 1 < xi) : Lemma4Parameters :=
  { epsilonInt := epsilonInt, epsilonInt_pos := he0,
    epsilonInt_le_tenth := he1, xi := xi, xi_gt_one := hxi,
    sigma := 2, sigma_ge_two := le_rfl, theta := 2,
    theta_ge_two := le_rfl, sigma_ge_theta := le_rfl }

@[expose] def localP4Parameters
    (theta epsilonInt sigma xi : ℝ) (htheta : 2 ≤ theta)
    (he0 : 0 < epsilonInt) (he1 : epsilonInt ≤ 1 / 10)
    (hsigma : theta ≤ sigma) (hxi : 1 < xi) : Lemma4Parameters :=
  { epsilonInt := epsilonInt, epsilonInt_pos := he0,
    epsilonInt_le_tenth := he1, xi := xi, xi_gt_one := hxi,
    sigma := sigma, sigma_ge_two := htheta.trans hsigma,
    theta := theta, theta_ge_two := htheta, sigma_ge_theta := hsigma }

@[expose] def localP4Mean
    (theta epsilonInt sigma xi x : ℝ) (htheta : 2 ≤ theta)
    (he0 : 0 < epsilonInt) (he1 : epsilonInt ≤ 1 / 10)
    (hsigma : theta ≤ sigma) (hxi : 1 < xi) : ℝ :=
  let q := localP4Parameters theta epsilonInt sigma xi htheta he0 he1 hsigma hxi
  ∑ n ∈ positiveNatsBelow x,
    if hn : 0 < n then normalizedClosePair q ⟨n, hn⟩ else 0

lemma roughIndicator_two (n : ℕ) : roughIndicator n 2 = 1 := by
  have hrough : IsRough n 2 := by
    intro p hp _
    exact_mod_cast hp.two_le
  simp [roughIndicator, hrough]

lemma roughTau_two (n : PosNat) : roughTau n 2 = tau n := by
  classical
  simp [roughTau, tau, roughIndicator_two]

lemma roughDensity_two : roughDensity 2 = 1 := by
  have hempty : strictPrimeRange 2 = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro n hn
    have hnprime := (Finset.mem_filter.1 hn).2
    have hnrange := (Finset.mem_filter.1 hn).1
    have hnlt : n < 2 := by
      norm_num [positiveNatsBelow] at hnrange
      omega
    exact (not_lt_of_ge hnprime.two_le) hnlt
  simp [roughDensity, hempty]

lemma p110_proof : P110Statement := by
  intro n
  exact ⟨roughIndicator_two n.1, roughTau_two n, rfl, roughDensity_two⟩

lemma p111_proof (h110 : P110Statement) (h034 : P034Statement) :
    P111Statement := by
  unfold P111Statement
  intro epsilonInt xi he0 he1 hxi A hA n hn alpha halpha halpha_le hevent
  let q := twoParameters epsilonInt xi he0 he1 hxi
  change L4Spec q A at hA
  change
    4 / (5 * alpha) - 1 ≤ normalizedClosePair q n ∧
      2 / (5 * alpha) ≤ 4 / (5 * alpha) - 1
  have hp034 := h034 q A hA n hn
  have hspec := h110 n
  have htau_pos : 0 < (tau n : ℝ) := by
    have : 0 < (roughTau n 2 : ℝ) := by
      exact_mod_cast hp034.rough_count_positive
    simpa [q, hspec.2.1] using this
  have htauPlus_pos : 0 < (tauPlusAtTwo n : ℝ) := by
    change 0 < (tauPlus n 2 : ℝ)
    exact_mod_cast hp034.occupied_count_positive
  have hratio : (1 : ℝ) / alpha ≤ (tau n : ℝ) / tauPlusAtTwo n := by
    apply (div_le_div_iff₀ halpha htauPlus_pos).2
    simpa [mul_comm] using hevent
  have hscaled :
      (4 / 5 : ℝ) * ((1 : ℝ) / alpha) ≤
        (4 / 5 : ℝ) * ((tau n : ℝ) / tauPlusAtTwo n) :=
    mul_le_mul_of_nonneg_left hratio (by norm_num)
  have hbound :
      (4 / 5 : ℝ) * ((tau n : ℝ) / tauPlusAtTwo n) ≤
        1 + closePairSum q n / tau n := by
    simpa [q, twoParameters, tauPlusAtTwo, hspec.2.1] using hp034.bound
  have hmain : 4 / (5 * alpha) - 1 ≤ closePairSum q n / tau n := by
    have hchain := hscaled.trans hbound
    have hid : (4 / 5 : ℝ) * ((1 : ℝ) / alpha) = 4 / (5 * alpha) := by
      field_simp [halpha.ne']
    rw [hid] at hchain
    linarith
  have hindicator : roughIndicator n.1 q.theta = 1 := (hA.1 n.1 hn).2
  have hnormalized :
      normalizedClosePair q n = closePairSum q n / tau n := by
    simp [normalizedClosePair, hindicator]
  have hdenom : 0 < 5 * alpha := mul_pos (by norm_num) halpha
  have hone : (1 : ℝ) ≤ 2 / (5 * alpha) := by
    apply (le_div_iff₀ hdenom).2
    nlinarith [halpha_le]
  constructor
  · simpa [hnormalized] using hmain
  · have hid : 4 / (5 * alpha) = 2 * (2 / (5 * alpha)) := by ring
    rw [hid]
    nlinarith

lemma prefixDensity_nonneg (A : Set ℕ) (x : ℕ) :
    0 ≤ prefixDensity A x := by
  unfold prefixDensity
  positivity

lemma prefixDensity_mono {A B : Set ℕ} (hAB : A ⊆ B) (x : ℕ) :
    prefixDensity A x ≤ prefixDensity B x := by
  classical
  unfold prefixDensity
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Finset.card_le_card (show
      (Finset.range x).filter (fun n => 0 < n ∧ n ∈ A) ⊆
        (Finset.range x).filter (fun n => 0 < n ∧ n ∈ B) by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
      exact ⟨hn.1, hn.2.1, hAB hn.2.2⟩)
  · positivity

lemma prefixDensity_union_le (A B : Set ℕ) (x : ℕ) :
    prefixDensity (A ∪ B) x ≤ prefixDensity A x + prefixDensity B x := by
  classical
  have hsub :
      (Finset.range x).filter (fun n => 0 < n ∧ n ∈ A ∪ B) ⊆
        ((Finset.range x).filter (fun n => 0 < n ∧ n ∈ A)) ∪
          ((Finset.range x).filter (fun n => 0 < n ∧ n ∈ B)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union,
      Set.mem_union] at hn ⊢
    rcases hn.2.2 with hA | hB
    · exact Or.inl ⟨hn.1, hn.2.1, hA⟩
    · exact Or.inr ⟨hn.1, hn.2.1, hB⟩
  have hcard : prefixCount (A ∪ B) x ≤ prefixCount A x + prefixCount B x := by
    unfold prefixCount
    simpa using (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  unfold prefixDensity
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

lemma prefixDensity_compl_add_le_one (A : Set ℕ) (x : ℕ) (hx : 0 < x) :
    prefixDensity Aᶜ x + prefixDensity A x ≤ 1 := by
  classical
  have hpartition :
      ((Finset.range x).filter (fun n => 0 < n ∧ n ∈ Aᶜ)).card +
          ((Finset.range x).filter (fun n => 0 < n ∧ n ∈ A)).card =
        ((Finset.range x).filter (fun n => 0 < n)).card := by
    simpa [Finset.filter_filter, and_assoc, add_comm] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.range x).filter (fun n => 0 < n))
        (p := fun n => n ∈ A))
  have hcard :
      ((Finset.range x).filter (fun n => 0 < n ∧ n ∈ Aᶜ)).card +
          ((Finset.range x).filter (fun n => 0 < n ∧ n ∈ A)).card ≤ x := by
    rw [hpartition]
    simpa using Finset.card_le_card
      (Finset.filter_subset (fun n => 0 < n) (Finset.range x))
  unfold prefixDensity prefixCount
  rw [← add_div]
  apply (div_le_one (by exact_mod_cast hx)).2
  norm_cast
  convert hcard using 1 <;> congr

lemma normalizedClosePair_nonneg (q : Lemma4Parameters) (n : PosNat) :
    0 ≤ normalizedClosePair q n := by
  classical
  have hclose : 0 ≤ closePairSum q n := by
    unfold closePairSum
    apply Finset.sum_nonneg
    intro d hd
    apply Finset.sum_nonneg
    intro d' hd'
    split_ifs <;> positivity
  unfold normalizedClosePair
  positivity

lemma positiveNatsBelow_natCast (x : ℕ) :
    positiveNatsBelow (x : ℝ) =
      (Finset.range x).filter (fun n => 0 < n) := by
  ext n
  simp [positiveNatsBelow]
  aesop

lemma event_intersection_count_le_mean
    (h111 : P111Statement)
    (epsilonInt xi : ℝ) (he0 : 0 < epsilonInt)
    (he1 : epsilonInt ≤ 1 / 10) (hxi : 1 < xi)
    (A : Set ℕ) (hA : L4Spec (twoParameters epsilonInt xi he0 he1 hxi) A)
    (alpha : ℝ) (halpha : 0 < alpha) (halpha_le : alpha ≤ 2 / 5)
    (x : ℕ) :
    (prefixCount (densityEvent alpha ∩ A) x : ℝ) ≤
      (5 * alpha / 2) *
        localP4Mean 2 epsilonInt 2 xi x (by norm_num) he0 he1
          (by norm_num) hxi := by
  classical
  let q := twoParameters epsilonInt xi he0 he1 hxi
  let s := positiveNatsBelow (x : ℝ)
  have hs : s = (Finset.range x).filter (fun n => 0 < n) :=
    positiveNatsBelow_natCast x
  have hcard :
      (prefixCount (densityEvent alpha ∩ A) x : ℝ) =
        ∑ n ∈ s, if n ∈ densityEvent alpha ∩ A then (1 : ℝ) else 0 := by
    have hf :
        (Finset.range x).filter
            (fun n => 0 < n ∧ n ∈ densityEvent alpha ∩ A) =
          ((Finset.range x).filter (fun n => 0 < n)).filter
            (fun n => n ∈ densityEvent alpha ∩ A) := by
      ext n
      simp [and_assoc]
    rw [hs]
    unfold prefixCount
    have hfc :
        (↑(#((Finset.range x).filter
          (fun n => 0 < n ∧ n ∈ densityEvent alpha ∩ A))) : ℝ) =
          ↑(#(((Finset.range x).filter (fun n => 0 < n)).filter
            (fun n => n ∈ densityEvent alpha ∩ A))) :=
      congrArg (fun t : Finset ℕ => (t.card : ℝ)) hf
    have hsum :
        (↑(#(((Finset.range x).filter (fun n => 0 < n)).filter
          (fun n => n ∈ densityEvent alpha ∩ A))) : ℝ) =
          ∑ n ∈ (Finset.range x).filter (fun n => 0 < n),
            if n ∈ densityEvent alpha ∩ A then (1 : ℝ) else 0 := by
      simp
    convert hfc.trans hsum using 1 <;> congr
  rw [hcard]
  change
    (∑ n ∈ s, if n ∈ densityEvent alpha ∩ A then (1 : ℝ) else 0) ≤
      (5 * alpha / 2) *
        (∑ n ∈ s, if hn : 0 < n then normalizedClosePair q ⟨n, hn⟩ else 0)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hnpos : 0 < n := by
    rw [hs] at hn
    exact (Finset.mem_filter.1 hn).2
  simp only [dif_pos hnpos]
  by_cases hmem : n ∈ densityEvent alpha ∩ A
  · rw [if_pos hmem]
    have hevent :
        (tauPlusAtTwo ⟨n, hnpos⟩ : ℝ) ≤ alpha * tau ⟨n, hnpos⟩ := by
      have := hmem.1
      simp only [densityEvent, Set.mem_setOf_eq, hnpos, ↓reduceDIte] at this
      exact this
    have hlowerPair :
        2 / (5 * alpha) ≤ normalizedClosePair q ⟨n, hnpos⟩ := by
      have hresult := h111 epsilonInt xi he0 he1 hxi A hA
        ⟨n, hnpos⟩ hmem.2 alpha halpha halpha_le hevent
      exact hresult.2.trans hresult.1
    have hfactor : 0 ≤ 5 * alpha / 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hlowerPair hfactor
    have hid : (5 * alpha / 2) * (2 / (5 * alpha)) = (1 : ℝ) := by
      field_simp [halpha.ne']
    rw [hid] at hmul
    exact hmul
  · rw [if_neg hmem]
    exact mul_nonneg (by positivity) (normalizedClosePair_nonneg q ⟨n, hnpos⟩)

lemma p112_proof
    (h110 : P110Statement) (h111 : P111Statement)
    (h020 : P020Statement) (h102 : P102Statement) : P112Statement := by
  intro q
  obtain ⟨l4⟩ := h020 q.epsilonInt q.epsilonInt_pos q.epsilonInt_le_tenth
  let q4 : P102Parameters :=
    { theta := 2, theta_ge_two := by norm_num,
      y := q.y, y_pos := q.y_pos, y_lt_one := q.y_lt_one,
      epsilonInt := q.epsilonInt, epsilonInt_pos := q.epsilonInt_pos,
      epsilonInt_le_tenth := q.epsilonInt_le_tenth,
      admissible := q.admissible }
  obtain ⟨p4⟩ := h102 q4
  let K : ℝ := (5 / 2) * p4.coefficient * (Real.log 2).rpow (-1)
  let Cden : ℝ := 1 + K
  have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hKpos : 0 < K := by
    dsimp [K]
    exact mul_pos (mul_pos (by norm_num) p4.coefficient_pos)
      (Real.rpow_pos_of_pos hlogtwo _)
  have hCden_pos : 0 < Cden := by
    dsimp [Cden]
    linarith
  refine ⟨{
    Cgrid := l4.Cgrid
    Cgrid_pos := l4.Cgrid_pos
    Xi0 := l4.Xi0
    Xi0_gt_one := l4.Xi0_gt_one
    CP4 := p4.coefficient
    CP4_pos := p4.coefficient_pos
    Cden := Cden
    Cden_pos := hCden_pos
    density_bound := ?_
  }⟩
  intro xi hxi alpha halpha halpha_le
  have hxi_one : 1 < xi := l4.Xi0_gt_one.trans_le hxi
  obtain ⟨A, hA⟩ := l4.witness xi 2 2 hxi (by norm_num) (by norm_num)
  change L4Spec (twoParameters q.epsilonInt xi q.epsilonInt_pos
    q.epsilonInt_le_tenth hxi_one) A at hA
  let T : ℝ := (Real.log xi).rpow (-P112BBal q)
  let L : ℝ := (Real.log xi).rpow (P112ABal q)
  have hlogxi : 0 < Real.log xi := Real.log_pos hxi_one
  have hTpos : 0 < T := by dsimp [T]; positivity
  have hLpos : 0 < L := by dsimp [L]; positivity
  have hrho : roughDensity 2 = 1 := (h110 ⟨1, by norm_num⟩).2.2.2
  have hlower : 1 - T ≤ lowerDensity A := by
    have hbase := hA.2.1
    change
      (1 - (Real.log xi).rpow (-(9 / 10) * q.epsilonInt ^ 2)) *
          roughDensity 2 ≤ lowerDensity A at hbase
    rw [hrho, mul_one] at hbase
    simpa [T, P112BBal] using hbase
  have hsigma : q4.theta ≤ (2 : ℝ) := by simp [q4]
  have remSpec := p4.fixed_parameter_remainder 2 hsigma xi hxi_one
  have hp4Real := remSpec.eventual_bound
  change ∀ᶠ x : ℝ in atTop,
    localP4Mean 2 q.epsilonInt 2 xi x (by norm_num)
      q.epsilonInt_pos q.epsilonInt_le_tenth (by norm_num) hxi_one ≤
      p4.coefficient * x * (Real.log xi).rpow (P112ABal q) *
        (Real.log 2).rpow (-1) + remSpec.remainder x at hp4Real
  intro epsilon hepsilon
  have hprefix_bdd :
      IsBoundedUnder (· ≥ ·) atTop (prefixDensity A) :=
    isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall (prefixDensity_nonneg A))
  have hAevent : ∀ᶠ x : ℕ in atTop,
      1 - T - epsilon / 2 < prefixDensity A x := by
    have := eventually_add_neg_lt_of_le_liminf hprefix_bdd hlower
      (show -epsilon / 2 < (0 : ℝ) by linarith)
    filter_upwards [this] with x hx
    linarith
  have hremReal := remSpec.littleO.bound (show 0 < epsilon / 2 by linarith)
  have hp4Nat := tendsto_natCast_atTop_atTop.eventually hp4Real
  have hremNat := tendsto_natCast_atTop_atTop.eventually hremReal
  have hxevent : ∀ᶠ x : ℕ in atTop, 0 < x := by
    filter_upwards [eventually_ge_atTop 1] with x hx
    omega
  filter_upwards [hAevent, hp4Nat, hremNat, hxevent] with x hxA hxP4 hxrem hxpos
  have hfactor_nonneg : 0 ≤ 5 * alpha / 2 := by positivity
  have hfactor_le_one : 5 * alpha / 2 ≤ 1 := by nlinarith
  have hxrem' :
      ‖remSpec.remainder (x : ℝ)‖ ≤ (epsilon / 2) * x := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ x by positivity)] using hxrem
  have hrem_le : remSpec.remainder (x : ℝ) ≤ (epsilon / 2) * x := by
    have habs : remSpec.remainder (x : ℝ) ≤ ‖remSpec.remainder (x : ℝ)‖ :=
      by rw [Real.norm_eq_abs]; exact le_abs_self _
    exact habs.trans hxrem'
  have hscaledRem :
      (5 * alpha / 2) * remSpec.remainder (x : ℝ) ≤
        (epsilon / 2) * x := by
    calc
      (5 * alpha / 2) * remSpec.remainder (x : ℝ) ≤
          (5 * alpha / 2) * ‖remSpec.remainder (x : ℝ)‖ :=
        mul_le_mul_of_nonneg_left
          (by rw [Real.norm_eq_abs]; exact le_abs_self _) hfactor_nonneg
      _ ≤ 1 * ((epsilon / 2) * x) :=
        mul_le_mul hfactor_le_one hxrem' (norm_nonneg _) (by norm_num)
      _ = (epsilon / 2) * x := one_mul _
  have hmeanScaled :
      (5 * alpha / 2) *
          localP4Mean 2 q.epsilonInt 2 xi x (by norm_num)
            q.epsilonInt_pos q.epsilonInt_le_tenth (by norm_num) hxi_one ≤
        (x : ℝ) * (K * alpha * L + epsilon / 2) := by
    have hm := mul_le_mul_of_nonneg_left hxP4 hfactor_nonneg
    have hmainIdentity :
        (5 * alpha / 2) *
            (p4.coefficient * (x : ℝ) * L * (Real.log 2).rpow (-1)) =
          (x : ℝ) * (K * alpha * L) := by
      dsimp [K]
      ring
    rw [mul_add, hmainIdentity] at hm
    nlinarith
  have hcount := event_intersection_count_le_mean h111
    q.epsilonInt xi q.epsilonInt_pos q.epsilonInt_le_tenth hxi_one
    A hA alpha halpha halpha_le x
  have hintersection :
      prefixDensity (densityEvent alpha ∩ A) x ≤
        K * alpha * L + epsilon / 2 := by
    unfold prefixDensity
    calc
      (prefixCount (densityEvent alpha ∩ A) x : ℝ) / x ≤
          ((5 * alpha / 2) *
            localP4Mean 2 q.epsilonInt 2 xi x (by norm_num)
              q.epsilonInt_pos q.epsilonInt_le_tenth (by norm_num) hxi_one) / x :=
        div_le_div_of_nonneg_right hcount (by positivity)
      _ ≤ K * alpha * L + epsilon / 2 := by
        apply (div_le_iff₀ (by exact_mod_cast hxpos)).2
        simpa [mul_comm] using hmeanScaled
  have hcomplement : prefixDensity Aᶜ x < T + epsilon / 2 := by
    have hsum := prefixDensity_compl_add_le_one A x hxpos
    linarith
  have hsubset : densityEvent alpha ⊆
      (densityEvent alpha ∩ A) ∪ Aᶜ := by
    intro n hn
    by_cases hnA : n ∈ A
    · exact Or.inl ⟨hn, hnA⟩
    · exact Or.inr hnA
  have hsplit : prefixDensity (densityEvent alpha) x ≤
      prefixDensity (densityEvent alpha ∩ A) x + prefixDensity Aᶜ x :=
    (prefixDensity_mono hsubset x).trans
      (prefixDensity_union_le (densityEvent alpha ∩ A) Aᶜ x)
  have hraw : prefixDensity (densityEvent alpha) x <
      K * alpha * L + T + epsilon := by
    linarith
  have hKle : K ≤ Cden := by dsimp [Cden]; linarith
  have honele : (1 : ℝ) ≤ Cden := by dsimp [Cden]; linarith
  have hmainNonneg : 0 ≤ alpha * L := mul_nonneg halpha.le hLpos.le
  have hcoef : K * alpha * L + T ≤ Cden * (alpha * L + T) := by
    have hfirst := mul_le_mul_of_nonneg_right hKle hmainNonneg
    have hsecond := mul_le_mul_of_nonneg_right honele hTpos.le
    nlinarith
  change prefixDensity (densityEvent alpha) x ≤
    Cden * (alpha * (Real.log xi).rpow (P112ABal q) +
      (Real.log xi).rpow (-P112BBal q)) + epsilon
  dsimp [L, T] at hraw hcoef ⊢
  exact le_trans hraw.le (by
    simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hcoef epsilon)

theorem node_p110 : P110Statement :=
  p110_proof

theorem node_p111 (h034 : P034Statement) : P111Statement :=
  p111_proof p110_proof h034

theorem node_p112 (h020 : P020Statement) (h034 : P034Statement)
    (h102 : P102Statement) : P112Statement :=
  p112_proof p110_proof (p111_proof p110_proof h034) h020 h102

end

end Erdos448.Stage7.ROOT13.Recovered.P110112
