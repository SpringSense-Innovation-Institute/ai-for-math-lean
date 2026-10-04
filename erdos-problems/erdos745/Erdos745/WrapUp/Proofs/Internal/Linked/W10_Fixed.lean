module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W10_Sprinkling
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


namespace Erdos745.WrapUp.Proofs.Internal.W10_GIANT_Coupling

noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

open W10_GIANT_Bridges
open W10_GIANT_Closure
open W10_GIANT_Sprinkling
open W10_GIANT_SprinklingBounds
open W09_TREE_MASS_Finite

/-- The old mass measured in units of the large-component cutoff. -/
def oldMassRatio {n : ℕ} (G : Graph n) (h : ℕ) : ℝ :=
  ((vertices (largeFamily G h)).card : ℝ) / (h : ℝ)

private lemma oldMassRatio_nonneg {n h : ℕ} (G : Graph n) :
    0 ≤ oldMassRatio G h := by
  unfold oldMassRatio
  positivity

private lemma family_card_le_ratio {n h : ℕ} (G : Graph n) (hh : 0 < h) :
    ((largeFamily G h).card : ℝ) ≤ oldMassRatio G h := by
  have hcount := family_card_lower (G := G) (h := h)
    (R := largeFamily G h) (Finset.Subset.rfl)
  have hcountR : (h : ℝ) * (largeFamily G h).card ≤
      ((vertices (largeFamily G h)).card : ℝ) := by
    exact_mod_cast hcount
  exact (le_div_iff₀ (by exact_mod_cast hh)).2 (by
    simpa [mul_comm] using! hcountR)

private lemma family_nonempty_of_ratio_pos {n h : ℕ} (G : Graph n)
    (hx : 0 < oldMassRatio G h) : (largeFamily G h).Nonempty := by
  by_contra hne
  have he : largeFamily G h = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hne
  have hzero : oldMassRatio G h = 0 := by
    simp [oldMassRatio, he, vertices]
  linarith

/-- The accepted finite cut bound, expressed as a decaying function of old mass. -/
theorem finite_sprinkling_profile (hF : FiniteEnumerationStatement)
    {n h t : ℕ} (G : Graph n) {c : ℝ}
    (hh : 0 < h) (hcap : G.card + t ≤ capacity n)
    (hcap0 : 0 < capacity n)
    (hcoef : c ≤ (t : ℝ) * (h : ℝ) ^ 2 / (2 * (capacity n : ℝ)))
    (hx : 1 ≤ oldMassRatio G h) :
    growProb G t (fun H => ¬ oldLargeJoined G H h) ≤
      Real.exp (oldMassRatio G h *
        Real.exp (-c * oldMassRatio G h)) - 1 := by
  let x := oldMassRatio G h
  let K := largeFamily G h
  have hx0 : 0 ≤ x := oldMassRatio_nonneg G
  have hK : (K.card : ℝ) ≤ x := family_card_le_ratio G hh
  have hex : K.Nonempty := family_nonempty_of_ratio_pos G (by linarith)
  have hcapR : (0 : ℝ) < capacity n := by exact_mod_cast hcap0
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hcoefx := mul_le_mul_of_nonneg_right hcoef hx0
  have hidentity :
      ((t : ℝ) * (h : ℝ) ^ 2 / (2 * (capacity n : ℝ))) * x =
        (t : ℝ) * h * (vertices K).card / (2 * (capacity n : ℝ)) := by
    dsimp [x, oldMassRatio, K]
    field_simp [ne_of_gt hhR, ne_of_gt hcapR]
  have hmain : c * x ≤
      (t : ℝ) * h * (vertices K).card / (2 * (capacity n : ℝ)) := by
    rw [hidentity] at hcoefx
    exact hcoefx
  have hexp : Real.exp (-(t : ℝ) * h * (vertices K).card /
      (2 * (capacity n : ℝ))) ≤ Real.exp (-c * x) := by
    rw [Real.exp_le_exp]
    convert neg_le_neg hmain using 1 <;> ring
  have hproduct : (K.card : ℝ) *
      Real.exp (-(t : ℝ) * h * (vertices K).card /
        (2 * (capacity n : ℝ))) ≤ x * Real.exp (-c * x) := by
    calc
      (K.card : ℝ) * Real.exp (-(t : ℝ) * h * (vertices K).card /
          (2 * (capacity n : ℝ))) ≤ (K.card : ℝ) * Real.exp (-c * x) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ x * Real.exp (-c * x) :=
        mul_le_mul_of_nonneg_right hK (Real.exp_nonneg _)
  calc
    growProb G t (fun H => ¬ oldLargeJoined G H h) ≤
        Real.exp ((K.card : ℝ) *
          Real.exp (-(t : ℝ) * h * (vertices K).card /
            (2 * (capacity n : ℝ)))) - 1 := by
      simpa [K] using! finite_sprinkling_exp_bound hF G hcap hcap0 hex
    _ ≤ Real.exp (x * Real.exp (-c * x)) - 1 := by
      exact sub_le_sub_right (Real.exp_le_exp.mpr hproduct) 1

private lemma profile_tendsto_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => Real.exp (x * Real.exp (-c * x)) - 1)
      atTop (𝓝 0) := by
  have hf : Tendsto (fun x : ℝ => x * Real.exp (-c * x)) atTop (𝓝 0) := by
    simpa [Real.rpow_one] using!
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) c hc)
  simpa using! ((Real.continuous_exp.tendsto 0).comp hf).sub_const (1 : ℝ)

private lemma probM_nonneg {n M : ℕ} (A : Graph n → Prop) :
    0 ≤ probM n M A := by
  unfold probM
  positivity

private lemma expectM_nonneg {n M : ℕ} (f : Graph n → ℝ)
    (hf : ∀ G, 0 ≤ f G) : 0 ≤ expectM n M f := by
  unfold expectM
  exact div_nonneg (Finset.sum_nonneg (fun G _ => hf G)) (by positivity)

private lemma growProb_nonneg {n t : ℕ} (G : Graph n)
    (A : Graph n → Prop) : 0 ≤ growProb G t A := by
  unfold growProb
  positivity

private lemma probM_eq_on_fixed {n M : ℕ} (A B : Graph n → Prop)
    (hAB : ∀ G : Graph n, G.card = M → (A G ↔ B G)) :
    probM n M A = probM n M B := by
  have hf : (fixedGraphs n M).filter A = (fixedGraphs n M).filter B := by
    apply Finset.filter_congr
    intro G hG
    exact hAB G (Finset.mem_filter.mp hG).2
  simp only [probM, hf]

/-- Tightness at a scale smaller than the cutoff turns a diverging center into
arbitrarily large old mass in cutoff units. -/
theorem ratio_lower_tail_of_tight (M : NatSeq)
    (X : (n : ℕ) → Graph n → ℝ) (center scale cutoff : RealSeq)
    (htight : tightScaled M X center scale)
    (hcut : ∀ᶠ n : ℕ in atTop, 0 < cutoff n)
    (hcenter : Tendsto (fun n => center n / cutoff n) atTop atTop)
    (hscale : Tendsto (fun n => scale n / cutoff n) atTop (𝓝 0))
    (L : ℝ) :
    Tendsto (fun n => probM n (M n)
      (fun G => X n G / cutoff n < L)) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards with n
    exact lt_of_lt_of_le ha (probM_nonneg _)
  · intro d hd
    obtain ⟨K, hK, hdev⟩ := htight (d / 2) (by linarith)
    have hc := (tendsto_atTop.1 hcenter) (L + 1)
    have hs := (tendsto_order.1 hscale).2 (1 / K) (by positivity)
    filter_upwards [hcut, hc, hs, hdev] with n hn hc hs hdev
    have hsubset : ∀ G : Graph n,
        X n G / cutoff n < L →
          |X n G - center n| > K * scale n := by
      intro G hX
      have hX' := (div_lt_iff₀ hn).mp hX
      have hc' := (le_div_iff₀ hn).mp hc
      have hKsdiv : K * (scale n / cutoff n) < 1 := by
        have := (lt_div_iff₀ hK).mp hs
        nlinarith
      have hKs : K * scale n < cutoff n := by
        have hq : K * scale n / cutoff n < 1 := by
          convert hKsdiv using 1 <;> ring
        have ht := (div_lt_iff₀ hn).mp hq
        nlinarith
      have habs : center n - X n G ≤ |X n G - center n| := by
        calc
          center n - X n G = -(X n G - center n) := by ring
          _ ≤ |X n G - center n| := neg_le_abs _
      linarith
    have hmono := probM_mono (n := n) (M := M n) hsubset
    linarith

theorem oldMassRatio_lower_tail_of_tight (M : NatSeq)
    (h : NatSeq) (center scale : RealSeq)
    (htight : tightScaled M
      (fun n G => largeMass G (h n)) center scale)
    (hcut : ∀ᶠ n : ℕ in atTop, 0 < h n)
    (hcenter : Tendsto (fun n => center n / (h n : ℝ)) atTop atTop)
    (hscale : Tendsto (fun n => scale n / (h n : ℝ)) atTop (𝓝 0))
    (L : ℝ) :
    Tendsto (fun n => probM n (M n)
      (fun G => oldMassRatio G (h n) < L)) atTop (𝓝 0) := by
  have hh : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < h n :=
    hcut.mono (fun n hn => by exact_mod_cast hn)
  convert ratio_lower_tail_of_tight M
    (fun n G => largeMass G (h n)) center scale
    (fun n => (h n : ℝ)) htight hh hcenter hscale L using 1
  ext n
  congr 1
  funext G
  simp only [oldMassRatio, largeFamily_mass]

/-- Vanishing of the averaged owner-respecting connection failure, given
large old mass and a positive sprinkling coefficient. -/
theorem sprinkling_join_failure_tendsto_zero
    (hF : FiniteEnumerationStatement) (M₀ h t : NatSeq) {c : ℝ}
    (hc : 0 < c)
    (hsize : ∀ᶠ n : ℕ in atTop, M₀ n + t n ≤ capacity n)
    (hcut : ∀ᶠ n : ℕ in atTop, 0 < h n)
    (hcap : ∀ᶠ n : ℕ in atTop, 0 < capacity n)
    (hcoef : ∀ᶠ n : ℕ in atTop,
      c ≤ (t n : ℝ) * (h n : ℝ) ^ 2 / (2 * (capacity n : ℝ)))
    (htail : ∀ L : ℝ, Tendsto (fun n => probM n (M₀ n)
      (fun G => oldMassRatio G (h n) < L)) atTop (𝓝 0)) :
    Tendsto (fun n => expectM n (M₀ n) (fun G =>
      growProb G (t n) (fun H => ¬ oldLargeJoined G H (h n))))
      atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards with n
    exact lt_of_lt_of_le ha (expectM_nonneg _ (fun G =>
      growProb_nonneg (t := t n) G _))
  · intro d hd
    have hprofile := profile_tendsto_zero hc
    have hsmall := (tendsto_order.1 hprofile).2 (d / 2) (by linarith)
    obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.1 hsmall
    let L := max 1 L₀
    have hL : 1 ≤ L := le_max_left _ _
    have hL₀' : L₀ ≤ L := le_max_right _ _
    have hbad := (tendsto_order.1 (htail L)).2 (d / 2) (by linarith)
    filter_upwards [hsize, hcut, hcap, hcoef, hbad]
        with n hnsize hncut hncap hncoef hbad
    let Bad : Graph n → Prop := fun G =>
      G.card ≠ M₀ n ∨ oldMassRatio G (h n) < L
    have hgood : ∀ G : Graph n, ¬ Bad G →
        growProb G (t n) (fun H => ¬ oldLargeJoined G H (h n)) ≤ d / 2 := by
      intro G hG
      have hp := not_or.mp hG
      have hcard : G.card = M₀ n := not_not.mp hp.1
      have hx : L ≤ oldMassRatio G (h n) := le_of_not_gt hp.2
      have hg := finite_sprinkling_profile hF G hncut
        (by simpa [hcard] using! hnsize) hncap hncoef
        (hL.trans hx)
      exact hg.trans (hL₀ (oldMassRatio G (h n)) (hL₀'.trans hx)).le
    have havg := averaged_conditional_failure_bound hF
      (fun G H => ¬ oldLargeJoined G H (h n)) Bad (d / 2)
      (le_trans (Nat.le_add_right (M₀ n) (t n)) hnsize)
      (by linarith) hgood
    have heq : probM n (M₀ n) Bad = probM n (M₀ n)
        (fun G => oldMassRatio G (h n) < L) := by
      apply probM_eq_on_fixed
      intro G hG
      simp [Bad, hG]
    rw [heq] at havg
    linarith

/-- The exact finite bridge: one old large component exists, all old large
components join, and less than one cutoff of mass is newly large. -/
theorem unique_of_endpoint_control {n h : ℕ} {G H : Graph n}
    {c₀ c₁ a : ℝ} (hGH : G ⊆ H) (hh : 0 < h)
    (hlarge : 1 ≤ oldMassRatio G h)
    (hjoin : oldLargeJoined G H h)
    (hOld : |largeMass G h - c₀| ≤ a)
    (hFinal : |largeMass H h - c₁| ≤ a)
    (hgap : c₁ - c₀ + 2 * a < h) :
    countGE H h = 1 := by
  have hex : ∃ S ∈ components G, h ≤ S.card := by
    obtain ⟨S, hS⟩ := family_nonempty_of_ratio_pos G (by linarith)
    exact ⟨S, (Finset.mem_filter.mp hS).1, (Finset.mem_filter.mp hS).2⟩
  have hdiff : largeMass H h - largeMass G h < h := by
    have hO := (abs_le.mp hOld).1
    have hF := (abs_le.mp hFinal).2
    linarith
  exact unique_large_of_joined hGH hh hex hjoin hdiff

/-- Finite two-time budget. The old-graph-dependent join event remains inside
the expectation; only the final endpoint event is averaged as a fixed event. -/
theorem finite_unique_bad_bound (hF : FiniteEnumerationStatement)
    {n M₀ t h : ℕ} (c₀ c₁ a : ℝ)
    (hsize : M₀ + t ≤ capacity n) (hh : 0 < h)
    (hgap : c₁ - c₀ + 2 * a < h) :
    probM n (M₀ + t) (fun H => countGE H h ≠ 1) ≤
      probM n M₀ (fun G => |largeMass G h - c₀| > a) +
      probM n (M₀ + t) (fun H => |largeMass H h - c₁| > a) +
      probM n M₀ (fun G => oldMassRatio G h < 1) +
      expectM n M₀ (fun G => growProb G t
        (fun H => ¬ oldLargeJoined G H h)) := by
  let OldBad : Graph n → Prop := fun G => |largeMass G h - c₀| > a
  let FinalBad : Graph n → Prop := fun H => |largeMass H h - c₁| > a
  let MassBad : Graph n → Prop := fun G => oldMassRatio G h < 1
  let Bad : Graph n → Prop := fun G => OldBad G ∨ MassBad G
  have hpoint : ∀ G : Graph n,
      growProb G t (fun H => countGE H h ≠ 1) ≤
        (if Bad G then (1 : ℝ) else 0) +
        growProb G t FinalBad +
        growProb G t (fun H => ¬ oldLargeJoined G H h) := by
    intro G
    by_cases hB : Bad G
    · simp only [if_pos hB]
      have hle := growProb_le_one (t := t) G (fun H => countGE H h ≠ 1)
      have hf := growProb_nonneg (t := t) G FinalBad
      have hj := growProb_nonneg (t := t) G (fun H => ¬ oldLargeJoined G H h)
      linarith
    · have hnot := not_or.mp hB
      have hOld : |largeMass G h - c₀| ≤ a := le_of_not_gt hnot.1
      have hlarge : 1 ≤ oldMassRatio G h := le_of_not_gt hnot.2
      have hmono : growProb G t (fun H => countGE H h ≠ 1) ≤
          growProb G t (fun H => FinalBad H ∨
            ¬ oldLargeJoined G H h) := by
        apply growProb_mono_on_completions
        intro H hGH hfail
        by_contra hnone
        have hnot' := not_or.mp hnone
        exact hfail (unique_of_endpoint_control hGH hh hlarge
          (not_not.mp hnot'.2) hOld (le_of_not_gt hnot'.1) hgap)
      have hunion := growProb_union_le (G := G) (t := t) FinalBad
        (fun H => ¬ oldLargeJoined G H h)
      simpa [hB] using! hmono.trans hunion
  have haverage : probM n (M₀ + t) (fun H => countGE H h ≠ 1) ≤
      probM n M₀ Bad + probM n (M₀ + t) FinalBad +
      expectM n M₀ (fun G => growProb G t
        (fun H => ¬ oldLargeJoined G H h)) := by
    calc
      probM n (M₀ + t) (fun H => countGE H h ≠ 1) =
          expectM n M₀ (fun G => growProb G t
            (fun H => countGE H h ≠ 1)) :=
        (hF.2.2.1 n M₀ t _ hsize).symm
      _ ≤ expectM n M₀ (fun G =>
          (if Bad G then (1 : ℝ) else 0) +
          growProb G t FinalBad +
          growProb G t (fun H => ¬ oldLargeJoined G H h)) :=
        expectM_mono hpoint
      _ = probM n M₀ Bad + probM n (M₀ + t) FinalBad +
          expectM n M₀ (fun G => growProb G t
            (fun H => ¬ oldLargeJoined G H h)) := by
        have hi : expectM n M₀ (fun G => if Bad G then (1 : ℝ) else 0) =
            probM n M₀ Bad := by
          unfold expectM probM
          congr 1
          norm_cast
          rw [Finset.sum_boole]
          apply congrArg Finset.card
          ext G
          simp
        have hf : expectM n M₀ (fun G => growProb G t FinalBad) =
            probM n (M₀ + t) FinalBad := hF.2.2.1 n M₀ t FinalBad hsize
        rw [expectM_add, expectM_add]
        exact congrArg₂ (fun x y : ℝ => x + y) (congrArg₂ (· + ·) hi hf) rfl
  have hbad := probM_or_le (n := n) (M := M₀) OldBad MassBad
  dsimp [Bad, OldBad, FinalBad, MassBad] at haverage hbad
  linarith

/-- The asymptotic two-time criterion shared by the near and fixed branches. -/
theorem unique_bad_tendsto_zero_of_center_comparison
    (hF : FiniteEnumerationStatement) (M₀ M h t : NatSeq)
    (c₀ c₁ a : RealSeq)
    (hsize : ∀ᶠ n : ℕ in atTop, M₀ n + t n = M n ∧
      M n ≤ capacity n)
    (hcut : ∀ᶠ n : ℕ in atTop, 0 < h n)
    (hgap : ∀ᶠ n : ℕ in atTop,
      c₁ n - c₀ n + 2 * a n < h n)
    (hOld : Tendsto (fun n => probM n (M₀ n)
      (fun G => |largeMass G (h n) - c₀ n| > a n)) atTop (𝓝 0))
    (hFinal : Tendsto (fun n => probM n (M n)
      (fun H => |largeMass H (h n) - c₁ n| > a n)) atTop (𝓝 0))
    (hMass : Tendsto (fun n => probM n (M₀ n)
      (fun G => oldMassRatio G (h n) < 1)) atTop (𝓝 0))
    (hJoin : Tendsto (fun n => expectM n (M₀ n) (fun G =>
      growProb G (t n) (fun H => ¬ oldLargeJoined G H (h n))))
      atTop (𝓝 0)) :
    Tendsto (fun n => probM n (M n)
      (fun H => countGE H (h n) ≠ 1)) atTop (𝓝 0) := by
  have hbound : ∀ᶠ n : ℕ in atTop,
      probM n (M n) (fun H => countGE H (h n) ≠ 1) ≤
        probM n (M₀ n) (fun G => |largeMass G (h n) - c₀ n| > a n) +
        probM n (M n) (fun H => |largeMass H (h n) - c₁ n| > a n) +
        probM n (M₀ n) (fun G => oldMassRatio G (h n) < 1) +
        expectM n (M₀ n) (fun G => growProb G (t n)
          (fun H => ¬ oldLargeJoined G H (h n))) := by
    filter_upwards [hsize, hcut, hgap] with n hn hcutn hgapn
    rcases hn with ⟨heq, hcap⟩
    rw [← heq]
    exact finite_unique_bad_bound hF
      (c₀ n) (c₁ n) (a n) (by rw [heq]; exact hcap) hcutn hgapn
  have hsum := ((hOld.add hFinal).add hMass).add hJoin
  have hnonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ probM n (M n) (fun H => countGE H (h n) ≠ 1) := by
    filter_upwards with n
    exact probM_nonneg _
  exact squeeze_zero' hnonneg hbound (by simpa using! hsum)

end
end Erdos745.WrapUp.Proofs.Internal.W10_GIANT_Coupling


namespace Erdos745.WrapUp.Proofs.Internal.W10_GIANT_Numerics

noncomputable section
open Filter
open scoped Topology BigOperators
attribute [local instance] Classical.propDecidable

open W10_GIANT_Coupling
open W10_GIANT_Exclusions

def sprinkleTime (δ : ℝ) (n : ℕ) : ℕ := ⌊δ * (largeCutoff n : ℝ)⌋₊

lemma n23_pos {n : ℕ} (hn : 0 < n) : 0 < n23 n := by
  unfold n23
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _

lemma n23_cube {n : ℕ} (hn : 0 < n) : n23 n ^ 3 = (n : ℝ) ^ 2 := by
  have hnR : (0 : ℝ) ≤ n := by positivity
  unfold n23
  calc
    ((n : ℝ) ^ (2 / 3 : ℝ)) ^ 3 =
        ((n : ℝ) ^ (2 / 3 : ℝ)) ^ (3 : ℝ) := by
          exact (Real.rpow_natCast _ 3).symm
    _ = (n : ℝ) ^ ((2 / 3 : ℝ) * 3) :=
      (Real.rpow_mul hnR _ _).symm
    _ = (n : ℝ) ^ (2 : ℝ) := by congr 1; norm_num
    _ = (n : ℝ) ^ (2 : ℕ) := Real.rpow_natCast _ _

lemma cutoff_cube_ge_square {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ 2 ≤ (largeCutoff n : ℝ) ^ 3 := by
  rw [← n23_cube hn]
  exact pow_le_pow_left₀ (n23_pos hn).le (Nat.le_ceil _) _

lemma n23_div_n_tendsto_zero :
    Tendsto (fun n : ℕ => n23 n / (n : ℝ)) atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 3 : ℝ)))
      atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      tendsto_natCast_atTop_atTop
  apply hp.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold n23
  symm
  calc
    (n : ℝ) ^ (2 / 3 : ℝ) / n =
        (n : ℝ) ^ (2 / 3 : ℝ) / (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = (n : ℝ) ^ ((2 / 3 : ℝ) - 1) := (Real.rpow_sub hnR _ _).symm
    _ = (n : ℝ) ^ (-(1 / 3 : ℝ)) := by norm_num

lemma cutoff_div_n_tendsto_zero :
    Tendsto (fun n : ℕ => (largeCutoff n : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun n : ℕ => n23 n / (n : ℝ) + (n : ℝ)⁻¹)
      atTop (𝓝 0) := by simpa using! n23_div_n_tendsto_zero.add hinv
  apply squeeze_zero'
  · filter_upwards with n
    positivity
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hceil : (largeCutoff n : ℝ) ≤ n23 n + 1 :=
      (Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity) _)).le
    have := div_le_div_of_nonneg_right hceil hnR.le
    convert this using 1
  · convert hu using 1
    ext n
    ring

lemma n_div_cutoff_tendsto_atTop :
    Tendsto (fun n : ℕ => (n : ℝ) / (largeCutoff n : ℝ))
      atTop atTop := by
  apply tendsto_atTop.2
  intro B
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (largeCutoff n : ℝ) / (n : ℝ) < 1 / (max 1 B) :=
    (tendsto_order.1 cutoff_div_n_tendsto_zero).2 _ (by positivity)
  filter_upwards [hsmall, largeCutoff_eventually_pos,
    eventually_gt_atTop 0] with n hs hh hn
  have hhR : (0 : ℝ) < largeCutoff n := by exact_mod_cast hh
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hB : 0 < max 1 B := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hmul := (div_lt_iff₀ hnR).mp hs
  have hback : max 1 B < (n : ℝ) / (largeCutoff n : ℝ) := by
    apply (lt_div_iff₀ hhR).2
    have hmul' : (largeCutoff n : ℝ) < (n : ℝ) / max 1 B := by
      simpa [div_eq_mul_inv, mul_comm] using! hmul
    simpa [mul_comm] using! (lt_div_iff₀ hB).mp hmul'
  exact (le_max_right _ _).trans hback.le

lemma cutoff_sq_div_n_sq_tendsto_zero :
    Tendsto (fun n : ℕ => (largeCutoff n : ℝ) ^ 2 / (n : ℝ) ^ 2)
      atTop (𝓝 0) := by
  simpa [div_pow] using! cutoff_div_n_tendsto_zero.pow 2

lemma sqrt_n_div_cutoff_tendsto_zero :
    Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) / (largeCutoff n : ℝ))
      atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 6 : ℝ)))
      atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp
      tendsto_natCast_atTop_atTop
  apply squeeze_zero'
  · filter_upwards with n
    positivity
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have h23 : 0 < n23 n := n23_pos hn
    have hcut : n23 n ≤ (largeCutoff n : ℝ) := Nat.le_ceil _
    have hsqrt : Real.sqrt (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) :=
      Real.sqrt_eq_rpow _
    have hratio : Real.sqrt (n : ℝ) / n23 n =
        (n : ℝ) ^ (-(1 / 6 : ℝ)) := by
      rw [hsqrt]
      unfold n23
      calc
        (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ) =
            (n : ℝ) ^ ((1 / 2 : ℝ) - 2 / 3) :=
          (Real.rpow_sub hnR _ _).symm
        _ = (n : ℝ) ^ (-(1 / 6 : ℝ)) := by norm_num
    calc
      Real.sqrt (n : ℝ) / (largeCutoff n : ℝ) ≤
          Real.sqrt (n : ℝ) / n23 n := by gcongr
      _ = _ := hratio
  · exact hp

lemma sprinkleTime_le (δ : ℝ) (hδ : 0 ≤ δ) (n : ℕ) :
    (sprinkleTime δ n : ℝ) ≤ δ * (largeCutoff n : ℝ) := by
  exact Nat.floor_le (mul_nonneg hδ (by positivity))

lemma sprinkleTime_lower (δ : ℝ) (n : ℕ) :
    δ * (largeCutoff n : ℝ) - 1 < (sprinkleTime δ n : ℝ) := by
  exact sub_lt_iff_lt_add.mpr (Nat.lt_floor_add_one _)

lemma sprinkleTime_div_n_tendsto_zero (δ : ℝ) (hδ : 0 ≤ δ) :
    Tendsto (fun n : ℕ => (sprinkleTime δ n : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
  have hu : Tendsto (fun n : ℕ => δ * ((largeCutoff n : ℝ) / (n : ℝ)))
      atTop (𝓝 0) := by simpa using! cutoff_div_n_tendsto_zero.const_mul δ
  apply squeeze_zero'
  · filter_upwards with n
    positivity
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have ht := sprinkleTime_le δ hδ n
    have := div_le_div_of_nonneg_right ht hnR.le
    simpa [mul_div_assoc] using! this
  · exact hu

lemma sprinkleTime_le_M_eventually {M : NatSeq} {lam δ : ℝ}
    (hlam : 0 < lam) (hδ : 0 ≤ δ)
    (hdeg : Tendsto (degree M) atTop (𝓝 lam)) :
    ∀ᶠ n : ℕ in atTop, sprinkleTime δ n ≤ M n := by
  have ht := sprinkleTime_div_n_tendsto_zero δ hδ
  have htlo : ∀ᶠ n : ℕ in atTop,
      (sprinkleTime δ n : ℝ) / n < lam / 4 :=
    (tendsto_order.1 ht).2 _ (by linarith)
  have hdlo : ∀ᶠ n : ℕ in atTop, lam / 2 < degree M n :=
    (tendsto_order.1 hdeg).1 _ (by linarith)
  filter_upwards [htlo, hdlo, eventually_gt_atTop 0]
    with n ht hd hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hreal : (sprinkleTime δ n : ℝ) ≤ (M n : ℝ) := by
    unfold degree at hd
    have htm := (div_lt_iff₀ hnR).mp ht
    have hdm := (lt_div_iff₀ hnR).mp hd
    nlinarith
  exact_mod_cast hreal

lemma capacity_le_n_sq (n : ℕ) :
    (capacity n : ℝ) ≤ (n : ℝ) ^ 2 := by
  exact_mod_cast (Nat.choose_le_pow n 2)

lemma capacity_eventually_pos :
    ∀ᶠ n : ℕ in atTop, 0 < capacity n := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact Nat.choose_pos hn

lemma sprinkle_coefficient_lower (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      δ / 4 ≤ (sprinkleTime δ n : ℝ) * (largeCutoff n : ℝ) ^ 2 /
        (2 * (capacity n : ℝ)) := by
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (largeCutoff n : ℝ) ^ 2 / (n : ℝ) ^ 2 < δ / 2 :=
    (tendsto_order.1 cutoff_sq_div_n_sq_tendsto_zero).2 _ (by linarith)
  filter_upwards [hsmall, capacity_eventually_pos, eventually_gt_atTop 0]
    with n hs hc hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcR : (0 : ℝ) < capacity n := by exact_mod_cast hc
  have htime := sprinkleTime_lower δ n
  have hcube := cutoff_cube_ge_square hn
  have hcap := capacity_le_n_sq n
  have hsmall' := (div_lt_iff₀ (sq_pos_of_pos hnR)).mp hs
  have hnum : δ / 2 * (n : ℝ) ^ 2 ≤
      (sprinkleTime δ n : ℝ) * (largeCutoff n : ℝ) ^ 2 := by
    have ht : (δ * (largeCutoff n : ℝ) - 1) *
        (largeCutoff n : ℝ) ^ 2 ≤
        (sprinkleTime δ n : ℝ) * (largeCutoff n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right htime.le (sq_nonneg _)
    have hcubemul := mul_le_mul_of_nonneg_left hcube hδ.le
    nlinarith
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * capacity n)).2
  nlinarith

/-- Tightness on a scale negligible compared with a positive cutoff forces
every fixed fractional-cutoff deviation to vanish. -/
theorem deviation_tendsto_zero_of_tight (M : NatSeq)
    (X : (n : ℕ) → Graph n → ℝ) (center scale cutoff : RealSeq)
    (htight : tightScaled M X center scale)
    (hscale : Tendsto (fun n => scale n / cutoff n) atTop (𝓝 0))
    (hcut : ∀ᶠ n : ℕ in atTop, 0 < cutoff n)
    (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun n => probM n (M n)
      (fun G => |X n G - center n| > β * cutoff n))
      atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards with n
    exact lt_of_lt_of_le ha (by unfold probM; positivity)
  · intro d hd
    obtain ⟨K, hK, hdev⟩ := htight (d / 2) (by linarith)
    have hs : ∀ᶠ n : ℕ in atTop,
        scale n / cutoff n < β / K :=
      (tendsto_order.1 hscale).2 _ (div_pos hβ hK)
    filter_upwards [hdev, hs, hcut] with n hdev hs hc
    have hKs : K * scale n < β * cutoff n := by
      have h1 := (div_lt_iff₀ hc).mp hs
      have h2 : scale n < β * cutoff n / K := by
        convert h1 using 1; ring
      simpa [mul_comm] using! (lt_div_iff₀ hK).mp h2
    have hmono := W10_GIANT_Closure.probM_mono
      (n := n) (M := M n)
      (A := fun G => |X n G - center n| > β * cutoff n)
      (B := fun G => |X n G - center n| > K * scale n)
      (by intro G hG; linarith)
    linarith

end
end Erdos745.WrapUp.Proofs.Internal.W10_GIANT_Numerics


namespace Erdos745.WrapUp.Proofs.Internal.W10_GIANT_Fixed

noncomputable section
open Filter
open scoped Topology BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

open W10_GIANT_Numerics
open W10_GIANT_Coupling
open W10_GIANT_Concentration
open W10_GIANT_Exclusions
open W10_GIANT_Trees
open W10_GIANT_Sprinkling
open W10_GIANT_Bridges

private lemma giantFraction_pos (hRate : RateStatement) {lam : ℝ}
    (hlam : 1 < lam) : 0 < giantFraction lam := by
  obtain ⟨hconj, hlt, _⟩ := hRate.2.1 lam hlam
  unfold giantFraction
  have hdiv : conjugate lam / lam < 1 := by
    apply (div_lt_iff₀ (by linarith)).2
    linarith
  linarith

private lemma fixed_deriv_bound (hRate : RateStatement) {lam : ℝ}
    (hlam : 1 < lam) :
    ∃ D : ℝ, 0 < D ∧
      ∀ x ∈ Set.Icc ((lam + 1) / 2) ((3 * lam - 1) / 2),
        |deriv giantFraction x| ≤ D := by
  let a := (lam + 1) / 2
  let b := (3 * lam - 1) / 2
  have hsub : Set.Icc a b ⊆ Set.Ioi (1 : ℝ) := by
    intro x hx
    change 1 < x
    have ha : 1 < a := by dsimp [a]; linarith
    exact ha.trans_le hx.1
  have hc : ContinuousOn (deriv giantFraction) (Set.Icc a b) :=
    hRate.2.2.2.1.mono hsub
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc a b)).exists_bound_of_continuousOn
      (f := deriv giantFraction) hc
  refine ⟨max 1 C, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro x hx
  have := hC x hx
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_right _ _)

private lemma fixed_giantFraction_tendsto (hRate : RateStatement)
    {M : NatSeq} {lam : ℝ} (hlam : 1 < lam)
    (hdeg : Tendsto (degree M) atTop (𝓝 lam)) :
    Tendsto (fun n => giantFraction (degree M n))
      atTop (𝓝 (giantFraction lam)) := by
  have hc : ContinuousAt giantFraction lam :=
    hRate.2.2.1.continuousOn.continuousAt
      (IsOpen.mem_nhds isOpen_Ioi hlam)
  exact hc.tendsto.comp hdeg

private lemma fixed_center_div_cutoff_tendsto_atTop
    (hRate : RateStatement) {M : NatSeq} {lam : ℝ}
    (hlam : 1 < lam)
    (hdeg : Tendsto (degree M) atTop (𝓝 lam)) :
    Tendsto (fun n => giantCenter M n / (largeCutoff n : ℝ))
      atTop atTop := by
  have hp := fixed_giantFraction_tendsto hRate hlam hdeg
  have hmul := hp.pos_mul_atTop (giantFraction_pos hRate hlam)
    n_div_cutoff_tendsto_atTop
  apply hmul.congr'
  filter_upwards with n
  simp only [giantCenter]
  ring

private lemma fixed_scale_div_cutoff_tendsto_zero :
    Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) / (largeCutoff n : ℝ))
      atTop (𝓝 0) := sqrt_n_div_cutoff_tendsto_zero

private lemma fixed_endpoint_tight_bad
    (hF : FiniteEnumerationStatement)
    (hCyc : CyclicStructureStatement) (hTree : TreeMassStatement)
    (M : NatSeq) (lam : ℝ) (hM : admissible M)
    (hlam : 1 < lam)
    (hdeg : Tendsto (degree M) atTop (𝓝 lam)) :
    Tendsto (fun n => probM n (M n)
      (fun G => |largeMass G (largeCutoff n) - giantCenter M n| >
        (largeCutoff n : ℝ) / 4)) atTop (𝓝 0) := by
  have htight := fixed_largeMass_tight hF hCyc hTree M lam hM hlam hdeg
  have hbase := deviation_tendsto_zero_of_tight M
    (fun n G => largeMass G (largeCutoff n)) (giantCenter M)
    (fun n => Real.sqrt (n : ℝ)) (fun n => (largeCutoff n : ℝ))
    htight fixed_scale_div_cutoff_tendsto_zero
    (by filter_upwards [largeCutoff_eventually_pos] with n hn
        exact_mod_cast hn)
    (1 / 4) (by norm_num)
  simpa [div_eq_mul_inv, mul_comm] using! hbase

private lemma fixed_old_degree (M : NatSeq) (δ : ℝ) (hδ : 0 ≤ δ)
    (lam : ℝ) (hlam : 0 < lam)
    (hdeg : Tendsto (degree M) atTop (𝓝 lam)) :
    Tendsto (degree (fun n => M n - sprinkleTime δ n))
      atTop (𝓝 lam) := by
  have ht := sprinkleTime_div_n_tendsto_zero δ hδ
  have hdiff : Tendsto
      (fun n => degree M n - 2 * ((sprinkleTime δ n : ℝ) / (n : ℝ)))
      atTop (𝓝 lam) := by
    simpa using! hdeg.sub (ht.const_mul 2)
  apply hdiff.congr'
  filter_upwards [sprinkleTime_le_M_eventually hlam hδ hdeg,
    eventually_gt_atTop 0] with n hle hn
  have hcast : ((M n - sprinkleTime δ n : ℕ) : ℝ) =
      (M n : ℝ) - (sprinkleTime δ n : ℝ) := Nat.cast_sub hle
  unfold degree
  rw [hcast]
  ring

private lemma fixed_old_admissible {M : NatSeq} (hM : admissible M)
    (δ : ℝ) :
    admissible (fun n => M n - sprinkleTime δ n) := by
  filter_upwards [hM] with n hn
  exact (Nat.sub_le _ _).trans hn

private lemma fixed_center_gap
    (hRate : RateStatement) {M : NatSeq} {lam D δ : ℝ}
    (hlam : 1 < lam) (hD : 0 < D)
    (hderiv : ∀ x ∈ Set.Icc ((lam + 1) / 2) ((3 * lam - 1) / 2),
      |deriv giantFraction x| ≤ D)
    (hδ : 0 ≤ δ) (hsmall : 2 * D * δ < 1 / 2)
    (hdeg : Tendsto (degree M) atTop (𝓝 lam)) :
    ∀ᶠ n : ℕ in atTop,
      giantCenter M n -
        giantCenter (fun n => M n - sprinkleTime δ n) n +
          2 * ((largeCutoff n : ℝ) / 4) <
        (largeCutoff n : ℝ) := by
  let M₀ : NatSeq := fun n => M n - sprinkleTime δ n
  have hdeg0 := fixed_old_degree M δ hδ lam (by linarith) hdeg
  have hM : ∀ᶠ n : ℕ in atTop,
      degree M n ∈ Set.Icc ((lam + 1) / 2) ((3 * lam - 1) / 2) := by
    have hleft := (tendsto_order.1 hdeg).1 ((lam + 1) / 2) (by linarith)
    have hright := (tendsto_order.1 hdeg).2 ((3 * lam - 1) / 2) (by linarith)
    filter_upwards [hleft, hright] with n hl hr
    exact ⟨hl.le, hr.le⟩
  have hM0 : ∀ᶠ n : ℕ in atTop,
      degree M₀ n ∈ Set.Icc ((lam + 1) / 2) ((3 * lam - 1) / 2) := by
    have hleft := (tendsto_order.1 hdeg0).1 ((lam + 1) / 2) (by linarith)
    have hright := (tendsto_order.1 hdeg0).2 ((3 * lam - 1) / 2) (by linarith)
    filter_upwards [hleft, hright] with n hl hr
    exact ⟨hl.le, hr.le⟩
  have hdiff : ∀ x ∈ Set.Icc ((lam + 1) / 2) ((3 * lam - 1) / 2),
      DifferentiableAt ℝ giantFraction x := by
    intro x hx
    have hx1 : x ∈ Set.Ioi (1 : ℝ) := by
      change 1 < x
      linarith [hx.1]
    exact (hRate.2.2.1 x hx1).differentiableAt
      (IsOpen.mem_nhds isOpen_Ioi hx1)
  have hle := sprinkleTime_le_M_eventually (show 0 < lam by linarith) hδ hdeg
  filter_upwards [hM, hM0, hle, largeCutoff_eventually_pos,
    eventually_gt_atTop 0] with n hnM hnM0 ht hh hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hhR : (0 : ℝ) < largeCutoff n := by exact_mod_cast hh
  have hLip := Convex.norm_image_sub_le_of_norm_deriv_le hdiff
      (by intro x hx; simpa [Real.norm_eq_abs] using! hderiv x hx)
      (convex_Icc ((lam + 1) / 2) ((3 * lam - 1) / 2))
      hnM0 hnM
  have hdegeq : degree M n - degree M₀ n =
      2 * (sprinkleTime δ n : ℝ) / (n : ℝ) := by
    dsimp [M₀, degree]
    rw [Nat.cast_sub ht]
    ring
  have hdegnonneg : 0 ≤ degree M n - degree M₀ n := by
    rw [hdegeq]
    positivity
  have hcenter : giantCenter M n - giantCenter M₀ n ≤
      2 * D * (sprinkleTime δ n : ℝ) := by
    simp only [Real.norm_eq_abs, abs_of_nonneg hdegnonneg] at hLip
    have hLip' : giantFraction (degree M n) -
        giantFraction (degree M₀ n) ≤
        D * (degree M n - degree M₀ n) :=
      (le_abs_self _).trans hLip
    rw [hdegeq] at hLip'
    calc
      giantCenter M n - giantCenter M₀ n =
          (n : ℝ) * (giantFraction (degree M n) -
            giantFraction (degree M₀ n)) := by unfold giantCenter; ring
      _ ≤ (n : ℝ) * (D * (2 * (sprinkleTime δ n : ℝ) / (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hLip' hnR.le
      _ = 2 * D * (sprinkleTime δ n : ℝ) := by field_simp
  have htime := sprinkleTime_le δ hδ n
  have hupper : giantCenter M n - giantCenter M₀ n ≤
      2 * D * δ * (largeCutoff n : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left htime
      (by positivity : 0 ≤ 2 * D)
    nlinarith
  change giantCenter M n - giantCenter M₀ n +
    2 * ((largeCutoff n : ℝ) / 4) < (largeCutoff n : ℝ)
  have hmargin : 0 < (1 / 2 - 2 * D * δ) * (largeCutoff n : ℝ) :=
    mul_pos (by linarith) hhR
  nlinarith

/-- Fixed supercritical nonuniqueness vanishes after the exact two-time
sprinkling comparison. -/
theorem fixed_unique_bad_tendsto_zero
    (hF : FiniteEnumerationStatement) (hRate : RateStatement)
    (hCyc : CyclicStructureStatement) (hTree : TreeMassStatement)
    (M : NatSeq) (lam : ℝ) (hM : admissible M) (hlam : 1 < lam)
    (hdeg : Tendsto (degree M) atTop (𝓝 lam)) :
    Tendsto (fun n => probM n (M n)
      (fun G => countGE G (largeCutoff n) ≠ 1)) atTop (𝓝 0) := by
  obtain ⟨D, hD, hderiv⟩ := fixed_deriv_bound hRate hlam
  let δ : ℝ := 1 / (16 * D)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : 2 * D * δ < 1 / 2 := by
    dsimp [δ]
    field_simp [hD.ne']
    norm_num
  let t : NatSeq := sprinkleTime δ
  let M₀ : NatSeq := fun n => M n - t n
  let h : NatSeq := largeCutoff
  let a : RealSeq := fun n => (h n : ℝ) / 4
  have htime := sprinkleTime_le_M_eventually
    (show 0 < lam by linarith) hδ.le hdeg
  have hsize : ∀ᶠ n : ℕ in atTop,
      M₀ n + t n = M n ∧ M n ≤ capacity n := by
    filter_upwards [htime, hM] with n ht hm
    exact ⟨Nat.sub_add_cancel ht, hm⟩
  have hcut : ∀ᶠ n : ℕ in atTop, 0 < h n :=
    largeCutoff_eventually_pos
  have hdeg0 : Tendsto (degree M₀) atTop (𝓝 lam) := by
    simpa [M₀, t] using! fixed_old_degree M δ hδ.le lam
      (by linarith) hdeg
  have hM0 : admissible M₀ := fixed_old_admissible hM δ
  have hgap : ∀ᶠ n : ℕ in atTop,
      giantCenter M n - giantCenter M₀ n + 2 * a n < h n := by
    simpa [M₀, t, h, a] using!
      fixed_center_gap hRate hlam hD hderiv hδ.le hsmall hdeg
  have hOld : Tendsto (fun n => probM n (M₀ n)
      (fun G => |largeMass G (h n) - giantCenter M₀ n| > a n))
      atTop (𝓝 0) := by
    simpa [h, a] using! fixed_endpoint_tight_bad
      hF hCyc hTree M₀ lam hM0 hlam hdeg0
  have hFinal : Tendsto (fun n => probM n (M n)
      (fun G => |largeMass G (h n) - giantCenter M n| > a n))
      atTop (𝓝 0) := by
    simpa [h, a] using! fixed_endpoint_tight_bad
      hF hCyc hTree M lam hM hlam hdeg
  have hcenter := fixed_center_div_cutoff_tendsto_atTop hRate hlam hdeg0
  have hMass : Tendsto (fun n => probM n (M₀ n)
      (fun G => oldMassRatio G (h n) < 1)) atTop (𝓝 0) := by
    exact oldMassRatio_lower_tail_of_tight M₀ h
      (giantCenter M₀) (fun n => Real.sqrt (n : ℝ))
      (fixed_largeMass_tight hF hCyc hTree M₀ lam hM0 hlam hdeg0)
      hcut hcenter fixed_scale_div_cutoff_tendsto_zero 1
  have hJoin : Tendsto (fun n => expectM n (M₀ n) (fun G =>
      growProb G (t n) (fun H => ¬ oldLargeJoined G H (h n))))
      atTop (𝓝 0) := by
    apply sprinkling_join_failure_tendsto_zero hF M₀ h t
      (c := δ / 4) (by linarith)
    · exact hsize.mono fun n hn => hn.1.le.trans hn.2
    · exact hcut
    · exact capacity_eventually_pos
    · simpa [h, t] using! sprinkle_coefficient_lower δ hδ
    · intro L
      exact oldMassRatio_lower_tail_of_tight M₀ h
        (giantCenter M₀) (fun n => Real.sqrt (n : ℝ))
        (fixed_largeMass_tight hF hCyc hTree M₀ lam hM0 hlam hdeg0)
        hcut hcenter fixed_scale_div_cutoff_tendsto_zero L
  exact unique_bad_tendsto_zero_of_center_comparison hF M₀ M h t
    (giantCenter M₀) (giantCenter M) a
    hsize hcut hgap hOld hFinal hMass hJoin

/-- All three fixed supercritical giant conclusions, ready for the public
six-input assembly. -/
theorem fixed_giant_branch
    (hF : FiniteEnumerationStatement) (hRate : RateStatement)
    (hTuple : TupleEstimatesStatement)
    (hCyc : CyclicStructureStatement) (hTree : TreeMassStatement)
    (M : NatSeq) (lam : ℝ) (hM : admissible M) (hlam : 1 < lam)
    (hdeg : Tendsto (degree M) atTop (𝓝 lam)) :
    tightScaled M (fun n G => largeMass G (largeCutoff n)) (giantCenter M)
      (fun n => Real.sqrt (n : ℝ)) ∧
    tightScaled M (fun _ G => (rankSize G 1 : ℝ)) (giantCenter M)
      (fun n => Real.sqrt (n : ℝ)) ∧
    Tendsto (fun n => probM n (M n) separatedStructure) atTop (𝓝 1) := by
  exact fixed_giantBranch_of_unique_tree hF hCyc hTree M lam hM hlam hdeg
    (fixed_unique_bad_tendsto_zero hF hRate hCyc hTree M lam hM hlam hdeg)
    (fixed_tree_bad_tendsto_zero hF hTuple hM hlam hdeg)

end
end Erdos745.WrapUp.Proofs.Internal.W10_GIANT_Fixed
