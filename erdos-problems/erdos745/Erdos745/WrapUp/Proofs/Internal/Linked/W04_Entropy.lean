module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W04_Foundation
public import Erdos745.WrapUp.Proofs.Internal.Linked.W06_P02

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


/-! Signed rate and entropy inequalities used by the global W04 majorant. -/
namespace Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_RateEntropy

noncomputable section

open W04_TUPLES_Local

private theorem hasDerivAt_rate {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt rate (1 - 1 / x) x := by
  unfold rate
  convert! (((hasDerivAt_id x).sub_const 1).sub
    ((hasDerivAt_id x).log hx)) using 1

theorem rate_quadratic_lower {x : ℝ} (hx : 0 < x) (hx2 : x ≤ 2) :
    (x - 1) ^ 2 / 4 ≤ rate x := by
  by_cases hx1 : x ≤ 1
  · let g : ℝ → ℝ := fun y => rate y - (y - 1) ^ 2 / 2
    have hgderiv : ∀ y ∈ Set.Icc x 1,
        HasDerivAt g (-(y - 1) ^ 2 / y) y := by
      intro y hy
      have hy0 : y ≠ 0 := ne_of_gt (lt_of_lt_of_le hx hy.1)
      dsimp [g]
      have hsq := ((hasDerivAt_id y).sub_const 1).pow 2
      convert! (hasDerivAt_rate hy0).sub (hsq.div_const 2) using 1
      norm_num [id_eq]
      field_simp [hy0]
      ring
    have hanti : AntitoneOn g (Set.Icc x 1) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc x 1)
        (fun y hy => (hgderiv y hy).continuousAt.continuousWithinAt)
        (fun y hy =>
          (hgderiv y (interior_subset hy)).hasDerivWithinAt)
        (fun y hy => by
          have hy' := interior_subset hy
          have hypos : 0 < y := lt_of_lt_of_le hx hy'.1
          exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) hypos.le)
    have hmono := hanti (Set.left_mem_Icc.mpr hx1) (Set.right_mem_Icc.mpr hx1) hx1
    have hg1 : g 1 = 0 := by simp [g, rate]
    have hgx : 0 ≤ g x := by simpa [hg1] using! hmono
    dsimp [g] at hgx
    nlinarith [sq_nonneg (x - 1)]
  · have h1x : 1 ≤ x := le_of_not_ge hx1
    let g : ℝ → ℝ := fun y => rate y - (y - 1) ^ 2 / (2 * y)
    have hgderiv : ∀ y ∈ Set.Icc 1 x,
        HasDerivAt g ((y - 1) ^ 2 / (2 * y ^ 2)) y := by
      intro y hy
      have hy0 : y ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hy.1)
      dsimp [g]
      have hnum := ((hasDerivAt_id y).sub_const 1).pow 2
      have hden := (hasDerivAt_const y 2).mul (hasDerivAt_id y)
      convert! (hasDerivAt_rate hy0).sub (hnum.div hden (mul_ne_zero two_ne_zero hy0)) using 1
      norm_num [id_eq]
      field_simp [hy0]
      ring
    have hmono : MonotoneOn g (Set.Icc 1 x) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 1 x)
        (fun y hy => (hgderiv y hy).continuousAt.continuousWithinAt)
        (fun y hy =>
          (hgderiv y (interior_subset hy)).hasDerivWithinAt)
        (fun y hy => by positivity)
    have hmain := hmono (Set.left_mem_Icc.mpr h1x) (Set.right_mem_Icc.mpr h1x) h1x
    have hg1 : g 1 = 0 := by simp [g, rate]
    have hgx : 0 ≤ g x := by simpa [hg1] using! hmain
    dsimp [g] at hgx
    have hdiv : (x - 1) ^ 2 / 4 ≤ (x - 1) ^ 2 / (2 * x) := by
      have hs : 0 ≤ (x - 1) ^ 2 := sq_nonneg _
      apply div_le_div_of_nonneg_left hs (by positivity)
      nlinarith
    linarith

theorem rate_quadratic_lower_compact {x H : ℝ}
    (hx : 0 < x) (hH : 1 ≤ H) (hxH : x ≤ H) :
    (x - 1) ^ 2 / (4 * H) ≤ rate x := by
  by_cases hx2 : x ≤ 2
  · have h := rate_quadratic_lower hx hx2
    have hs : 0 ≤ (x - 1) ^ 2 := sq_nonneg _
    have hden : 4 ≤ 4 * H := by nlinarith
    exact le_trans (div_le_div_of_nonneg_left hs (by norm_num) hden) h
  · have h1x : 1 ≤ x := by linarith
    let g : ℝ → ℝ := fun y => rate y - (y - 1) ^ 2 / (2 * y)
    have hgderiv : ∀ y ∈ Set.Icc 1 x,
        HasDerivAt g ((y - 1) ^ 2 / (2 * y ^ 2)) y := by
      intro y hy
      have hy0 : y ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hy.1)
      dsimp [g]
      have hnum := ((hasDerivAt_id y).sub_const 1).pow 2
      have hden := (hasDerivAt_const y 2).mul (hasDerivAt_id y)
      convert! (hasDerivAt_rate hy0).sub
        (hnum.div hden (mul_ne_zero two_ne_zero hy0)) using 1
      norm_num [id_eq]
      field_simp [hy0]
      ring
    have hmono : MonotoneOn g (Set.Icc 1 x) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 1 x)
        (fun y hy => (hgderiv y hy).continuousAt.continuousWithinAt)
        (fun y hy => (hgderiv y (interior_subset hy)).hasDerivWithinAt)
        (fun y hy => by positivity)
    have hmain := hmono (Set.left_mem_Icc.mpr h1x)
      (Set.right_mem_Icc.mpr h1x) h1x
    have hg1 : g 1 = 0 := by simp [g, rate]
    have hgx : 0 ≤ g x := by simpa [hg1] using! hmain
    dsimp [g] at hgx
    have hs : 0 ≤ (x - 1) ^ 2 := sq_nonneg _
    have hden : 2 * x ≤ 4 * H := by nlinarith
    have hfrac : (x - 1) ^ 2 / (4 * H) ≤
        (x - 1) ^ 2 / (2 * x) := by
      exact div_le_div_of_nonneg_left hs (by positivity) hden
    linarith

theorem entropyCore_global_upper {lam t : ℝ}
    (hlo : (1 : ℝ) / 2 ≤ lam) (hhi : lam ≤ (3 : ℝ) / 2)
    (ht0 : 0 ≤ t) (ht : t ≤ (1 : ℝ) / 16) :
    entropyCore lam t ≤
      -(((lam - 1) ^ 2 * t + t ^ 3) / 64) := by
  let H : ℝ → ℝ := fun z =>
    entropyCore lam z + (1 / 4 : ℝ) *
      ((lam - 1) ^ 2 * z - (lam - 1) * z ^ 2 + z ^ 3 / 3)
  have hHderiv : ∀ z ∈ Set.Icc (0 : ℝ) t,
      HasDerivAt H
        (-rate ((lam - 2 * z) / (1 - z)) +
          (1 / 4 : ℝ) * (lam - 1 - z) ^ 2) z := by
    intro z hz
    have hz1 : z < 1 := by linarith [hz.2, ht]
    have h2z : 2 * z < lam := by linarith [hz.2, ht, hlo]
    dsimp [H]
    have hpoly :=
      (((hasDerivAt_const z ((lam - 1) ^ 2)).mul (hasDerivAt_id z)).sub
        (((hasDerivAt_const z (lam - 1)).mul ((hasDerivAt_id z).pow 2)))).add
        (((hasDerivAt_id z).pow 3).div_const 3)
    have hscaled := hpoly.const_mul (1 / 4)
    have hcore := hasDerivAt_entropyCore (lam := lam) (t := z)
      (lt_of_lt_of_le (by norm_num) hlo) hz1 h2z
    change HasDerivAt (entropyCore lam)
      (-rate ((lam - 2 * z) / (1 - z))) z at hcore
    convert! hcore.add hscaled using 1
    simp only [id_eq]
    ring
  have hderivNonpos : ∀ z ∈ Set.Ioo (0 : ℝ) t,
      -rate ((lam - 2 * z) / (1 - z)) +
          (1 / 4 : ℝ) * (lam - 1 - z) ^ 2 ≤ 0 := by
    intro z hz
    have hz0 : 0 ≤ z := hz.1.le
    have hzle : z ≤ (1 : ℝ) / 16 := le_trans hz.2.le ht
    have hden : 0 < 1 - z := by linarith
    let y : ℝ := (lam - 2 * z) / (1 - z)
    have hy0 : 0 < y := by
      dsimp [y]
      exact div_pos (by linarith) hden
    have hy2 : y ≤ 2 := by
      dsimp [y]
      apply (div_le_iff₀ hden).2
      linarith
    have hyrate := rate_quadratic_lower hy0 hy2
    have hyEq : y - 1 = (lam - 1 - z) / (1 - z) := by
      dsimp [y]
      field_simp [ne_of_gt hden]
      ring
    have hsq : (lam - 1 - z) ^ 2 ≤ (y - 1) ^ 2 := by
      rw [hyEq]
      have hdenOne : 1 - z ≤ 1 := by linarith
      have habs : |lam - 1 - z| ≤ |(lam - 1 - z) / (1 - z)| := by
        rw [abs_div, abs_of_pos hden]
        exact (le_div_iff₀ hden).2 (by
          have := abs_nonneg (lam - 1 - z)
          nlinarith)
      have hm := (abs_le_iff_mul_self_le).mp habs
      nlinarith
    dsimp [y] at hyrate
    nlinarith
  have hanti : AntitoneOn H (Set.Icc (0 : ℝ) t) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 t)
      (fun z hz => (hHderiv z hz).continuousAt.continuousWithinAt)
      (fun z hz =>
        (hHderiv z (interior_subset hz)).hasDerivWithinAt)
      (fun z hz => hderivNonpos z (by
        simpa only [interior_Icc, Set.mem_Ioo] using! hz))
  have hHt := hanti (Set.left_mem_Icc.mpr ht0) (Set.right_mem_Icc.mpr ht0) ht0
  have hH0 : H 0 = 0 := by simp [H]
  have hHtle : H t ≤ 0 := by simpa [hH0] using! hHt
  have hpoly :
      (1 / 16 : ℝ) * ((lam - 1) ^ 2 * t + t ^ 3) ≤
        (lam - 1) ^ 2 * t - (lam - 1) * t ^ 2 + t ^ 3 / 3 := by
    have hs := sq_nonneg (45 * (lam - 1) - 24 * t)
    have ht3 : t ^ 3 = t * t ^ 2 := by ring
    rw [ht3]
    nlinarith [mul_nonneg ht0 hs]
  dsimp [H] at hHtle
  nlinarith

end

end Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_RateEntropy


/-! Signed entropy for the independent-edge tuple envelope. -/
namespace Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_IndependentEntropy

noncomputable section

open W04_TUPLES_RateEntropy

def independentEntropy (lam t : ℝ) : ℝ :=
  -(1 - t) * Real.log (1 - t) + t * Real.log lam - lam * t + lam * t ^ 2 / 2

@[simp] theorem independentEntropy_zero (lam : ℝ) : independentEntropy lam 0 = 0 := by
  simp [independentEntropy]

theorem hasDerivAt_independentEntropy {lam t : ℝ}
    (hlam : 0 < lam) (ht : t < 1) :
    HasDerivAt (independentEntropy lam)
      (-rate (lam * (1 - t))) t := by
  unfold independentEntropy
  have hlog : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht)
  have hleft := ((hasDerivAt_const t (-1)).mul
    ((hasDerivAt_const t 1).sub (hasDerivAt_id t))).mul
      (((hasDerivAt_const t 1).sub (hasDerivAt_id t)).log hlog)
  have hrest := (((hasDerivAt_id t).mul_const (Real.log lam)).sub
    ((hasDerivAt_id t).const_mul lam)).add
      (((hasDerivAt_id t).mul (hasDerivAt_id t)).const_mul lam |>.div_const 2)
  have hleft' : HasDerivAt
      (fun z : ℝ => -(1 - z) * Real.log (1 - z))
      (Real.log (1 - t) + 1) t := by
    convert! hleft using 1
    · ext z
      simp [id_eq]
    · simp only [Pi.sub_apply, Pi.mul_apply, id_eq]
      field_simp [hlog]
      ring
  have hrest' : HasDerivAt
      (fun z : ℝ => z * Real.log lam - lam * z + lam * z * z / 2)
      (Real.log lam - lam + lam * t) t := by
    convert! hrest using 1
    · ext z
      simp [id_eq]
      ring
    · simp only [id_eq]
      ring
  convert! hleft'.add hrest' using 1
  · ext z
    simp [independentEntropy]
    ring
  · unfold rate
    rw [Real.log_mul hlam.ne' hlog]
    ring

private theorem entropyIntegral_lower {lam t : ℝ}
    (hlam : 0 < lam) (ht0 : 0 ≤ t) :
    (lam - 1) ^ 2 * t - (lam - 1) * lam * t ^ 2 + lam ^ 2 * t ^ 3 / 3 ≥
      (lam - 1) ^ 2 * t / 8 + lam ^ 2 * t ^ 3 / 24 := by
  have hs₁ := sq_nonneg (3 * (lam - 1) - 2 * lam * t)
  have hs₂ := sq_nonneg ((lam - 1) - lam * t / 2)
  nlinarith [mul_nonneg ht0 hs₁, mul_nonneg ht0 hs₂]

theorem independentEntropy_compact_upper {lam H t : ℝ}
    (hlam : 0 < lam) (hH : 1 ≤ H) (hlamH : lam ≤ H)
    (ht0 : 0 ≤ t) (ht : t < 1) :
    independentEntropy lam t ≤
      -(((lam - 1) ^ 2 * t / 8 + lam ^ 2 * t ^ 3 / 24) / (4 * H)) := by
  let G : ℝ → ℝ := fun z =>
    independentEntropy lam z +
      ((lam - 1) ^ 2 * z - (lam - 1) * lam * z ^ 2 +
        lam ^ 2 * z ^ 3 / 3) / (4 * H)
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hGderiv : ∀ z ∈ Set.Icc (0 : ℝ) t,
      HasDerivAt G
        (-rate (lam * (1 - z)) + (lam * (1 - z) - 1) ^ 2 / (4 * H)) z := by
    intro z hz
    have hz1 : z < 1 := lt_of_le_of_lt hz.2 ht
    have hmain := hasDerivAt_independentEntropy hlam hz1
    have hpoly :=
      ((((hasDerivAt_const z ((lam - 1) ^ 2)).mul (hasDerivAt_id z)).sub
        (((hasDerivAt_const z ((lam - 1) * lam)).mul
          ((hasDerivAt_id z).pow 2)))).add
        (((hasDerivAt_id z).pow 3).const_mul (lam ^ 2) |>.div_const 3)).div_const
          (4 * H)
    convert! hmain.add hpoly using 1
    all_goals simp only [id_eq]
    all_goals field_simp [ne_of_gt hHpos]
    all_goals ring
  have hnonpos : ∀ z ∈ Set.Ioo (0 : ℝ) t,
      -rate (lam * (1 - z)) + (lam * (1 - z) - 1) ^ 2 / (4 * H) ≤ 0 := by
    intro z hz
    have hz1 : z < 1 := lt_of_lt_of_le hz.2 ht.le
    have hy0 : 0 < lam * (1 - z) := mul_pos hlam (sub_pos.mpr hz1)
    have hyH : lam * (1 - z) ≤ H := by
      have hz0 : 0 ≤ z := hz.1.le
      have : 1 - z ≤ 1 := by linarith
      nlinarith [mul_le_mul_of_nonneg_left this hlam.le]
    linarith [rate_quadratic_lower_compact hy0 hH hyH]
  have hanti : AntitoneOn G (Set.Icc (0 : ℝ) t) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 t)
      (fun z hz => (hGderiv z hz).continuousAt.continuousWithinAt)
      (fun z hz => (hGderiv z (interior_subset hz)).hasDerivWithinAt)
      (fun z hz => hnonpos z (by simpa only [interior_Icc, Set.mem_Ioo] using! hz))
  have hGt := hanti (Set.left_mem_Icc.mpr ht0) (Set.right_mem_Icc.mpr ht0) ht0
  have hG0 : G 0 = 0 := by simp [G]
  have hGtle : G t ≤ 0 := by simpa [hG0] using! hGt
  have hpoly := entropyIntegral_lower hlam ht0
  dsimp [G] at hGtle
  have hden : 0 < 4 * H := by positivity
  nlinarith [div_le_div_of_nonneg_right hpoly hden.le]

theorem independentEntropy_near_large {lam t : ℝ}
    (hlo : (1 : ℝ) / 2 ≤ lam) (hhi : lam ≤ (3 : ℝ) / 2)
    (ht0 : 0 ≤ t) (ht : t < 1) (htLarge : (1 : ℝ) / 16 ≤ t) :
    independentEntropy lam t ≤ -t / 393216 := by
  have h := independentEntropy_compact_upper
    (lt_of_lt_of_le (by norm_num) hlo) (H := 2) (by norm_num) (by linarith)
    ht0 ht
  have hlamSq : (1 : ℝ) / 4 ≤ lam ^ 2 := by nlinarith
  have htSq : (1 : ℝ) / 256 ≤ t ^ 2 := by nlinarith
  have hprod : (1 : ℝ) / 1024 ≤ lam ^ 2 * t ^ 2 := by
    nlinarith [mul_le_mul hlamSq htSq (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hprod ht0]

theorem independentEntropy_separated {lam H delta t : ℝ}
    (hlam : 0 < lam) (hH : 1 ≤ H) (hlamH : lam ≤ H)
    (hdelta : 0 < delta) (hsep : delta ≤ |lam - 1|)
    (ht0 : 0 ≤ t) (ht : t < 1) :
    independentEntropy lam t ≤ -(delta ^ 2 / (32 * H)) * t := by
  have h := independentEntropy_compact_upper hlam hH hlamH ht0 ht
  have hs : delta ^ 2 ≤ (lam - 1) ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_pos hdelta] using! hsep
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hterm : delta ^ 2 * t / (32 * H) ≤
      (((lam - 1) ^ 2 * t / 8 + lam ^ 2 * t ^ 3 / 24) / (4 * H)) := by
    have hcubic : 0 ≤ lam ^ 2 * t ^ 3 / 24 := by positivity
    rw [show delta ^ 2 * t / (32 * H) =
        (delta ^ 2 * t / 8) / (4 * H) by field_simp; ring]
    exact div_le_div_of_nonneg_right (by
      nlinarith [mul_le_mul_of_nonneg_right hs ht0]) (by positivity)
  convert! le_trans h (neg_le_neg hterm) using 1 <;> ring

end

end Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_IndependentEntropy


/-!
Finite conditioning estimates for W04.  The key point is that no asymptotic
equivalence is used: the hypergeometric factor is one summand of a binomial
expansion, and the binomial mass at its mean is bounded below by an explicit
polynomial factor using the exact Stirling sequence.
-/
namespace Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_Conditioning

noncomputable section
open scoped BigOperators

open W04_TUPLES_Foundation
open Erdos745.WrapUp.Proofs.W06_POISSON

def binomialMass (N M : ℕ) : ℝ :=
  (N.choose M : ℝ) * ((M : ℝ) / N) ^ M *
    (((N - M : ℕ) : ℝ) / N) ^ (N - M)

theorem stirlingSeq_upper {m : ℕ} (hm : 0 < m) :
    Stirling.stirlingSeq m ≤ Stirling.stirlingSeq 1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  exact Stirling.stirlingSeq'_antitone (Nat.zero_le j)

theorem factorial_eq_stirlingSeq {m : ℕ} (hm : 0 < m) :
    (m.factorial : ℝ) = Stirling.stirlingSeq m *
      (Real.sqrt (2 * (m : ℝ)) * (((m : ℝ) / Real.exp 1) ^ m)) := by
  unfold Stirling.stirlingSeq
  have hsqrt : Real.sqrt (2 * (m : ℝ)) ≠ 0 := by positivity
  have hpow : ((m : ℝ) / Real.exp 1) ^ m ≠ 0 := by positivity
  field_simp

private theorem stirling_mass_identity
    {N M : ℕ} (hM : 0 < M) (hMN : M < N) :
    binomialMass N M =
      Stirling.stirlingSeq N /
          (Stirling.stirlingSeq M * Stirling.stirlingSeq (N - M)) *
        (Real.sqrt (2 * (N : ℝ)) /
          (Real.sqrt (2 * (M : ℝ)) * Real.sqrt (2 * ((N - M : ℕ) : ℝ)))) := by
  have hN : 0 < N := lt_of_lt_of_le hM (Nat.le_of_lt hMN)
  have hL : 0 < N - M := Nat.sub_pos_of_lt hMN
  have hMNle : M ≤ N := Nat.le_of_lt hMN
  have hsum : M + (N - M) = N := Nat.add_sub_of_le hMNle
  rw [binomialMass, Nat.cast_choose ℝ hMNle]
  rw [factorial_eq_stirlingSeq hN, factorial_eq_stirlingSeq hM,
    factorial_eq_stirlingSeq hL]
  have hNr : (N : ℝ) ≠ 0 := by positivity
  have hMr : (M : ℝ) ≠ 0 := by positivity
  have hLr : ((N - M : ℕ) : ℝ) ≠ 0 := by positivity
  have he : Real.exp 1 ≠ 0 := Real.exp_ne_zero _
  have hsN : Real.sqrt (2 * (N : ℝ)) ≠ 0 := by positivity
  have hsM : Real.sqrt (2 * (M : ℝ)) ≠ 0 := by positivity
  have hsL : Real.sqrt (2 * ((N - M : ℕ) : ℝ)) ≠ 0 := by positivity
  have hseqN : Stirling.stirlingSeq N ≠ 0 := by
    rw [Stirling.stirlingSeq]
    positivity
  have hseqM : Stirling.stirlingSeq M ≠ 0 := by
    rw [Stirling.stirlingSeq]
    positivity
  have hseqL : Stirling.stirlingSeq (N - M) ≠ 0 := by
    rw [Stirling.stirlingSeq]
    positivity
  rw [div_pow, div_pow, div_pow]
  field_simp
  simp only [div_pow]
  field_simp
  have hepow : Real.exp 1 ^ M * Real.exp 1 ^ (N - M) = Real.exp 1 ^ N := by
    rw [← pow_add, hsum]
  have hNpow : (N : ℝ) ^ M * (N : ℝ) ^ (N - M) = (N : ℝ) ^ N := by
    rw [← pow_add, hsum]
  calc
    (N : ℝ) ^ N * Real.exp 1 ^ M * Real.exp 1 ^ (N - M) =
        (N : ℝ) ^ N * (Real.exp 1 ^ M * Real.exp 1 ^ (N - M)) := by ring
    _ = (N : ℝ) ^ N * Real.exp 1 ^ N := by rw [hepow]
    _ = ((N : ℝ) ^ M * (N : ℝ) ^ (N - M)) * Real.exp 1 ^ N := by rw [hNpow]

theorem binomialMass_lower
    {N M : ℕ} (hM : 0 < M) (hMN : M < N) :
    1 / (8 * (N : ℝ)) ≤ binomialMass N M := by
  have hN : 0 < N := lt_of_lt_of_le hM (Nat.le_of_lt hMN)
  have hL : 0 < N - M := Nat.sub_pos_of_lt hMN
  have hMNle : M ≤ N := Nat.le_of_lt hMN
  have hLN : N - M ≤ N := Nat.sub_le _ _
  have hseqN : Real.sqrt Real.pi ≤ Stirling.stirlingSeq N :=
    Stirling.sqrt_pi_le_stirlingSeq hN.ne'
  have hseqM : Stirling.stirlingSeq M ≤ Stirling.stirlingSeq 1 :=
    stirlingSeq_upper hM
  have hseqL : Stirling.stirlingSeq (N - M) ≤ Stirling.stirlingSeq 1 :=
    stirlingSeq_upper hL
  have hseq1 : Stirling.stirlingSeq 1 = Real.exp 1 / Real.sqrt 2 :=
    Stirling.stirlingSeq_one
  have hseqN0 : 0 < Stirling.stirlingSeq N := by
    rw [Stirling.stirlingSeq]
    positivity
  have hseqM0 : 0 < Stirling.stirlingSeq M := by
    rw [Stirling.stirlingSeq]
    positivity
  have hseqL0 : 0 < Stirling.stirlingSeq (N - M) := by
    rw [Stirling.stirlingSeq]
    positivity
  have hrootN : 1 ≤ Real.sqrt (N : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hN.ne'))
  have hrootM : Real.sqrt (M : ℝ) ≤ Real.sqrt (N : ℝ) := by
    exact Real.sqrt_le_sqrt (by exact_mod_cast hMNle)
  have hrootL : Real.sqrt ((N - M : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) := by
    exact Real.sqrt_le_sqrt (by exact_mod_cast hLN)
  have hsqrtTwo : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hsqrtPi : 1 ≤ Real.sqrt Real.pi := by
    have hr := Real.sqrt_nonneg Real.pi
    nlinarith [Real.sq_sqrt Real.pi_nonneg, Real.pi_gt_three]
  have hexp : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans_le (by norm_num)
  rw [stirling_mass_identity hM hMN]
  have hseqRatio :
      (1 : ℝ) / 8 ≤ Stirling.stirlingSeq N /
        (Stirling.stirlingSeq M * Stirling.stirlingSeq (N - M)) := by
    rw [div_eq_mul_inv]
    have hden : Stirling.stirlingSeq M * Stirling.stirlingSeq (N - M) ≤ 9 / 2 := by
      rw [hseq1] at hseqM hseqL
      have hsqrt2sq : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hprod : Stirling.stirlingSeq M * Stirling.stirlingSeq (N - M) ≤
          (Real.exp 1 / Real.sqrt 2) * (Real.exp 1 / Real.sqrt 2) := by
        gcongr
      calc
        Stirling.stirlingSeq M * Stirling.stirlingSeq (N - M) ≤
            (Real.exp 1 / Real.sqrt 2) ^ 2 := by simpa [pow_two] using! hprod
        _ ≤ 9 / 2 := by
          rw [div_pow, hsqrt2sq]
          have hsq : (Real.exp 1) ^ 2 < 9 := by
            nlinarith [mul_pos (sub_pos.mpr hexp)
              (add_pos (by norm_num : (0 : ℝ) < 3) (Real.exp_pos 1))]
          linarith
    have hden0 : 0 < Stirling.stirlingSeq M * Stirling.stirlingSeq (N - M) :=
      mul_pos hseqM0 hseqL0
    apply (le_div_iff₀ hden0).2
    nlinarith
  have hrootRatio :
      1 / (N : ℝ) ≤ Real.sqrt (2 * (N : ℝ)) /
        (Real.sqrt (2 * (M : ℝ)) * Real.sqrt (2 * ((N - M : ℕ) : ℝ))) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hNr : 0 < (N : ℝ) := by positivity
    have hden : 0 <
        (Real.sqrt 2 * Real.sqrt (M : ℝ)) *
          (Real.sqrt 2 * Real.sqrt ((N - M : ℕ) : ℝ)) := by positivity
    apply (div_le_div_iff₀ hNr hden).2
    have hprodRoot : Real.sqrt (M : ℝ) * Real.sqrt ((N - M : ℕ) : ℝ) ≤ N := by
      calc
        _ ≤ Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) :=
          mul_le_mul hrootM hrootL (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ = N := Real.mul_self_sqrt (by positivity)
    have hdenle :
        (Real.sqrt 2 * Real.sqrt (M : ℝ)) *
          (Real.sqrt 2 * Real.sqrt ((N - M : ℕ) : ℝ)) ≤ 2 * N := by
      rw [show (Real.sqrt 2 * Real.sqrt (M : ℝ)) *
          (Real.sqrt 2 * Real.sqrt ((N - M : ℕ) : ℝ)) =
          (Real.sqrt 2 * Real.sqrt 2) *
            (Real.sqrt (M : ℝ) * Real.sqrt ((N - M : ℕ) : ℝ)) by ring,
        Real.mul_self_sqrt (by norm_num)]
      gcongr
    have hNtwo : 2 ≤ N := by omega
    have hnum : 2 ≤ Real.sqrt 2 * Real.sqrt (N : ℝ) := by
      rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * N by positivity)
      have hr := Real.sqrt_nonneg (2 * (N : ℝ))
      have hNtwoR : (2 : ℝ) ≤ N := by exact_mod_cast hNtwo
      nlinarith
    show 1 * ((Real.sqrt 2 * Real.sqrt (M : ℝ)) *
      (Real.sqrt 2 * Real.sqrt ((N - M : ℕ) : ℝ))) ≤
      (Real.sqrt 2 * Real.sqrt (N : ℝ)) * (N : ℝ)
    calc
      1 * ((Real.sqrt 2 * Real.sqrt (M : ℝ)) *
          (Real.sqrt 2 * Real.sqrt ((N - M : ℕ) : ℝ))) =
          (Real.sqrt 2 * Real.sqrt (M : ℝ)) *
            (Real.sqrt 2 * Real.sqrt ((N - M : ℕ) : ℝ)) := by ring
      _ ≤ (2 : ℝ) * (N : ℝ) := hdenle
      _ ≤ (Real.sqrt 2 * Real.sqrt (N : ℝ)) * (N : ℝ) := by
        exact mul_le_mul_of_nonneg_right hnum (by positivity)
  have hrootRatio0 : 0 ≤ Real.sqrt (2 * (N : ℝ)) /
      (Real.sqrt (2 * (M : ℝ)) * Real.sqrt (2 * ((N - M : ℕ) : ℝ))) := by
    positivity
  calc
    1 / (8 * (N : ℝ)) = (1 / 8) * (1 / (N : ℝ)) := by ring
    _ ≤ (1 / 8) *
        (Real.sqrt (2 * (N : ℝ)) /
          (Real.sqrt (2 * (M : ℝ)) * Real.sqrt (2 * ((N - M : ℕ) : ℝ)))) := by
      gcongr
    _ ≤ (Stirling.stirlingSeq N /
          (Stirling.stirlingSeq M * Stirling.stirlingSeq (N - M))) *
        (Real.sqrt (2 * (N : ℝ)) /
          (Real.sqrt (2 * (M : ℝ)) * Real.sqrt (2 * ((N - M : ℕ) : ℝ)))) := by
      exact mul_le_mul_of_nonneg_right hseqRatio hrootRatio0

theorem binomial_summand_le_one
    {A b : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (A.choose b : ℝ) * p ^ b * (1 - p) ^ (A - b) ≤ 1 := by
  by_cases hb : b ≤ A
  · have hmem : b ∈ Finset.range (A + 1) := Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hb)
    have hterm0 : ∀ j ∈ Finset.range (A + 1),
        0 ≤ p ^ j * (1 - p) ^ (A - j) * (A.choose j : ℝ) := by
      intro j hj
      exact mul_nonneg (mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _))
        (by positivity)
    calc
      (A.choose b : ℝ) * p ^ b * (1 - p) ^ (A - b) =
          p ^ b * (1 - p) ^ (A - b) * (A.choose b : ℝ) := by ring
      _ ≤ ∑ j ∈ Finset.range (A + 1),
          p ^ j * (1 - p) ^ (A - j) * (A.choose j : ℝ) :=
        Finset.single_le_sum hterm0 hmem
      _ = (p + (1 - p)) ^ A := (add_pow p (1 - p) A).symm
      _ = 1 := by simp
  · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hb)]
    norm_num

set_option maxHeartbeats 800000 in
theorem tupleMoment_le_conditionedIndependent
    (hF : FiniteEnumerationStatement)
    (n M q : ℕ) (ks : Fin q → ℕ)
    (hn : 4 ≤ n) (hMN : M < capacity n) (hMpos : 0 < M)
    (hpos : ∀ i, 0 < ks i) :
    tupleMoment n M q ks ≤
      8 * (capacity n : ℝ) *
        ((falling n (∑ i, ks i) : ℝ) *
          (∏ i, (cayley (ks i) : ℝ) / ((ks i).factorial : ℝ)) *
          ((M : ℝ) / capacity n) ^ ((∑ i, ks i) - q) *
          (1 - (M : ℝ) / capacity n) ^
            (capacity n - (n - ∑ i, ks i).choose 2 -
              ((∑ i, ks i) - q))) := by
  let K : ℕ := ∑ i, ks i
  let N : ℕ := capacity n
  let A : ℕ := (n - K).choose 2
  let r : ℕ := K - q
  let b : ℕ := M + q - K
  have hM : M ≤ capacity n := Nat.le_of_lt hMN
  have hNpos : 0 < N := by
    dsimp [N, capacity]
    exact Nat.choose_pos (by omega)
  have hMN' : M < N := by simpa [N] using! hMN
  by_cases hguard : K ≤ n ∧ K ≤ M + q
  · rcases hguard with ⟨hKn, hKM⟩
    by_cases hbA : b ≤ A
    · have hqK : q ≤ K := by
        have hcard := Finset.card_nsmul_le_sum
          (Finset.univ : Finset (Fin q)) ks 1 (by
            intro i hi
            exact Nat.succ_le_iff.mpr (hpos i))
        simpa [K] using! hcard
      have hrM : r ≤ M := by dsimp [r, K]; omega
      have hbEq : b = M - r := by dsimp [b, r, K]; omega
      have hArN : A + K ≤ N := by
        have hreal : ((A + K : ℕ) : ℝ) ≤ N := by
          dsimp [A, N]
          unfold capacity
          rw [Nat.cast_add, Nat.cast_choose_two, Nat.cast_sub hKn,
            Nat.cast_choose_two]
          have hKnR : (K : ℝ) ≤ n := by exact_mod_cast hKn
          nlinarith [mul_nonneg (show (0 : ℝ) ≤ K by positivity)
            (sub_nonneg.mpr hKnR),
            mul_nonneg (show (0 : ℝ) ≤ K by positivity)
              (by
                have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
                linarith : 0 ≤ 2 * (n : ℝ) - K - 3)]
        exact_mod_cast hreal
      have hrNA : r ≤ N - A := by
        have hrK : r ≤ K := Nat.sub_le _ _
        omega
      have hsumNM : N - M = (N - A - r) + (A - b) := by
        omega
      have hsumM : M = r + b := by rw [hbEq]; omega
      have hp0 : 0 ≤ (M : ℝ) / N := by positivity
      have hp1 : (M : ℝ) / N ≤ 1 := by
        exact (div_le_one (by positivity : (0 : ℝ) < N)).2 (by exact_mod_cast hM)
      have hmass := binomialMass_lower hMpos hMN'
      have hsummand := binomial_summand_le_one (A := A) (b := b) hp0 hp1
      rw [exactTupleFormula hF n M q ks hM hpos hKn hKM]
      have hchooseN : 0 < (N.choose M : ℝ) := by
        exact_mod_cast Nat.choose_pos hM
      have hmassPos : 0 < binomialMass N M := lt_of_lt_of_le (by positivity) hmass
      have hprod0 : 0 ≤ ∏ i, (cayley (ks i) : ℝ) / ((ks i).factorial : ℝ) := by
        positivity
      have hfall0 : 0 ≤ (falling n K : ℝ) := by positivity
      have hbase0 : 0 ≤ 1 - (M : ℝ) / N := sub_nonneg.mpr hp1
      have hmul : binomialMass N M *
          ((falling n K : ℝ) *
            (∏ i, (cayley (ks i) : ℝ) / ((ks i).factorial : ℝ)) *
            (A.choose b : ℝ) / (N.choose M : ℝ)) ≤
          binomialMass N M *
            (8 * (N : ℝ) *
              ((falling n K : ℝ) *
                (∏ i, (cayley (ks i) : ℝ) / ((ks i).factorial : ℝ)) *
                ((M : ℝ) / N) ^ r *
                (1 - (M : ℝ) / N) ^ (N - A - r))) := by
        calc
        binomialMass N M *
            ((falling n K : ℝ) *
              (∏ i, (cayley (ks i) : ℝ) / ((ks i).factorial : ℝ)) *
              (A.choose b : ℝ) / (N.choose M : ℝ)) =
          (falling n K : ℝ) *
              (∏ i, (cayley (ks i) : ℝ) / ((ks i).factorial : ℝ)) *
              (((A.choose b : ℝ) * ((M : ℝ) / N) ^ b *
                (1 - (M : ℝ) / N) ^ (A - b)) *
              (((M : ℝ) / N) ^ r *
                (1 - (M : ℝ) / N) ^ (N - A - r))) := by
          unfold binomialMass
          have hpM : ((M : ℝ) / N) ^ M =
              ((M : ℝ) / N) ^ r * ((M : ℝ) / N) ^ b := by
            rw [hsumM, pow_add]
          have hpN : (1 - (M : ℝ) / N) ^ (N - M) =
              (1 - (M : ℝ) / N) ^ (N - A - r) *
                (1 - (M : ℝ) / N) ^ (A - b) := by
            rw [hsumNM, pow_add]
          have hcomp : ((N - M : ℕ) : ℝ) / N = 1 - (M : ℝ) / N := by
            rw [Nat.cast_sub (Nat.le_of_lt hMN')]
            field_simp
          rw [hpM, hcomp, hpN]
          field_simp
        _ ≤ (falling n K : ℝ) *
              (∏ i, (cayley (ks i) : ℝ) / ((ks i).factorial : ℝ)) *
            (((M : ℝ) / N) ^ r *
              (1 - (M : ℝ) / N) ^ (N - A - r)) := by
          have hI0 : 0 ≤ ((M : ℝ) / N) ^ r *
              (1 - (M : ℝ) / N) ^ (N - A - r) := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hsummand hI0,
            mul_nonneg hfall0 hprod0]
        _ ≤ binomialMass N M *
            (8 * (N : ℝ) *
              ((falling n K : ℝ) *
                (∏ i, (cayley (ks i) : ℝ) / ((ks i).factorial : ℝ)) *
                ((M : ℝ) / N) ^ r *
                (1 - (M : ℝ) / N) ^ (N - A - r))) := by
          have hscale : 1 ≤ binomialMass N M * (8 * (N : ℝ)) := by
            have hs := mul_le_mul_of_nonneg_right hmass
              (show 0 ≤ 8 * (N : ℝ) by positivity)
            convert! hs using 1 <;> field_simp
          have hI0 : 0 ≤ (falling n K : ℝ) *
              (∏ i, (cayley (ks i) : ℝ) / ((ks i).factorial : ℝ)) *
              ((M : ℝ) / N) ^ r *
              (1 - (M : ℝ) / N) ^ (N - A - r) := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hscale hI0]
      calc
        (falling n K : ℝ) *
              (∏ i, (cayley (ks i) : ℝ) / ((ks i).factorial : ℝ)) *
              (A.choose b : ℝ) / (N.choose M : ℝ) =
            (binomialMass N M *
              ((falling n K : ℝ) *
                (∏ i, (cayley (ks i) : ℝ) / ((ks i).factorial : ℝ)) *
                (A.choose b : ℝ) / (N.choose M : ℝ))) /
              binomialMass N M := by field_simp
        _ ≤ (binomialMass N M *
              (8 * (N : ℝ) *
                ((falling n K : ℝ) *
                  (∏ i, (cayley (ks i) : ℝ) / ((ks i).factorial : ℝ)) *
                  ((M : ℝ) / N) ^ r *
                  (1 - (M : ℝ) / N) ^ (N - A - r)))) /
              binomialMass N M :=
          div_le_div_of_nonneg_right hmul hmassPos.le
        _ = 8 * (N : ℝ) *
                ((falling n K : ℝ) *
                  (∏ i, (cayley (ks i) : ℝ) / ((ks i).factorial : ℝ)) *
                  ((M : ℝ) / N) ^ r *
                  (1 - (M : ℝ) / N) ^ (N - A - r)) := by field_simp
    · rw [exactTupleFormula hF n M q ks hM hpos hKn hKM]
      rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hbA)]
      norm_num
      have hp1 : (M : ℝ) / capacity n ≤ 1 := by
        exact (div_le_one (by
          dsimp [capacity]
          positivity : (0 : ℝ) < capacity n)).2 (by exact_mod_cast hM)
      have hbase : 0 ≤ 1 - (M : ℝ) / capacity n := sub_nonneg.mpr hp1
      positivity
  · have hbad : ¬ ((∀ i, 0 < ks i) ∧ K ≤ n ∧ K ≤ M + q) := by
      simpa [hpos] using! hguard
    rw [tupleMoment_eq_zero_of_guard_failure hF n M q ks hM (by simpa [K] using! hbad)]
    have hp1 : (M : ℝ) / capacity n ≤ 1 := by
      exact (div_le_one (by
        dsimp [capacity]
        positivity : (0 : ℝ) < capacity n)).2 (by exact_mod_cast hM)
    have hbase : 0 ≤ 1 - (M : ℝ) / capacity n := sub_nonneg.mpr hp1
    positivity

end

end Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_Conditioning
