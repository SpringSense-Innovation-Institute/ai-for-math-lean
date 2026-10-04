module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W09_NearMean

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


namespace Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_NearVarianceSums

noncomputable section
open Filter
open scoped BigOperators Topology
open Erdos745.WrapUp.Proofs.W06_POISSON
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_Analytic
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_LocalMean
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_NearCutoff

private lemma near_mass_upper
    {n M k : ℕ} {C D e u : ℝ}
    (hn : 0 < n) (hk : 0 < k) (hlam : 0 < degreeAt n M)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (he : e = |degreeAt n M - 1|)
    (hlocal : tupleLocalBound n M 1 (fun _ => k) C)
    (hsmall : C * ((k : ℝ) / n + e * k ^ 2 / n +
      (k : ℝ) ^ 3 / (n : ℝ) ^ 2) ≤ 1)
    (hfloor : u ≤ rate (degreeAt n M))
    (hbound : leadingMassTerm n M k ≤
      D * n * Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
        Real.exp (-rate (degreeAt n M) * k)) :
    massTerm n M k ≤ 3 * D * n *
      (Real.rpow (k : ℝ) (-(3 / 2) : ℝ) * Real.exp (-u * k)) := by
  have hthree := local_one_upper hk hlam hlocal
    (e := C * ((k : ℝ) / n + e * k ^ 2 / n +
      (k : ℝ) ^ 3 / (n : ℝ) ^ 2)) (by rw [he])
    (by simpa [he] using! hsmall)
  have hlead := leadingMassTerm_bound_at_rate_floor hk hD hbound hfloor
  calc
    massTerm n M k ≤ 3 * leadingMassTerm n M k := hthree
    _ ≤ 3 * (D * n * Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
      Real.exp (-u * k)) := mul_le_mul_of_nonneg_left hlead (by norm_num)
    _ = _ := by ring

private lemma mass_sum_zero_bound {n M H : ℕ} {D u : ℝ}
    (hD : 0 ≤ D) (hu : 0 ≤ u)
    (hpoint : ∀ k ∈ Finset.Ico 1 (H + 1), massTerm n M k ≤
      3 * D * n * (Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
        Real.exp (-u * k))) :
    (∑ k ∈ Finset.Ico 1 (H + 1), massTerm n M k) ≤ 9 * D * n := by
  have htail := negThreeHalfTail_le H 1 (by omega)
  have hsum : (∑ k ∈ Finset.Ico 1 (H + 1),
      Real.rpow (k : ℝ) (-(3 / 2) : ℝ) * Real.exp (-u * k)) ≤ 3 := by
    calc
      _ ≤ negThreeHalfTail H 1 := by
        unfold negThreeHalfTail
        apply Finset.sum_le_sum
        intro k hk
        have hk0 : 0 ≤ (k : ℝ) := by positivity
        have hexp : Real.exp (-u * k) ≤ 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (by nlinarith)
        simpa using! mul_le_of_le_one_right
          (Real.rpow_nonneg hk0 _) hexp
      _ ≤ 3 := by simpa using! htail
  calc
    _ ≤ 3 * D * n * (∑ k ∈ Finset.Ico 1 (H + 1),
      Real.rpow (k : ℝ) (-(3 / 2) : ℝ) * Real.exp (-u * k)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum hpoint
    _ ≤ 3 * D * n * 3 := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

private lemma mass_sum_one_bound (hA : AnalyticSumsStatement)
    {n M H : ℕ} {D u : ℝ}
    (hD : 0 ≤ D) (hu : 0 < u) (hu1 : u ≤ 1)
    (hpoint : ∀ k ∈ Finset.Ico 1 (H + 1), massTerm n M k ≤
      3 * D * n * (Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
        Real.exp (-u * k))) :
    (∑ k ∈ Finset.Ico 1 (H + 1), (k : ℝ) * massTerm n M k) ≤
      3 * D * n *
        (Classical.choose (analytic_power_bound hA (-(1 / 2) : ℝ)
          (by norm_num)) * Real.rpow u (-(1 / 2) : ℝ)) := by
  have hsum := finite_power_exp_sum_le hA
    (beta := (-(1 / 2) : ℝ)) (by norm_num) hu hu1 H
  calc
    _ ≤ 3 * D * n * (∑ k ∈ Finset.Ico 1 (H + 1),
        Real.rpow (k : ℝ) (-(1 / 2) : ℝ) * Real.exp (-u * k)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k hk
      have hkpos : 0 < k := (Finset.mem_Ico.mp hk).1
      have hmul := mul_le_mul_of_nonneg_left (hpoint k hk)
        (by positivity : (0 : ℝ) ≤ k)
      calc
        (k : ℝ) * massTerm n M k ≤
            (k : ℝ) * (3 * D * n *
              (Real.rpow (k : ℝ) (-(3 / 2) : ℝ) * Real.exp (-u * k))) := hmul
        _ = 3 * D * n *
            (Real.rpow (k : ℝ) (-(1 / 2) : ℝ) * Real.exp (-u * k)) := by
          rw [← mul_rpow_neg_three_half k hkpos]
          ring
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [show -(-(1 / 2 : ℝ)) - 1 = -(1 / 2 : ℝ) by norm_num]
          using! hsum) (by positivity)

private lemma mass_sum_two_bound (hA : AnalyticSumsStatement)
    {n M H : ℕ} {D u : ℝ}
    (hD : 0 ≤ D) (hu : 0 < u) (hu1 : u ≤ 1)
    (hpoint : ∀ k ∈ Finset.Ico 1 (H + 1), massTerm n M k ≤
      3 * D * n * (Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
        Real.exp (-u * k))) :
    (∑ k ∈ Finset.Ico 1 (H + 1), (k : ℝ) ^ 2 * massTerm n M k) ≤
      3 * D * n *
        (Classical.choose (analytic_power_bound hA (1 / 2 : ℝ)
          (by norm_num)) * Real.rpow u (-(3 / 2) : ℝ)) := by
  have hsum := finite_power_exp_sum_le hA
    (beta := (1 / 2 : ℝ)) (by norm_num) hu hu1 H
  calc
    _ ≤ 3 * D * n * (∑ k ∈ Finset.Ico 1 (H + 1),
        Real.rpow (k : ℝ) (1 / 2 : ℝ) * Real.exp (-u * k)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k hk
      have hkpos : 0 < k := (Finset.mem_Ico.mp hk).1
      have hmul := mul_le_mul_of_nonneg_left (hpoint k hk)
        (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 2)
      calc
        (k : ℝ) ^ 2 * massTerm n M k ≤
            (k : ℝ) ^ 2 * (3 * D * n *
              (Real.rpow (k : ℝ) (-(3 / 2) : ℝ) * Real.exp (-u * k))) := hmul
        _ = 3 * D * n *
            (Real.rpow (k : ℝ) (1 / 2 : ℝ) * Real.exp (-u * k)) := by
          rw [← sq_mul_rpow_neg_three_half k hkpos]
          ring
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [show -(1 / 2 : ℝ) - 1 = -(3 / 2 : ℝ) by norm_num]
          using! hsum) (by positivity)

lemma near_mass_weighted_sums
    (hRate : RateStatement) (hT : TupleEstimatesStatement)
    (hA : AnalyticSumsStatement)
    {M : NatSeq} (hbare : bareSuper M)
    (B : ℝ) (hB : 4 < B) :
    ∃ A₀ A₁ A₂ : ℝ, 0 < A₀ ∧ 0 < A₁ ∧ 0 < A₂ ∧
      ∀ᶠ n in atTop,
        (∑ k ∈ Finset.Ico 1 (nearCutoff B M n + 1),
          massTerm n (M n) k) ≤ A₀ * n ∧
        (∑ k ∈ Finset.Ico 1 (nearCutoff B M n + 1),
          (k : ℝ) * massTerm n (M n) k) ≤ A₁ * n / epsilon M n ∧
        (∑ k ∈ Finset.Ico 1 (nearCutoff B M n + 1),
          (k : ℝ) ^ 2 * massTerm n (M n) k) ≤
            A₂ * n / epsilon M n ^ 3 := by
  obtain ⟨C₁, κ₁, hC₁, hκ₁, n₀, htuple⟩ := hT.1 1 (by omega)
  let D := Classical.choose leadingMassTerm_bound
  let E₁ := Classical.choose
    (analytic_power_bound hA (-(1 / 2) : ℝ) (by norm_num))
  let E₂ := Classical.choose
    (analytic_power_bound hA (1 / 2 : ℝ) (by norm_num))
  have hD : 0 < D := (Classical.choose_spec leadingMassTerm_bound).1
  have hE₁ : 0 < E₁ :=
    (Classical.choose_spec (analytic_power_bound hA (-(1 / 2) : ℝ) (by norm_num))).1
  have hE₂ : 0 < E₂ :=
    (Classical.choose_spec (analytic_power_bound hA (1 / 2 : ℝ) (by norm_num))).1
  refine ⟨9 * D, 6 * D * E₁, 24 * D * E₂,
    by positivity, by positivity, by positivity, ?_⟩
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
  have hpoint : ∀ k ∈ Finset.Ico 1 (nearCutoff B M n + 1),
      massTerm n (M n) k ≤ 3 * D * n *
        (Real.rpow (k : ℝ) (-(3 / 2) : ℝ) * Real.exp (-u * k)) := by
    intro k hk
    have hkpos : 0 < k := (Finset.mem_Ico.mp hk).1
    have hkK : k ≤ nearCutoff B M n :=
      Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hk).2
    have hkr : (k : ℝ) ≤ (nearCutoff B M n : ℝ) := by exact_mod_cast hkK
    have hsum : (∑ i : Fin 1, ((fun _ => k) i : ℝ)) ≤ (n : ℝ) / 16 := by
      simp only [Fin.sum_univ_one]
      have hcast : ((2 * nearCutoff B M n : ℕ) : ℝ) =
          2 * (nearCutoff B M n : ℝ) := by norm_num
      rw [hcast] at hpair
      linarith
    have hlocal := (htuple n (M n) (fun _ => k) hn₀ hcap hlo hhi
      (fun _ => hkpos)).2 hsum
    have hsmall := one_error_below_cutoff hn he.le hC₁.le hkK herr
    have hbound := (Classical.choose_spec leadingMassTerm_bound).2
      n (M n) k hkpos hlo
    exact near_mass_upper hn hkpos (lt_of_lt_of_le (by norm_num) hlo)
      hC₁.le hD.le (by rfl) hlocal hsmall hfloor hbound
  have hzero := mass_sum_zero_bound hD.le hu.le hpoint
  have hone := mass_sum_one_bound hA hD.le hu hu1 hpoint
  have htwo := mass_sum_two_bound hA hD.le hu hu1 hpoint
  have hpow1 := rpow_sq_quarter_neg_half he
  have hpow2 := rpow_sq_quarter_neg_three_half he
  change Real.rpow (e ^ 2 / 4) (-(1 / 2) : ℝ) = 2 / e at hpow1
  change Real.rpow (e ^ 2 / 4) (-(3 / 2) : ℝ) = 8 / e ^ 3 at hpow2
  constructor
  · simpa only [mul_assoc] using! hzero
  constructor
  · calc
      _ ≤ 3 * D * n * (E₁ * Real.rpow u (-(1 / 2) : ℝ)) := by
        simpa only [D, E₁] using! hone
      _ = (6 * D * E₁) * n / e := by
        rw [show u = e ^ 2 / 4 from rfl, hpow1]
        ring
  · calc
      _ ≤ 3 * D * n * (E₂ * Real.rpow u (-(3 / 2) : ℝ)) := by
        simpa only [D, E₂] using! htwo
      _ = (24 * D * E₂) * n / e ^ 3 := by
        rw [show u = e ^ 2 / 4 from rfl, hpow2]
        ring

end
end Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_NearVarianceSums


namespace Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_NearVariance

noncomputable section
open Filter
open scoped BigOperators Topology
open Erdos745.WrapUp.Proofs.W06_POISSON
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_Finite
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_Analytic
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_NearCutoff
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_NearVarianceSums

private lemma mixed_cutoff_error
    {M : NatSeq} {B C : ℝ} {n k l : ℕ}
    (hn : 0 < n) (he : 0 ≤ epsilon M n) (hC : 0 ≤ C)
    (hk : k ≤ nearCutoff B M n) (hl : l ≤ nearCutoff B M n)
    (hcut : cutoffError 2 C B M n ≤ 1) :
    C * (((k : ℝ) + l) / n + epsilon M n * k * l / n +
      (k : ℝ) * l * (k + l) / (n : ℝ) ^ 2) ≤ 1 := by
  let K : ℝ := nearCutoff B M n
  let x : ℝ := (k : ℝ) + l
  have hkr : (k : ℝ) ≤ K := by
    change (k : ℝ) ≤ (nearCutoff B M n : ℝ)
    exact_mod_cast hk
  have hlr : (l : ℝ) ≤ K := by
    change (l : ℝ) ≤ (nearCutoff B M n : ℝ)
    exact_mod_cast hl
  have hk0 : 0 ≤ (k : ℝ) := by positivity
  have hl0 : 0 ≤ (l : ℝ) := by positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hxK : x ≤ 2 * K := by dsimp [x]; linarith
  have hkl : (k : ℝ) * l ≤ x ^ 2 := by dsimp [x]; nlinarith
  have hklx : (k : ℝ) * l * x ≤ x ^ 3 := by
    exact mul_le_mul_of_nonneg_right hkl hx |>.trans_eq (by ring)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hfirst : x / n ≤ (2 * K) / n := by gcongr
  have hsecond : epsilon M n * (k : ℝ) * l / n ≤
      epsilon M n * (2 * K) ^ 2 / n := by
    apply div_le_div_of_nonneg_right _ hnR.le
    have := mul_le_mul_of_nonneg_left hkl he
    have hsq : x ^ 2 ≤ (2 * K) ^ 2 := by gcongr
    nlinarith
  have hthird : (k : ℝ) * l * x / (n : ℝ) ^ 2 ≤
      (2 * K) ^ 3 / (n : ℝ) ^ 2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    have hcube : x ^ 3 ≤ (2 * K) ^ 3 := by gcongr
    linarith
  have hmain : x / n + epsilon M n * k * l / n +
      (k : ℝ) * l * x / (n : ℝ) ^ 2 ≤
      (2 * K) / n + epsilon M n * (2 * K) ^ 2 / n +
        (2 * K) ^ 3 / (n : ℝ) ^ 2 := by linarith
  calc
    _ = C * (x / n + epsilon M n * k * l / n +
      (k : ℝ) * l * x / (n : ℝ) ^ 2) := rfl
    _ ≤ C * ((2 * K) / n + epsilon M n * (2 * K) ^ 2 / n +
      (2 * K) ^ 3 / (n : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hmain hC
    _ ≤ 1 := by simpa [cutoffError, K] using! hcut

private lemma pair_covariance_bound
    {n M k l : ℕ} {C e : ℝ}
    (hk : 0 < k) (hl : 0 < l)
    (hJk : 0 < momentOne n M k) (hJl : 0 < momentOne n M l)
    (hJ2 : 0 < momentTwo n M k l)
    (hlog : |Real.log (momentTwo n M k l /
      (momentOne n M k * momentOne n M l))| ≤
      C * (((k : ℝ) + l) / n + |degreeAt n M - 1| * k * l / n +
        (k : ℝ) * l * (k + l) / (n : ℝ) ^ 2))
    (he : e = |degreeAt n M - 1|)
    (hsmall : C * (((k : ℝ) + l) / n + e * k * l / n +
      (k : ℝ) * l * (k + l) / (n : ℝ) ^ 2) ≤ 1) :
    (k : ℝ) * l * momentTwo n M k l -
      massTerm n M k * massTerm n M l ≤
      2 * C * massTerm n M k * massTerm n M l *
        (((k : ℝ) + l) / n + e * k * l / n +
          (k : ℝ) * l * (k + l) / (n : ℝ) ^ 2) := by
  have hrel := mixed_relative hk hl hJk hJl hJ2 hlog
    (e := C * (((k : ℝ) + l) / n + e * k * l / n +
      (k : ℝ) * l * (k + l) / (n : ℝ) ^ 2))
    (by rw [he]) (by simpa [he] using! hsmall)
  exact (le_abs_self _).trans (by simpa [he] using! hrel)

private lemma double_sum_mul (s : Finset ℕ) (f g : ℕ → ℝ) :
    (∑ k ∈ s, ∑ l ∈ s, f k * g l) =
      (∑ k ∈ s, f k) * (∑ l ∈ s, g l) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]

private lemma double_sum_const (s : Finset ℕ) (c : ℝ)
    (f : ℕ → ℕ → ℝ) :
    (∑ k ∈ s, ∑ l ∈ s, c * f k l) =
      c * (∑ k ∈ s, ∑ l ∈ s, f k l) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum]

private lemma covariance_sum_algebra
    (s : Finset ℕ) (a : ℕ → ℝ) (n e C : ℝ)
    (hn : 0 < n) (hC : 0 ≤ C) (he : 0 ≤ e)
    (ha : ∀ k ∈ s, 0 ≤ a k) :
    (∑ k ∈ s, ∑ l ∈ s,
      2 * C * a k * a l *
        (((k : ℝ) + l) / n + e * k * l / n +
          (k : ℝ) * l * (k + l) / n ^ 2)) =
      2 * C * (2 * (∑ k ∈ s, a k) *
        (∑ k ∈ s, (k : ℝ) * a k) / n +
        e * (∑ k ∈ s, (k : ℝ) * a k) ^ 2 / n +
        2 * (∑ k ∈ s, (k : ℝ) * a k) *
          (∑ k ∈ s, (k : ℝ) ^ 2 * a k) / n ^ 2) := by
  have h0 : (∑ k ∈ s, ∑ l ∈ s,
      a k * a l * ((k : ℝ) + l)) =
      2 * (∑ k ∈ s, a k) * (∑ k ∈ s, (k : ℝ) * a k) := by
    calc
      _ = (∑ k ∈ s, ∑ l ∈ s, ((k : ℝ) * a k) * a l) +
          (∑ k ∈ s, ∑ l ∈ s, a k * ((l : ℝ) * a l)) := by
        simp only [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro l hl
        ring
      _ = (∑ k ∈ s, (k : ℝ) * a k) * (∑ l ∈ s, a l) +
          (∑ k ∈ s, a k) * (∑ l ∈ s, (l : ℝ) * a l) := by
        rw [double_sum_mul, double_sum_mul]
      _ = _ := by ring
  have h1 : (∑ k ∈ s, ∑ l ∈ s,
      a k * a l * ((k : ℝ) * l)) =
      (∑ k ∈ s, (k : ℝ) * a k) ^ 2 := by
    calc
      _ = ∑ k ∈ s, ∑ l ∈ s,
          ((k : ℝ) * a k) * ((l : ℝ) * a l) := by
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro l hl
        ring
      _ = _ := by rw [double_sum_mul]; ring
  have h2 : (∑ k ∈ s, ∑ l ∈ s,
      a k * a l * ((k : ℝ) * l * ((k : ℝ) + l))) =
      2 * (∑ k ∈ s, (k : ℝ) * a k) *
        (∑ k ∈ s, (k : ℝ) ^ 2 * a k) := by
    calc
      _ = (∑ k ∈ s, ∑ l ∈ s,
            ((k : ℝ) ^ 2 * a k) * ((l : ℝ) * a l)) +
          (∑ k ∈ s, ∑ l ∈ s,
            ((k : ℝ) * a k) * ((l : ℝ) ^ 2 * a l)) := by
        simp only [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro l hl
        ring
      _ = (∑ k ∈ s, (k : ℝ) ^ 2 * a k) *
            (∑ l ∈ s, (l : ℝ) * a l) +
          (∑ k ∈ s, (k : ℝ) * a k) *
            (∑ l ∈ s, (l : ℝ) ^ 2 * a l) := by
        rw [double_sum_mul, double_sum_mul]
      _ = _ := by ring
  calc
    _ = (∑ k ∈ s, ∑ l ∈ s,
          (2 * C / n) * (a k * a l * ((k : ℝ) + l))) +
        (∑ k ∈ s, ∑ l ∈ s,
          (2 * C * e / n) * (a k * a l * ((k : ℝ) * l))) +
        (∑ k ∈ s, ∑ l ∈ s,
          (2 * C / n ^ 2) *
            (a k * a l * ((k : ℝ) * l * ((k : ℝ) + l)))) := by
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _ = (2 * C / n) * (∑ k ∈ s, ∑ l ∈ s,
          a k * a l * ((k : ℝ) + l)) +
        (2 * C * e / n) * (∑ k ∈ s, ∑ l ∈ s,
          a k * a l * ((k : ℝ) * l)) +
        (2 * C / n ^ 2) * (∑ k ∈ s, ∑ l ∈ s,
          a k * a l * ((k : ℝ) * l * ((k : ℝ) + l))) := by
      rw [double_sum_const, double_sum_const, double_sum_const]
    _ = 2 * C * ((∑ k ∈ s, ∑ l ∈ s,
        a k * a l * ((k : ℝ) + l)) / n +
        e * (∑ k ∈ s, ∑ l ∈ s,
          a k * a l * ((k : ℝ) * l)) / n +
        (∑ k ∈ s, ∑ l ∈ s,
          a k * a l * ((k : ℝ) * l * ((k : ℝ) + l))) / n ^ 2) := by ring
    _ = _ := by rw [h0, h1, h2]

private lemma variance_from_weighted_sums
    {n M : ℕ} (s : Finset ℕ) {e C A₀ A₁ A₂ : ℝ}
    (hn : 0 < n) (he : 0 < e) (he1 : e ≤ 1)
    (hw : 1 ≤ (n : ℝ) * e ^ 3)
    (hC : 0 < C) (hA₀ : 0 < A₀) (hA₁ : 0 < A₁) (hA₂ : 0 < A₂)
    (hNorm : expectM n M (fun _ => 1) = 1)
    (hs0 : (∑ k ∈ s, massTerm n M k) ≤ A₀ * n)
    (hs1 : (∑ k ∈ s, (k : ℝ) * massTerm n M k) ≤ A₁ * n / e)
    (hs2 : (∑ k ∈ s, (k : ℝ) ^ 2 * massTerm n M k) ≤ A₂ * n / e ^ 3)
    (hcov : ∀ k ∈ s, ∀ l ∈ s,
      (k : ℝ) * l * momentTwo n M k l -
        massTerm n M k * massTerm n M l ≤
      2 * C * massTerm n M k * massTerm n M l *
        (((k : ℝ) + l) / n + e * k * l / n +
          (k : ℝ) * l * (k + l) / (n : ℝ) ^ 2)) :
    varianceM n M (fun G => treeMassSum G s) ≤
      (A₁ + 2 * C * (2 * A₀ * A₁ + A₁ ^ 2 + 2 * A₁ * A₂)) * n / e := by
  let S₀ := ∑ k ∈ s, massTerm n M k
  let S₁ := ∑ k ∈ s, (k : ℝ) * massTerm n M k
  let S₂ := ∑ k ∈ s, (k : ℝ) ^ 2 * massTerm n M k
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hS₀ : 0 ≤ S₀ := Finset.sum_nonneg (fun k _ => massTerm_nonneg n M k)
  have hS₁ : 0 ≤ S₁ := Finset.sum_nonneg (fun k _ => mul_nonneg (by positivity)
    (massTerm_nonneg n M k))
  have hS₂ : 0 ≤ S₂ := Finset.sum_nonneg (fun k _ => mul_nonneg (by positivity)
    (massTerm_nonneg n M k))
  have hvar := variance_treeMassSum_eq s hNorm
  have hmajor : varianceM n M (fun G => treeMassSum G s) ≤
      S₁ + 2 * C * (2 * S₀ * S₁ / n + e * S₁ ^ 2 / n +
        2 * S₁ * S₂ / (n : ℝ) ^ 2) := by
    rw [hvar]
    have hdiag : (∑ k ∈ s, (k : ℝ) ^ 2 * tupleMoment n M 1 (fun _ => k)) = S₁ := by
      dsimp [S₁]
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [massTerm, momentOne]
      ring
    rw [hdiag]
    have hpair : (∑ k ∈ s, ∑ l ∈ s,
        ((k : ℝ) * l * tupleMoment n M 2 (pairSizes k l) -
          ((k : ℝ) * tupleMoment n M 1 (fun _ => k)) *
            ((l : ℝ) * tupleMoment n M 1 (fun _ => l)))) ≤
        ∑ k ∈ s, ∑ l ∈ s,
          2 * C * massTerm n M k * massTerm n M l *
            (((k : ℝ) + l) / n + e * k * l / n +
              (k : ℝ) * l * (k + l) / (n : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      simpa only [momentTwo, massTerm, momentOne] using! hcov k hk l hl
    have halg := covariance_sum_algebra s (massTerm n M) n e C hnR hC.le
      he.le (fun k _ => massTerm_nonneg n M k)
    rw [halg] at hpair
    simpa [add_comm, add_left_comm, add_assoc, S₀, S₁, S₂] using!
      add_le_add_left hpair S₁
  have hnum :
      2 * S₀ * S₁ / n + e * S₁ ^ 2 / n +
        2 * S₁ * S₂ / (n : ℝ) ^ 2 ≤
      (2 * A₀ * A₁ + A₁ ^ 2 + 2 * A₁ * A₂) * n / e := by
    have h0 : 2 * S₀ * S₁ / n ≤ 2 * A₀ * A₁ * n / e := by
      have hm := mul_le_mul hs0 hs1 hS₁ (by positivity)
      calc
        _ = 2 * (S₀ * S₁) / n := by ring
        _ ≤ 2 * ((A₀ * n) * (A₁ * n / e)) / n := by gcongr
        _ = _ := by field_simp [hnR.ne', he.ne']
    have h1 : e * S₁ ^ 2 / n ≤ A₁ ^ 2 * n / e := by
      have hm : S₁ ^ 2 ≤ (A₁ * n / e) ^ 2 := by gcongr
      calc
        _ ≤ e * (A₁ * n / e) ^ 2 / n := by gcongr
        _ = _ := by field_simp [hnR.ne', he.ne']
    have h2 : 2 * S₁ * S₂ / (n : ℝ) ^ 2 ≤ 2 * A₁ * A₂ * n / e := by
      have hm := mul_le_mul hs1 hs2 hS₂ (by positivity)
      have hden : 0 < (n : ℝ) ^ 2 := by positivity
      have he4 : 0 < e ^ 4 := by positivity
      have hw' : 1 / e ^ 4 ≤ (n : ℝ) / e := by
        apply (div_le_div_iff₀ he4 he).2
        nlinarith [mul_le_mul_of_nonneg_left hw he.le]
      have hraw : 2 * S₁ * S₂ / (n : ℝ) ^ 2 ≤
          2 * A₁ * A₂ / e ^ 4 := by
        calc
          _ = 2 * (S₁ * S₂) / (n : ℝ) ^ 2 := by ring
          _ ≤ 2 * ((A₁ * n / e) * (A₂ * n / e ^ 3)) /
              (n : ℝ) ^ 2 := by gcongr
          _ = _ := by field_simp [hnR.ne', he.ne']
      exact hraw.trans (by
        calc
          _ = (2 * A₁ * A₂) * (1 / e ^ 4) := by ring
          _ ≤ (2 * A₁ * A₂) * ((n : ℝ) / e) :=
            mul_le_mul_of_nonneg_left hw' (by positivity)
          _ = _ := by ring)
    calc
      _ ≤ 2 * A₀ * A₁ * n / e + A₁ ^ 2 * n / e +
        2 * A₁ * A₂ * n / e := by linarith
      _ = _ := by ring
  calc
    _ ≤ S₁ + 2 * C * (2 * S₀ * S₁ / n + e * S₁ ^ 2 / n +
        2 * S₁ * S₂ / (n : ℝ) ^ 2) := hmajor
    _ ≤ A₁ * n / e + 2 * C *
        ((2 * A₀ * A₁ + A₁ ^ 2 + 2 * A₁ * A₂) * n / e) := by
      exact add_le_add hs1 (mul_le_mul_of_nonneg_left hnum (by positivity))
    _ = _ := by ring

lemma near_truncated_variance_bound
    (hF : FiniteEnumerationStatement) (hRate : RateStatement)
    (hT : TupleEstimatesStatement) (hA : AnalyticSumsStatement)
    {M : NatSeq} (hbare : bareSuper M)
    (B : ℝ) (hB : 4 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      varianceM n (M n) (fun G =>
        treeMassSum G (Finset.Ico 1 (nearCutoff B M n + 1))) ≤
        C * n / epsilon M n := by
  obtain ⟨A₀, A₁, A₂, hA₀, hA₁, hA₂, hsums⟩ :=
    near_mass_weighted_sums hRate hT hA hbare B hB
  obtain ⟨C₁, κ₁, hC₁, hκ₁, n₁, htuple₁⟩ := hT.1 1 (by omega)
  obtain ⟨C₂, κ₂, hC₂, hκ₂, n₂, htuple₂⟩ := hT.1 2 (by omega)
  obtain ⟨Cmix, hCmix, nmix, hmixed⟩ := hT.2.1
  let C := A₁ + 2 * Cmix * (2 * A₀ * A₁ + A₁ ^ 2 + 2 * A₁ * A₂)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hcommon := near_common_cutoff_ranges hRate hbare B C₁ C₂ Cmix hB
    (max n₁ (max n₂ nmix))
  filter_upwards [hcommon, hsums] with n h hsum
  obtain ⟨hn, hn₀, hcap, hKpos, hKlarge, hpair, hlo, hhi,
    heq, he, he1, hw, hrate, herr₁, herr₂, herrmix⟩ := h
  have hn₁ : n₁ ≤ n := le_trans (Nat.le_max_left ..) hn₀
  have hn₂ : n₂ ≤ n := le_trans (Nat.le_trans (Nat.le_max_left ..)
    (Nat.le_max_right ..)) hn₀
  have hnmix : nmix ≤ n := le_trans (Nat.le_trans (Nat.le_max_right ..)
    (Nat.le_max_right ..)) hn₀
  have hnorm := hF.1 n (M n) hcap
  have hcov : ∀ k ∈ Finset.Ico 1 (nearCutoff B M n + 1),
      ∀ l ∈ Finset.Ico 1 (nearCutoff B M n + 1),
      (k : ℝ) * l * momentTwo n (M n) k l -
        massTerm n (M n) k * massTerm n (M n) l ≤
      2 * Cmix * massTerm n (M n) k * massTerm n (M n) l *
        (((k : ℝ) + l) / n + epsilon M n * k * l / n +
          (k : ℝ) * l * (k + l) / (n : ℝ) ^ 2) := by
    intro k hk l hl
    have hkpos : 0 < k := (Finset.mem_Ico.mp hk).1
    have hlpos : 0 < l := (Finset.mem_Ico.mp hl).1
    have hkK : k ≤ nearCutoff B M n :=
      Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hk).2
    have hlK : l ≤ nearCutoff B M n :=
      Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hl).2
    have hsumk : (∑ i : Fin 1, ((fun _ => k) i : ℝ)) ≤ (n : ℝ) / 16 := by
      simp only [Fin.sum_univ_one]
      have hkr : (k : ℝ) ≤ (nearCutoff B M n : ℝ) := by exact_mod_cast hkK
      have hcast : ((2 * nearCutoff B M n : ℕ) : ℝ) =
          2 * (nearCutoff B M n : ℝ) := by norm_num
      rw [hcast] at hpair
      linarith
    have hsuml : (∑ i : Fin 1, ((fun _ => l) i : ℝ)) ≤ (n : ℝ) / 16 := by
      simp only [Fin.sum_univ_one]
      have hlr : (l : ℝ) ≤ (nearCutoff B M n : ℝ) := by exact_mod_cast hlK
      have hcast : ((2 * nearCutoff B M n : ℕ) : ℝ) =
          2 * (nearCutoff B M n : ℝ) := by norm_num
      rw [hcast] at hpair
      linarith
    have hJk : 0 < momentOne n (M n) k := by
      exact (htuple₁ n (M n) (fun _ => k) hn₁ hcap hlo hhi
        (fun _ => hkpos)).2 hsumk |>.1
    have hJl : 0 < momentOne n (M n) l := by
      exact (htuple₁ n (M n) (fun _ => l) hn₁ hcap hlo hhi
        (fun _ => hlpos)).2 hsuml |>.1
    have hpairRange := pair_size_below_cutoff hkK hlK hpair
    have hJ2 : 0 < momentTwo n (M n) k l := by
      have hlocal := (htuple₂ n (M n) (pairSizes k l) hn₂ hcap hlo hhi
        (by intro i; fin_cases i <;> simp [pairSizes, hkpos, hlpos])).2
      have hsum : (∑ i : Fin 2, (pairSizes k l i : ℝ)) ≤ (n : ℝ) / 16 := by
        simpa [pairSizes, Fin.sum_univ_two, Nat.cast_add] using! hpairRange
      exact (hlocal hsum).1
    have hlog := hmixed n (M n) k l hnmix hcap hlo hhi hkpos hlpos
      hpairRange
    have hsmall := mixed_cutoff_error hn he.le hCmix.le hkK hlK herrmix
    exact pair_covariance_bound hkpos hlpos hJk hJl hJ2
      (by simpa only [momentOne, momentTwo] using! hlog)
      (by rfl) hsmall
  have hwidth : 1 ≤ (n : ℝ) * epsilon M n ^ 3 := by
    simpa [widthParameter] using! hw
  have hbound := variance_from_weighted_sums
    (s := Finset.Ico 1 (nearCutoff B M n + 1)) hn he he1 hwidth
    hCmix hA₀ hA₁ hA₂ hnorm hsum.1 hsum.2.1 hsum.2.2 hcov
  simpa only [C] using! hbound

end
end Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_NearVariance


namespace Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_NearVarianceTail

noncomputable section
open Filter
open scoped BigOperators Topology
open Erdos745.WrapUp.Proofs.W06_POISSON
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_Finite
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_Analytic
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_NearCutoff
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_NearTail
open Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_NearVariance

private lemma rpow_scaled_sq_neg_half {a e : ℝ} (ha : 0 < a) (he : 0 < e) :
    Real.rpow (a * e ^ 2) (-(1 / 2) : ℝ) =
      Real.rpow a (-(1 / 2) : ℝ) * e⁻¹ := by
  calc
    Real.rpow (a * e ^ 2) (-(1 / 2) : ℝ) =
        Real.rpow a (-(1 / 2) : ℝ) *
          Real.rpow (e ^ 2) (-(1 / 2) : ℝ) :=
      Real.mul_rpow ha.le (sq_nonneg e)
    _ = Real.rpow a (-(1 / 2) : ℝ) * e⁻¹ := by
      congr 1
      calc
        Real.rpow (e ^ 2) (-(1 / 2) : ℝ) =
            Real.rpow (Real.rpow e 2) (-(1 / 2) : ℝ) := by
          exact congrArg (fun x : ℝ => Real.rpow x (-(1 / 2) : ℝ))
            (Real.rpow_two e).symm
        _ = Real.rpow e ((2 : ℝ) * (-(1 / 2) : ℝ)) :=
          (Real.rpow_mul he.le 2 (-(1 / 2) : ℝ)).symm
        _ = e⁻¹ := by
          norm_num
          rw [Real.rpow_neg he.le, Real.rpow_one]

private lemma global_one_diagonal_bound {n M k : ℕ} {C κ : ℝ}
    (hk : 0 < k) (hC : 0 ≤ C) (hκ : 0 < κ)
    (hg : tupleGlobalBound n M 1 (fun _ => k) C κ) :
    (k : ℝ) ^ 2 * momentOne n M k ≤
      C * n * (Real.rpow (k : ℝ) (-(1 / 2) : ℝ) *
        Real.exp (-κ * |degreeAt n M - 1| ^ 2 * k)) := by
  have hmass := global_one_mass_bound hk hC hκ hg
  calc
    (k : ℝ) ^ 2 * momentOne n M k = (k : ℝ) * massTerm n M k := by
      unfold massTerm
      ring
    _ ≤ (k : ℝ) *
        (C * n * Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
          Real.exp (-κ * |degreeAt n M - 1| ^ 2 * k)) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by
      rw [← mul_rpow_neg_three_half k hk]
      ring

private lemma global_pair_mass_bound {n M k l : ℕ} {C κ : ℝ}
    (hk : 0 < k) (hl : 0 < l) (hC : 0 ≤ C) (hκ : 0 < κ)
    (hg : tupleGlobalBound n M 2 (pairSizes k l) C κ) :
    (k : ℝ) * l * momentTwo n M k l ≤
      C * n ^ 2 *
        (Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
          Real.exp (-κ * |degreeAt n M - 1| ^ 2 * k)) *
        (Real.rpow (l : ℝ) (-(3 / 2) : ℝ) *
          Real.exp (-κ * |degreeAt n M - 1| ^ 2 * l)) := by
  let e := |degreeAt n M - 1|
  have hcubic : 0 ≤ ((k + l : ℕ) : ℝ) ^ 3 / (n : ℝ) ^ 2 := by positivity
  have hexp :
      Real.exp (-κ * (e ^ 2 * ((k : ℝ) + l) +
        ((k : ℝ) + l) ^ 3 / (n : ℝ) ^ 2)) ≤
      Real.exp (-κ * e ^ 2 * k) * Real.exp (-κ * e ^ 2 * l) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hnonneg : 0 ≤ ((k : ℝ) + l) ^ 3 / (n : ℝ) ^ 2 := by positivity
    nlinarith [mul_nonneg hκ.le hnonneg]
  have hglobal : momentTwo n M k l ≤
      C * n ^ 2 *
        (Real.rpow (k : ℝ) (-(5 / 2) : ℝ) *
          Real.rpow (l : ℝ) (-(5 / 2) : ℝ)) *
        Real.exp (-κ * (e ^ 2 * ((k : ℝ) + l) +
          ((k : ℝ) + l) ^ 3 / (n : ℝ) ^ 2)) := by
    simpa [tupleGlobalBound, momentTwo, pairSizes, Fin.prod_univ_two,
      Fin.sum_univ_two, e, sq_abs, Nat.cast_add, neg_div] using! hg
  have hcoef : 0 ≤ C * (n : ℝ) ^ 2 *
      (Real.rpow (k : ℝ) (-(5 / 2) : ℝ) *
        Real.rpow (l : ℝ) (-(5 / 2) : ℝ)) := by
    exact mul_nonneg (mul_nonneg hC (sq_nonneg _))
      (mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg (by positivity) _))
  calc
    (k : ℝ) * l * momentTwo n M k l ≤
        (k : ℝ) * l *
          (C * n ^ 2 *
            (Real.rpow (k : ℝ) (-(5 / 2) : ℝ) *
              Real.rpow (l : ℝ) (-(5 / 2) : ℝ)) *
            Real.exp (-κ * (e ^ 2 * ((k : ℝ) + l) +
              ((k : ℝ) + l) ^ 3 / (n : ℝ) ^ 2))) :=
      mul_le_mul_of_nonneg_left hglobal (by positivity)
    _ ≤ (k : ℝ) * l *
          (C * n ^ 2 *
            (Real.rpow (k : ℝ) (-(5 / 2) : ℝ) *
              Real.rpow (l : ℝ) (-(5 / 2) : ℝ)) *
            (Real.exp (-κ * e ^ 2 * k) *
              Real.exp (-κ * e ^ 2 * l))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hexp hcoef) (by positivity)
    _ = _ := by
      rw [show (k : ℝ) * l *
          (C * n ^ 2 *
            (Real.rpow (k : ℝ) (-(5 / 2) : ℝ) *
              Real.rpow (l : ℝ) (-(5 / 2) : ℝ)) *
            (Real.exp (-κ * e ^ 2 * k) *
              Real.exp (-κ * e ^ 2 * l))) =
          C * n ^ 2 *
            ((k : ℝ) * Real.rpow (k : ℝ) (-(5 / 2) : ℝ)) *
            ((l : ℝ) * Real.rpow (l : ℝ) (-(5 / 2) : ℝ)) *
            Real.exp (-κ * e ^ 2 * k) *
            Real.exp (-κ * e ^ 2 * l) by ring]
      rw [mul_rpow_neg_five_half hk, mul_rpow_neg_five_half hl]
      ring

private lemma diagonal_tail_bound
    (hA : AnalyticSumsStatement) {n H : ℕ} {M : NatSeq} {C κ : ℝ}
    (hn : 0 < n) (he : 0 < epsilon M n)
    (hC : 0 < C) (hκ : 0 < κ) (hκe : κ * epsilon M n ^ 2 ≤ 1)
    (hpoint : ∀ k ∈ Finset.Ico 1 (H + 1),
      (k : ℝ) ^ 2 * momentOne n (M n) k ≤
        C * n * (Real.rpow (k : ℝ) (-(1 / 2) : ℝ) *
          Real.exp (-κ * epsilon M n ^ 2 * k))) :
    (∑ k ∈ Finset.Ico 1 (H + 1),
      (k : ℝ) ^ 2 * momentOne n (M n) k) ≤
      C * Classical.choose
        (analytic_power_bound hA (-(1 / 2) : ℝ) (by norm_num)) *
        Real.rpow κ (-(1 / 2) : ℝ) * n / epsilon M n := by
  let A := Classical.choose
    (analytic_power_bound hA (-(1 / 2) : ℝ) (by norm_num))
  have hsum₀ := finite_power_exp_sum_le hA (beta := (-(1 / 2) : ℝ))
    (by norm_num) (mul_pos hκ (sq_pos_of_pos he)) hκe H
  have hsum : (∑ k ∈ Finset.Ico 1 (H + 1),
      Real.rpow (k : ℝ) (-(1 / 2) : ℝ) *
        Real.exp (-κ * epsilon M n ^ 2 * k)) ≤
      A * Real.rpow (κ * epsilon M n ^ 2) (-(1 / 2) : ℝ) := by
    convert hsum₀ using 1
    · congr 1
      ext k
      ring
    · dsimp [A]
      congr 1
      ring
  calc
    _ ≤ C * n * (∑ k ∈ Finset.Ico 1 (H + 1),
          Real.rpow (k : ℝ) (-(1 / 2) : ℝ) *
            Real.exp (-κ * epsilon M n ^ 2 * k)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hpoint
    _ ≤ C * n * (A * Real.rpow (κ * epsilon M n ^ 2) (-(1 / 2) : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
      rw [rpow_scaled_sq_neg_half hκ he]
      dsimp [A]
      ring

private lemma pair_tail_bound {n H N : ℕ} {M : NatSeq} {C κ : ℝ}
    (hn : 0 < n) (he : 0 < epsilon M n)
    (hC : 0 < C) (hκ : 0 < κ)
    (hpoint : ∀ k ∈ Finset.Ico (H + 1) N,
      ∀ l ∈ Finset.Ico (H + 1) N,
      (k : ℝ) * l * momentTwo n (M n) k l ≤
        C * n ^ 2 *
          (Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
            Real.exp (-κ * epsilon M n ^ 2 * k)) *
          (Real.rpow (l : ℝ) (-(3 / 2) : ℝ) *
            Real.exp (-κ * epsilon M n ^ 2 * l)))
    (htail : (∑ k ∈ Finset.Ico (H + 1) N,
      Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
        Real.exp (-κ * epsilon M n ^ 2 * k)) ≤
          3 / ((n : ℝ) * epsilon M n ^ 2)) :
    (∑ k ∈ Finset.Ico (H + 1) N,
      ∑ l ∈ Finset.Ico (H + 1) N,
        (k : ℝ) * l * momentTwo n (M n) k l) ≤
      9 * C / epsilon M n ^ 4 := by
  let s := Finset.Ico (H + 1) N
  let f := fun k : ℕ => Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
    Real.exp (-κ * epsilon M n ^ 2 * k)
  have hfn : 0 ≤ ∑ k ∈ s, f k :=
    Finset.sum_nonneg (fun k _ => by dsimp [f]; positivity)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  calc
    (∑ k ∈ s, ∑ l ∈ s, (k : ℝ) * l * momentTwo n (M n) k l) ≤
        ∑ k ∈ s, ∑ l ∈ s, C * n ^ 2 * f k * f l := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      simpa [s, f, mul_assoc] using! hpoint k hk l hl
    _ = (∑ k ∈ s, C * n ^ 2 * f k) * (∑ l ∈ s, f l) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
    _ = C * n ^ 2 * (∑ k ∈ s, f k) ^ 2 := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ C * n ^ 2 * (3 / ((n : ℝ) * epsilon M n ^ 2)) ^ 2 := by
      have hsq := pow_le_pow_left₀ hfn (by simpa [s, f] using! htail) 2
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 9 * C / epsilon M n ^ 4 := by
      field_simp [hnR.ne', he.ne'] <;> ring

set_option maxHeartbeats 800000 in
lemma near_discarded_second_bound
    (hRate : RateStatement) (hT : TupleEstimatesStatement)
    (hA : AnalyticSumsStatement) {M : NatSeq} (hbare : bareSuper M) :
    ∃ B : ℝ, 4 < B ∧ ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      expectM n (M n) (fun G =>
        treeMassSum G (Finset.Ico (nearCutoff B M n + 1) (largeCutoff n)) ^ 2) ≤
        C * n / epsilon M n := by
  obtain ⟨C₁, κ₁, hC₁, hκ₁, n₁, htuple₁⟩ := hT.1 1 (by omega)
  obtain ⟨C₂, κ₂, hC₂, hκ₂, n₂, htuple₂⟩ := hT.1 2 (by omega)
  let B : ℝ := 5 + κ₂⁻¹
  have hB : 4 < B := by
    dsimp [B]
    have : 0 ≤ κ₂⁻¹ := inv_nonneg.mpr hκ₂.le
    linarith
  have hB1 : 1 ≤ B := by linarith
  have hκB : 1 ≤ κ₂ * B := by
    dsimp [B]
    rw [mul_add, mul_inv_cancel₀ hκ₂.ne']
    nlinarith
  let A := Classical.choose
    (analytic_power_bound hA (-(1 / 2) : ℝ) (by norm_num))
  let Q := Real.rpow κ₁ (-(1 / 2) : ℝ)
  let C := C₁ * A * Q + 9 * C₂
  have hApos : 0 < A :=
    (Classical.choose_spec
      (analytic_power_bound hA (-(1 / 2) : ℝ) (by norm_num))).1
  have hQ : 0 < Q := Real.rpow_pos_of_pos hκ₁ _
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨B, hB, C, hC, ?_⟩
  have hcommon := near_common_cutoff_ranges hRate hbare B C₁ C₂ 0 hB
    (max n₁ n₂)
  have hlog : ∀ᶠ n in atTop, 1 ≤ Real.log (widthParameter M n) :=
    (tendsto_atTop.1 (Real.tendsto_log_atTop.comp
      (bare_width_tendsto_atTop (Or.inr hbare)))) 1
  have hκsmall : ∀ᶠ n in atTop,
      epsilon M n ≤ min 1 κ₁⁻¹ := by
    have ht := bare_epsilon_tendsto_zero (Or.inr hbare)
    have hmin : (0 : ℝ) < min 1 κ₁⁻¹ := lt_min zero_lt_one (inv_pos.mpr hκ₁)
    exact ((tendsto_order.1 ht).2 (min 1 κ₁⁻¹) hmin).mono
      (fun _ h => h.le)
  filter_upwards [hcommon, hlog, hκsmall] with n h hlog hsmall
  obtain ⟨hn, hn₀, hcap, hKpos, hKlarge, hpair, hlo, hhi,
    heq, he, he1, hw, hrate, herr₁, herr₂, herrmix⟩ := h
  have hn₁ : n₁ ≤ n := le_trans (Nat.le_max_left ..) hn₀
  have hn₂ : n₂ ≤ n := le_trans (Nat.le_max_right ..) hn₀
  have hκe : κ₁ * epsilon M n ^ 2 ≤ 1 := by
    have hle1 : epsilon M n ≤ 1 := hsmall.trans (min_le_left ..)
    have hleκ : epsilon M n ≤ κ₁⁻¹ := hsmall.trans (min_le_right ..)
    have hmul := mul_le_mul_of_nonneg_left hleκ hκ₁.le
    rw [mul_inv_cancel₀ hκ₁.ne'] at hmul
    nlinarith [mul_nonneg hκ₁.le (sq_nonneg (epsilon M n))]
  let s := Finset.Ico (nearCutoff B M n + 1) (largeCutoff n)
  have hdiagPoint : ∀ k ∈ s,
      (k : ℝ) ^ 2 * momentOne n (M n) k ≤
        C₁ * n * (Real.rpow (k : ℝ) (-(1 / 2) : ℝ) *
          Real.exp (-κ₁ * epsilon M n ^ 2 * k)) := by
    intro k hk
    have hkpos : 0 < k := by
      have := (Finset.mem_Ico.mp hk).1
      omega
    have hg := (htuple₁ n (M n) (fun _ => k) hn₁ hcap hlo hhi
      (fun _ => hkpos)).1
    simpa [epsilon, degree, degreeAt, mul_assoc] using!
      global_one_diagonal_bound hkpos hC₁.le hκ₁ hg
  have hdiag : (∑ k ∈ s, (k : ℝ) ^ 2 * momentOne n (M n) k) ≤
      C₁ * A * Q * n / epsilon M n := by
    have hfullPoint : ∀ k ∈ Finset.Ico 1 (largeCutoff n + 1),
        (k : ℝ) ^ 2 * momentOne n (M n) k ≤
          C₁ * n * (Real.rpow (k : ℝ) (-(1 / 2) : ℝ) *
            Real.exp (-κ₁ * epsilon M n ^ 2 * k)) := by
      intro k hk
      have hkpos : 0 < k := (Finset.mem_Ico.mp hk).1
      have hg := (htuple₁ n (M n) (fun _ => k) hn₁ hcap hlo hhi
        (fun _ => hkpos)).1
      simpa [epsilon, degree, degreeAt, mul_assoc] using!
        global_one_diagonal_bound hkpos hC₁.le hκ₁ hg
    have hsubset : s ⊆ Finset.Ico 1 (largeCutoff n + 1) := by
      intro k hk
      have hk' := Finset.mem_Ico.mp hk
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    calc
      _ ≤ ∑ k ∈ Finset.Ico 1 (largeCutoff n + 1),
          (k : ℝ) ^ 2 * momentOne n (M n) k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun k _ _ => mul_nonneg (sq_nonneg _) (momentOne_nonneg n (M n) k))
      _ ≤ _ := by
        exact diagonal_tail_bound hA hn he hC₁ hκ₁ hκe hfullPoint
  have hpairPoint : ∀ k ∈ s, ∀ l ∈ s,
      (k : ℝ) * l * momentTwo n (M n) k l ≤
        C₂ * n ^ 2 *
          (Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
            Real.exp (-κ₂ * epsilon M n ^ 2 * k)) *
          (Real.rpow (l : ℝ) (-(3 / 2) : ℝ) *
            Real.exp (-κ₂ * epsilon M n ^ 2 * l)) := by
    intro k hk l hl
    have hkpos : 0 < k := by
      have := (Finset.mem_Ico.mp hk).1
      omega
    have hlpos : 0 < l := by
      have := (Finset.mem_Ico.mp hl).1
      omega
    have hg := (htuple₂ n (M n) (pairSizes k l) hn₂ hcap hlo hhi
      (by intro i; fin_cases i <;> simp [pairSizes, hkpos, hlpos])).1
    simpa [epsilon, degree, degreeAt, mul_assoc] using!
      global_pair_mass_bound hkpos hlpos hC₂.le hκ₂ hg
  have hkernel : (∑ k ∈ s,
      Real.rpow (k : ℝ) (-(3 / 2) : ℝ) *
        Real.exp (-κ₂ * epsilon M n ^ 2 * k)) ≤
          3 / ((n : ℝ) * epsilon M n ^ 2) := by
    have htail := cutoff_negThreeHalf_tail_bound
      (N := largeCutoff n) he hB1 hw hlog hκ₂ hκB
    have hsubset : s ⊆
        Finset.Ico (nearCutoff B M n + 1) (largeCutoff n + 1) := by
      intro k hk
      change k ∈ Finset.Ico (nearCutoff B M n + 1) (largeCutoff n) at hk
      rcases Finset.mem_Ico.mp hk with ⟨hklo, hkhi⟩
      exact Finset.mem_Ico.mpr ⟨hklo, by omega⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun k _ _ => mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.exp_pos _).le)).trans htail
  have hpair : (∑ k ∈ s, ∑ l ∈ s,
      (k : ℝ) * l * momentTwo n (M n) k l) ≤
      9 * C₂ / epsilon M n ^ 4 :=
    pair_tail_bound hn he hC₂ hκ₂ hpairPoint hkernel
  have hwidth : 1 ≤ (n : ℝ) * epsilon M n ^ 3 := by
    simpa [widthParameter] using! hw
  have hpairAbsorb : 9 * C₂ / epsilon M n ^ 4 ≤
      9 * C₂ * n / epsilon M n := by
    have he4 : 0 < epsilon M n ^ 4 := pow_pos he _
    have hle : 1 / epsilon M n ^ 4 ≤ (n : ℝ) / epsilon M n := by
      apply (div_le_div_iff₀ he4 he).2
      nlinarith [hwidth]
    calc
      9 * C₂ / epsilon M n ^ 4 =
          (9 * C₂) * (1 / epsilon M n ^ 4) := by ring
      _ ≤ (9 * C₂) * ((n : ℝ) / epsilon M n) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 9 * C₂ * n / epsilon M n := by ring
  have hsq := expect_treeMassSum_sq (n := n) (M := M n) s
  have hfinal : expectM n (M n) (fun G => treeMassSum G s ^ 2) ≤
      (C₁ * A * Q + 9 * C₂) * n / epsilon M n := by
    rw [hsq]
    calc
      _ ≤ C₁ * A * Q * n / epsilon M n +
          9 * C₂ / epsilon M n ^ 4 := add_le_add hdiag hpair
      _ ≤ (C₁ * A * Q + 9 * C₂) * n / epsilon M n := by
        calc
          _ ≤ C₁ * A * Q * n / epsilon M n +
              9 * C₂ * n / epsilon M n := add_le_add le_rfl hpairAbsorb
          _ = _ := by ring
  simpa [s, C] using! hfinal

lemma near_variance_boundedBy
    (hF : FiniteEnumerationStatement) (hRate : RateStatement)
    (hT : TupleEstimatesStatement) (hA : AnalyticSumsStatement)
    {M : NatSeq} (hbare : bareSuper M) :
    boundedBy
      (fun n => varianceM n (M n)
        (fun G => treeMassBelow G (largeCutoff n)))
      (fun n => (n : ℝ) / epsilon M n) := by
  obtain ⟨B, hB, Ctail, hCtail, htail⟩ :=
    near_discarded_second_bound hRate hT hA hbare
  obtain ⟨Chead, hChead, hhead⟩ :=
    near_truncated_variance_bound hF hRate hT hA hbare B hB
  refine ⟨2 * Chead + 2 * Ctail, by positivity, ?_⟩
  have hcut := cutoff_below_large_of_error (Or.inr hbare) B
    (lt_trans (by norm_num) hB)
  filter_upwards [htail, hhead, hcut, hbare.1] with n htailn hheadn hcutn hcap
  let U := fun G : Graph n =>
    treeMassSum G (Finset.Ico 1 (nearCutoff B M n + 1))
  let V := fun G : Graph n =>
    treeMassSum G (Finset.Ico (nearCutoff B M n + 1) (largeCutoff n))
  have hsplit : (fun G : Graph n => treeMassBelow G (largeCutoff n)) =
      fun G => U G + V G := by
    funext G
    exact treeMassBelow_split G (by omega)
  have hnorm := hF.1 n (M n) hcap
  have hV := variance_le_second V hnorm
  have hnonneg := variance_nonneg (n := n) (M := M n)
    (fun G => treeMassBelow G (largeCutoff n))
  have hmain : varianceM n (M n)
      (fun G => treeMassBelow G (largeCutoff n)) ≤
      (2 * Chead + 2 * Ctail) * n / epsilon M n := by
    rw [hsplit]
    calc
      varianceM n (M n) (fun G => U G + V G) ≤
          2 * varianceM n (M n) U +
            2 * varianceM n (M n) V := variance_add_le U V
      _ ≤ 2 * (Chead * n / epsilon M n) +
          2 * (Ctail * n / epsilon M n) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (by simpa [U] using! hheadn) (by norm_num)
        · exact mul_le_mul_of_nonneg_left
            (hV.trans (by simpa [V] using! htailn)) (by norm_num)
      _ = (2 * Chead + 2 * Ctail) * n / epsilon M n := by ring
  rw [abs_of_nonneg hnonneg]
  convert hmain using 1 <;> ring

end
end Erdos745.WrapUp.Proofs.Internal.W09_TREE_MASS_NearVarianceTail
