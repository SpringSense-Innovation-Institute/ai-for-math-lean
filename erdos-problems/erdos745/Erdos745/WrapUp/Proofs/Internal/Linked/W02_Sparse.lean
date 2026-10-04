module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W02_ExpansionCore
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Probability.Moments.IntegrableExpMul

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


/-!
# Endpoint-safe rooted-tree coefficient normalization

This file establishes equation (10) from the accepted W02 reconstruction.
The proof treats `j = k` through `tau_self`, so no natural power with exponent
`-1` is introduced.
-/

open scoped BigOperators

noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Coefficient

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Expansion

/-- After multiplying by `k^j`, both branches of the rooted-forest count have
one endpoint-safe formula. -/
theorem tau_scaled_identity (hF : FiniteEnumerationStatement) (k j : ℕ)
    (hk : 0 < k) (hj : 1 ≤ j) (hjk : j ≤ k) :
    (k : ℝ) ^ j * (tau k j : ℝ) =
      (k : ℝ) ^ (k - 1) * (j : ℝ) * (falling k j : ℝ) := by
  by_cases hEq : j = k
  · subst j
    have hfall : falling k k = k.factorial := by
      rw [show falling k k = k.descFactorial k by
        simp [falling, Nat.descFactorial_eq_prod_range]]
      exact Nat.descFactorial_self k
    rw [tau_self hF, hfall]
    calc
      (k : ℝ) ^ k * (k.factorial : ℝ) =
          ((k : ℝ) ^ (k - 1) * (k : ℝ)) * (k.factorial : ℝ) := by
        rw [← pow_succ, show k - 1 + 1 = k by omega]
      _ = (k : ℝ) ^ (k - 1) * (k : ℝ) * (k.factorial : ℝ) := by ring
  · have hjk' : j < k := lt_of_le_of_ne hjk hEq
    rw [tau_of_lt hF k j hjk']
    push_cast
    have hexp : j + (k - j - 1) = k - 1 := by omega
    calc
      (k : ℝ) ^ j *
          ((falling k j : ℝ) * ((j : ℝ) * (k : ℝ) ^ (k - j - 1))) =
          (falling k j : ℝ) * (j : ℝ) *
            ((k : ℝ) ^ j * (k : ℝ) ^ (k - j - 1)) := by ring
      _ = (falling k j : ℝ) * (j : ℝ) * (k : ℝ) ^ (k - 1) := by
        rw [← pow_add, hexp]
      _ = (k : ℝ) ^ (k - 1) * (j : ℝ) * (falling k j : ℝ) := by ring

/-- Division form of `tau_scaled_identity`; positivity of `k` makes the
normalizing power nonzero. -/
theorem tau_div_identity (hF : FiniteEnumerationStatement) (k j : ℕ)
    (hk : 0 < k) (hj : 1 ≤ j) (hjk : j ≤ k) :
    (tau k j : ℝ) =
      (k : ℝ) ^ (k - 1) * (j : ℝ) * (falling k j : ℝ) /
        (k : ℝ) ^ j := by
  apply (eq_div_iff (pow_ne_zero j (by positivity : (k : ℝ) ≠ 0))).2
  simpa [mul_comm] using! tau_scaled_identity hF k j hk hj hjk

/-- Equation (10), including the `j = k` endpoint. -/
theorem Q_one_identity (hF : FiniteEnumerationStatement) (k b : ℕ)
    (hk : 0 < k) :
    (Q k 1 b : ℝ) =
      (k : ℝ) ^ (k - 1) *
        ∑ j ∈ Finset.Icc 1 k,
          (j : ℝ) * ((b + j - 2).choose (b - 1) : ℝ) *
            (falling k j : ℝ) / (k : ℝ) ^ j := by
  unfold Q
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_Icc.mp hj
  rw [Nat.cast_mul, tau_div_identity hF k j hk hj'.1 hj'.2]
  have harg : b + j - 1 - 1 = b + j - 2 := by omega
  rw [harg]
  ring

end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Coefficient


/-!
# Finite Gaussian bounds for the sparse kernel estimate

This module isolates the two finite Gaussian estimates used in the uniform
bound for `Q k 1 b`.  The estimates are deliberately stated for the exact
finite interval occurring in `Q`; no infinite-series interface is needed.
-/

open scoped BigOperators

noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Gaussian

open Set MeasureTheory

private def gaussian (k : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-x ^ 2 / (4 * (k : ℝ)))

private theorem gaussian_nonneg (k : ℕ) (x : ℝ) :
    0 ≤ gaussian k x := by
  exact (Real.exp_pos _).le

private theorem gaussian_antitone (k : ℕ) (hk : 0 < k) :
    AntitoneOn (gaussian k) (Ici 0) := by
  intro x hx y hy hxy
  unfold gaussian
  apply Real.exp_monotone
  have hkR : (0 : ℝ) < k := by positivity
  have hsq : x ^ 2 ≤ y ^ 2 := by
    simpa [pow_two] using! mul_self_le_mul_self hx hxy
  exact div_le_div_of_nonneg_right (neg_le_neg hsq) (by positivity)

private theorem integral_gaussian_Ioi (k : ℕ) (hk : 0 < k) :
    (∫ x : ℝ in Ioi 0, gaussian k x) =
      Real.sqrt (Real.pi * (k : ℝ)) := by
  let a : ℝ := 1 / (4 * (k : ℝ))
  have ha : 0 < a := by positivity
  have hint : Integrable (fun x : ℝ => Real.exp (-a * x ^ 2)) :=
    integrable_exp_neg_mul_sq ha
  have heven : (fun x : ℝ => Real.exp (-a * (-x) ^ 2)) =
      (fun x : ℝ => Real.exp (-a * x ^ 2)) := by
    funext x
    congr 2
    ring
  have hneg := integral_comp_neg_Ioi 0
    (fun x : ℝ => Real.exp (-a * x ^ 2))
  rw [heven, neg_zero] at hneg
  have hsplit := MeasureTheory.integral_add_compl measurableSet_Ioi hint
    (s := Ioi (0 : ℝ))
  rw [compl_Ioi] at hsplit
  have hfull :=
    GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℝ) ha
  have hfull' :
      (∫ x : ℝ, Real.exp (-a * x ^ 2)) =
        Real.sqrt (Real.pi / a) := by
    simpa [Real.norm_eq_abs, sq_abs, Real.sqrt_eq_rpow] using! hfull
  have haform : Real.pi / a = 4 * (Real.pi * (k : ℝ)) := by
    dsimp [a]
    field_simp
  have hsqrt4 : Real.sqrt (4 * (Real.pi * (k : ℝ))) =
      2 * Real.sqrt (Real.pi * (k : ℝ)) := by
    rw [show (4 : ℝ) * (Real.pi * (k : ℝ)) =
        4 * (Real.pi * (k : ℝ)) by rfl,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hhalf :
      (∫ x : ℝ in Ioi 0, Real.exp (-a * x ^ 2)) =
        Real.sqrt (Real.pi * (k : ℝ)) := by
    have hsplit' :
        2 * (∫ x : ℝ in Ioi 0, Real.exp (-a * x ^ 2)) =
          ∫ x : ℝ, Real.exp (-a * x ^ 2) := by
      calc
        2 * (∫ x : ℝ in Ioi 0, Real.exp (-a * x ^ 2)) =
            (∫ x : ℝ in Ioi 0, Real.exp (-a * x ^ 2)) +
              ∫ x : ℝ in Ioi 0, Real.exp (-a * x ^ 2) := by ring
        _ = (∫ x : ℝ in Ioi 0, Real.exp (-a * x ^ 2)) +
              ∫ x : ℝ in Iic 0, Real.exp (-a * x ^ 2) := by rw [hneg]
        _ = ∫ x : ℝ, Real.exp (-a * x ^ 2) := hsplit
    rw [hfull', haform, hsqrt4] at hsplit'
    linarith
  have hfun : gaussian k =
      (fun x : ℝ => Real.exp (-a * x ^ 2)) := by
    funext x
    unfold gaussian
    dsimp [a]
    congr 1
    ring
  rw [hfun]
  exact hhalf

private theorem interval_gaussian_le (k : ℕ) (hk : 0 < k) :
    (∫ x : ℝ in (0 : ℝ)..(k : ℝ), gaussian k x) ≤
      Real.sqrt (Real.pi * (k : ℝ)) := by
  rw [intervalIntegral.integral_of_le (by positivity)]
  have hint : Integrable (gaussian k) := by
    apply (integrable_exp_neg_mul_sq
      (show 0 < (1 : ℝ) / (4 * (k : ℝ)) by positivity)).congr
    filter_upwards with x
    unfold gaussian
    congr 1
    ring
  calc
    (∫ x : ℝ in Ioc (0 : ℝ) (k : ℝ), gaussian k x) ≤
        ∫ x : ℝ in Ioi 0, gaussian k x := by
      apply MeasureTheory.setIntegral_mono_set hint.integrableOn
      · filter_upwards with x
        exact gaussian_nonneg k x
      · filter_upwards with x hx
        exact hx.1
    _ = Real.sqrt (Real.pi * (k : ℝ)) := integral_gaussian_Ioi k hk

private theorem sqrt_pi_mul_le_two_sqrt (k : ℕ) :
    Real.sqrt (Real.pi * (k : ℝ)) ≤ 2 * Real.sqrt (k : ℝ) := by
  have hpi : Real.sqrt Real.pi ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [Real.pi_le_four]
  rw [Real.sqrt_mul Real.pi_pos.le]
  exact mul_le_mul_of_nonneg_right hpi (Real.sqrt_nonneg _)

private theorem sum_Icc_one_eq_range {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (k : ℕ) :
    (∑ j ∈ Finset.Icc 1 k, f j) =
      ∑ i ∈ Finset.range k, f (i + 1) := by
  have hset : Finset.Icc 1 k = Finset.Ico 1 (k + 1) := by
    ext j
    simp
  rw [hset, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  omega

/-- The finite decreasing Gaussian sum used after the falling-factor bound. -/
theorem sum_gaussian_le (k : ℕ) (hk : 0 < k) :
    (∑ j ∈ Finset.Icc 1 k,
      Real.exp (-((j : ℝ) ^ 2) / (4 * (k : ℝ)))) ≤
      2 * Real.sqrt (k : ℝ) := by
  rw [sum_Icc_one_eq_range]
  have hmono : AntitoneOn (gaussian k)
      (Icc (0 : ℝ) (0 + (k : ℝ))) :=
    (gaussian_antitone k hk).mono (by
      intro x hx
      exact hx.1)
  have hsum := hmono.sum_le_integral
  calc
    (∑ i ∈ Finset.range k,
        Real.exp (-(((i + 1 : ℕ) : ℝ) ^ 2) /
          (4 * (k : ℝ)))) =
        ∑ i ∈ Finset.range k, gaussian k (0 + ((i + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [gaussian]
    _ ≤ ∫ x : ℝ in (0 : ℝ)..(k : ℝ), gaussian k x := by
      simpa using! hsum
    _ ≤ Real.sqrt (Real.pi * (k : ℝ)) := interval_gaussian_le k hk
    _ ≤ 2 * Real.sqrt (k : ℝ) := sqrt_pi_mul_le_two_sqrt k

private theorem pow_mul_gaussian_half_le (k b : ℕ) (hk : 0 < k)
    (hb : 0 < b) (x : ℝ) (hx : 0 ≤ x) :
    x ^ b * Real.exp (-x ^ 2 / (4 * (k : ℝ))) ≤
      Real.rpow (4 * (b : ℝ) * (k : ℝ)) ((b : ℝ) / 2) *
        Real.exp (-x ^ 2 / (8 * (k : ℝ))) := by
  let t : ℝ := 1 / (8 * (k : ℝ))
  let p : ℝ := (b : ℝ) / 2
  have ht : t ≠ 0 := by positivity
  have hp : 0 ≤ p := by positivity
  have hpow := ProbabilityTheory.rpow_abs_le_mul_exp_abs (x ^ 2)
    (t := t) (p := p) hp ht
  have habs_t : |t| = t := abs_of_pos (by positivity)
  have habs_sq : |x ^ 2| = x ^ 2 := abs_of_nonneg (sq_nonneg x)
  rw [habs_t, habs_sq] at hpow
  have hconst : p / t = 4 * (b : ℝ) * (k : ℝ) := by
    dsimp [p, t]
    field_simp
    ring
  rw [hconst] at hpow
  have hxpow : (x : ℝ) ^ b = Real.rpow (x ^ 2) p := by
    rw [← Real.rpow_natCast]
    calc
      Real.rpow x (b : ℝ) = Real.rpow x (2 * p) := by
        congr 1
        dsimp [p]
        ring
      _ = Real.rpow (Real.rpow x 2) p := Real.rpow_mul hx 2 p
      _ = Real.rpow (x ^ 2) p := by
        congr 1
        exact Real.rpow_two x
  rw [hxpow]
  calc
    Real.rpow (x ^ 2) p * Real.exp (-x ^ 2 / (4 * (k : ℝ))) ≤
        (Real.rpow (4 * (b : ℝ) * (k : ℝ)) p *
          Real.exp (t * x ^ 2)) *
            Real.exp (-x ^ 2 / (4 * (k : ℝ))) := by
      exact mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = Real.rpow (4 * (b : ℝ) * (k : ℝ)) p *
        Real.exp (-x ^ 2 / (8 * (k : ℝ))) := by
      rw [mul_assoc]
      congr 1
      rw [← Real.exp_add]
      dsimp [t]
      congr 2
      field_simp
      ring

/-- A finite Gaussian moment bound with constants chosen for the later
coefficient absorption. -/
theorem sum_pow_mul_gaussian_le (k b : ℕ) (hk : 0 < k) (hb : 0 < b) :
    (∑ j ∈ Finset.Icc 1 k,
      (j : ℝ) ^ b *
        Real.exp (-((j : ℝ) ^ 2) / (4 * (k : ℝ)))) ≤
      (8 : ℝ) ^ b *
        Real.rpow (b : ℝ) (((b : ℝ) + 1) / 2) *
        Real.rpow (k : ℝ) (((b : ℝ) + 1) / 2) := by
  have hk2 : 0 < 2 * k := by omega
  have hpoint : ∀ j ∈ Finset.Icc 1 k,
      (j : ℝ) ^ b * Real.exp (-((j : ℝ) ^ 2) / (4 * (k : ℝ))) ≤
        Real.rpow (4 * (b : ℝ) * (k : ℝ)) ((b : ℝ) / 2) *
          Real.exp (-((j : ℝ) ^ 2) / (4 * ((2 * k : ℕ) : ℝ))) := by
    intro j hj
    convert pow_mul_gaussian_half_le k b hk hb (j : ℝ) (by positivity) using 1 <;>
      push_cast <;> ring_nf
  calc
    (∑ j ∈ Finset.Icc 1 k,
      (j : ℝ) ^ b *
        Real.exp (-((j : ℝ) ^ 2) / (4 * (k : ℝ)))) ≤
        ∑ j ∈ Finset.Icc 1 k,
          Real.rpow (4 * (b : ℝ) * (k : ℝ)) ((b : ℝ) / 2) *
            Real.exp (-((j : ℝ) ^ 2) /
              (4 * ((2 * k : ℕ) : ℝ))) := by
      exact Finset.sum_le_sum fun j hj => hpoint j hj
    _ ≤ Real.rpow (4 * (b : ℝ) * (k : ℝ)) ((b : ℝ) / 2) *
        (2 * Real.sqrt ((2 * k : ℕ) : ℝ)) := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left
      · exact (Finset.sum_le_sum_of_subset_of_nonneg
        (show Finset.Icc 1 k ⊆ Finset.Icc 1 (2 * k) by
          intro j hj
          simp only [Finset.mem_Icc] at hj ⊢
          omega)
        (by
          intro j hj hnot
          positivity)).trans (sum_gaussian_le (2 * k) hk2)
      · exact Real.rpow_nonneg (by positivity) _
    _ ≤ (8 : ℝ) ^ b *
        Real.rpow (b : ℝ) (((b : ℝ) + 1) / 2) *
        Real.rpow (k : ℝ) (((b : ℝ) + 1) / 2) := by
      have hbR : (0 : ℝ) < b := by positivity
      have hkR : (0 : ℝ) < k := by positivity
      have hfactor :
          Real.rpow (4 * (b : ℝ) * (k : ℝ)) ((b : ℝ) / 2) =
            (2 : ℝ) ^ b * Real.rpow (b : ℝ) ((b : ℝ) / 2) *
              Real.rpow (k : ℝ) ((b : ℝ) / 2) := by
        calc
          Real.rpow (4 * (b : ℝ) * (k : ℝ)) ((b : ℝ) / 2) =
              Real.rpow (4 * (b : ℝ)) ((b : ℝ) / 2) *
                Real.rpow (k : ℝ) ((b : ℝ) / 2) :=
            Real.mul_rpow
              (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hbR.le) hkR.le
          _ = (Real.rpow (4 : ℝ) ((b : ℝ) / 2) *
                Real.rpow (b : ℝ) ((b : ℝ) / 2)) *
                  Real.rpow (k : ℝ) ((b : ℝ) / 2) := by
            congr 1
            exact Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hbR.le
          _ = _ := by
            congr 2
            calc
              Real.rpow (4 : ℝ) ((b : ℝ) / 2) =
                  Real.rpow (Real.rpow (2 : ℝ) 2) ((b : ℝ) / 2) := by
                congr 2
                norm_num [Real.rpow_two]
              _ = Real.rpow (2 : ℝ) (2 * ((b : ℝ) / 2)) :=
                (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) 2 _).symm
              _ = Real.rpow (2 : ℝ) (b : ℝ) := by congr 1 <;> ring
              _ = (2 : ℝ) ^ b := Real.rpow_natCast 2 b
      have hsqrt2k : Real.sqrt (((2 * k : ℕ) : ℝ)) =
          Real.sqrt 2 * Real.sqrt (k : ℝ) := by
        push_cast
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [hfactor, hsqrt2k]
      have hkhalf : Real.sqrt (k : ℝ) =
          Real.rpow (k : ℝ) (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
      have hbhalf : Real.sqrt (b : ℝ) =
          Real.rpow (b : ℝ) (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
      have hexp : ((b : ℝ) + 1) / 2 = (b : ℝ) / 2 + 1 / 2 := by ring
      have hbexp : Real.rpow (b : ℝ) (((b : ℝ) + 1) / 2) =
          Real.rpow (b : ℝ) ((b : ℝ) / 2) * Real.sqrt (b : ℝ) := by
        calc
          Real.rpow (b : ℝ) (((b : ℝ) + 1) / 2) =
              Real.rpow (b : ℝ) ((b : ℝ) / 2 + 1 / 2) := by rw [hexp]
          _ = Real.rpow (b : ℝ) ((b : ℝ) / 2) *
              Real.rpow (b : ℝ) (1 / 2) := Real.rpow_add hbR _ _
          _ = _ := by rw [← hbhalf]
      have hkexp : Real.rpow (k : ℝ) (((b : ℝ) + 1) / 2) =
          Real.rpow (k : ℝ) ((b : ℝ) / 2) * Real.sqrt (k : ℝ) := by
        calc
          Real.rpow (k : ℝ) (((b : ℝ) + 1) / 2) =
              Real.rpow (k : ℝ) ((b : ℝ) / 2 + 1 / 2) := by rw [hexp]
          _ = Real.rpow (k : ℝ) ((b : ℝ) / 2) *
              Real.rpow (k : ℝ) (1 / 2) := Real.rpow_add hkR _ _
          _ = _ := by rw [← hkhalf]
      rw [hbexp, hkexp]
      have hsqrt2 : Real.sqrt 2 ≤ 2 := by
        rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      have htwo : (2 : ℝ) * Real.sqrt 2 * (2 : ℝ) ^ b ≤ 8 ^ b := by
        calc
          (2 : ℝ) * Real.sqrt 2 * 2 ^ b ≤ 4 * 2 ^ b := by
            have : (2 : ℝ) * Real.sqrt 2 ≤ 4 := by nlinarith
            exact mul_le_mul_of_nonneg_right this (by positivity)
          _ ≤ 8 ^ b := by
            have hb1 : 1 ≤ b := hb
            calc
              (4 : ℝ) * 2 ^ b ≤ 4 ^ b * 2 ^ b := by
                gcongr
                simpa using!
                  (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hb1)
              _ = 8 ^ b := by rw [← mul_pow]; norm_num
      have hsqrtb : 1 ≤ Real.sqrt (b : ℝ) := by
        rw [Real.one_le_sqrt]
        exact_mod_cast hb
      have hcommon : 0 ≤ Real.rpow (b : ℝ) ((b : ℝ) / 2) *
          (Real.rpow (k : ℝ) ((b : ℝ) / 2) * Real.sqrt (k : ℝ)) := by
        exact mul_nonneg (Real.rpow_nonneg hbR.le _)
          (mul_nonneg (Real.rpow_nonneg hkR.le _) (Real.sqrt_nonneg _))
      calc
        ((2 : ℝ) ^ b * Real.rpow (b : ℝ) ((b : ℝ) / 2) *
              Real.rpow (k : ℝ) ((b : ℝ) / 2)) *
            (2 * (Real.sqrt 2 * Real.sqrt (k : ℝ))) =
            (2 * Real.sqrt 2 * (2 : ℝ) ^ b) *
              (Real.rpow (b : ℝ) ((b : ℝ) / 2) *
                (Real.rpow (k : ℝ) ((b : ℝ) / 2) * Real.sqrt (k : ℝ))) := by ring
        _ ≤ (8 : ℝ) ^ b *
              (Real.rpow (b : ℝ) ((b : ℝ) / 2) *
                (Real.rpow (k : ℝ) ((b : ℝ) / 2) * Real.sqrt (k : ℝ))) :=
          mul_le_mul_of_nonneg_right htwo hcommon
        _ ≤ (8 : ℝ) ^ b *
              ((Real.rpow (b : ℝ) ((b : ℝ) / 2) * Real.sqrt (b : ℝ)) *
                (Real.rpow (k : ℝ) ((b : ℝ) / 2) * Real.sqrt (k : ℝ))) := by
          apply mul_le_mul_of_nonneg_left
          · apply mul_le_mul_of_nonneg_right
            · exact le_mul_of_one_le_right (Real.rpow_nonneg hbR.le _) hsqrtb
            · exact mul_nonneg (Real.rpow_nonneg hkR.le _) (Real.sqrt_nonneg _)
          · positivity
        _ = _ := by ring

end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Gaussian


/-!
# Uniform sparse coefficient estimate

This module proves the finite estimate (11) for the exact endpoint-safe
coefficient `Q k 1 b`.  The proof never replaces the `j = k` term by a
negative natural exponent; that endpoint is already handled by
`Q_one_identity`.
-/

open scoped BigOperators

noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_SparseCoefficient

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Expansion
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Coefficient
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Gaussian

private theorem real_sum_range_id (j : ℕ) :
    (∑ i ∈ Finset.range j, (i : ℝ)) =
      (j : ℝ) * ((j : ℝ) - 1) / 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- The normalized falling factorial has the elementary Gaussian envelope
coming from `1-x ≤ exp(-x)`. -/
private theorem falling_div_pow_le_exp (k j : ℕ) (hk : 0 < k)
    (hjk : j ≤ k) :
    (falling k j : ℝ) / (k : ℝ) ^ j ≤
      Real.exp (-((j : ℝ) * ((j : ℝ) - 1)) /
        (2 * (k : ℝ))) := by
  have hkR : (0 : ℝ) < k := by positivity
  rw [falling, Nat.cast_prod]
  have hden : (k : ℝ) ^ j = ∏ i ∈ Finset.range j, (k : ℝ) := by simp
  rw [hden, ← Finset.prod_div_distrib]
  calc
    (∏ i ∈ Finset.range j, ((k - i : ℕ) : ℝ) / (k : ℝ)) ≤
        ∏ i ∈ Finset.range j,
          Real.exp (-((i : ℝ) / (k : ℝ))) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        have hik : i ≤ k := by
          have hij : i < j := Finset.mem_range.mp hi
          omega
        positivity
      · intro i hi
        have hij : i < j := Finset.mem_range.mp hi
        have hik : i ≤ k := by omega
        rw [Nat.cast_sub hik]
        have heq : ((k : ℝ) - (i : ℝ)) / (k : ℝ) =
            1 - (i : ℝ) / (k : ℝ) := by field_simp
        rw [heq]
        exact Real.one_sub_le_exp_neg _
    _ = Real.exp (∑ i ∈ Finset.range j,
          -((i : ℝ) / (k : ℝ))) := by
      rw [Real.exp_sum]
    _ = Real.exp (-((j : ℝ) * ((j : ℝ) - 1)) /
        (2 * (k : ℝ))) := by
      congr 1
      rw [Finset.sum_neg_distrib, ← Finset.sum_div, real_sum_range_id]
      field_simp

private theorem falling_div_pow_le_gaussian (k j : ℕ) (hk : 0 < k)
    (hj : 2 ≤ j) (hjk : j ≤ k) :
    (falling k j : ℝ) / (k : ℝ) ^ j ≤
      Real.exp (-((j : ℝ) ^ 2) / (4 * (k : ℝ))) := by
  refine (falling_div_pow_le_exp k j hk hjk).trans ?_
  apply Real.exp_monotone
  have hkR : (0 : ℝ) < k := by positivity
  have hjR : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hleft : -((j : ℝ) * ((j : ℝ) - 1)) / (2 * (k : ℝ)) =
      (-((j : ℝ) * ((j : ℝ) - 1)) / 2) / (k : ℝ) := by ring
  have hright : -((j : ℝ) ^ 2) / (4 * (k : ℝ)) =
      (-((j : ℝ) ^ 2) / 4) / (k : ℝ) := by ring
  rw [hleft, hright]
  apply (div_le_div_iff_of_pos_right hkR).2
  nlinarith

/-- The binomial factor in one summand is bounded by a single `b`th power
over `(b-1)!`. -/
private theorem choose_factor_le (b j : ℕ) (hb : 0 < b) :
    (j : ℝ) * ((b + j - 2).choose (b - 1) : ℝ) ≤
      (b + j : ℝ) ^ b / ((b - 1).factorial : ℝ) := by
  have hchoose := Nat.choose_le_pow_div (α := ℝ) (b - 1) (b + j - 2)
  have hjle : (j : ℝ) ≤ b + j := by
    exact_mod_cast (Nat.le_add_left j b)
  have hnle : ((b + j - 2 : ℕ) : ℝ) ≤ b + j := by
    exact_mod_cast (show b + j - 2 ≤ b + j by omega)
  have hfac : (0 : ℝ) < (b - 1).factorial := by positivity
  calc
    (j : ℝ) * ((b + j - 2).choose (b - 1) : ℝ) ≤
        (j : ℝ) * (((b + j - 2 : ℕ) : ℝ) ^ (b - 1) /
          ((b - 1).factorial : ℝ)) := by gcongr
    _ ≤ (b + j : ℝ) * ((b + j : ℝ) ^ (b - 1) /
          ((b - 1).factorial : ℝ)) := by gcongr
    _ = (b + j : ℝ) ^ b / ((b - 1).factorial : ℝ) := by
      have hpow : (b + j : ℝ) ^ b =
          (b + j : ℝ) ^ (b - 1) * (b + j : ℝ) := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ b)]
      rw [hpow]
      ring

private theorem factorial_lower (n : ℕ) (hn : 0 < n) :
    ((n : ℝ) / 3) ^ n ≤ (n.factorial : ℝ) := by
  have hbase : (n : ℝ) / 3 ≤ (n : ℝ) / Real.exp 1 := by
    gcongr
    exact Real.exp_one_lt_three.le
  have hp : ((n : ℝ) / 3) ^ n ≤ ((n : ℝ) / Real.exp 1) ^ n :=
    pow_le_pow_left₀ (by positivity) hbase n
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (n : ℝ)) := by
    rw [Real.one_le_sqrt]
    have hpi : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  calc
    ((n : ℝ) / 3) ^ n ≤ ((n : ℝ) / Real.exp 1) ^ n := hp
    _ ≤ Real.sqrt (2 * Real.pi * (n : ℝ)) *
        ((n : ℝ) / Real.exp 1) ^ n := by
      exact le_mul_of_one_le_left (by positivity) hsqrt
    _ ≤ (n.factorial : ℝ) := Stirling.le_factorial_stirling n

/-- A denominator form of the elementary factorial estimate. -/
private theorem inv_factorial_pred_le (b : ℕ) (hb : 0 < b) :
    ((b - 1).factorial : ℝ)⁻¹ ≤
      (6 : ℝ) ^ b / (b : ℝ) ^ (b - 1) := by
  by_cases hb1 : b = 1
  · subst b
    norm_num
  · have hb2 : 2 ≤ b := by omega
    have hpred : 0 < b - 1 := by omega
    have hfac := factorial_lower (b - 1) hpred
    have hbase : (b : ℝ) / 6 ≤ ((b - 1 : ℕ) : ℝ) / 3 := by
      rw [Nat.cast_sub (by omega : 1 ≤ b)]
      have hb2R : (2 : ℝ) ≤ b := by exact_mod_cast hb2
      linarith
    have hpow : ((b : ℝ) / 6) ^ (b - 1) ≤
        (((b - 1 : ℕ) : ℝ) / 3) ^ (b - 1) := by gcongr
    have hlower : ((b : ℝ) / 6) ^ (b - 1) ≤
        ((b - 1).factorial : ℝ) := hpow.trans hfac
    have hfacpos : (0 : ℝ) < (b - 1).factorial := by positivity
    have hbasepos : (0 : ℝ) < ((b : ℝ) / 6) ^ (b - 1) := by positivity
    calc
      ((b - 1).factorial : ℝ)⁻¹ = 1 / ((b - 1).factorial : ℝ) := by rw [one_div]
      _ ≤ 1 / (((b : ℝ) / 6) ^ (b - 1)) :=
        one_div_le_one_div_of_le hbasepos hlower
      _ = (6 : ℝ) ^ (b - 1) / (b : ℝ) ^ (b - 1) := by
        rw [div_pow]
        field_simp
      _ ≤ (6 : ℝ) ^ b / (b : ℝ) ^ (b - 1) := by
        apply div_le_div_of_nonneg_right
        · exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 6) (by omega)
        · positivity

private def normalizedTerm (k b j : ℕ) : ℝ :=
  (j : ℝ) * ((b + j - 2).choose (b - 1) : ℝ) *
    (falling k j : ℝ) / (k : ℝ) ^ j

private theorem normalizedTerm_one (k b : ℕ) (hk : 0 < k)
    (hb : 0 < b) : normalizedTerm k b 1 = 1 := by
  unfold normalizedTerm
  have : b + 1 - 2 = b - 1 := by omega
  rw [this, Nat.choose_self]
  simp [falling, Nat.ne_of_gt hk]

private theorem normalizedTerm_le (k b j : ℕ) (hk : 0 < k)
    (hb : 0 < b) (hj : 2 ≤ j) (hjk : j ≤ k) :
    normalizedTerm k b j ≤
      ((6 : ℝ) ^ b / (b : ℝ) ^ (b - 1)) *
        (2 : ℝ) ^ (b - 1) *
        ((b : ℝ) ^ b + (j : ℝ) ^ b) *
        Real.exp (-((j : ℝ) ^ 2) / (4 * (k : ℝ))) := by
  have hchoose := choose_factor_le b j hb
  have hfall := falling_div_pow_le_gaussian k j hk hj hjk
  have hadd := add_pow_le (show (0 : ℝ) ≤ b by positivity)
    (show (0 : ℝ) ≤ j by positivity) b
  have hinv := inv_factorial_pred_le b hb
  unfold normalizedTerm
  rw [div_eq_mul_inv]
  calc
    (j : ℝ) * ((b + j - 2).choose (b - 1) : ℝ) *
        (falling k j : ℝ) * ((k : ℝ) ^ j)⁻¹ =
        ((j : ℝ) * ((b + j - 2).choose (b - 1) : ℝ)) *
          ((falling k j : ℝ) / (k : ℝ) ^ j) := by
      rw [div_eq_mul_inv]
      ring
    _ ≤ ((b + j : ℝ) ^ b / ((b - 1).factorial : ℝ)) *
          ((falling k j : ℝ) / (k : ℝ) ^ j) := by
      exact mul_le_mul_of_nonneg_right hchoose (by positivity)
    _ ≤ ((b + j : ℝ) ^ b / ((b - 1).factorial : ℝ)) *
          Real.exp (-((j : ℝ) ^ 2) / (4 * (k : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hfall (by positivity)
    _ =
        ((b + j : ℝ) ^ b * ((b - 1).factorial : ℝ)⁻¹) *
          Real.exp (-((j : ℝ) ^ 2) / (4 * (k : ℝ))) := by
      rw [div_eq_mul_inv]
    _ ≤ ((b + j : ℝ) ^ b *
          ((6 : ℝ) ^ b / (b : ℝ) ^ (b - 1))) *
          Real.exp (-((j : ℝ) ^ 2) / (4 * (k : ℝ))) := by gcongr
    _ ≤ (((2 : ℝ) ^ (b - 1) *
          ((b : ℝ) ^ b + (j : ℝ) ^ b)) *
          ((6 : ℝ) ^ b / (b : ℝ) ^ (b - 1))) *
          Real.exp (-((j : ℝ) ^ 2) / (4 * (k : ℝ))) := by gcongr
    _ = _ := by ring

private theorem normalized_sum_le (k b : ℕ) (hk : 0 < k)
    (hb : 0 < b) :
    (∑ j ∈ Finset.Icc 1 k, normalizedTerm k b j) ≤
      1 + ((6 : ℝ) ^ b / (b : ℝ) ^ (b - 1)) *
        (2 : ℝ) ^ (b - 1) *
        ((b : ℝ) ^ b * (2 * Real.sqrt (k : ℝ)) +
          (8 : ℝ) ^ b *
            Real.rpow (b : ℝ) (((b : ℝ) + 1) / 2) *
            Real.rpow (k : ℝ) (((b : ℝ) + 1) / 2)) := by
  let s := Finset.Icc 1 k
  have hk1 : 1 ≤ k := hk
  have h1 : 1 ∈ s := by simp [s, hk1]
  rw [← Finset.add_sum_erase s _ h1, Finset.erase_eq]
  rw [normalizedTerm_one k b hk hb]
  gcongr
  let S0 : ℝ := ∑ j ∈ s,
    Real.exp (-((j : ℝ) ^ 2) / (4 * (k : ℝ)))
  let Sb : ℝ := ∑ j ∈ s, (j : ℝ) ^ b *
    Real.exp (-((j : ℝ) ^ 2) / (4 * (k : ℝ)))
  have hS0 : S0 ≤ 2 * Real.sqrt (k : ℝ) := by
    simpa [S0, s] using! sum_gaussian_le k hk
  have hSb : Sb ≤ (8 : ℝ) ^ b *
      Real.rpow (b : ℝ) (((b : ℝ) + 1) / 2) *
      Real.rpow (k : ℝ) (((b : ℝ) + 1) / 2) := by
    simpa [Sb, s] using! sum_pow_mul_gaussian_le k b hk hb
  calc
    (∑ j ∈ s \ {1}, normalizedTerm k b j) ≤
        ∑ j ∈ s \ {1},
          ((6 : ℝ) ^ b / (b : ℝ) ^ (b - 1)) *
            (2 : ℝ) ^ (b - 1) *
            ((b : ℝ) ^ b + (j : ℝ) ^ b) *
            Real.exp (-((j : ℝ) ^ 2) / (4 * (k : ℝ))) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjs : j ∈ s := (Finset.mem_sdiff.mp hj).1
      have hjne : j ≠ 1 := by simpa using! (Finset.mem_sdiff.mp hj).2
      have hj' := Finset.mem_Icc.mp hjs
      exact normalizedTerm_le k b j hk hb (by omega) hj'.2
    _ ≤ ∑ j ∈ s,
          ((6 : ℝ) ^ b / (b : ℝ) ^ (b - 1)) *
            (2 : ℝ) ^ (b - 1) *
            ((b : ℝ) ^ b + (j : ℝ) ^ b) *
            Real.exp (-((j : ℝ) ^ 2) / (4 * (k : ℝ))) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
      intro j hj hnot
      positivity
    _ = ((6 : ℝ) ^ b / (b : ℝ) ^ (b - 1)) *
        (2 : ℝ) ^ (b - 1) *
        ((b : ℝ) ^ b * S0 + Sb) := by
      have hA :
          (∑ j ∈ s,
            ((6 : ℝ) ^ b / (b : ℝ) ^ (b - 1)) *
              (2 : ℝ) ^ (b - 1) * (b : ℝ) ^ b *
              Real.exp (-((j : ℝ) ^ 2) / (4 * (k : ℝ)))) =
            ((6 : ℝ) ^ b / (b : ℝ) ^ (b - 1)) *
              (2 : ℝ) ^ (b - 1) * ((b : ℝ) ^ b * S0) := by
        dsimp [S0]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring_nf
      have hB :
          (∑ j ∈ s,
            ((6 : ℝ) ^ b / (b : ℝ) ^ (b - 1)) *
              (2 : ℝ) ^ (b - 1) * (j : ℝ) ^ b *
              Real.exp (-((j : ℝ) ^ 2) / (4 * (k : ℝ)))) =
            ((6 : ℝ) ^ b / (b : ℝ) ^ (b - 1)) *
              (2 : ℝ) ^ (b - 1) * Sb := by
        dsimp [Sb]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring_nf
      calc
        (∑ j ∈ s,
          ((6 : ℝ) ^ b / (b : ℝ) ^ (b - 1)) *
            (2 : ℝ) ^ (b - 1) *
            ((b : ℝ) ^ b + (j : ℝ) ^ b) *
            Real.exp (-((j : ℝ) ^ 2) / (4 * (k : ℝ)))) =
            (∑ j ∈ s,
              ((6 : ℝ) ^ b / (b : ℝ) ^ (b - 1)) *
                (2 : ℝ) ^ (b - 1) * (b : ℝ) ^ b *
                Real.exp (-((j : ℝ) ^ 2) / (4 * (k : ℝ)))) +
            ∑ j ∈ s,
              ((6 : ℝ) ^ b / (b : ℝ) ^ (b - 1)) *
                (2 : ℝ) ^ (b - 1) * (j : ℝ) ^ b *
                Real.exp (-((j : ℝ) ^ 2) / (4 * (k : ℝ))) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = _ := by rw [hA, hB]; ring
    _ ≤ ((6 : ℝ) ^ b / (b : ℝ) ^ (b - 1)) *
        (2 : ℝ) ^ (b - 1) *
        ((b : ℝ) ^ b * (2 * Real.sqrt (k : ℝ)) +
          (8 : ℝ) ^ b *
            Real.rpow (b : ℝ) (((b : ℝ) + 1) / 2) *
            Real.rpow (k : ℝ) (((b : ℝ) + 1) / 2)) := by
      apply mul_le_mul_of_nonneg_left
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_left hS0 (by positivity)
        · exact hSb
      · positivity

private def targetScale (k b : ℕ) : ℝ :=
  Real.rpow (b : ℝ) (-(b : ℝ) / 2) *
    Real.rpow (k : ℝ) (((b : ℝ) + 1) / 2)

private theorem log_nat_le_mul_log_two (b : ℕ) (hb : 0 < b) :
    Real.log (b : ℝ) ≤ (b : ℝ) * Real.log 2 := by
  have hpow : (b : ℝ) ≤ (2 : ℝ) ^ b := by
    have h := Nat.cast_le_pow_div_sub (by norm_num : (1 : ℝ) < 2) b
    convert h using 1 <;> ring
  have hlog := Real.strictMonoOn_log.monotoneOn
    (show (b : ℝ) ∈ Set.Ioi 0 by
      change (0 : ℝ) < b
      positivity)
    (show (2 : ℝ) ^ b ∈ Set.Ioi 0 by
      change (0 : ℝ) < (2 : ℝ) ^ b
      exact pow_pos (by norm_num) _) hpow
  simpa [Real.log_pow] using! hlog

private theorem first_contribution_le (k b : ℕ) (hk : 0 < k)
    (hb : 0 < b) (hbk : b ≤ 3 * k) :
    (12 : ℝ) ^ b * (b : ℝ) * Real.sqrt (k : ℝ) ≤
      (48 : ℝ) ^ b * targetScale k b := by
  have hbR : (0 : ℝ) < b := by positivity
  have hkR : (0 : ℝ) < k := by positivity
  have hbkR : (b : ℝ) ≤ 3 * (k : ℝ) := by exact_mod_cast hbk
  have hlogbk : Real.log (b : ℝ) - Real.log (k : ℝ) ≤ Real.log 3 := by
    have h := Real.strictMonoOn_log.monotoneOn
      (show (b : ℝ) ∈ Set.Ioi 0 by exact hbR)
      (show (3 * (k : ℝ)) ∈ Set.Ioi 0 by
        exact mul_pos (by norm_num) hkR) hbkR
    rw [Real.log_mul (by norm_num) (ne_of_gt hkR)] at h
    linarith
  have hlogb := log_nat_le_mul_log_two b hb
  have hlog3 : Real.log 3 ≤ 2 * Real.log 2 := by
    have h := Real.strictMonoOn_log.monotoneOn
      (show (3 : ℝ) ∈ Set.Ioi 0 by norm_num)
      (show (4 : ℝ) ∈ Set.Ioi 0 by norm_num) (by norm_num)
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h
    norm_num at h ⊢
    exact h
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hmul : ((b : ℝ) / 2) *
      (Real.log (b : ℝ) - Real.log (k : ℝ)) ≤
      ((b : ℝ) / 2) * Real.log 3 :=
    mul_le_mul_of_nonneg_left hlogbk (by positivity)
  have hlog12 : Real.log 48 = Real.log 12 + Real.log 4 := by
    rw [show (48 : ℝ) = 12 * 4 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  have hlogsqrt : Real.log (Real.sqrt (k : ℝ)) =
      (1 / 2 : ℝ) * Real.log (k : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.log_rpow hkR]
  have hlogscale : Real.log (targetScale k b) =
      (-(b : ℝ) / 2) * Real.log (b : ℝ) +
        (((b : ℝ) + 1) / 2) * Real.log (k : ℝ) := by
    unfold targetScale
    rw [Real.log_mul
      (x := Real.rpow (b : ℝ) (-(b : ℝ) / 2))
      (y := Real.rpow (k : ℝ) (((b : ℝ) + 1) / 2))
      (ne_of_gt (Real.rpow_pos_of_pos hbR _))
      (ne_of_gt (Real.rpow_pos_of_pos hkR _))]
    exact congrArg₂ (· + ·) (Real.log_rpow hbR _)
      (Real.log_rpow hkR _)
  apply (Real.strictMonoOn_log.le_iff_le
    (show (12 : ℝ) ^ b * (b : ℝ) * Real.sqrt (k : ℝ) ∈ Set.Ioi 0 by
      exact mul_pos (mul_pos (pow_pos (by norm_num) _) hbR)
        (Real.sqrt_pos.2 hkR))
    (show (48 : ℝ) ^ b * targetScale k b ∈ Set.Ioi 0 by
      unfold targetScale
      exact mul_pos (pow_pos (by norm_num) _)
        (mul_pos (Real.rpow_pos_of_pos hbR _) (Real.rpow_pos_of_pos hkR _)))).mp
  rw [Real.log_mul
      (x := (12 : ℝ) ^ b * (b : ℝ)) (y := Real.sqrt (k : ℝ))
      (mul_ne_zero (by positivity) (ne_of_gt hbR))
      (ne_of_gt (Real.sqrt_pos.2 hkR)),
    Real.log_mul (x := (12 : ℝ) ^ b) (y := (b : ℝ))
      (by positivity) (ne_of_gt hbR), Real.log_pow,
    Real.log_mul (x := (48 : ℝ) ^ b) (y := targetScale k b)
      (by positivity) (by
        unfold targetScale
        exact ne_of_gt (mul_pos (Real.rpow_pos_of_pos hbR _)
          (Real.rpow_pos_of_pos hkR _))),
    Real.log_pow, hlogsqrt, hlogscale, hlog12]
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith

private theorem second_contribution_le (k b : ℕ) (hk : 0 < k)
    (hb : 0 < b) :
    ((96 : ℝ) ^ b / 2) *
        Real.rpow (b : ℝ) ((3 - (b : ℝ)) / 2) *
        Real.rpow (k : ℝ) (((b : ℝ) + 1) / 2) ≤
      ((384 : ℝ) ^ b / 2) * targetScale k b := by
  have hbR : (0 : ℝ) < b := by positivity
  have hkR : (0 : ℝ) < k := by positivity
  have hlogb := log_nat_le_mul_log_two b hb
  have hlog4 : Real.log 384 = Real.log 96 + Real.log 4 := by
    rw [show (384 : ℝ) = 96 * 4 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  have hlog4' : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlogscale : Real.log (targetScale k b) =
      (-(b : ℝ) / 2) * Real.log (b : ℝ) +
        (((b : ℝ) + 1) / 2) * Real.log (k : ℝ) := by
    unfold targetScale
    rw [Real.log_mul
      (x := Real.rpow (b : ℝ) (-(b : ℝ) / 2))
      (y := Real.rpow (k : ℝ) (((b : ℝ) + 1) / 2))
      (ne_of_gt (Real.rpow_pos_of_pos hbR _))
      (ne_of_gt (Real.rpow_pos_of_pos hkR _))]
    exact congrArg₂ (· + ·) (Real.log_rpow hbR _)
      (Real.log_rpow hkR _)
  have hlogpair :
      Real.log (Real.rpow (b : ℝ) ((3 - (b : ℝ)) / 2)) +
        Real.log (Real.rpow (k : ℝ) (((b : ℝ) + 1) / 2)) =
      ((3 - (b : ℝ)) / 2) * Real.log (b : ℝ) +
        (((b : ℝ) + 1) / 2) * Real.log (k : ℝ) :=
    congrArg₂ (· + ·) (Real.log_rpow hbR _) (Real.log_rpow hkR _)
  have hrhslog : Real.log (((384 : ℝ) ^ b / 2) * targetScale k b) =
      (b : ℝ) * Real.log 384 - Real.log 2 +
        Real.log (targetScale k b) := by
    rw [Real.log_mul (x := (384 : ℝ) ^ b / 2) (y := targetScale k b)
      (by positivity) (by
        unfold targetScale
        exact ne_of_gt (mul_pos (Real.rpow_pos_of_pos hbR _)
          (Real.rpow_pos_of_pos hkR _))),
      Real.log_div (by positivity) (by norm_num), Real.log_pow]
  apply (Real.strictMonoOn_log.le_iff_le
    (show ((96 : ℝ) ^ b / 2) *
        Real.rpow (b : ℝ) ((3 - (b : ℝ)) / 2) *
        Real.rpow (k : ℝ) (((b : ℝ) + 1) / 2) ∈ Set.Ioi 0 by
      exact mul_pos (mul_pos (div_pos (pow_pos (by norm_num) _) (by norm_num))
        (Real.rpow_pos_of_pos hbR _)) (Real.rpow_pos_of_pos hkR _))
    (show ((384 : ℝ) ^ b / 2) * targetScale k b ∈ Set.Ioi 0 by
      unfold targetScale
      exact mul_pos (div_pos (pow_pos (by norm_num) _) (by norm_num))
        (mul_pos (Real.rpow_pos_of_pos hbR _) (Real.rpow_pos_of_pos hkR _)))).mp
  rw [Real.log_mul
      (x := ((96 : ℝ) ^ b / 2) * Real.rpow (b : ℝ) ((3 - (b : ℝ)) / 2))
      (y := Real.rpow (k : ℝ) (((b : ℝ) + 1) / 2))
      (by
        exact ne_of_gt (mul_pos (div_pos (pow_pos (by norm_num) _) (by norm_num))
          (Real.rpow_pos_of_pos hbR _)))
      (ne_of_gt (Real.rpow_pos_of_pos hkR _)),
    Real.log_mul (x := (96 : ℝ) ^ b / 2)
      (y := Real.rpow (b : ℝ) ((3 - (b : ℝ)) / 2))
      (by positivity) (ne_of_gt (Real.rpow_pos_of_pos hbR _)),
    Real.log_div (by positivity) (by norm_num), Real.log_pow]
  rw [hrhslog, hlogscale, hlog4, hlog4']
  calc
    (b : ℝ) * Real.log 96 - Real.log 2 +
        Real.log (Real.rpow (b : ℝ) ((3 - (b : ℝ)) / 2)) +
        Real.log (Real.rpow (k : ℝ) (((b : ℝ) + 1) / 2)) =
      (b : ℝ) * Real.log 96 - Real.log 2 +
        (Real.log (Real.rpow (b : ℝ) ((3 - (b : ℝ)) / 2)) +
          Real.log (Real.rpow (k : ℝ) (((b : ℝ) + 1) / 2))) := by ring
    _ = (b : ℝ) * Real.log 96 - Real.log 2 +
        (((3 - (b : ℝ)) / 2) * Real.log (b : ℝ) +
          (((b : ℝ) + 1) / 2) * Real.log (k : ℝ)) := by rw [hlogpair]
    _ ≤ (b : ℝ) * (Real.log 96 + 2 * Real.log 2) - Real.log 2 +
        ((-(b : ℝ) / 2) * Real.log (b : ℝ) +
          (((b : ℝ) + 1) / 2) * Real.log (k : ℝ)) := by
      have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      nlinarith

private theorem envelope_le (k b : ℕ) (hk : 0 < k) (hb : 0 < b)
    (hbk : b ≤ 3 * k) :
    1 + (12 : ℝ) ^ b * (b : ℝ) * Real.sqrt (k : ℝ) +
        ((96 : ℝ) ^ b / 2) *
          Real.rpow (b : ℝ) ((3 - (b : ℝ)) / 2) *
          Real.rpow (k : ℝ) (((b : ℝ) + 1) / 2) ≤
      (864 : ℝ) ^ b * targetScale k b := by
  have hfirst := first_contribution_le k b hk hb hbk
  have hsecond := second_contribution_le k b hk hb
  have hone : (1 : ℝ) ≤ (12 : ℝ) ^ b * (b : ℝ) * Real.sqrt (k : ℝ) := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hsqrt : 1 ≤ Real.sqrt (k : ℝ) := by rw [Real.one_le_sqrt]; exact hk1
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
    have hp : (1 : ℝ) ≤ 12 ^ b := one_le_pow₀ (by norm_num)
    calc
      (1 : ℝ) ≤ (12 : ℝ) ^ b := hp
      _ ≤ (12 : ℝ) ^ b * (b : ℝ) :=
        le_mul_of_one_le_right (by positivity) hb1
      _ ≤ (12 : ℝ) ^ b * (b : ℝ) * Real.sqrt (k : ℝ) :=
        le_mul_of_one_le_right (by positivity) hsqrt
  have h48 : (2 : ℝ) * 48 ^ b ≤ 192 ^ b := by
    have hb1 : 1 ≤ b := hb
    calc
      (2 : ℝ) * 48 ^ b ≤ 4 ^ b * 48 ^ b := by
        gcongr
        exact (show (2 : ℝ) ≤ 4 by norm_num).trans
          (by simpa using! (pow_le_pow_right₀
            (by norm_num : (1 : ℝ) ≤ 4) hb1))
      _ = 192 ^ b := by rw [← mul_pow]; norm_num
  have h192 : (192 : ℝ) ^ b + (384 ^ b / 2) ≤ 384 ^ b := by
    have hp : (2 : ℝ) * 192 ^ b ≤ 384 ^ b := by
      calc
        (2 : ℝ) * 192 ^ b ≤ 2 ^ b * 192 ^ b := by
          gcongr
          simpa using! (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hb)
        _ = 384 ^ b := by rw [← mul_pow]; norm_num
    linarith
  have hconst : (2 : ℝ) * 48 ^ b + 384 ^ b / 2 ≤ 864 ^ b := by
    calc
      (2 : ℝ) * 48 ^ b + 384 ^ b / 2 ≤ 192 ^ b + 384 ^ b / 2 := by gcongr
      _ ≤ 384 ^ b := h192
      _ ≤ 864 ^ b := by gcongr <;> norm_num
  have hscale : 0 ≤ targetScale k b := by
    unfold targetScale
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by positivity) _)
  calc
    1 + (12 : ℝ) ^ b * (b : ℝ) * Real.sqrt (k : ℝ) +
        ((96 : ℝ) ^ b / 2) *
          Real.rpow (b : ℝ) ((3 - (b : ℝ)) / 2) *
          Real.rpow (k : ℝ) (((b : ℝ) + 1) / 2) ≤
        2 * ((12 : ℝ) ^ b * (b : ℝ) * Real.sqrt (k : ℝ)) +
          ((96 : ℝ) ^ b / 2) *
            Real.rpow (b : ℝ) ((3 - (b : ℝ)) / 2) *
            Real.rpow (k : ℝ) (((b : ℝ) + 1) / 2) := by linarith
    _ ≤ (2 * 48 ^ b + 384 ^ b / 2) * targetScale k b := by
      nlinarith
    _ ≤ 864 ^ b * targetScale k b :=
      mul_le_mul_of_nonneg_right hconst hscale

/-- Equation (11): the uniform elementary coefficient estimate, including
the endpoint contribution inherited from `Q_one_identity`. -/
theorem Q_one_uniform (hF : FiniteEnumerationStatement) (k b : ℕ)
    (hk : 0 < k) (hb : 0 < b) (hbk : b ≤ 3 * k) :
    (Q k 1 b : ℝ) ≤
      (864 : ℝ) ^ b *
        Real.rpow (b : ℝ) (-(b : ℝ) / 2) *
        Real.rpow (k : ℝ) ((k : ℝ) + ((b : ℝ) - 1) / 2) := by
  rw [Q_one_identity hF k b hk]
  have hsum :
      (∑ j ∈ Finset.Icc 1 k,
        (j : ℝ) * ((b + j - 2).choose (b - 1) : ℝ) *
          (falling k j : ℝ) / (k : ℝ) ^ j) =
        ∑ j ∈ Finset.Icc 1 k, normalizedTerm k b j := by rfl
  rw [hsum]
  have hnorm := normalized_sum_le k b hk hb
  have henv := envelope_le k b hk hb hbk
  have hbR : (0 : ℝ) < b := by positivity
  have hbp : 1 ≤ b := hb
  have hratio_nat : (b : ℝ) ^ b / (b : ℝ) ^ (b - 1) = (b : ℝ) := by
    have hpow : (b : ℝ) ^ b = (b : ℝ) ^ (b - 1) * (b : ℝ) := by
      rw [← pow_succ, Nat.sub_add_cancel hbp]
    rw [hpow]
    field_simp
  have hpowcast : (b : ℝ) ^ (b - 1) =
      Real.rpow (b : ℝ) ((b : ℝ) - 1) := by
    calc
      (b : ℝ) ^ (b - 1) = Real.rpow (b : ℝ) ((b - 1 : ℕ) : ℝ) :=
        (Real.rpow_natCast (b : ℝ) (b - 1)).symm
      _ = Real.rpow (b : ℝ) ((b : ℝ) - 1) := by
        congr 1
        rw [Nat.cast_sub hbp]
        norm_num
  have hratio_rpow :
      Real.rpow (b : ℝ) (((b : ℝ) + 1) / 2) /
          (b : ℝ) ^ (b - 1) =
        Real.rpow (b : ℝ) ((3 - (b : ℝ)) / 2) := by
    rw [hpowcast]
    calc
      Real.rpow (b : ℝ) (((b : ℝ) + 1) / 2) /
          Real.rpow (b : ℝ) ((b : ℝ) - 1) =
          Real.rpow (b : ℝ)
            ((((b : ℝ) + 1) / 2) - ((b : ℝ) - 1)) :=
        (Real.rpow_sub hbR _ _).symm
      _ = _ := by congr 1; ring
  have hcoef1 :
      (6 : ℝ) ^ b * (2 : ℝ) ^ (b - 1) * 2 = 12 ^ b := by
    have h2 : (2 : ℝ) ^ (b - 1) * 2 = 2 ^ b := by
      rw [← pow_succ, Nat.sub_add_cancel hbp]
    calc
      (6 : ℝ) ^ b * 2 ^ (b - 1) * 2 = 6 ^ b * (2 ^ (b - 1) * 2) := by ring
      _ = 6 ^ b * 2 ^ b := by rw [h2]
      _ = 12 ^ b := by rw [← mul_pow]; norm_num
  have hcoef2 :
      (6 : ℝ) ^ b * (2 : ℝ) ^ (b - 1) * 8 ^ b = 96 ^ b / 2 := by
    have h2 : (2 : ℝ) ^ (b - 1) * 2 = 2 ^ b := by
      rw [← pow_succ, Nat.sub_add_cancel hbp]
    apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2
    calc
      ((6 : ℝ) ^ b * 2 ^ (b - 1) * 8 ^ b) * 2 =
          6 ^ b * (2 ^ (b - 1) * 2) * 8 ^ b := by ring
      _ = 6 ^ b * 2 ^ b * 8 ^ b := by rw [h2]
      _ = 96 ^ b := by rw [← mul_pow, ← mul_pow]; norm_num
  have hrewrite :
      1 + ((6 : ℝ) ^ b / (b : ℝ) ^ (b - 1)) *
          (2 : ℝ) ^ (b - 1) *
          ((b : ℝ) ^ b * (2 * Real.sqrt (k : ℝ)) +
            (8 : ℝ) ^ b *
              Real.rpow (b : ℝ) (((b : ℝ) + 1) / 2) *
              Real.rpow (k : ℝ) (((b : ℝ) + 1) / 2)) =
        1 + (12 : ℝ) ^ b * (b : ℝ) * Real.sqrt (k : ℝ) +
          ((96 : ℝ) ^ b / 2) *
            Real.rpow (b : ℝ) ((3 - (b : ℝ)) / 2) *
            Real.rpow (k : ℝ) (((b : ℝ) + 1) / 2) := by
    rw [mul_add]
    have hfirsteq :
        ((6 : ℝ) ^ b / (b : ℝ) ^ (b - 1)) *
            (2 : ℝ) ^ (b - 1) *
            ((b : ℝ) ^ b * (2 * Real.sqrt (k : ℝ))) =
          (12 : ℝ) ^ b * (b : ℝ) * Real.sqrt (k : ℝ) := by
      calc
        ((6 : ℝ) ^ b / (b : ℝ) ^ (b - 1)) *
            2 ^ (b - 1) * ((b : ℝ) ^ b * (2 * Real.sqrt (k : ℝ))) =
            ((6 : ℝ) ^ b * 2 ^ (b - 1) * 2) *
              ((b : ℝ) ^ b / (b : ℝ) ^ (b - 1)) *
                Real.sqrt (k : ℝ) := by ring
        _ = ((6 : ℝ) ^ b * 2 ^ (b - 1) * 2) *
              (b : ℝ) * Real.sqrt (k : ℝ) := by rw [hratio_nat]
        _ =
            ((6 : ℝ) ^ b * 2 ^ (b - 1) * 2) *
              (b : ℝ) * Real.sqrt (k : ℝ) := by ring
        _ = _ := by rw [hcoef1]
    have hsecondeq :
        ((6 : ℝ) ^ b / (b : ℝ) ^ (b - 1)) *
            (2 : ℝ) ^ (b - 1) *
            ((8 : ℝ) ^ b *
              Real.rpow (b : ℝ) (((b : ℝ) + 1) / 2) *
              Real.rpow (k : ℝ) (((b : ℝ) + 1) / 2)) =
          ((96 : ℝ) ^ b / 2) *
            Real.rpow (b : ℝ) ((3 - (b : ℝ)) / 2) *
            Real.rpow (k : ℝ) (((b : ℝ) + 1) / 2) := by
      rw [show ((6 : ℝ) ^ b / (b : ℝ) ^ (b - 1)) *
          2 ^ (b - 1) * (8 ^ b *
            Real.rpow (b : ℝ) (((b : ℝ) + 1) / 2) *
            Real.rpow (k : ℝ) (((b : ℝ) + 1) / 2)) =
          ((6 : ℝ) ^ b * 2 ^ (b - 1) * 8 ^ b) *
            (Real.rpow (b : ℝ) (((b : ℝ) + 1) / 2) /
              (b : ℝ) ^ (b - 1)) *
            Real.rpow (k : ℝ) (((b : ℝ) + 1) / 2) by ring,
        hcoef2, hratio_rpow]
    rw [hfirsteq, hsecondeq]
    ring
  have hscale :
      (k : ℝ) ^ (k - 1) * targetScale k b =
        Real.rpow (b : ℝ) (-(b : ℝ) / 2) *
          Real.rpow (k : ℝ) ((k : ℝ) + ((b : ℝ) - 1) / 2) := by
    have hkR : (0 : ℝ) < k := by positivity
    have hk1 : 1 ≤ k := hk
    have hkpow : (k : ℝ) ^ (k - 1) =
        Real.rpow (k : ℝ) ((k : ℝ) - 1) := by
      calc
        (k : ℝ) ^ (k - 1) = Real.rpow (k : ℝ) ((k - 1 : ℕ) : ℝ) :=
          (Real.rpow_natCast (k : ℝ) (k - 1)).symm
        _ = _ := by
          congr 1
          rw [Nat.cast_sub hk1]
          norm_num
    rw [hkpow]
    unfold targetScale
    calc
      Real.rpow (k : ℝ) ((k : ℝ) - 1) *
          (Real.rpow (b : ℝ) (-(b : ℝ) / 2) *
            Real.rpow (k : ℝ) (((b : ℝ) + 1) / 2)) =
          Real.rpow (b : ℝ) (-(b : ℝ) / 2) *
            (Real.rpow (k : ℝ) ((k : ℝ) - 1) *
              Real.rpow (k : ℝ) (((b : ℝ) + 1) / 2)) := by ring
      _ = Real.rpow (b : ℝ) (-(b : ℝ) / 2) *
          Real.rpow (k : ℝ)
            (((k : ℝ) - 1) + (((b : ℝ) + 1) / 2)) := by
        congr 1
        exact (Real.rpow_add hkR _ _).symm
      _ = _ := by congr 2 <;> ring
  calc
    (k : ℝ) ^ (k - 1) *
        ∑ j ∈ Finset.Icc 1 k, normalizedTerm k b j ≤
        (k : ℝ) ^ (k - 1) *
          (1 + ((6 : ℝ) ^ b / (b : ℝ) ^ (b - 1)) *
            (2 : ℝ) ^ (b - 1) *
            ((b : ℝ) ^ b * (2 * Real.sqrt (k : ℝ)) +
              (8 : ℝ) ^ b *
                Real.rpow (b : ℝ) (((b : ℝ) + 1) / 2) *
                Real.rpow (k : ℝ) (((b : ℝ) + 1) / 2))) := by gcongr
    _ = (k : ℝ) ^ (k - 1) *
        (1 + (12 : ℝ) ^ b * (b : ℝ) * Real.sqrt (k : ℝ) +
          ((96 : ℝ) ^ b / 2) *
            Real.rpow (b : ℝ) ((3 - (b : ℝ)) / 2) *
            Real.rpow (k : ℝ) (((b : ℝ) + 1) / 2)) := by rw [hrewrite]
    _ ≤ (k : ℝ) ^ (k - 1) * ((864 : ℝ) ^ b * targetScale k b) := by
      gcongr
    _ = (864 : ℝ) ^ b *
        Real.rpow (b : ℝ) (-(b : ℝ) / 2) *
        Real.rpow (k : ℝ) ((k : ℝ) + ((b : ℝ) - 1) / 2) := by
      calc
        (k : ℝ) ^ (k - 1) * ((864 : ℝ) ^ b * targetScale k b) =
            (864 : ℝ) ^ b * ((k : ℝ) ^ (k - 1) * targetScale k b) := by ring
        _ = _ := by rw [hscale]; ring


end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_SparseCoefficient


/-!
# Sparse-excess expansion majorant

This module combines the uniform kernel-mass and coefficient estimates and
sums over the admissible kernel sizes.  It closes exactly the `r < k` range;
the dense range remains the separate direct graph estimate.
-/

open scoped BigOperators

noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_SparseFinal

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Expansion
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Mass
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_SparseCoefficient

private def finalScale (k r : ℕ) : ℝ :=
  Real.rpow (r : ℝ) (-(r : ℝ) / 2) *
    Real.rpow (k : ℝ) ((k : ℝ) + (3 * (r : ℝ) - 1) / 2)

private theorem log_finalScale (k r : ℕ) (hk : 0 < k) (hr : 0 < r) :
    Real.log (finalScale k r) =
      (-(r : ℝ) / 2) * Real.log (r : ℝ) +
        ((k : ℝ) + (3 * (r : ℝ) - 1) / 2) *
          Real.log (k : ℝ) := by
  have hkR : (0 : ℝ) < k := by positivity
  have hrR : (0 : ℝ) < r := by positivity
  unfold finalScale
  rw [Real.log_mul
    (x := Real.rpow (r : ℝ) (-(r : ℝ) / 2))
    (y := Real.rpow (k : ℝ) ((k : ℝ) + (3 * (r : ℝ) - 1) / 2))
    (ne_of_gt (Real.rpow_pos_of_pos hrR _))
    (ne_of_gt (Real.rpow_pos_of_pos hkR _))]
  exact congrArg₂ (· + ·) (Real.log_rpow hrR _)
    (Real.log_rpow hkR _)

/-- The nonconstant factor in one kernel-size summand is at most the final
`r,k` scale whenever `r ≤ b ≤ 3r` and `r < k`. -/
private theorem summand_scale_le (k r b : ℕ) (hk : 0 < k) (hr : 0 < r)
    (hrb : r ≤ b) (hb3 : b ≤ 3 * r) (hrk : r < k) :
    (r : ℝ) ^ r * Real.rpow (b : ℝ) (-(b : ℝ) / 2) *
        Real.rpow (k : ℝ) ((k : ℝ) + ((b : ℝ) - 1) / 2) ≤
      finalScale k r := by
  have hkR : (0 : ℝ) < k := by positivity
  have hrR : (0 : ℝ) < r := by positivity
  have hbpos : 0 < b := lt_of_lt_of_le hr hrb
  have hbR : (0 : ℝ) < b := by exact_mod_cast hbpos
  have hrbR : (r : ℝ) ≤ b := by exact_mod_cast hrb
  have hrkR : (r : ℝ) ≤ k := by exact_mod_cast hrk.le
  have hlogrb : Real.log (r : ℝ) ≤ Real.log (b : ℝ) :=
    Real.strictMonoOn_log.monotoneOn (by exact hrR) (by exact hbR) hrbR
  have hlogrk : Real.log (r : ℝ) ≤ Real.log (k : ℝ) :=
    Real.strictMonoOn_log.monotoneOn (by exact hrR) (by exact hkR) hrkR
  let d : ℕ := 3 * r - b
  have hbd : b + d = 3 * r := by
    dsimp [d]
    omega
  have hdR : (0 : ℝ) ≤ d := by positivity
  have hweighted :
      (3 * (r : ℝ)) * Real.log (r : ℝ) ≤
        (b : ℝ) * Real.log (b : ℝ) +
          (d : ℝ) * Real.log (k : ℝ) := by
    have h₁ := mul_le_mul_of_nonneg_left hlogrb (show (0 : ℝ) ≤ b by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hlogrk hdR
    have hbdR : (b : ℝ) + d = 3 * (r : ℝ) := by exact_mod_cast hbd
    calc
      (3 * (r : ℝ)) * Real.log (r : ℝ) =
          ((b : ℝ) + (d : ℝ)) * Real.log (r : ℝ) := by rw [hbdR]
      _ = (b : ℝ) * Real.log (r : ℝ) +
          (d : ℝ) * Real.log (r : ℝ) := by ring
      _ ≤ (b : ℝ) * Real.log (b : ℝ) +
          (d : ℝ) * Real.log (k : ℝ) := add_le_add h₁ h₂
  have hsource :
      Real.log ((r : ℝ) ^ r * Real.rpow (b : ℝ) (-(b : ℝ) / 2) *
        Real.rpow (k : ℝ) ((k : ℝ) + ((b : ℝ) - 1) / 2)) =
      (r : ℝ) * Real.log (r : ℝ) +
        (-(b : ℝ) / 2) * Real.log (b : ℝ) +
        ((k : ℝ) + ((b : ℝ) - 1) / 2) * Real.log (k : ℝ) := by
    rw [Real.log_mul
      (x := (r : ℝ) ^ r * Real.rpow (b : ℝ) (-(b : ℝ) / 2))
      (y := Real.rpow (k : ℝ) ((k : ℝ) + ((b : ℝ) - 1) / 2))
      (mul_ne_zero (pow_ne_zero _ (ne_of_gt hrR))
        (ne_of_gt (Real.rpow_pos_of_pos hbR _)))
      (ne_of_gt (Real.rpow_pos_of_pos hkR _)),
      Real.log_mul (x := (r : ℝ) ^ r)
        (y := Real.rpow (b : ℝ) (-(b : ℝ) / 2))
        (pow_ne_zero _ (ne_of_gt hrR))
        (ne_of_gt (Real.rpow_pos_of_pos hbR _)),
      Real.log_pow]
    exact congrArg₂ (fun x y => (r : ℝ) * Real.log (r : ℝ) + x + y)
      (Real.log_rpow hbR _) (Real.log_rpow hkR _)
  have htarget := log_finalScale k r hk hr
  apply (Real.strictMonoOn_log.le_iff_le
    (show (r : ℝ) ^ r * Real.rpow (b : ℝ) (-(b : ℝ) / 2) *
        Real.rpow (k : ℝ) ((k : ℝ) + ((b : ℝ) - 1) / 2) ∈
          Set.Ioi 0 by
      exact mul_pos (mul_pos (pow_pos hrR _) (Real.rpow_pos_of_pos hbR _))
        (Real.rpow_pos_of_pos hkR _))
    (show finalScale k r ∈ Set.Ioi 0 by
      unfold finalScale
      exact mul_pos (Real.rpow_pos_of_pos hrR _) (Real.rpow_pos_of_pos hkR _))).mp
  rw [hsource, htarget]
  have hdcast : (d : ℝ) = 3 * (r : ℝ) - (b : ℝ) := by
    dsimp [d]
    rw [Nat.cast_sub hb3]
    push_cast
    rfl
  rw [hdcast] at hweighted
  nlinarith

private theorem expansionMajorant_le_Q_one (k r : ℕ) :
    expansionMajorant k r ≤
      ∑ v ∈ Finset.Icc 1 (2 * r),
        kernelMass v r * (Q k 1 (v + r) : ℝ) := by
  unfold expansionMajorant
  gcongr with v hv
  · unfold kernelMass kernelWeight
    positivity
  · have hvpos : 0 < v := (Finset.mem_Icc.mp hv).1
    exact_mod_cast Q_le_Q_one k v (v + r) hvpos

private theorem summand_le (hF : FiniteEnumerationStatement)
    (k r v : ℕ) (hk : 0 < k) (hr : 0 < r) (hrk : r < k)
    (hv : v ∈ Finset.Icc 1 (2 * r)) :
    kernelMass v r * (Q k 1 (v + r) : ℝ) ≤
      (1944 : ℝ) ^ r * (864 : ℝ) ^ (3 * r) * finalScale k r := by
  have hv' := Finset.mem_Icc.mp hv
  have hb : 0 < v + r := by omega
  have hb3k : v + r ≤ 3 * k := by omega
  have hb3r : v + r ≤ 3 * r := by omega
  have hrb : r ≤ v + r := by omega
  have hmass := kernelMass_uniform v r hv'.1 hr hv'.2
  have hQ := Q_one_uniform hF k (v + r) hk hb hb3k
  have h864 : (864 : ℝ) ^ (v + r) ≤ 864 ^ (3 * r) :=
    pow_le_pow_right₀ (by norm_num) hb3r
  have hscale := summand_scale_le k r (v + r) hk hr hrb hb3r hrk
  have hmassnonneg : 0 ≤ kernelMass v r := by
    unfold kernelMass kernelWeight
    positivity
  have hQnonneg : (0 : ℝ) ≤ Q k 1 (v + r) := by positivity
  calc
    kernelMass v r * (Q k 1 (v + r) : ℝ) ≤
        ((1944 : ℝ) ^ r * (r : ℝ) ^ r) *
          ((864 : ℝ) ^ (v + r) *
            Real.rpow (((v + r : ℕ) : ℝ)) (-(((v + r : ℕ) : ℝ)) / 2) *
            Real.rpow (k : ℝ)
              ((k : ℝ) + (((v + r : ℕ) : ℝ) - 1) / 2)) := by
      exact mul_le_mul hmass hQ hQnonneg (by positivity)
    _ ≤ ((1944 : ℝ) ^ r * (r : ℝ) ^ r) *
          ((864 : ℝ) ^ (3 * r) *
            Real.rpow (((v + r : ℕ) : ℝ)) (-(((v + r : ℕ) : ℝ)) / 2) *
            Real.rpow (k : ℝ)
              ((k : ℝ) + (((v + r : ℕ) : ℝ) - 1) / 2)) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h864
            (Real.rpow_nonneg (by positivity) _))
          (Real.rpow_nonneg (by positivity) _)
      · positivity
    _ ≤ (1944 : ℝ) ^ r * (864 : ℝ) ^ (3 * r) *
          finalScale k r := by
      have hscale' :
          (r : ℝ) ^ r * Real.rpow (((v + r : ℕ) : ℝ))
              (-(((v + r : ℕ) : ℝ)) / 2) *
              Real.rpow (k : ℝ)
                ((k : ℝ) + (((v + r : ℕ) : ℝ) - 1) / 2) ≤
            finalScale k r := by
        exact hscale
      calc
        ((1944 : ℝ) ^ r * (r : ℝ) ^ r) *
            ((864 : ℝ) ^ (3 * r) *
              Real.rpow (((v + r : ℕ) : ℝ)) (-(((v + r : ℕ) : ℝ)) / 2) *
              Real.rpow (k : ℝ)
                ((k : ℝ) + (((v + r : ℕ) : ℝ) - 1) / 2)) =
            ((1944 : ℝ) ^ r * (864 : ℝ) ^ (3 * r)) *
              ((r : ℝ) ^ r *
                Real.rpow (((v + r : ℕ) : ℝ)) (-(((v + r : ℕ) : ℝ)) / 2) *
                Real.rpow (k : ℝ)
                  ((k : ℝ) + (((v + r : ℕ) : ℝ) - 1) / 2)) := by ring
        _ ≤ ((1944 : ℝ) ^ r * (864 : ℝ) ^ (3 * r)) * finalScale k r :=
          mul_le_mul_of_nonneg_left hscale' (by positivity)
        _ = _ := by ring

private theorem two_mul_le_four_pow (r : ℕ) (hr : 0 < r) :
    ((2 * r : ℕ) : ℝ) ≤ (4 : ℝ) ^ r := by
  have hrpow : (r : ℝ) ≤ (2 : ℝ) ^ r := by
    have h := Nat.cast_le_pow_div_sub (by norm_num : (1 : ℝ) < 2) r
    convert h using 1 <;> ring
  have htwo : (2 : ℝ) ≤ 2 ^ r := by
    have hr1 : 1 ≤ r := hr
    simpa using! pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hr1
  calc
    ((2 * r : ℕ) : ℝ) = 2 * (r : ℝ) := by push_cast; ring
    _ ≤ (2 : ℝ) ^ r * 2 ^ r := mul_le_mul htwo hrpow (by positivity) (by positivity)
    _ = (4 : ℝ) ^ r := by rw [← mul_pow]; norm_num

/-- Equation (18): the sparse-excess bound for the exact finite expansion
majorant. -/
theorem expansionMajorant_sparse (hF : FiniteEnumerationStatement)
    (k r : ℕ) (hk : 0 < k) (hr : 0 < r) (hrk : r < k) :
    expansionMajorant k r ≤
      (5015306502144 : ℝ) ^ r *
        Real.rpow (r : ℝ) (-(r : ℝ) / 2) *
        Real.rpow (k : ℝ) ((k : ℝ) + (3 * (r : ℝ) - 1) / 2) := by
  have hterm : ∀ v ∈ Finset.Icc 1 (2 * r),
      kernelMass v r * (Q k 1 (v + r) : ℝ) ≤
        (1944 : ℝ) ^ r * (864 : ℝ) ^ (3 * r) * finalScale k r :=
    fun v hv => summand_le hF k r v hk hr hrk hv
  have hcard : (Finset.Icc 1 (2 * r)).card = 2 * r := by
    simp
  have hcount := two_mul_le_four_pow r hr
  calc
    expansionMajorant k r ≤
        ∑ v ∈ Finset.Icc 1 (2 * r),
          kernelMass v r * (Q k 1 (v + r) : ℝ) :=
      expansionMajorant_le_Q_one k r
    _ ≤ ∑ _v ∈ Finset.Icc 1 (2 * r),
        ((1944 : ℝ) ^ r * (864 : ℝ) ^ (3 * r) * finalScale k r) := by
      exact Finset.sum_le_sum fun v hv => hterm v hv
    _ = ((2 * r : ℕ) : ℝ) *
        ((1944 : ℝ) ^ r * (864 : ℝ) ^ (3 * r) * finalScale k r) := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
    _ ≤ (4 : ℝ) ^ r *
        ((1944 : ℝ) ^ r * (864 : ℝ) ^ (3 * r) * finalScale k r) := by
      exact mul_le_mul_of_nonneg_right hcount (by
        exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
          (by
            unfold finalScale
            exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
              (Real.rpow_nonneg (by positivity) _)))
    _ = (5015306502144 : ℝ) ^ r * finalScale k r := by
      rw [show (864 : ℝ) ^ (3 * r) = (864 ^ 3) ^ r by rw [pow_mul]]
      calc
        (4 : ℝ) ^ r *
            ((1944 : ℝ) ^ r * (864 ^ 3) ^ r * finalScale k r) =
            ((4 : ℝ) * 1944 * 864 ^ 3) ^ r * finalScale k r := by
          rw [mul_pow, mul_pow]
          ring
        _ = _ := by norm_num
    _ = (5015306502144 : ℝ) ^ r *
        Real.rpow (r : ℝ) (-(r : ℝ) / 2) *
        Real.rpow (k : ℝ) ((k : ℝ) + (3 * (r : ℝ) - 1) / 2) := by
      unfold finalScale
      ring

end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_SparseFinal
