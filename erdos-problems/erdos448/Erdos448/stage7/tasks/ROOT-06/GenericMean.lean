module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage6.TaskContracts

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT06.GenericMean

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Finset
open scoped BigOperators

noncomputable section

instance (p : Prop) : Decidable p := Classical.propDecidable p

lemma term_nonnegative
    {w : ArithmeticWeight} {c C Lambda : ℝ}
    (hw : WeightTypeSpec w c C Lambda) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    0 ≤ w (p ^ j) / (p : ℝ) ^ j := by
  cases j with
  | zero => simp [hw.normalized]
  | succ j =>
      exact div_nonneg
        (hw.prime_power_bounds p hp (j + 1) (by omega)).1
        (pow_nonneg (Nat.cast_nonneg p) _)

lemma series_summable
    {w : ArithmeticWeight} {c C Lambda : ℝ}
    (hw : WeightTypeSpec w c C Lambda) {p : ℕ} (hp : p.Prime) :
    Summable fun j : ℕ => w (p ^ j) / (p : ℝ) ^ j := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hr0 : 0 ≤ 1 / (p : ℝ) := by positivity
  have hr1 : 1 / (p : ℝ) < 1 := by
    rw [div_lt_one hp0]
    exact_mod_cast hp.one_lt
  refine .of_norm_bounded
    ((summable_geometric_of_lt_one hr0 hr1).mul_left (max 1 Lambda)) ?_
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg (term_nonnegative hw hp j)]
  cases j with
  | zero => simp [hw.normalized, le_max_left]
  | succ j =>
      calc
        w (p ^ (j + 1)) / (p : ℝ) ^ (j + 1)
            ≤ Lambda / (p : ℝ) ^ (j + 1) := by
              gcongr
              exact (hw.prime_power_bounds p hp (j + 1) (by omega)).2
        _ = Lambda * (1 / (p : ℝ)) ^ (j + 1) := by
          simp [div_eq_mul_inv, inv_pow]
        _ ≤ max 1 Lambda * (1 / (p : ℝ)) ^ (j + 1) := by
          gcongr
          exact le_max_right _ _

set_option maxHeartbeats 4000000 in
lemma geometric_tail_bound
    {Lambda : ℝ} (hLambda : 0 < Lambda) {p : ℕ} (hp : p.Prime) :
    (∑' j : ℕ, Lambda * (1 / (p : ℝ)) ^ (j + 2)) ≤
      2 * Lambda * (p : ℝ).rpow (-2) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hr0 : 0 ≤ 1 / (p : ℝ) := by positivity
  have hr1 : 1 / (p : ℝ) < 1 := by
    rw [div_lt_one hp0]
    linarith
  have hvalue :
      (∑' j : ℕ, Lambda * (1 / (p : ℝ)) ^ (j + 2)) =
        Lambda / ((p : ℝ) * ((p : ℝ) - 1)) := by
    calc
      (∑' j : ℕ, Lambda * (1 / (p : ℝ)) ^ (j + 2)) =
          (∑' j : ℕ, (1 / (p : ℝ)) ^ j *
            (Lambda * (1 / (p : ℝ)) ^ 2)) := by
              apply tsum_congr
              intro j
              rw [pow_add]
              ring
      _ = (∑' j : ℕ, (1 / (p : ℝ)) ^ j) *
          (Lambda * (1 / (p : ℝ)) ^ 2) := _root_.tsum_mul_right
      _ = (1 - 1 / (p : ℝ))⁻¹ *
          (Lambda * (1 / (p : ℝ)) ^ 2) := by
            rw [tsum_geometric_of_lt_one hr0 hr1]
      _ = Lambda / ((p : ℝ) * ((p : ℝ) - 1)) := by
        have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0
        have hpmne : (p : ℝ) - 1 ≠ 0 := by linarith
        field_simp [hpne, hpmne]
  rw [hvalue]
  have hrpowZ : (p : ℝ).rpow (-2 : ℝ) = (p : ℝ) ^ (-2 : ℤ) :=
    Real.rpow_neg_ofNat (p : ℝ) 2
  rw [hrpowZ, zpow_neg, zpow_ofNat]
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0
  field_simp [hpne, hpm1.ne']
  nlinarith

set_option maxHeartbeats 1000000 in
lemma series_tail_bound
    {w : ArithmeticWeight} {c C Lambda : ℝ}
    (hw : WeightTypeSpec w c C Lambda) {p : ℕ} (hp : p.Prime) :
    |meanEulerSeries w p - (1 + w p / p)| ≤
      2 * Lambda * (p : ℝ).rpow (-2) := by
  let f : ℕ → ℝ := fun j => w (p ^ j) / (p : ℝ) ^ j
  have hf : Summable f := series_summable hw hp
  have hf0 : f 0 = 1 := by simp [f, hw.normalized]
  have hf1 : f 1 = w p / p := by simp [f]
  have hinj1 : Function.Injective (fun j : ℕ => j + 1) := by
    intro a b h
    exact Nat.add_right_cancel h
  have hinj2 : Function.Injective (fun j : ℕ => j + 2) := by
    intro a b h
    exact Nat.add_right_cancel h
  have hfshift : Summable fun j : ℕ => f (j + 1) := hf.comp_injective hinj1
  have hfshift2 : Summable fun j : ℕ => f (j + 2) := hf.comp_injective hinj2
  have hsplit : meanEulerSeries w p =
      1 + w p / p + ∑' j : ℕ, f (j + 2) := by
    rw [meanEulerSeries,
      show (fun j => w (p ^ j) / (p : ℝ) ^ j) = f from rfl,
      hf.tsum_eq_zero_add, hfshift.tsum_eq_zero_add, hf0, hf1]
    ring
  have htail0 : ∀ j : ℕ, 0 ≤ f (j + 2) := by
    intro j
    exact term_nonnegative hw hp (j + 2)
  have htail : ∀ j : ℕ,
      f (j + 2) ≤ Lambda * (1 / (p : ℝ)) ^ (j + 2) := by
    intro j
    calc
      f (j + 2) ≤ Lambda / (p : ℝ) ^ (j + 2) := by
        dsimp [f]
        gcongr
        exact (hw.prime_power_bounds p hp (j + 2) (by omega)).2
      _ = Lambda * (1 / (p : ℝ)) ^ (j + 2) := by
        simp [div_eq_mul_inv, inv_pow]
  have hgeom : Summable fun j : ℕ =>
      Lambda * (1 / (p : ℝ)) ^ (j + 2) := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hr0 : 0 ≤ 1 / (p : ℝ) := by positivity
    have hr1 : 1 / (p : ℝ) < 1 := by
      rw [div_lt_one hp0]
      exact_mod_cast hp.one_lt
    have h := (summable_geometric_of_lt_one hr0 hr1).mul_left
      (Lambda * (1 / (p : ℝ)) ^ 2)
    simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using h
  have htailSum :
      (∑' j : ℕ, f (j + 2)) ≤
        ∑' j : ℕ, Lambda * (1 / (p : ℝ)) ^ (j + 2) :=
    hfshift2.tsum_le_tsum htail hgeom
  rw [hsplit]
  have htailNonneg : 0 ≤ ∑' j : ℕ, f (j + 2) := tsum_nonneg htail0
  rw [show 1 + w p / (p : ℝ) + (∑' j : ℕ, f (j + 2)) -
      (1 + w p / (p : ℝ)) = ∑' j : ℕ, f (j + 2) by ring,
    abs_of_nonneg htailNonneg]
  exact htailSum.trans (geometric_tail_bound hw.Lambda_pos hp)

lemma local_floor
    {w : ArithmeticWeight} {c C Lambda : ℝ}
    (hw : WeightTypeSpec w c C Lambda) {p : ℕ} (hp : p.Prime) :
    1 ≤ meanEulerSeries w p := by
  have hs := series_summable hw hp
  have hnonneg : ∀ j : ℕ, 0 ≤ w (p ^ j) / (p : ℝ) ^ j :=
    term_nonnegative hw hp
  have h := hs.sum_le_tsum {0} (fun j _ => hnonneg j)
  simpa [meanEulerSeries, hw.normalized] using h

lemma local_error
    {w : ArithmeticWeight} {c C Lambda : ℝ}
    (hw : WeightTypeSpec w c C Lambda) {p : ℕ} (hp : p.Prime) :
    |meanEulerSeries w p - (1 + (1 / 2 : ℝ) / p)| ≤
      (C + 2 * Lambda) * (p : ℝ).rpow (-1 - min c 1) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have htail := series_tail_bound hw hp
  have hfirst : |w p / p - (1 / 2 : ℝ) / p| ≤
      C * (p : ℝ).rpow (-1 - min c 1) := by
    have hwerr : |w p - 1 / 2| ≤ C * (p : ℝ).rpow (-c) := by
      simpa using hw.prime_power p hp 1 (by omega)
    have hpow : (p : ℝ).rpow (-c) * (p : ℝ)⁻¹ ≤
        (p : ℝ).rpow (-1 - min c 1) := by
      calc
        (p : ℝ).rpow (-c) * (p : ℝ)⁻¹ =
            (p : ℝ).rpow (-c + (-1 : ℝ)) := by
              rw [← Real.rpow_neg_one]
              exact (Real.rpow_add hp0 (-c) (-1 : ℝ)).symm
        _ ≤ (p : ℝ).rpow (-1 - min c 1) :=
          Real.rpow_le_rpow_of_exponent_le hp1 (by
            have := min_le_left c 1
            linarith)
    calc
      |w p / p - (1 / 2 : ℝ) / p| = |w p - 1 / 2| * (p : ℝ)⁻¹ := by
        rw [show w p / (p : ℝ) - (1 / 2 : ℝ) / p =
          (w p - 1 / 2) * (p : ℝ)⁻¹ by ring, abs_mul,
          abs_inv, abs_of_pos hp0]
      _ ≤ (C * (p : ℝ).rpow (-c)) * (p : ℝ)⁻¹ := by
        gcongr
      _ ≤ C * (p : ℝ).rpow (-1 - min c 1) := by
        calc
          (C * (p : ℝ).rpow (-c)) * (p : ℝ)⁻¹ =
              C * ((p : ℝ).rpow (-c) * (p : ℝ)⁻¹) := by ring
          _ ≤ C * (p : ℝ).rpow (-1 - min c 1) := by
            gcongr
            exact hw.C_pos.le
  have heta : (-2 : ℝ) ≤ -1 - min c 1 := by
    have := min_le_right c 1
    linarith
  have htail' : 2 * Lambda * (p : ℝ).rpow (-2) ≤
      2 * Lambda * (p : ℝ).rpow (-1 - min c 1) := by
    gcongr
    · exact mul_nonneg (by norm_num) hw.Lambda_pos.le
    · exact Real.rpow_le_rpow_of_exponent_le hp1 heta
  calc
    |meanEulerSeries w p - (1 + (1 / 2 : ℝ) / p)| ≤
        |meanEulerSeries w p - (1 + w p / p)| +
          |w p / p - (1 / 2 : ℝ) / p| := by
            rw [show meanEulerSeries w p - (1 + (1 / 2 : ℝ) / p) =
              (meanEulerSeries w p - (1 + w p / p)) +
                (w p / p - (1 / 2 : ℝ) / p) by ring]
            exact abs_add_le _ _
    _ ≤ 2 * Lambda * (p : ℝ).rpow (-1 - min c 1) +
        C * (p : ℝ).rpow (-1 - min c 1) := add_le_add (htail.trans htail') hfirst
    _ = (C + 2 * Lambda) * (p : ℝ).rpow (-1 - min c 1) := by ring

lemma geometric_bound
    {w : ArithmeticWeight} {c C Lambda : ℝ}
    (hw : WeightTypeSpec w c C Lambda) :
    PrimePowerGeometricBound w (max 1 Lambda) 1 := by
  intro p hp j
  cases j with
  | zero => simp [hw.normalized, le_max_left]
  | succ j =>
      constructor
      · exact (hw.prime_power_bounds p hp (j + 1) (by omega)).1
      · simpa using (hw.prime_power_bounds p hp (j + 1) (by omega)).2.trans
          (le_max_right 1 Lambda)

lemma strict_product_eq_interval
    (L : ℕ → ℝ) (Z : ℝ) :
    (∏ p ∈ strictPrimeRange Z, L p) = primeIntervalProduct L 2 Z := by
  unfold primeIntervalProduct
  apply Finset.prod_congr rfl
  intro p hp
  have hpprime : p.Prime := (Finset.mem_filter.mp hp).2
  simp [show (2 : ℝ) ≤ p by exact_mod_cast hpprime.two_le]

theorem p059 (hEXT001 : EXT001Statement) (hP008 : P008Statement.{0}) :
    P059Statement.{0} := by
  intro Q w hQ cw Cw LambdaW hcw hCw hLambdaW hw
  let eta : ℝ := min cw 1
  let Cerr : ℝ := Cw + 2 * LambdaW
  have heta : 0 < eta := lt_min hcw zero_lt_one
  have hCerr : 0 < Cerr := by dsimp [Cerr]; linarith
  obtain ⟨E⟩ := hEXT001 (max 1 LambdaW) 1
    ⟨zero_le_one.trans (le_max_left _ _), zero_le_one, by norm_num⟩
  obtain ⟨P⟩ := hP008 Q hQ (1 / 2) (1 / 2) (le_refl _)
    (by norm_num) eta Cerr heta hCerr 2 1 1 (le_refl _)
    zero_lt_one (le_refl _) (fun _ : Q => (1 / 2 : ℝ))
    (fun _ => ⟨le_rfl, le_rfl⟩)
    (fun q p => meanEulerSeries (w q) p)
    (fun q p hp => local_floor (hw q) hp)
    (fun q p hp _ => by simpa [eta, Cerr] using local_error (hw q) hp)
    (fun q p hp hp2 hplt => by
      exfalso
      exact (not_lt_of_ge (by exact_mod_cast hp2 : (2 : ℝ) ≤ p)) hplt)
  let B : ℝ := max 1 P.comparison.upper
  have hB : 1 ≤ B := le_max_left _ _
  have hPB : P.comparison.upper ≤ B := le_max_right _ _
  let Cmean : ℝ := E.constant * B *
    (Real.log 2).rpow (-1 / 2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hCmean : 0 < Cmean := mul_pos (mul_pos E.constant_pos (zero_lt_one.trans_le hB))
    (Real.rpow_pos_of_pos hlog2 _)
  refine ⟨Cmean, hCmean, ?_⟩
  intro q Z hZ
  have hmean := E.bound (w q) (hw q).nonnegative_multiplicative
    (geometric_bound (hw q)) Z hZ
  have hprod : primeIntervalProduct (fun p => meanEulerSeries (w q) p) 2 Z ≤
      B * (Real.log Z / Real.log 2).rpow (1 / 2 : ℝ) := by
    by_cases heq : Z = 2
    · subst Z
      rw [P.empty_branch q 2 2 le_rfl le_rfl le_rfl]
      simp [hlog2.ne', hB]
    · exact ((P.family_bounds q 2 Z le_rfl (lt_of_le_of_ne hZ (Ne.symm heq))).2).trans
        (mul_le_mul_of_nonneg_right hPB (Real.rpow_nonneg
          (div_nonneg (Real.log_nonneg (one_le_two.trans hZ))
            (Real.log_nonneg one_le_two)) _))
  unfold familyPartialSum
  unfold strictMean at hmean
  rw [strictEulerProduct, strict_product_eq_interval] at hmean
  have hlogZ : 0 < Real.log Z := Real.log_pos (one_lt_two.trans_le hZ)
  have hpow : (Real.log Z / Real.log 2).rpow (1 / 2 : ℝ) =
      (Real.log Z).rpow (1 / 2 : ℝ) *
        (Real.log 2).rpow (-1 / 2 : ℝ) := by
    calc
      (Real.log Z / Real.log 2).rpow (1 / 2 : ℝ) =
          (Real.log Z).rpow (1 / 2 : ℝ) /
            (Real.log 2).rpow (1 / 2 : ℝ) :=
        Real.div_rpow hlogZ.le hlog2.le (1 / 2 : ℝ)
      _ = (Real.log Z).rpow (1 / 2 : ℝ) *
          (Real.log 2).rpow (-1 / 2 : ℝ) := by
            rw [div_eq_mul_inv]
            congr 1
            symm
            simpa only [Real.rpow_eq_pow, show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring] using
              Real.rpow_neg hlog2.le (1 / 2 : ℝ)
  calc
      ∑ r ∈ positiveNatsBelow Z, w q r
          ≤ E.constant * (Z / Real.log Z) *
              primeIntervalProduct (meanEulerSeries (w q)) 2 Z := hmean
      _ ≤ E.constant * (Z / Real.log Z) *
          (B *
            (Real.log Z / Real.log 2).rpow (1 / 2 : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hprod
                (mul_nonneg E.constant_pos.le
                  (div_nonneg (zero_le_two.trans hZ)
                    (Real.log_nonneg (one_le_two.trans hZ))))
      _ = Cmean * Z * (Real.log Z).rpow (-1 / 2) := by
        rw [hpow]
        dsimp [Cmean]
        have hcombine : (Real.log Z).rpow (-1 : ℝ) *
            (Real.log Z).rpow (1 / 2 : ℝ) =
            (Real.log Z).rpow (-1 / 2 : ℝ) := by
          calc
            (Real.log Z).rpow (-1 : ℝ) * (Real.log Z).rpow (1 / 2 : ℝ) =
                (Real.log Z).rpow ((-1 : ℝ) + 1 / 2) :=
              (Real.rpow_add hlogZ (-1 : ℝ) (1 / 2 : ℝ)).symm
            _ = (Real.log Z).rpow (-1 / 2 : ℝ) := by norm_num
        rw [show Z / Real.log Z = Z * (Real.log Z)⁻¹ by ring,
          ← Real.rpow_neg_one (Real.log Z)]
        calc
          E.constant * (Z * (Real.log Z).rpow (-1)) *
              (B * ((Real.log Z).rpow (1 / 2) * (Real.log 2).rpow (-1 / 2))) =
            E.constant * B * (Real.log 2).rpow (-1 / 2) * Z *
              ((Real.log Z).rpow (-1) * (Real.log Z).rpow (1 / 2)) := by ring
          _ = E.constant * B * (Real.log 2).rpow (-1 / 2) * Z *
              (Real.log Z).rpow (-1 / 2) := by rw [hcombine]

end

end Erdos448.Stage7.ROOT06.GenericMean
