module

public import Erdos745.WrapUp.Proofs.Internal.Linked.W04_Foundation
public import Erdos745.WrapUp.Proofs.Internal.Linked.W04_Finite

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


/-!
Sharp two-variable consequences of the entropy curvature estimate.  These are
kept separate from the one-variable local development because the mixed W04
estimate needs a rectangle difference, not three applications of a local
absolute-value bound.
-/
namespace Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_Entropy

noncomputable section

open W04_TUPLES_Local

theorem entropySlope_rectangle_bound {lam x y : ℝ}
    (hlo : (1 : ℝ) / 2 ≤ lam) (hhi : lam ≤ (3 : ℝ) / 2)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hxy : x + y ≤ (1 : ℝ) / 16) :
    |entropySlope lam (x + y) - entropySlope lam y| ≤
      32 * (|lam - 1| + x + y) * x := by
  let C : ℝ := 32 * (|lam - 1| + x + y)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hderiv : ∀ u ∈ Set.Icc (0 : ℝ) x,
      HasDerivWithinAt (fun z : ℝ => entropySlope lam (z + y))
        (entropyCurvature lam (u + y)) (Set.Icc (0 : ℝ) x) u := by
    intro u hu
    have hu0 : 0 ≤ u := hu.1
    have huy : u + y < 1 := by linarith [hu.2, hxy]
    have h2uy : 2 * (u + y) < lam := by linarith [hu.2, hxy, hlo]
    convert ((hasDerivAt_entropySlope (lam := lam) (t := u + y)
      huy h2uy).comp u ((hasDerivAt_id u).add_const y)).hasDerivWithinAt using 1
    all_goals simp
  have hbound : ∀ u ∈ Set.Ico (0 : ℝ) x,
      ‖entropyCurvature lam (u + y)‖ ≤ C := by
    intro u hu
    rw [Real.norm_eq_abs]
    have huv0 : 0 ≤ u + y := add_nonneg hu.1 hy0
    have huv : u + y ≤ (1 : ℝ) / 16 := by
      linarith [hu.2.le, hxy]
    calc
      |entropyCurvature lam (u + y)| ≤
          32 * (|lam - 1| + (u + y)) :=
        entropyCurvature_bound hlo hhi huv0 huv
      _ ≤ C := by
        dsimp [C]
        nlinarith [abs_nonneg (lam - 1), hu.2.le]
  have hmain := norm_image_sub_le_of_norm_deriv_le_segment'
    hderiv hbound x ⟨hx0, le_rfl⟩
  simp only [zero_add, Real.norm_eq_abs] at hmain
  simpa [C, add_assoc, add_comm, add_left_comm] using! hmain

theorem entropy_rectangle_bound {lam x y : ℝ}
    (hlo : (1 : ℝ) / 2 ≤ lam) (hhi : lam ≤ (3 : ℝ) / 2)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hxy : x + y ≤ (1 : ℝ) / 16) :
    |entropyCore lam (x + y) - entropyCore lam x - entropyCore lam y| ≤
      32 * (|lam - 1| + x + y) * x * y := by
  have hlam : 0 < lam := lt_of_lt_of_le (by norm_num) hlo
  let C : ℝ := 32 * (|lam - 1| + x + y) * x
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hderiv : ∀ v ∈ Set.Icc (0 : ℝ) y,
      HasDerivWithinAt
        (fun z : ℝ => entropyCore lam (x + z) -
          entropyCore lam x - entropyCore lam z)
        (entropySlope lam (x + v) - entropySlope lam v)
        (Set.Icc (0 : ℝ) y) v := by
    intro v hv
    have hv0 : 0 ≤ v := hv.1
    have hxv1 : x + v < 1 := by linarith [hv.2, hxy]
    have h2xv : 2 * (x + v) < lam := by linarith [hv.2, hxy, hlo]
    have hv1 : v < 1 := by linarith [hv.2, hxy, hx0]
    have h2v : 2 * v < lam := by linarith [hv.2, hxy, hx0, hlo]
    have hleft := (hasDerivAt_entropyCore (lam := lam) (t := x + v)
      hlam hxv1 h2xv).comp v ((hasDerivAt_const v x).add (hasDerivAt_id v))
    have hright := hasDerivAt_entropyCore (lam := lam) (t := v)
      hlam hv1 h2v
    convert ((hleft.sub_const (entropyCore lam x)).sub hright).hasDerivWithinAt using 1
    all_goals simp
  have hbound : ∀ v ∈ Set.Ico (0 : ℝ) y,
      ‖entropySlope lam (x + v) - entropySlope lam v‖ ≤ C := by
    intro v hv
    rw [Real.norm_eq_abs]
    have h := entropySlope_rectangle_bound hlo hhi hx0 hv.1
      (by linarith [hv.2.le, hxy])
    dsimp [C]
    exact le_trans h (by
      gcongr
      linarith [hv.2.le])
  have hmain := norm_image_sub_le_of_norm_deriv_le_segment'
    hderiv hbound y ⟨hy0, le_rfl⟩
  simp only [add_zero, entropyCore_zero, sub_zero, Real.norm_eq_abs] at hmain
  simpa [C, mul_assoc] using! hmain

theorem scaled_entropy_rectangle {n lam k l : ℝ}
    (hn : 0 < n)
    (hlo : (1 : ℝ) / 2 ≤ lam) (hhi : lam ≤ (3 : ℝ) / 2)
    (hk0 : 0 ≤ k) (hl0 : 0 ≤ l)
    (hkl : k + l ≤ n / 16) :
    |n * (entropyCore lam ((k + l) / n) -
        entropyCore lam (k / n) - entropyCore lam (l / n))| ≤
      32 * (|lam - 1| * k * l / n + k * l * (k + l) / n ^ 2) := by
  have hx0 : 0 ≤ k / n := div_nonneg hk0 hn.le
  have hy0 : 0 ≤ l / n := div_nonneg hl0 hn.le
  have hxy : k / n + l / n ≤ (1 : ℝ) / 16 := by
    rw [← add_div]
    exact (div_le_iff₀ hn).2 (by linarith)
  have h := entropy_rectangle_bound hlo hhi hx0 hy0 hxy
  have hn0 : 0 ≤ n := hn.le
  rw [abs_mul, abs_of_pos hn]
  calc
    n * |entropyCore lam ((k + l) / n) -
        entropyCore lam (k / n) - entropyCore lam (l / n)| =
        n * |entropyCore lam (k / n + l / n) -
          entropyCore lam (k / n) - entropyCore lam (l / n)| := by
          rw [add_div]
    _ ≤ n * (32 * (|lam - 1| + k / n + l / n) *
          (k / n) * (l / n)) := mul_le_mul_of_nonneg_left h hn0
    _ = 32 * (|lam - 1| * k * l / n +
          k * l * (k + l) / n ^ 2) := by
      field_simp
      ring

end

end Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_Entropy


/-!
Assembly lemmas for the two near-critical consumers of W04.

The finite combinatorial part is deliberately represented by a bound on the
deviation from `n * entropyCore + rate * K`.  This is the common output of the
exact finite-ratio calculation.  The lemmas below perform the remaining
one-variable entropy cancellation and the genuinely two-variable mixed
subtraction without losing the `k*l` structure.
-/
namespace Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_Assembly

noncomputable section
open scoped BigOperators

open W04_TUPLES_Local
open W04_TUPLES_Entropy
open W04_TUPLES_Mixed

theorem localBound_of_logRemainder
    (n M q : ℕ) (ks : Fin q → ℕ) (D C : ℝ)
    (hn : 0 < n)
    (hlo : (1 : ℝ) / 2 ≤ degreeAt n M)
    (hhi : degreeAt n M ≤ (3 : ℝ) / 2)
    (hK0 : 0 ≤ ∑ i, (ks i : ℝ))
    (hK : (∑ i, (ks i : ℝ)) ≤ (n : ℝ) / 16)
    (hJ : 0 < tupleMoment n M q ks)
    (hrem :
      |Real.log (tupleMoment n M q ks / tupleLeading n M q ks) -
          ((n : ℝ) * entropyCore (degreeAt n M)
              ((∑ i, (ks i : ℝ)) / n) +
            rate (degreeAt n M) * (∑ i, (ks i : ℝ)))| ≤
        D * (∑ i, (ks i : ℝ)) / n)
    (hDC : D ≤ C) (h32C : 32 ≤ C) :
    tupleLocalBound n M q ks C := by
  dsimp only [tupleLocalBound]
  constructor
  · exact hJ
  · have hmain := finiteLog_to_local
        (L := Real.log (tupleMoment n M q ks / tupleLeading n M q ks))
        (n := n) (lam := degreeAt n M)
        (K := ∑ i, (ks i : ℝ)) (C := D)
        (Nat.cast_pos.mpr hn) hlo hhi hK0 hK hrem
    have hn0 : 0 ≤ (n : ℝ) := (Nat.cast_pos.mpr hn).le
    have hKn : 0 ≤ (∑ i, (ks i : ℝ)) / n :=
      div_nonneg hK0 hn0
    have hquad : 0 ≤
        |degreeAt n M - 1| * (∑ i, (ks i : ℝ)) ^ 2 / n := by
      positivity
    have hcubic : 0 ≤
        (∑ i, (ks i : ℝ)) ^ 3 / (n : ℝ) ^ 2 := by
      positivity
    calc
      |Real.log (tupleMoment n M q ks / tupleLeading n M q ks)| ≤
          D * ((∑ i, (ks i : ℝ)) / n) +
            32 * (|degreeAt n M - 1| *
              (∑ i, (ks i : ℝ)) ^ 2 / n +
              (∑ i, (ks i : ℝ)) ^ 3 / (n : ℝ) ^ 2) := by
        convert hmain using 1 <;> ring
      _ ≤ C * ((∑ i, (ks i : ℝ)) / n +
            |degreeAt n M - 1| *
              (∑ i, (ks i : ℝ)) ^ 2 / n +
            (∑ i, (ks i : ℝ)) ^ 3 / (n : ℝ) ^ 2) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hDC) hKn,
          mul_nonneg (sub_nonneg.mpr h32C) hquad,
          mul_nonneg (sub_nonneg.mpr h32C) hcubic]

theorem mixedBound_of_logRemainders
    (n M k l : ℕ) (D₂ D₁ C : ℝ)
    (hn : 0 < n)
    (hlo : (1 : ℝ) / 2 ≤ degreeAt n M)
    (hhi : degreeAt n M ≤ (3 : ℝ) / 2)
    (hk : 0 < k) (hl : 0 < l)
    (hkl : ((k + l : ℕ) : ℝ) ≤ (n : ℝ) / 16)
    (hJ₂ : 0 < tupleMoment n M 2
      (fun i => if i.val = 0 then k else l))
    (hJk : 0 < tupleMoment n M 1 (fun _ => k))
    (hJl : 0 < tupleMoment n M 1 (fun _ => l))
    (hrem₂ :
      |Real.log (tupleMoment n M 2
          (fun i => if i.val = 0 then k else l) /
          tupleLeading n M 2 (fun i => if i.val = 0 then k else l)) -
        ((n : ℝ) * entropyCore (degreeAt n M) (((k : ℝ) + l) / n) +
          rate (degreeAt n M) * ((k : ℝ) + l))| ≤
        D₂ * ((k : ℝ) + l) / n)
    (hremk :
      |Real.log (tupleMoment n M 1 (fun _ => k) /
          tupleLeading n M 1 (fun _ => k)) -
        ((n : ℝ) * entropyCore (degreeAt n M) ((k : ℝ) / n) +
          rate (degreeAt n M) * k)| ≤ D₁ * k / n)
    (hreml :
      |Real.log (tupleMoment n M 1 (fun _ => l) /
          tupleLeading n M 1 (fun _ => l)) -
        ((n : ℝ) * entropyCore (degreeAt n M) ((l : ℝ) / n) +
          rate (degreeAt n M) * l)| ≤ D₁ * l / n)
    (hD₂0 : 0 ≤ D₂) (hD₁0 : 0 ≤ D₁)
    (hDC : D₂ + D₁ ≤ C) (h32C : 32 ≤ C) :
    let pair : Fin 2 → ℕ := fun i => if i.val = 0 then k else l
    |Real.log (tupleMoment n M 2 pair /
      (tupleMoment n M 1 (fun _ => k) *
        tupleMoment n M 1 (fun _ => l)))| ≤
      C * (((k : ℝ) + l) / n +
        |degreeAt n M - 1| * k * l / n +
        (k : ℝ) * l * (k + l) / (n : ℝ) ^ 2) := by
  dsimp only
  let L₂ := Real.log (tupleMoment n M 2
    (fun i => if i.val = 0 then k else l) /
      tupleLeading n M 2 (fun i => if i.val = 0 then k else l))
  let Lk := Real.log (tupleMoment n M 1 (fun _ => k) /
    tupleLeading n M 1 (fun _ => k))
  let Ll := Real.log (tupleMoment n M 1 (fun _ => l) /
    tupleLeading n M 1 (fun _ => l))
  let F₂ := (n : ℝ) * entropyCore (degreeAt n M) (((k : ℝ) + l) / n) +
    rate (degreeAt n M) * ((k : ℝ) + l)
  let Fk := (n : ℝ) * entropyCore (degreeAt n M) ((k : ℝ) / n) +
    rate (degreeAt n M) * k
  let Fl := (n : ℝ) * entropyCore (degreeAt n M) ((l : ℝ) / n) +
    rate (degreeAt n M) * l
  have hsubtract := mixedLog_subtract n M k l hn
    (lt_of_lt_of_le (by norm_num) hlo) hk hl hJ₂ hJk hJl
  have hentropy := scaled_entropy_rectangle
    (n := (n : ℝ)) (lam := degreeAt n M) (k := (k : ℝ)) (l := (l : ℝ))
    (Nat.cast_pos.mpr hn) hlo hhi (by positivity) (by positivity) (by
      exact_mod_cast hkl)
  have hdecomp :
      Real.log (tupleMoment n M 2
          (fun i => if i.val = 0 then k else l) /
        (tupleMoment n M 1 (fun _ => k) *
          tupleMoment n M 1 (fun _ => l))) =
        (L₂ - F₂) - (Lk - Fk) - (Ll - Fl) +
          (n : ℝ) *
            (entropyCore (degreeAt n M) (((k : ℝ) + l) / n) -
              entropyCore (degreeAt n M) ((k : ℝ) / n) -
              entropyCore (degreeAt n M) ((l : ℝ) / n)) := by
    rw [hsubtract]
    dsimp [L₂, Lk, Ll, F₂, Fk, Fl]
    ring
  rw [hdecomp]
  have hres :
      |(L₂ - F₂) - (Lk - Fk) - (Ll - Fl)| ≤
        (D₂ + D₁) * (((k : ℝ) + l) / n) := by
    have hrem₂' : |L₂ - F₂| ≤ D₂ * (((k : ℝ) + l) / n) := by
      dsimp [L₂, F₂]
      convert hrem₂ using 1 <;> ring
    have hremk' : |Lk - Fk| ≤ D₁ * ((k : ℝ) / n) := by
      dsimp [Lk, Fk]
      convert hremk using 1 <;> ring
    have hreml' : |Ll - Fl| ≤ D₁ * ((l : ℝ) / n) := by
      dsimp [Ll, Fl]
      convert hreml using 1 <;> ring
    calc
      |(L₂ - F₂) - (Lk - Fk) - (Ll - Fl)| ≤
          |L₂ - F₂| + |Lk - Fk| + |Ll - Fl| := by
        linarith [abs_sub (L₂ - F₂) (Lk - Fk),
          abs_sub ((L₂ - F₂) - (Lk - Fk)) (Ll - Fl)]
      _ ≤ D₂ * (((k : ℝ) + l) / n) +
          D₁ * ((k : ℝ) / n) + D₁ * ((l : ℝ) / n) := by
        exact add_le_add (add_le_add hrem₂' hremk') hreml'
      _ = (D₂ + D₁) * (((k : ℝ) + l) / n) := by ring
  have hbase : 0 ≤ ((k : ℝ) + l) / n := by positivity
  have hquad : 0 ≤ |degreeAt n M - 1| * (k : ℝ) * l / n := by
    positivity
  have hcubic : 0 ≤
      (k : ℝ) * l * ((k : ℝ) + l) / (n : ℝ) ^ 2 := by
    positivity
  calc
    |(L₂ - F₂) - (Lk - Fk) - (Ll - Fl) +
        (n : ℝ) *
          (entropyCore (degreeAt n M) (((k : ℝ) + l) / n) -
            entropyCore (degreeAt n M) ((k : ℝ) / n) -
            entropyCore (degreeAt n M) ((l : ℝ) / n))| ≤
      |(L₂ - F₂) - (Lk - Fk) - (Ll - Fl)| +
        |(n : ℝ) *
          (entropyCore (degreeAt n M) (((k : ℝ) + l) / n) -
            entropyCore (degreeAt n M) ((k : ℝ) / n) -
            entropyCore (degreeAt n M) ((l : ℝ) / n))| := abs_add_le _ _
    _ ≤ (D₂ + D₁) * (((k : ℝ) + l) / n) +
        32 * (|degreeAt n M - 1| * (k : ℝ) * l / n +
          (k : ℝ) * l * ((k : ℝ) + l) / (n : ℝ) ^ 2) :=
      add_le_add hres hentropy
    _ ≤ C * (((k : ℝ) + l) / n +
        |degreeAt n M - 1| * k * l / n +
        (k : ℝ) * l * (k + l) / (n : ℝ) ^ 2) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hDC) hbase,
        mul_nonneg (sub_nonneg.mpr h32C) hquad,
        mul_nonneg (sub_nonneg.mpr h32C) hcubic]

end

end Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_Assembly


/-!
Uniform finite log remainder in the near-critical range.

This module discharges the natural-number guards and the four finite-factor
side conditions needed by `tupleLog_to_finiteMain`, then joins that estimate
to the algebraic finite-main remainder.
-/
namespace Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_Near

noncomputable section
open scoped BigOperators

open W04_TUPLES_Foundation
open W04_TUPLES_Local
open W04_TUPLES_FiniteBridge

private theorem finite_factor_error_bound
    {n M A b r K : ℝ}
    (hn : 0 < n) (hK1 : 1 ≤ K)
    (hr0 : 0 ≤ r) (hrK : r ≤ K)
    (hb0 : 0 ≤ b) (hbn : b ≤ n)
    (hMlo : n / 4 ≤ M) (hMhi : M ≤ n)
    (hAlower : n ^ 2 / 4 ≤ A)
    (hNlower : n ^ 2 / 4 ≤ (n * (n - 1) / 2)) :
    2 * K / n + 2 * b ^ 3 / A ^ 2 + 2 * r / M +
        2 * M ^ 3 / (n * (n - 1) / 2) ^ 2 ≤
      74 * K / n := by
  have hn4 : 0 < n / 4 := by positivity
  have hM0 : 0 < M := lt_of_lt_of_le hn4 hMlo
  have hbase0 : 0 < n ^ 2 / 4 := by positivity
  have hA0 : 0 < A := lt_of_lt_of_le hbase0 hAlower
  have hN0 : 0 < n * (n - 1) / 2 := lt_of_lt_of_le hbase0 hNlower
  have hb3 : b ^ 3 ≤ n ^ 3 := by gcongr
  have hM3 : M ^ 3 ≤ n ^ 3 := by gcongr
  have hA2 : (n ^ 2 / 4) ^ 2 ≤ A ^ 2 := by gcongr
  have hN2 : (n ^ 2 / 4) ^ 2 ≤ (n * (n - 1) / 2) ^ 2 := by gcongr
  have hbterm : 2 * b ^ 3 / A ^ 2 ≤ 32 / n := by
    calc
      2 * b ^ 3 / A ^ 2 ≤ 2 * n ^ 3 / (n ^ 2 / 4) ^ 2 := by
        gcongr
      _ = 32 / n := by field_simp; ring
  have hMterm : 2 * M ^ 3 / (n * (n - 1) / 2) ^ 2 ≤ 32 / n := by
    calc
      2 * M ^ 3 / (n * (n - 1) / 2) ^ 2 ≤
          2 * n ^ 3 / (n ^ 2 / 4) ^ 2 := by
        gcongr
      _ = 32 / n := by field_simp; ring
  have hrterm : 2 * r / M ≤ 8 * K / n := by
    calc
      2 * r / M ≤ 2 * K / (n / 4) := by gcongr
      _ = 8 * K / n := by field_simp; ring
  have hone : 1 / n ≤ K / n := by gcongr
  calc
    2 * K / n + 2 * b ^ 3 / A ^ 2 + 2 * r / M +
        2 * M ^ 3 / (n * (n - 1) / 2) ^ 2 ≤
      2 * K / n + 32 / n + 8 * K / n + 32 / n := by
        exact add_le_add (add_le_add (add_le_add le_rfl hbterm) hrterm) hMterm
    _ ≤ 2 * K / n + 32 * K / n + 8 * K / n + 32 * K / n := by
      gcongr <;> nlinarith [hK1]
    _ = 74 * K / n := by ring

set_option maxHeartbeats 800000 in
theorem nearFiniteLogRemainder
    (hF : FiniteEnumerationStatement)
    (n M q : ℕ) (ks : Fin q → ℕ)
    (hq : 0 < q) (hn64 : 64 ≤ n) (hM : M ≤ capacity n)
    (hpos : ∀ i, 0 < ks i)
    (hK : (∑ i, (ks i : ℝ)) ≤ (n : ℝ) / 16)
    (hlo : (1 : ℝ) / 2 ≤ degreeAt n M)
    (hhi : degreeAt n M ≤ (3 : ℝ) / 2) :
    0 < tupleMoment n M q ks ∧
    |Real.log (tupleMoment n M q ks / tupleLeading n M q ks) -
        ((n : ℝ) * entropyCore (degreeAt n M)
            ((∑ i, (ks i : ℝ)) / n) +
          rate (degreeAt n M) * (∑ i, (ks i : ℝ)))| ≤
      (64 * ((q : ℝ) + 1) + 74) *
        (∑ i, (ks i : ℝ)) / n := by
  let K : ℕ := ∑ i, ks i
  let A : ℕ := (n - K).choose 2
  let b : ℕ := M + q - K
  let r : ℕ := K - q
  have hn : 0 < n := by omega
  have hnr : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnr
  have hqK : q ≤ K := by
    have hcard := Finset.card_nsmul_le_sum
      (Finset.univ : Finset (Fin q)) ks 1 (by
        intro i hi
        exact Nat.succ_le_iff.mpr (hpos i))
    simpa [K] using! hcard
  have hKcast : (K : ℝ) = ∑ i, (ks i : ℝ) := by
    simp [K]
  have hK' : (K : ℝ) ≤ (n : ℝ) / 16 := by simpa [hKcast] using! hK
  have hK0 : 0 ≤ (K : ℝ) := by positivity
  have hqKreal : (q : ℝ) ≤ K := by exact_mod_cast hqK
  have hK1 : 1 ≤ (K : ℝ) := by
    have : 1 ≤ K := by
      omega
    exact_mod_cast this
  have hKn : K ≤ n := by
    exact_mod_cast (le_trans hK' (by nlinarith [hnr.le] : (n : ℝ) / 16 ≤ n))
  have hMlo : (n : ℝ) / 4 ≤ M := by
    unfold degreeAt at hlo
    field_simp [hn0] at hlo
    nlinarith
  have hMhi : (M : ℝ) ≤ n := by
    unfold degreeAt at hhi
    field_simp [hn0] at hhi
    nlinarith [hnr.le]
  have hMpos : 0 < M := by
    have : 0 < (M : ℝ) := lt_of_lt_of_le (by positivity) hMlo
    exact_mod_cast this
  have hKM : K ≤ M + q := by
    have hKMreal : (K : ℝ) ≤ M := by
      exact le_trans hK' (by nlinarith [hMlo])
    have hKMnat : K ≤ M := by exact_mod_cast hKMreal
    omega
  have hrM : r ≤ M := by
    dsimp [r]
    omega
  have hbEq : b = M - r := by
    dsimp [b, r]
    omega
  have hbM : b ≤ M := by rw [hbEq]; omega
  have hNcast : (capacity n : ℝ) = (n : ℝ) * (n - 1) / 2 := by
    unfold capacity
    rw [Nat.cast_choose_two]
  have hNlower : (n : ℝ) ^ 2 / 4 ≤ capacity n := by
    rw [hNcast]
    nlinarith [sq_nonneg ((n : ℝ) - 2)]
  have hNpos : 0 < capacity n := by
    have : 0 < (capacity n : ℝ) :=
      lt_of_lt_of_le (by positivity) hNlower
    exact_mod_cast this
  have hAcast : (A : ℝ) = ((n : ℝ) - K) * ((n : ℝ) - K - 1) / 2 := by
    dsimp [A]
    rw [Nat.cast_choose_two, Nat.cast_sub hKn]
  have hAlower : (n : ℝ) ^ 2 / 4 ≤ A := by
    rw [hAcast]
    have hx : 15 * (n : ℝ) / 16 ≤ (n : ℝ) - K := by nlinarith
    have hy : 7 * (n : ℝ) / 8 ≤ (n : ℝ) - K - 1 := by
      have : (64 : ℝ) ≤ n := by exact_mod_cast hn64
      nlinarith
    have hp := mul_le_mul hx hy (by positivity) (by nlinarith)
    nlinarith [sq_nonneg (n : ℝ)]
  have hApos : 0 < A := by
    have : 0 < (A : ℝ) := lt_of_lt_of_le (by positivity) hAlower
    exact_mod_cast this
  have hbcast : (b : ℝ) = (M : ℝ) - r := by
    rw [hbEq, Nat.cast_sub hrM]
  have hrcast : (r : ℝ) = (K : ℝ) - q := by
    dsimp [r]
    rw [Nat.cast_sub hqK]
  have h2K : 2 * (K : ℝ) ≤ n := by nlinarith
  have h2r : 2 * (r : ℝ) ≤ M := by
    rw [hrcast]
    nlinarith [hMlo]
  have h2b : 2 * (b : ℝ) ≤ A := by
    have hbN : (b : ℝ) ≤ n := by
      exact_mod_cast (le_trans hbM (by exact_mod_cast hMhi : M ≤ n))
    have hn64r : (64 : ℝ) ≤ n := by exact_mod_cast hn64
    nlinarith [hAlower, sq_nonneg ((n : ℝ) - 4)]
  have h2M : 2 * (M : ℝ) ≤ capacity n := by
    have hn64r : (64 : ℝ) ≤ n := by exact_mod_cast hn64
    nlinarith [hNlower, sq_nonneg ((n : ℝ) - 4)]
  have hbA : b ≤ A := by
    exact_mod_cast (le_trans (show (b : ℝ) ≤ 2 * b by
      have : 0 ≤ (b : ℝ) := by positivity
      linarith) h2b)
  have hJ : 0 < tupleMoment n M q ks := by
    apply tupleMoment_pos hF n M q ks hM hpos
    · simpa [K] using! hKn
    · simpa [K] using! hKM
    · simpa [K, A, b] using! hbA
  have hlog := tupleLog_to_finiteMain hF n M q ks hM hpos
    (by simpa [K] using! hKn) (by simpa [K] using hKM)
    (by simpa [K, A, b] using! hbA) hn hMpos
    (by simpa [K, A] using! hApos) hNpos
    (lt_of_lt_of_le (by norm_num) hlo) (by simpa [K] using! hqK)
    (by simpa [K] using! h2K) (by simpa [K, r] using h2r)
    (by simpa [K, A, b] using! h2b) h2M
  have hfinite := tupleFiniteMain_local_remainder
    (n := n) (M := M) (q := q) (K := K)
    (by omega) hqK (le_trans hqKreal hK') hK' hlo hhi
  have hfactor :
      2 * (K : ℝ) / n + 2 * (b : ℝ) ^ 3 / (A : ℝ) ^ 2 +
          2 * (r : ℝ) / M + 2 * (M : ℝ) ^ 3 / (capacity n : ℝ) ^ 2 ≤
        74 * (K : ℝ) / n := by
    rw [hNcast] at hNlower ⊢
    apply finite_factor_error_bound hnr hK1 (by positivity)
      (by exact_mod_cast (Nat.sub_le K q)) (by positivity)
      (by exact_mod_cast (le_trans hbM (by exact_mod_cast hMhi : M ≤ n)))
      hMlo hMhi hAlower hNlower
  constructor
  · exact hJ
  · have htriangle :
        |Real.log (tupleMoment n M q ks / tupleLeading n M q ks) -
            ((n : ℝ) * entropyCore (degreeAt n M) ((K : ℝ) / n) +
              rate (degreeAt n M) * K)| ≤
          |Real.log (tupleMoment n M q ks / tupleLeading n M q ks) -
              tupleFiniteMain n M q K| +
            |tupleFiniteMain n M q K -
              ((n : ℝ) * entropyCore (degreeAt n M) ((K : ℝ) / n) +
                rate (degreeAt n M) * K)| := by
        convert abs_add_le
          (Real.log (tupleMoment n M q ks / tupleLeading n M q ks) -
            tupleFiniteMain n M q K)
          (tupleFiniteMain n M q K -
            ((n : ℝ) * entropyCore (degreeAt n M) ((K : ℝ) / n) +
              rate (degreeAt n M) * K)) using 1 <;> ring_nf
    rw [← hKcast]
    exact le_trans htriangle (by
      calc
        _ ≤ (2 * (K : ℝ) / n + 2 * (b : ℝ) ^ 3 / (A : ℝ) ^ 2 +
              2 * (r : ℝ) / M + 2 * (M : ℝ) ^ 3 / (capacity n : ℝ) ^ 2) +
            64 * ((q : ℝ) + 1) * K / n := add_le_add hlog hfinite
        _ ≤ 74 * (K : ℝ) / n +
            64 * ((q : ℝ) + 1) * K / n := add_le_add hfactor le_rfl
        _ = (64 * ((q : ℝ) + 1) + 74) * K / n := by ring)

end

end Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_Near


/-!
Consumer-shaped near-critical conclusions for W04.
-/
namespace Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_PublicNear

noncomputable section
open scoped BigOperators

open W04_TUPLES_Assembly
open W04_TUPLES_Near
open W04_TUPLES_Local

theorem nearLocalEventually (hF : FiniteEnumerationStatement) :
    ∀ q : ℕ, 0 < q → ∃ C : ℝ, 0 < C ∧
      ∃ n0 : ℕ, ∀ (n M : ℕ) (ks : Fin q → ℕ),
        n0 ≤ n → M ≤ capacity n →
        1 / 2 ≤ degreeAt n M → degreeAt n M ≤ 3 / 2 →
        (∀ i, 0 < ks i) →
        ((∑ i, (ks i : ℝ)) ≤ (n : ℝ) / 16 →
          tupleLocalBound n M q ks C) := by
  intro q hq
  let C : ℝ := 64 * ((q : ℝ) + 1) + 74
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, 64, ?_⟩
  intro n M ks hn hM hlo hhi hpos hK
  obtain ⟨hJ, hrem⟩ := nearFiniteLogRemainder hF n M q ks hq hn hM hpos hK hlo hhi
  apply localBound_of_logRemainder n M q ks C C
    (lt_of_lt_of_le (by omega) hn) hlo hhi (by positivity) hK hJ hrem
  · exact le_rfl
  · dsimp [C]
    have hq0 : 0 ≤ (q : ℝ) := by positivity
    nlinarith

theorem mixedEventually (hF : FiniteEnumerationStatement) :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, ∀ n M k l : ℕ,
      n0 ≤ n → M ≤ capacity n →
      1 / 2 ≤ degreeAt n M → degreeAt n M ≤ 3 / 2 →
      0 < k → 0 < l → ((k + l : ℕ) : ℝ) ≤ (n : ℝ) / 16 →
        let pair : Fin 2 → ℕ := fun i => if i.val = 0 then k else l
        |Real.log (tupleMoment n M 2 pair /
          (tupleMoment n M 1 (fun _ => k) *
            tupleMoment n M 1 (fun _ => l)))| ≤
          C * (((k : ℝ) + l) / n +
            |degreeAt n M - 1| * k * l / n +
            (k : ℝ) * l * (k + l) / (n : ℝ) ^ 2) := by
  let D₂ : ℝ := 64 * ((2 : ℝ) + 1) + 74
  let D₁ : ℝ := 64 * ((1 : ℝ) + 1) + 74
  let C : ℝ := D₂ + D₁
  have hD₂ : 0 < D₂ := by dsimp [D₂]; positivity
  have hD₁ : 0 < D₁ := by dsimp [D₁]; positivity
  have hC : 0 < C := add_pos hD₂ hD₁
  refine ⟨C, hC, 64, ?_⟩
  intro n M k l hn hM hlo hhi hk hl hkl
  let pair : Fin 2 → ℕ := fun i => if i.val = 0 then k else l
  have hpairPos : ∀ i, 0 < pair i := by
    intro i
    fin_cases i <;> simp [pair, hk, hl]
  have hpairSum : ∑ i, (pair i : ℝ) = (k : ℝ) + l := by
    simp [pair, Fin.sum_univ_two]
  have hkl' : (k : ℝ) + l ≤ (n : ℝ) / 16 := by
    exact_mod_cast hkl
  obtain ⟨hJ₂, hrem₂⟩ := nearFiniteLogRemainder hF n M 2 pair
    (by omega) hn hM hpairPos (by simpa [hpairSum] using! hkl) hlo hhi
  obtain ⟨hJk, hremk⟩ := nearFiniteLogRemainder hF n M 1 (fun _ => k)
    (by omega) hn hM (fun _ => hk) (by
      have hkle : (k : ℝ) ≤ (k : ℝ) + l :=
        le_add_of_nonneg_right (by positivity)
      simpa using! hkle.trans hkl') hlo hhi
  obtain ⟨hJl, hreml⟩ := nearFiniteLogRemainder hF n M 1 (fun _ => l)
    (by omega) hn hM (fun _ => hl) (by
      have hlle : (l : ℝ) ≤ (k : ℝ) + l :=
        le_add_of_nonneg_left (by positivity)
      simpa using! hlle.trans hkl') hlo hhi
  have hrem₂' :
      |Real.log (tupleMoment n M 2 pair / tupleLeading n M 2 pair) -
        ((n : ℝ) * entropyCore (degreeAt n M) (((k : ℝ) + l) / n) +
          rate (degreeAt n M) * ((k : ℝ) + l))| ≤
        D₂ * ((k : ℝ) + l) / n := by
    dsimp [D₂]
    simpa [hpairSum] using! hrem₂
  have hremk' :
      |Real.log (tupleMoment n M 1 (fun _ => k) /
          tupleLeading n M 1 (fun _ => k)) -
        ((n : ℝ) * entropyCore (degreeAt n M) ((k : ℝ) / n) +
          rate (degreeAt n M) * k)| ≤ D₁ * k / n := by
    dsimp [D₁]
    simpa using! hremk
  have hreml' :
      |Real.log (tupleMoment n M 1 (fun _ => l) /
          tupleLeading n M 1 (fun _ => l)) -
        ((n : ℝ) * entropyCore (degreeAt n M) ((l : ℝ) / n) +
          rate (degreeAt n M) * l)| ≤ D₁ * l / n := by
    dsimp [D₁]
    simpa using! hreml
  simpa [pair] using! mixedBound_of_logRemainders n M k l D₂ D₁ C
    (lt_of_lt_of_le (by omega) hn) hlo hhi hk hl hkl hJ₂ hJk hJl
    hrem₂' hremk' hreml' hD₂.le hD₁.le le_rfl (by
      dsimp [C, D₂, D₁]
      norm_num)

end

end Erdos745.WrapUp.Proofs.Internal.W04_TUPLES_PublicNear
