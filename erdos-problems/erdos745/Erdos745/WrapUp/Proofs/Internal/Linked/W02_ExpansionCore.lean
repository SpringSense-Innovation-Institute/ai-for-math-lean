module

public import Mathlib
public import Erdos745.WrapUp.Contracts
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Fin.Rev

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local simp] Pi.div_def Pi.mul_def Pi.add_def Pi.sub_def Pi.neg_def Pi.inv_def Function.comp_def Pi.pow_def Pi.smul_def Real.rpow_eq_pow

@[expose] public section


/-!
# The finite compensated kernel mass

This file supplies the first internal boundary of `W02_KERNEL`.  A kernel
multiplicity array with `v` vertices and excess `r` is represented by a
multiset of exactly `v + r` elements of the triangular index type.  Thus the
edge-count condition is part of the type, rather than an unproved side
condition.  The definition of `kernelWeight` is the usual compensation factor;
`kernelWeight_eq_compensation` records its literal product form.
-/

open scoped BigOperators

noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Mass

/-- A position in a triangular multiplicity array. -/
abbrev KernelIndex (v : ℕ) := {p : Fin v × Fin v // p.1 ≤ p.2}

/-- A triangular multiplicity array with exactly `v + r` edges. -/
abbrev KernelArray (v r : ℕ) := Sym (KernelIndex v) (v + r)

/-- Multiplicity of an unordered vertex pair in an array. -/
def multiplicity {v r : ℕ} (H : KernelArray v r) (p : KernelIndex v) : ℕ :=
  H.1.count p

/-- Endpoint incidence; loops contribute two. -/
def incidence {v : ℕ} (i : Fin v) (p : KernelIndex v) : ℕ :=
  (if p.1.1 = i then 1 else 0) + (if p.1.2 = i then 1 else 0)

/-- Degree of a vertex in the multiplicity array. -/
def degree {v r : ℕ} (H : KernelArray v r) (i : Fin v) : ℕ :=
  (H.1.map (incidence i)).sum

/-- Number of loops, with multiplicity. -/
def loopCount {v r : ℕ} (H : KernelArray v r) : ℕ :=
  ∑ p : KernelIndex v, if p.1.1 = p.1.2 then multiplicity H p else 0

/-- Adjacency in the underlying graph, forgetting loops and multiplicities. -/
def kernelAdj {v r : ℕ} (H : KernelArray v r) (i j : Fin v) : Prop :=
  i ≠ j ∧ ∃ p ∈ H.1,
    (p.1.1 = i ∧ p.1.2 = j) ∨ (p.1.1 = j ∧ p.1.2 = i)

/-- Connectedness of the underlying graph. -/
def kernelConnected {v r : ℕ} (H : KernelArray v r) : Prop :=
  ∀ i j, Relation.ReflTransGen (kernelAdj H) i j

/-- The finite set of connected arrays of minimum degree at least three. -/
noncomputable def Kern (v r : ℕ) : Finset (KernelArray v r) := by
  classical
  exact Finset.univ.filter fun H => kernelConnected H ∧ ∀ i, 3 ≤ degree H i

/-- The usual multigraph compensation factor.  The multinomial quotient is
`1 / ∏ m_ij!`, and the final factor supplies `2^{-m_ii}` for loops. -/
def kernelWeight {v r : ℕ} (H : KernelArray v r) : ℝ :=
  (H.1.countPerms : ℝ) / ((v + r).factorial : ℝ) *
    (1 / 2 : ℝ) ^ loopCount H

/-- Total compensated mass, including the `1 / v!` label quotient. -/
def kernelMass (v r : ℕ) : ℝ :=
  (∑ H ∈ Kern v r, kernelWeight H) / (v.factorial : ℝ)

private lemma prod_factorial_all_eq_support {v r : ℕ} (H : KernelArray v r) :
    (∏ p : KernelIndex v, (multiplicity H p).factorial) =
      ∏ p ∈ H.1.toFinset, (multiplicity H p).factorial := by
  classical
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro p hpU hp
  simp only [multiplicity]
  rw [Multiset.count_eq_zero.mpr]
  · simp
  · simpa using! hp

/-- The multinomial normalization is exactly the reciprocal product of all
multiplicity factorials. -/
theorem multinomial_div_factorial_eq_prod_inv {v r : ℕ} (H : KernelArray v r) :
    (H.1.countPerms : ℝ) / ((v + r).factorial : ℝ) =
      ∏ p : KernelIndex v, (((multiplicity H p).factorial : ℝ)⁻¹) := by
  classical
  have hspec := Nat.multinomial_spec H.1.toFinset (fun p => H.1.count p)
  have hsum : ∑ p ∈ H.1.toFinset, H.1.count p = v + r := by
    rw [Multiset.sum_count_eq_card]
    · exact H.2
    · intro a ha
      simpa using! ha
  rw [hsum] at hspec
  have hprodNat :
      (∏ p : KernelIndex v, (multiplicity H p).factorial) * H.1.countPerms =
        (v + r).factorial := by
    rw [prod_factorial_all_eq_support]
    exact hspec
  have hprodReal :
      (∏ p : KernelIndex v, ((multiplicity H p).factorial : ℝ)) *
          (H.1.countPerms : ℝ) = ((v + r).factorial : ℝ) := by
    exact_mod_cast hprodNat
  rw [Finset.prod_inv_distrib]
  have hfac : ((v + r).factorial : ℝ) ≠ 0 := by positivity
  have hp : (∏ p : KernelIndex v,
      ((multiplicity H p).factorial : ℝ)) ≠ 0 := by positivity
  apply (div_eq_iff hfac).2
  have hm :
      (H.1.countPerms : ℝ) = ((v + r).factorial : ℝ) /
        (∏ p : KernelIndex v, ((multiplicity H p).factorial : ℝ)) := by
    apply (eq_div_iff hp).2
    simpa [mul_comm] using! hprodReal
  rw [hm]
  field_simp

/-- Literal compensation-product form: diagonal entries have the additional
`2^{-m_ii}` factor and every entry has `1 / m_ij!`. -/
theorem kernelWeight_eq_compensation {v r : ℕ} (H : KernelArray v r) :
    kernelWeight H =
      ∏ p : KernelIndex v,
        (((2 : ℝ) ^ (if p.1.1 = p.1.2 then multiplicity H p else 0) *
          ((multiplicity H p).factorial : ℝ))⁻¹) := by
  classical
  rw [kernelWeight, multinomial_div_factorial_eq_prod_inv]
  simp only [mul_inv_rev, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  rw [Finset.prod_pow_eq_pow_sum]
  simp only [loopCount]
  congr 1
  rw [one_div, inv_pow]

/-- The unweighted multinomial pairing identity.  It is the finite symmetric
power form of expanding an ordered list of `v+r` triangular edge slots. -/
theorem pairing_identity (v r : ℕ) :
    (∑ H : KernelArray v r, (H.1.countPerms : ℝ)) =
      (Fintype.card (KernelIndex v) : ℝ) ^ (v + r) := by
  classical
  have h := Finset.sum_pow (R := ℝ)
    (s := (Finset.univ : Finset (KernelIndex v)))
    (fun _ => (1 : ℝ)) (v + r)
  simp at h
  exact h.symm

private lemma kernelWeight_le_plain {v r : ℕ} (H : KernelArray v r) :
    kernelWeight H ≤ (H.1.countPerms : ℝ) / ((v + r).factorial : ℝ) := by
  unfold kernelWeight
  exact mul_le_of_le_one_right (by positivity)
    (pow_le_one₀ (by norm_num) (by norm_num))

/-- A finite pairing majorant obtained by dropping connectedness, the minimum
degree condition, and the helpful loop powers. -/
theorem kernelMass_pairing_bound (v r : ℕ) :
    kernelMass v r ≤
      (Fintype.card (KernelIndex v) : ℝ) ^ (v + r) /
        ((v.factorial : ℝ) * ((v + r).factorial : ℝ)) := by
  classical
  have hs :
      (∑ H ∈ Kern v r, kernelWeight H) ≤
        ∑ H : KernelArray v r,
          (H.1.countPerms : ℝ) / ((v + r).factorial : ℝ) := by
    calc
      (∑ H ∈ Kern v r, kernelWeight H) ≤
          ∑ H ∈ Kern v r,
            (H.1.countPerms : ℝ) / ((v + r).factorial : ℝ) := by
        gcongr with H hH
        exact kernelWeight_le_plain H
      _ ≤ ∑ H : KernelArray v r,
          (H.1.countPerms : ℝ) / ((v + r).factorial : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro H hHu hHK
        positivity
  unfold kernelMass
  calc
    (∑ H ∈ Kern v r, kernelWeight H) / (v.factorial : ℝ) ≤
        (∑ H : KernelArray v r,
          (H.1.countPerms : ℝ) / ((v + r).factorial : ℝ)) /
            (v.factorial : ℝ) := by gcongr
    _ = (Fintype.card (KernelIndex v) : ℝ) ^ (v + r) /
        ((v.factorial : ℝ) * ((v + r).factorial : ℝ)) := by
      rw [← Finset.sum_div, pairing_identity]
      ring

private lemma card_kernelIndex_le_sq (v : ℕ) :
    Fintype.card (KernelIndex v) ≤ v * v := by
  calc
    Fintype.card (KernelIndex v) ≤ Fintype.card (Fin v × Fin v) :=
      Fintype.card_subtype_le _
    _ = v * v := by simp

private lemma factorial_lower (n : ℕ) (hn : 0 < n) :
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

private lemma arithmetic_core (v r : ℕ) (hv : 0 < v) (hr : 0 < r)
    (hvr : v ≤ 2 * r) :
    (3 : ℝ) ^ (v + (v + r)) * (v : ℝ) ^ (2 * (v + r)) ≤
      (1944 : ℝ) ^ r * (r : ℝ) ^ r * (v : ℝ) ^ v *
        ((v + r : ℕ) : ℝ) ^ (v + r) := by
  by_cases hsmall : v ≤ r
  · have hexp : v + (v + r) ≤ 3 * r := by omega
    have h3 : (3 : ℝ) ^ (v + (v + r)) ≤ (1944 : ℝ) ^ r := by
      calc
        (3 : ℝ) ^ (v + (v + r)) ≤ 3 ^ (3 * r) :=
          pow_le_pow_right₀ (by norm_num) hexp
        _ = (27 : ℝ) ^ r := by rw [pow_mul]; norm_num
        _ ≤ (1944 : ℝ) ^ r := by gcongr <;> norm_num
    have hve : (v : ℝ) ^ (v + r) ≤ ((v + r : ℕ) : ℝ) ^ (v + r) := by
      gcongr <;> omega
    have hvrpow : (v : ℝ) ^ r ≤ (r : ℝ) ^ r := by gcongr
    calc
      (3 : ℝ) ^ (v + (v + r)) * (v : ℝ) ^ (2 * (v + r)) =
          3 ^ (v + (v + r)) *
            ((v : ℝ) ^ v * (v : ℝ) ^ (v + r) * (v : ℝ) ^ r) := by
        congr 1
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      _ ≤ (1944 : ℝ) ^ r *
          ((v : ℝ) ^ v * ((v + r : ℕ) : ℝ) ^ (v + r) * (r : ℝ) ^ r) := by
        gcongr
      _ = (1944 : ℝ) ^ r * (r : ℝ) ^ r * (v : ℝ) ^ v *
          ((v + r : ℕ) : ℝ) ^ (v + r) := by ring
  · have hlarge : r < v := Nat.lt_of_not_ge hsmall
    have hexp : v + (v + r) ≤ 5 * r := by omega
    have h3 : (3 : ℝ) ^ (v + (v + r)) ≤ (243 : ℝ) ^ r := by
      calc
        (3 : ℝ) ^ (v + (v + r)) ≤ 3 ^ (5 * r) :=
          pow_le_pow_right₀ (by norm_num) hexp
        _ = (243 : ℝ) ^ r := by rw [pow_mul]; norm_num
    have hve : (v : ℝ) ^ (v + r) ≤ ((v + r : ℕ) : ℝ) ^ (v + r) := by
      gcongr <;> omega
    have hvrpow : (v : ℝ) ^ r ≤ ((2 * r : ℕ) : ℝ) ^ r := by gcongr
    calc
      (3 : ℝ) ^ (v + (v + r)) * (v : ℝ) ^ (2 * (v + r)) =
          3 ^ (v + (v + r)) *
            ((v : ℝ) ^ v * (v : ℝ) ^ (v + r) * (v : ℝ) ^ r) := by
        congr 1
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      _ ≤ (243 : ℝ) ^ r *
          ((v : ℝ) ^ v * ((v + r : ℕ) : ℝ) ^ (v + r) *
            ((2 * r : ℕ) : ℝ) ^ r) := by
        gcongr
      _ = (486 : ℝ) ^ r * (r : ℝ) ^ r * (v : ℝ) ^ v *
          ((v + r : ℕ) : ℝ) ^ (v + r) := by
        push_cast
        rw [show (486 : ℝ) ^ r = 243 ^ r * 2 ^ r by
          rw [← mul_pow]
          norm_num]
        ring
      _ ≤ (1944 : ℝ) ^ r * (r : ℝ) ^ r * (v : ℝ) ^ v *
          ((v + r : ℕ) : ℝ) ^ (v + r) := by
        gcongr <;> norm_num

private lemma numerator_le (v r : ℕ) (hv : 0 < v) (hr : 0 < r)
    (hvr : v ≤ 2 * r) :
    ((v : ℝ) * (v : ℝ)) ^ (v + r) ≤
      (1944 : ℝ) ^ r * (r : ℝ) ^ r *
        (((v : ℝ) / 3) ^ v * (((v + r : ℕ) : ℝ) / 3) ^ (v + r)) := by
  have h := arithmetic_core v r hv hr hvr
  rw [div_pow, div_pow]
  have heq :
      (1944 : ℝ) ^ r * (r : ℝ) ^ r *
          ((v : ℝ) ^ v / 3 ^ v *
            (((v + r : ℕ) : ℝ) ^ (v + r) / 3 ^ (v + r))) =
        ((1944 : ℝ) ^ r * (r : ℝ) ^ r * (v : ℝ) ^ v *
          ((v + r : ℕ) : ℝ) ^ (v + r)) / 3 ^ (v + (v + r)) := by
    rw [pow_add]
    field_simp
    ring
  rw [heq]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 3 ^ (v + (v + r)))).2
  rw [mul_pow]
  calc
    ((v : ℝ) ^ (v + r) * (v : ℝ) ^ (v + r)) * 3 ^ (v + (v + r)) =
        3 ^ (v + (v + r)) * (v : ℝ) ^ (2 * (v + r)) := by
      rw [← pow_add]
      ring
    _ ≤ _ := h

/-- Uniform real kernel-mass bound, with both endpoints `v = 1` and `v = 2r`
included. -/
theorem kernelMass_uniform (v r : ℕ) (hv : 0 < v) (hr : 0 < r)
    (hvr : v ≤ 2 * r) :
    kernelMass v r ≤ (1944 : ℝ) ^ r * (r : ℝ) ^ r := by
  have hcardR : (Fintype.card (KernelIndex v) : ℝ) ≤ (v : ℝ) * (v : ℝ) := by
    exact_mod_cast card_kernelIndex_le_sq v
  have hnum0 : 0 ≤ (Fintype.card (KernelIndex v) : ℝ) := by positivity
  have hnum :
      (Fintype.card (KernelIndex v) : ℝ) ^ (v + r) ≤
        ((v : ℝ) * (v : ℝ)) ^ (v + r) :=
    pow_le_pow_left₀ hnum0 hcardR _
  have hfv := factorial_lower v hv
  have hfe := factorial_lower (v + r) (by omega)
  have hden :
      ((v : ℝ) / 3) ^ v * (((v + r : ℕ) : ℝ) / 3) ^ (v + r) ≤
        (v.factorial : ℝ) * ((v + r).factorial : ℝ) :=
    mul_le_mul hfv hfe (by positivity) (by positivity)
  have htop :
      (Fintype.card (KernelIndex v) : ℝ) ^ (v + r) ≤
        ((1944 : ℝ) ^ r * (r : ℝ) ^ r) *
          ((v.factorial : ℝ) * ((v + r).factorial : ℝ)) := by
    calc
      _ ≤ ((v : ℝ) * (v : ℝ)) ^ (v + r) := hnum
      _ ≤ (1944 : ℝ) ^ r * (r : ℝ) ^ r *
          (((v : ℝ) / 3) ^ v * (((v + r : ℕ) : ℝ) / 3) ^ (v + r)) :=
        numerator_le v r hv hr hvr
      _ ≤ ((1944 : ℝ) ^ r * (r : ℝ) ^ r) *
          ((v.factorial : ℝ) * ((v + r).factorial : ℝ)) := by
        gcongr
  calc
    kernelMass v r ≤
        (Fintype.card (KernelIndex v) : ℝ) ^ (v + r) /
          ((v.factorial : ℝ) * ((v + r).factorial : ℝ)) :=
      kernelMass_pairing_bound v r
    _ ≤ (1944 : ℝ) ^ r * (r : ℝ) ^ r := by
      exact (div_le_iff₀ (by positivity)).2 (by simpa [mul_assoc] using! htop)

end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Mass


/-!
# Endpoint-safe finite kernel expansion coefficients

This file is the second internal boundary of `W02_KERNEL`.  It defines the
finite rooted-tree coefficient `tau`, the weak-composition coefficient `Q`,
and the exact compensated kernel majorant.  The separate `j = k` theorem is
intentional: it avoids interpreting a natural power with exponent `-1`.

`PruningSuppressionEncoding` records the two quantitative facts delivered by
the canonical leaf-pruning and degree-two suppression map: every connected
graph receives compensated fibre mass at least one, and the total mass is at
most the explicit kernel/Q sum.  The final theorem below is the finite
double-counting implication from those data; it introduces no trusted leaf.
-/

open scoped BigOperators

noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Expansion

open Erdos745.WrapUp
open Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Mass

/-- The canonical set of the first `j` labels in `Fin k`. -/
def canonicalRoots (k j : ℕ) : Finset (Fin k) :=
  Finset.univ.filter fun i => i.val < j

theorem canonicalRoots_card (k j : ℕ) :
    (canonicalRoots k j).card = min k j := by
  exact Fin.card_filter_val_lt

theorem canonicalRoots_card_of_le (k j : ℕ) (hj : j ≤ k) :
    (canonicalRoots k j).card = j := by
  rw [canonicalRoots_card, min_eq_right hj]

/-- Number of ordered-root presentations of rooted forests on `Fin k` with
`j` roots.  `falling k j` orders the distinct roots; the forest count depends
only on their underlying set by the rooted-forest conjunct of `hF`. -/
def tau (k j : ℕ) : ℕ :=
  falling k j * rootedForestCount k (canonicalRoots k j)

private theorem falling_self (k : ℕ) : falling k k = k.factorial := by
  rw [show falling k k = k.descFactorial k by
    simp [falling, Nat.descFactorial_eq_prod_range]]
  exact Nat.descFactorial_self k

theorem tau_of_lt (hF : FiniteEnumerationStatement) (k j : ℕ)
    (hjk : j < k) :
    tau k j = falling k j * (j * k ^ (k - j - 1)) := by
  have hforest := hF.2.2.2.2.2.2.2.1
  rw [tau, hforest, canonicalRoots_card_of_le k j hjk.le]
  simp [Nat.ne_of_lt hjk]

/-- The endpoint `j = k` in equation (7): the forest is empty and the roots
may be ordered in exactly `k!` ways. -/
theorem tau_self (hF : FiniteEnumerationStatement) (k : ℕ) :
    tau k k = k.factorial := by
  have hforest := hF.2.2.2.2.2.2.2.1
  rw [tau, hforest, canonicalRoots_card_of_le k k le_rfl]
  simp [falling_self]

/-- There are no ordered choices of more than `k` distinct roots. -/
def Q (k v b : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc v k,
    (b + j - v - 1).choose (b - 1) * tau k j

theorem Q_le_Q_one (k v b : ℕ) (hv : 0 < v) :
    Q k v b ≤ Q k 1 b := by
  unfold Q
  calc
    (∑ j ∈ Finset.Icc v k,
        (b + j - v - 1).choose (b - 1) * tau k j) ≤
        ∑ j ∈ Finset.Icc v k,
          (b + j - 1 - 1).choose (b - 1) * tau k j := by
      gcongr with j hj
      omega
    _ ≤ ∑ j ∈ Finset.Icc 1 k,
        (b + j - 1 - 1).choose (b - 1) * tau k j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        simp only [Finset.mem_Icc] at hj ⊢
        omega
      · intro j hj hnot
        positivity

/-- The compensated kernel/Q sum in the first member of equation (9). -/
def expansionMajorant (k r : ℕ) : ℝ :=
  ∑ v ∈ Finset.Icc 1 (2 * r),
    kernelMass v r * (Q k v (v + r) : ℝ)

/-- The connected graphs counted by `connectedCount k (k+r)`. -/
noncomputable def positiveExcessGraphs (k r : ℕ) : Finset (Graph k) := by
  classical
  exact (fixedGraphs k (k + r)).filter fun G =>
    0 < k ∧ ∀ u v : Fin k, reach G u v

theorem positiveExcessGraphs_card (k r : ℕ) :
    (positiveExcessGraphs k r).card = connectedCount k (k + r) := by
  simp only [positiveExcessGraphs, connectedCount]

/-- Admissible positive kernel sizes in equation (9). -/
abbrev KernelSize (r : ℕ) := {v : ℕ // v ∈ Finset.Icc 1 (2 * r)}

/-- One labelled compensated kernel of an admissible size. -/
abbrev KernelChoice (v r : ℕ) := {H : KernelArray v r // H ∈ Kern v r}

/-- Admissible numbers of rooted trees in a `v`-vertex kernel expansion. -/
abbrev TreeCount (k v : ℕ) := {j : ℕ // j ∈ Finset.Icc v k}

/-- A finite overcounting code for the inverse kernel expansion.  Besides a
labelled kernel it contains a weak-composition index for the `j-v` non-kernel
trees among the `v+r` edge sequences, and an index for the ordered rooted
forest counted by `tau k j`. -/
abbrev ExpansionCode (k r : ℕ) :=
  Σ v : KernelSize r,
    KernelChoice v.1 r ×
      (Σ j : TreeCount k v.1,
        Fin ((v.1 + r + j.1 - v.1 - 1).choose (v.1 + r - 1)) ×
          Fin (tau k j.1))

/-- Compensation weight of an expansion code.  The factor `1/v!` cancels
kernel-label order; `kernelWeight` cancels loop orientations and parallel-edge
orders. -/
def expansionCodeWeight {k r : ℕ} (c : ExpansionCode k r) : ℝ :=
  kernelWeight c.2.1.1 / (c.1.1.factorial : ℝ)

theorem expansionCodeWeight_nonneg {k r : ℕ} (c : ExpansionCode k r) :
    0 ≤ expansionCodeWeight c := by
  unfold expansionCodeWeight kernelWeight
  positivity

private theorem sum_mem {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (s : Finset α) (f : α → M) :
    (∑ x : {x // x ∈ s}, f x.1) = ∑ x ∈ s, f x := by
  symm
  exact Finset.sum_subtype s (by simp) f

private def treeCodeMass (k r v j : ℕ) (H : KernelArray v r) : ℝ :=
  ∑ _ : Fin ((v + r + j - v - 1).choose (v + r - 1)),
    ∑ _ : Fin (tau k j), kernelWeight H / (v.factorial : ℝ)

private theorem treeCodeMass_eq (k r v j : ℕ) (H : KernelArray v r) :
    treeCodeMass k r v j H =
      ((v + r + j - v - 1).choose (v + r - 1) : ℝ) *
        (tau k j : ℝ) * (kernelWeight H / (v.factorial : ℝ)) := by
  simp [treeCodeMass]
  ring

private def kernelCodeMass (k r v : ℕ) (H : KernelArray v r) : ℝ :=
  ∑ j : TreeCount k v, treeCodeMass k r v j.1 H

private theorem kernelCodeMass_eq (k r v : ℕ) (H : KernelArray v r) :
    kernelCodeMass k r v H =
      kernelWeight H / (v.factorial : ℝ) * (Q k v (v + r) : ℝ) := by
  classical
  unfold kernelCodeMass
  calc
    (∑ j : TreeCount k v, treeCodeMass k r v j.1 H) =
        ∑ j ∈ Finset.Icc v k, treeCodeMass k r v j H :=
      sum_mem (Finset.Icc v k) (treeCodeMass k r v · H)
    _ = kernelWeight H / (v.factorial : ℝ) * (Q k v (v + r) : ℝ) := by
      unfold Q
      rw [Nat.cast_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [treeCodeMass_eq]
      push_cast
      ring

private def coefficientCodeMass (k r v : ℕ) : ℝ :=
  ∑ H : KernelChoice v r, kernelCodeMass k r v H.1

private theorem coefficientCodeMass_eq (k r v : ℕ) :
    coefficientCodeMass k r v =
      kernelMass v r * (Q k v (v + r) : ℝ) := by
  classical
  unfold coefficientCodeMass
  calc
    (∑ H : KernelChoice v r, kernelCodeMass k r v H.1) =
        ∑ H ∈ Kern v r, kernelCodeMass k r v H :=
      sum_mem (Kern v r) (kernelCodeMass k r v)
    _ = ∑ H ∈ Kern v r, kernelWeight H / (v.factorial : ℝ) *
        (Q k v (v + r) : ℝ) := by
      apply Finset.sum_congr rfl
      intro H hH
      exact kernelCodeMass_eq k r v H
    _ = kernelMass v r * (Q k v (v + r) : ℝ) := by
      unfold kernelMass
      rw [← Finset.sum_mul, ← Finset.sum_div]

/-- Exact finite enumeration of all labelled kernel/forest/composition codes.
This is the non-fibre half of the pruning/suppression coefficient argument. -/
theorem sum_expansionCodeWeight (k r : ℕ) :
    (∑ c : ExpansionCode k r, expansionCodeWeight c) =
      expansionMajorant k r := by
  classical
  rw [show (∑ c : ExpansionCode k r, expansionCodeWeight c) =
      ∑ v : KernelSize r, coefficientCodeMass k r v.1 by
    simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
    rfl]
  calc
    (∑ v : KernelSize r, coefficientCodeMass k r v.1) =
        ∑ v ∈ Finset.Icc 1 (2 * r), coefficientCodeMass k r v :=
      sum_mem (Finset.Icc 1 (2 * r)) (coefficientCodeMass k r)
    _ = expansionMajorant k r := by
      unfold expansionMajorant
      apply Finset.sum_congr rfl
      intro v hv
      exact coefficientCodeMass_eq k r v

/-- Quantitative interface of the canonical pruning/suppression encoding.
`fiberWeight G` is the total compensation weight of the labelled, oriented,
and parallel-edge-ordered inverse decorations that decode to `G`.

The first field is the exact cancellation statement for the `2^L ∏mᵢⱼ!`
representations of a simple expansion.  The second is the finite enumeration
of all allowed kernel arrays, ordered roots and weak edge-sequence
compositions. -/
structure PruningSuppressionEncoding (k r : ℕ) where
  /-- Expand the selected kernel, edge sequences and ordered forest. -/
  decode : ExpansionCode k r → Graph k
  compensated_fiber_covers :
    ∀ G ∈ positiveExcessGraphs k r,
      1 ≤ ∑ c : ExpansionCode k r,
        if decode c = G then expansionCodeWeight c else 0

/-- Finite compensated double counting: a valid canonical
pruning/suppression encoding gives the first inequality in equation (9). -/
theorem connectedCount_le_expansionMajorant {k r : ℕ}
    (enc : PruningSuppressionEncoding k r) :
    (connectedCount k (k + r) : ℝ) ≤ expansionMajorant k r := by
  rw [← positiveExcessGraphs_card]
  calc
    ((positiveExcessGraphs k r).card : ℝ) =
        ∑ G ∈ positiveExcessGraphs k r, (1 : ℝ) := by simp
    _ ≤ ∑ G ∈ positiveExcessGraphs k r,
        ∑ c : ExpansionCode k r,
          if enc.decode c = G then expansionCodeWeight c else 0 := by
      gcongr with G hG
      exact enc.compensated_fiber_covers G hG
    _ ≤ ∑ c : ExpansionCode k r, expansionCodeWeight c := by
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro c hc
      by_cases hm : enc.decode c ∈ positiveExcessGraphs k r
      · simp [hm]
      · simp [hm, expansionCodeWeight_nonneg c]
    _ = expansionMajorant k r := sum_expansionCodeWeight k r

/- Equation (9), including its monotone `v = 1` relaxation, once the
canonical compensated encoding has been constructed. -/
end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Expansion


/-!
# Semantic weak compositions for the kernel expansion

The coefficient in `ExpansionCode` is stored as a bare `Fin (Nat.choose …)`.
This module supplies a semantic recursively enumerable type of weak
compositions, proves the sum of its entries, and identifies its cardinality
with the same stars-and-bars coefficient.  The resulting equivalence is the
finite API needed by the suppression decoder.
-/

open scoped BigOperators

noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Composition

/-- A weak composition of `total` into `parts` ordered parts.  At a successor
step the head is chosen in `[0,total]` and the tail composes the remainder. -/
def WeakComposition : (parts total : ℕ) → Type
  | 0, 0 => PUnit
  | 0, _ + 1 => PEmpty
  | 1, _ => PUnit
  | parts + 2, total =>
      Σ head : Fin (total + 1), WeakComposition (parts + 1) (total - head.1)

instance weakCompositionFintype : ∀ parts total, Fintype (WeakComposition parts total)
  | 0, 0 => by simp only [WeakComposition]; infer_instance
  | 0, _ + 1 => by simp only [WeakComposition]; infer_instance
  | 1, _ => by simp only [WeakComposition]; infer_instance
  | parts + 2, total => by
      change Fintype (Σ head : Fin (total + 1),
        WeakComposition (parts + 1) (total - head.1))
      letI (head : Fin (total + 1)) :
          Fintype (WeakComposition (parts + 1) (total - head.1)) :=
        weakCompositionFintype (parts + 1) (total - head.1)
      infer_instance

instance weakCompositionDecidableEq : ∀ parts total,
    DecidableEq (WeakComposition parts total)
  | 0, 0 => by simp only [WeakComposition]; infer_instance
  | 0, _ + 1 => by simp only [WeakComposition]; infer_instance
  | 1, _ => by simp only [WeakComposition]; infer_instance
  | parts + 2, total => by
      change DecidableEq (Σ head : Fin (total + 1),
        WeakComposition (parts + 1) (total - head.1))
      letI (head : Fin (total + 1)) :
          DecidableEq (WeakComposition (parts + 1) (total - head.1)) :=
        weakCompositionDecidableEq (parts + 1) (total - head.1)
      infer_instance

/-- The ordered tuple represented by a semantic weak composition. -/
def WeakComposition.entries : {parts total : ℕ} →
    WeakComposition parts total → Fin parts → ℕ
  | 0, 0, _ => Fin.elim0
  | 0, _ + 1, h => nomatch h
  | 1, total, _ => fun _ => total
  | _ + 2, _, ⟨head, tail⟩ => Fin.cons head.1 (WeakComposition.entries tail)

/-- The semantic entries have the prescribed total. -/
theorem card_weakComposition (parts total : ℕ) (hparts : 0 < parts) :
    Fintype.card (WeakComposition parts total) =
      (total + parts - 1).choose (parts - 1) := by
  induction parts generalizing total with
  | zero => omega
  | succ parts ih =>
      cases parts with
      | zero =>
          simp [WeakComposition]
      | succ parts =>
          have ih' : ∀ m : ℕ,
              Fintype.card (WeakComposition (parts + 1) m) =
                (m + (parts + 1) - 1).choose ((parts + 1) - 1) := by
            intro m
            exact ih m (by omega)
          rw [show parts + 1 + 1 = parts + 2 by omega]
          change Fintype.card
              (Σ head : Fin (total + 1),
                WeakComposition (parts + 1) (total - head.1)) = _
          rw [Fintype.card_sigma]
          simp_rw [ih']
          rw [show (∑ x : Fin (total + 1),
              (total - x.1 + (parts + 1) - 1).choose (parts + 1 - 1)) =
              ∑ i ∈ Finset.range (total + 1),
                (total - i + (parts + 1) - 1).choose (parts + 1 - 1) by
            exact Fin.sum_univ_eq_sum_range
              (fun i : ℕ =>
                (total - i + (parts + 1) - 1).choose (parts + 1 - 1))
              (total + 1)]
          rw [show (∑ i ∈ Finset.range (total + 1),
              (total - i + (parts + 1) - 1).choose (parts + 1 - 1)) =
              ∑ i ∈ Finset.range (total + 1), (i + parts).choose parts by
            simpa [Nat.add_sub_cancel, Nat.add_assoc] using!
              Finset.sum_range_reflect (fun i => (i + parts).choose parts) (total + 1)]
          simpa [Nat.add_sub_cancel, Nat.add_assoc] using!
            Nat.sum_range_add_choose total parts

/-- The bare binomial index in `ExpansionCode` is equivalent to an actual
ordered weak composition. -/
noncomputable def finChooseEquivWeakComposition (parts total : ℕ)
    (hparts : 0 < parts) :
    Fin ((total + parts - 1).choose (parts - 1)) ≃
      WeakComposition parts total :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, card_weakComposition parts total hparts])

/-- Semantic interpretation of the exact weak-composition index used by a
kernel with `v+r` ordered edge occurrences and `j-v` inserted trees. -/
noncomputable def expansionParts (v r j : ℕ) (hv : 0 < v) (hvj : v ≤ j) :
    Fin ((v + r + j - v - 1).choose (v + r - 1)) →
      Fin (v + r) → ℕ :=
  fun code =>
    let e : Fin ((v + r + j - v - 1).choose (v + r - 1)) ≃
        WeakComposition (v + r) (j - v) := by
      have htop : (j - v) + (v + r) - 1 = v + r + j - v - 1 := by omega
      simpa only [htop] using!
        finChooseEquivWeakComposition (v + r) (j - v) (by omega)
    (e code).entries

/-- The interpreted edge-sequence lengths use exactly `j-v` trees. -/
theorem WeakComposition.exists_entries : ∀ (parts total : ℕ)
    (f : Fin parts → ℕ), (∑ i, f i) = total →
    ∃ c : WeakComposition parts total, c.entries = f
  | 0, total, f, hsum => by
      have htotal : total = 0 := by simpa using! hsum.symm
      subst total
      refine ⟨PUnit.unit, ?_⟩
      funext i
      exact Fin.elim0 i
  | 1, total, f, hsum => by
      refine ⟨PUnit.unit, ?_⟩
      funext i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simpa [WeakComposition.entries] using! hsum.symm
  | parts + 2, total, f, hsum => by
      have hhead : f 0 ≤ total := by
        have hle : f 0 ≤ ∑ i, f i := Finset.single_le_sum
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
        simpa [hsum] using! hle
      let head : Fin (total + 1) := ⟨f 0, by omega⟩
      let tail : Fin (parts + 1) → ℕ := fun i => f i.succ
      have htail : ∑ i, tail i = total - head.1 := by
        rw [Fin.sum_univ_succ] at hsum
        change f 0 + ∑ i, tail i = total at hsum
        dsimp [head]
        omega
      obtain ⟨c, hc⟩ := WeakComposition.exists_entries (parts + 1)
        (total - head.1) tail htail
      refine ⟨⟨head, c⟩, ?_⟩
      funext i
      refine Fin.cases ?_ (fun t => ?_) i
      · simp [WeakComposition.entries, head]
      · simpa [WeakComposition.entries, tail] using! congrFun hc t

/-- Surjectivity of the exact stars-and-bars index onto path-length vectors.
This is the inverse direction needed by suppression: once maximal paths have
been ordered, their internal-vertex counts determine an actual coefficient
index used by `decodeExpansionCode`. -/
theorem exists_expansionParts_code (v r j : ℕ) (hv : 0 < v) (hvj : v ≤ j)
    (f : Fin (v + r) → ℕ) (hsum : ∑ i, f i = j - v) :
    ∃ code : Fin ((v + r + j - v - 1).choose (v + r - 1)),
      expansionParts v r j hv hvj code = f := by
  let e : Fin ((v + r + j - v - 1).choose (v + r - 1)) ≃
      WeakComposition (v + r) (j - v) := by
    have htop : (j - v) + (v + r) - 1 = v + r + j - v - 1 := by omega
    simpa only [htop] using!
      finChooseEquivWeakComposition (v + r) (j - v) (by omega)
  obtain ⟨c, hc⟩ := WeakComposition.exists_entries (v + r) (j - v) f hsum
  refine ⟨e.symm c, ?_⟩
  unfold expansionParts
  change (e (e.symm c)).entries = f
  rw [e.apply_symm_apply, hc]

end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Composition


/-!
# Deterministic leaf pruning and the finite two-core

Vertices remain in the fixed ambient type `Fin k`; an active finset records
the current induced subgraph.  One degree-at-most-one vertex is removed at a
time.  This makes edge/vertex bookkeeping compatible with the later
suppression construction and gives a terminating process after at most `k`
steps.
-/

noncomputable section

namespace Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Core

open Erdos745.WrapUp

/- Edges of `G` induced by an active vertex set. -/
end Erdos745.WrapUp.Proofs.Internal.W02_KERNEL_Core
