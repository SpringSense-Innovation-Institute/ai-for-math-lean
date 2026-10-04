module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage4.contracts.GroupA

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT02.MomentLocal

open Finset
open scoped BigOperators ArithmeticFunction
open Erdos448.Stage4
open Erdos448.Stage4.Contracts

noncomputable section

instance (p : Prop) : Decidable p := Classical.propDecidable p

lemma isRough_one (s : ℝ) : IsRough 1 s := by
  intro p hp hpd
  exact (hp.ne_one (Nat.dvd_one.mp hpd)).elim

lemma isRough_mul_iff (a b : ℕ) (s : ℝ) :
    IsRough (a * b) s ↔ IsRough a s ∧ IsRough b s := by
  constructor
  · intro h
    exact ⟨fun p hp hpa => h p hp (dvd_mul_of_dvd_left hpa b),
      fun p hp hpb => h p hp (dvd_mul_of_dvd_right hpb a)⟩
  · rintro ⟨ha, hb⟩ p hp hpab
    rcases hp.dvd_mul.mp hpab with hpa | hpb
    · exact ha p hp hpa
    · exact hb p hp hpb

lemma roughIndicator_mul (a b : ℕ) (s : ℝ) :
    roughIndicator (a * b) s = roughIndicator a s * roughIndicator b s := by
  by_cases ha : IsRough a s <;> by_cases hb : IsRough b s
  · have hab := (isRough_mul_iff a b s).2 ⟨ha, hb⟩
    simp [roughIndicator, ha, hb, hab]
  · have hab : ¬IsRough (a * b) s := fun h => hb ((isRough_mul_iff a b s).1 h).2
    simp [roughIndicator, ha, hb, hab]
  · have hab : ¬IsRough (a * b) s := fun h => ha ((isRough_mul_iff a b s).1 h).1
    simp [roughIndicator, ha, hb, hab]
  · have hab : ¬IsRough (a * b) s := fun h => ha ((isRough_mul_iff a b s).1 h).1
    simp [roughIndicator, ha, hb, hab]

lemma omegaBelowRaw_mul_of_coprime
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (u : ℝ) :
    omegaBelowRaw (a * b) u = omegaBelowRaw a u + omegaBelowRaw b u := by
  have ha0 := ha.ne'
  have hb0 := hb.ne'
  simp only [omegaBelowRaw, dif_pos ha, dif_pos hb, dif_pos (Nat.mul_pos ha hb), omegaBelow]
  rw [hab.primeFactors_mul,
    Finset.sum_union ((Nat.disjoint_primeFactors ha0 hb0).2 hab)]
  congr 1
  · apply Finset.sum_congr rfl
    intro p hp
    by_cases hpu : (p : ℝ) < u
    · simp only [hpu, if_true]
      exact Nat.factorization_eq_of_coprime_left hab (List.mem_toFinset.mp hp)
    · simp [hpu]
  · apply Finset.sum_congr rfl
    intro p hp
    by_cases hpu : (p : ℝ) < u
    · simp only [hpu, if_true]
      exact Nat.factorization_eq_of_coprime_right hab (List.mem_toFinset.mp hp)
    · simp [hpu]

@[expose] def roughAF (s : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else roughIndicator n s, by simp⟩

@[expose] def momentSummandAF (q : MomentParameters) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else
      q.y.rpow (omegaBelowRaw n q.u : ℝ) * roughIndicator n q.sigma,
    by simp⟩

lemma roughAF_multiplicative (s : ℝ) :
    ArithmeticFunction.IsMultiplicative (roughAF s) := by
  constructor
  · simp [roughAF, roughIndicator, isRough_one]
  · intro a b hab
    by_cases ha : a = 0
    · subst a; simp [roughAF]
    by_cases hb : b = 0
    · subst b; simp [roughAF]
    change (if a * b = 0 then 0 else (roughIndicator (a * b) s : ℝ)) =
      (if a = 0 then 0 else (roughIndicator a s : ℝ)) *
        (if b = 0 then 0 else (roughIndicator b s : ℝ))
    rw [if_neg (mul_ne_zero ha hb), if_neg ha, if_neg hb, roughIndicator_mul]
    norm_cast

lemma momentSummandAF_multiplicative (q : MomentParameters) :
    ArithmeticFunction.IsMultiplicative (momentSummandAF q) := by
  constructor
  · simp [momentSummandAF, omegaBelowRaw, omegaBelow, roughIndicator, isRough_one]
  · intro a b hab
    by_cases ha0 : a = 0
    · subst a; simp [momentSummandAF]
    by_cases hb0 : b = 0
    · subst b; simp [momentSummandAF]
    have ha : 0 < a := Nat.pos_of_ne_zero ha0
    have hb : 0 < b := Nat.pos_of_ne_zero hb0
    change
      (if a * b = 0 then 0 else
        q.y.rpow (omegaBelowRaw (a * b) q.u : ℝ) * roughIndicator (a * b) q.sigma) =
      (if a = 0 then 0 else
        q.y.rpow (omegaBelowRaw a q.u : ℝ) * roughIndicator a q.sigma) *
      (if b = 0 then 0 else
        q.y.rpow (omegaBelowRaw b q.u : ℝ) * roughIndicator b q.sigma)
    rw [if_neg (mul_ne_zero ha0 hb0), if_neg ha0, if_neg hb0]
    rw [omegaBelowRaw_mul_of_coprime ha hb hab, Nat.cast_add,
      roughIndicator_mul]
    have hyadd :
        q.y.rpow ((omegaBelowRaw a q.u : ℝ) + omegaBelowRaw b q.u) =
          q.y.rpow (omegaBelowRaw a q.u : ℝ) *
            q.y.rpow (omegaBelowRaw b q.u : ℝ) :=
      Real.rpow_add q.y_pos _ _
    rw [hyadd]
    push_cast
    ring

@[expose] def roughDivisorAF (s : ℝ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.instSemiring.mul (roughAF s)
    (ArithmeticFunction.natToArithmeticFunction (R := ℝ) ArithmeticFunction.zeta)

@[expose] def momentDivisorAF (q : MomentParameters) : ArithmeticFunction ℝ :=
  ArithmeticFunction.instSemiring.mul (momentSummandAF q)
    (ArithmeticFunction.natToArithmeticFunction (R := ℝ) ArithmeticFunction.zeta)

lemma roughDivisorAF_multiplicative (s : ℝ) :
    ArithmeticFunction.IsMultiplicative (roughDivisorAF s) :=
  (roughAF_multiplicative s).mul
    (ArithmeticFunction.isMultiplicative_zeta.natCast)

lemma momentDivisorAF_multiplicative (q : MomentParameters) :
    ArithmeticFunction.IsMultiplicative (momentDivisorAF q) :=
  (momentSummandAF_multiplicative q).mul
    (ArithmeticFunction.isMultiplicative_zeta.natCast)

lemma roughDivisorAF_eq (n : ℕ) (hn : 0 < n) (s : ℝ) :
    roughDivisorAF s n = (roughTau ⟨n, hn⟩ s : ℝ) := by
  calc
    roughDivisorAF s n =
        ∑ d ∈ n.divisors, roughAF s d :=
      ArithmeticFunction.coe_mul_zeta_apply
    _ = (roughTau ⟨n, hn⟩ s : ℝ) := by
      unfold roughTau divisorSet roughAF
      push_cast
      apply Finset.sum_congr rfl
      intro d hd
      change (if d = 0 then 0 else (roughIndicator d s : ℝ)) = _
      rw [if_neg]
      intro hd0
      subst d
      have hdvd := (Nat.mem_divisors.mp hd).1
      simp at hdvd
      exact hn.ne' hdvd

lemma momentDivisorAF_eq (q : MomentParameters) (n : ℕ) (hn : 0 < n) :
    momentDivisorAF q n =
      ∑ d ∈ divisorSet ⟨n, hn⟩,
        q.y.rpow (omegaBelowRaw d q.u : ℝ) * (roughIndicator d q.sigma : ℝ) := by
  calc
    momentDivisorAF q n =
        ∑ d ∈ n.divisors, momentSummandAF q d :=
      ArithmeticFunction.coe_mul_zeta_apply
    _ = ∑ d ∈ divisorSet ⟨n, hn⟩,
          q.y.rpow (omegaBelowRaw d q.u : ℝ) *
            (roughIndicator d q.sigma : ℝ) := by
      unfold divisorSet momentSummandAF
      apply Finset.sum_congr rfl
      intro d hd
      change (if d = 0 then 0 else
        q.y.rpow (omegaBelowRaw d q.u : ℝ) * roughIndicator d q.sigma) = _
      rw [if_neg]
      intro hd0
      subst d
      have hdvd := (Nat.mem_divisors.mp hd).1
      simp at hdvd
      exact hn.ne' hdvd

@[expose] def combinedMomentAF (q : MomentParameters) : ArithmeticFunction ℝ :=
  ArithmeticFunction.pdiv
    (ArithmeticFunction.pmul (roughAF q.theta) (momentDivisorAF q))
    (roughDivisorAF q.sigma)

lemma combinedMomentAF_multiplicative (q : MomentParameters) :
    ArithmeticFunction.IsMultiplicative (combinedMomentAF q) :=
  ((roughAF_multiplicative q.theta).pmul
    (momentDivisorAF_multiplicative q)).pdiv
      (roughDivisorAF_multiplicative q.sigma)

lemma momentWeight_eq_combined (q : MomentParameters) :
    momentWeight q = combinedMomentAF q := by
  funext n
  by_cases hn : 0 < n
  · rw [momentWeight, dif_pos hn]
    change moment q ⟨n, hn⟩ =
      roughAF q.theta n * momentDivisorAF q n / roughDivisorAF q.sigma n
    rw [roughDivisorAF_eq n hn, momentDivisorAF_eq q n hn]
    unfold moment roughAF
    simp only [ArithmeticFunction.coe_mk, if_neg hn.ne']
    ring
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp [momentWeight, combinedMomentAF, ArithmeticFunction.pdiv,
      ArithmeticFunction.pmul, roughAF]

lemma roughTau_pos (n : PosNat) (s : ℝ) : 0 < roughTau n s := by
  unfold roughTau divisorSet
  have hone : 1 ∈ n.1.divisors := Nat.mem_divisors.mpr ⟨one_dvd _, n.property.ne'⟩
  have hind : roughIndicator 1 s = 1 := by simp [roughIndicator, isRough_one]
  have := Finset.single_le_sum (fun d _ => Nat.zero_le (roughIndicator d s)) hone
  have hsum : 1 ≤ ∑ d ∈ n.1.divisors, roughIndicator d s := by simpa [hind] using this
  omega

lemma moment_nonnegative (q : MomentParameters) (n : PosNat) :
    0 ≤ moment q n := by
  unfold moment
  apply mul_nonneg
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · apply Finset.sum_nonneg
    intro d hd
    exact mul_nonneg (Real.rpow_nonneg q.y_pos.le _) (Nat.cast_nonneg _)

lemma isRough_prime_pow_iff {p j : ℕ} (hp : p.Prime) (hj : 0 < j) (s : ℝ) :
    IsRough (p ^ j) s ↔ s ≤ p := by
  constructor
  · intro h
    exact h p hp (dvd_pow_self p hj.ne')
  · intro h r hr hrd
    have hrp : r ∣ p := hr.dvd_of_dvd_pow hrd
    have : r = p := (Nat.dvd_prime hp).mp hrp |>.resolve_left hr.ne_one
    simpa [this] using h

lemma roughIndicator_prime_pow {p j : ℕ} (hp : p.Prime) (s : ℝ) :
    roughIndicator (p ^ j) s = if j = 0 then 1 else if s ≤ p then 1 else 0 := by
  by_cases hj : j = 0
  · subst j; simp [roughIndicator, isRough_one]
  · have hjp : 0 < j := Nat.pos_of_ne_zero hj
    by_cases hs : s ≤ p
    · simp [roughIndicator, hj, hs, (isRough_prime_pow_iff hp hjp s).2 hs]
    · simp [roughIndicator, hj, hs, (isRough_prime_pow_iff hp hjp s).not.mpr hs]

lemma omegaBelowRaw_prime_pow {p j : ℕ} (hp : p.Prime) (u : ℝ) :
    omegaBelowRaw (p ^ j) u = if (p : ℝ) < u then j else 0 := by
  by_cases hj : j = 0
  · subst j; simp [omegaBelowRaw, omegaBelow]
  · have hpj : 0 < p ^ j := pow_pos hp.pos j
    simp only [omegaBelowRaw, dif_pos hpj, omegaBelow,
      Nat.primeFactors_prime_pow hj hp, Finset.sum_singleton]
    rw [Nat.factorization_pow_self hp]

lemma prime_power_divisor_sums
    (q : MomentParameters) (p nu : ℕ) (hp : p.Prime) (hnu : 1 ≤ nu) :
    roughTau ⟨p ^ nu, pow_pos hp.pos nu⟩ q.sigma =
        (if q.sigma ≤ p then nu + 1 else 1) ∧
      (∑ d ∈ divisorSet ⟨p ^ nu, pow_pos hp.pos nu⟩,
          q.y.rpow (omegaBelowRaw d q.u : ℝ) * (roughIndicator d q.sigma : ℝ)) =
        if q.sigma ≤ p then
          if (p : ℝ) < q.u then ∑ j ∈ Finset.range (nu + 1), q.y ^ j
          else (nu + 1 : ℕ)
        else 1 := by
  change
    (∑ d ∈ (p ^ nu).divisors, roughIndicator d q.sigma) =
        (if q.sigma ≤ p then nu + 1 else 1) ∧
      (∑ d ∈ (p ^ nu).divisors,
          q.y.rpow (omegaBelowRaw d q.u : ℝ) * (roughIndicator d q.sigma : ℝ)) = _
  rw [Nat.divisors_prime_pow hp, Finset.sum_map, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  simp_rw [roughIndicator_prime_pow hp, omegaBelowRaw_prime_pow hp]
  by_cases hs : q.sigma ≤ p
  · by_cases hpu : (p : ℝ) < q.u
    · constructor <;> simp [hs, hpu]
    · constructor <;> simp [hs, hpu]
  · have hp_lt_sigma : (p : ℝ) < q.sigma := lt_of_not_ge hs
    have hp_lt_u : (p : ℝ) < q.u := hp_lt_sigma.trans q.u_gt_sigma
    simp only [if_neg hs]
    constructor
    · rw [Finset.sum_eq_single 0]
      · simp
      · intro j hj hj0
        simp [hj0]
      · simp
    · rw [Finset.sum_eq_single 0]
      · simp
      · intro j hj hj0
        simp [hj0, hp_lt_u]
      · simp

theorem p010 : P010Statement := by
  intro q
  constructor
  · rw [momentWeight_eq_combined]
    refine ⟨?_, ?_⟩
    · intro n hn
      rw [← momentWeight_eq_combined]
      simp only [momentWeight, dif_pos hn]
      exact moment_nonnegative q ⟨n, hn⟩
    · exact ⟨(combinedMomentAF_multiplicative q).1,
        fun a b ha hb hab => (combinedMomentAF_multiplicative q).2 hab⟩
  · intro p nu hp hnu
    dsimp
    have hnu0 : nu ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le zero_lt_one hnu)
    have hmax_one : (1 : ℝ) ≤ max 1 q.y := le_max_left _ _
    have hmax_pow_one : (1 : ℝ) ≤ (max 1 q.y) ^ nu := by
      exact one_le_pow₀ hmax_one
    have hsums := prime_power_divisor_sums q p nu hp hnu
    unfold moment
    rw [hsums.1, hsums.2]
    have htheta_sigma : q.theta ≤ q.sigma := q.sigma_ge_theta
    by_cases hp_theta : (p : ℝ) < q.theta
    · have hrough : ¬q.theta ≤ p := not_le.mpr hp_theta
      simp [roughIndicator_prime_pow hp, hnu0, hrough, hp_theta,
        hmax_pow_one]
    · have htheta : q.theta ≤ p := le_of_not_gt hp_theta
      by_cases hp_sigma : (p : ℝ) < q.sigma
      · have hsigma : ¬q.sigma ≤ p := not_le.mpr hp_sigma
        simp [roughIndicator_prime_pow hp, hnu0, htheta, hsigma,
          hp_theta, hp_sigma, hmax_pow_one]
      · have hsigma : q.sigma ≤ p := le_of_not_gt hp_sigma
        by_cases hp_u : (p : ℝ) < q.u
        · have hy : ∀ j ∈ Finset.range (nu + 1), q.y ^ j ≤
              (max 1 q.y) ^ nu := by
            intro j hj
            have hjle : j ≤ nu := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
            calc
              q.y ^ j ≤ (max 1 q.y) ^ j :=
                pow_le_pow_left₀ q.y_pos.le (le_max_right _ _) j
              _ ≤ (max 1 q.y) ^ nu := pow_le_pow_right₀ hmax_one hjle
          have hsum := Finset.sum_le_sum hy
          have hav_le :
              (1 / (nu + 1 : ℕ) : ℝ) *
                  ∑ j ∈ Finset.range (nu + 1), q.y ^ j ≤
                (max 1 q.y) ^ nu := by
            rw [one_div, inv_mul_le_iff₀ (show (0 : ℝ) < (nu + 1 : ℕ) by positivity)]
            simpa [Finset.card_range] using hsum
          have hav_nonneg :
              0 ≤ (1 / (nu + 1 : ℕ) : ℝ) *
                  ∑ j ∈ Finset.range (nu + 1), q.y ^ j := by
            apply mul_nonneg (by positivity)
            exact Finset.sum_nonneg fun j hj => pow_nonneg q.y_pos.le _
          simp only [roughIndicator_prime_pow hp, hnu0, if_false,
            if_pos htheta, hsigma, hp_theta, hp_sigma, hp_u,
            Nat.cast_add_one, if_true, Nat.cast_zero, Nat.cast_one,
            zero_add, one_div]
          refine ⟨trivial, ?_, ?_⟩
          · simpa [Nat.cast_add_one, one_div] using hav_nonneg
          · simpa [Nat.cast_add_one, one_div] using hav_le
        · have hden : (0 : ℝ) < nu + 1 := by positivity
          simp [roughIndicator_prime_pow hp, hnu0, htheta, hsigma,
            hp_theta, hp_sigma, hp_u, Nat.cast_add_one, hden.ne', hmax_pow_one]

end

end Erdos448.Stage7.ROOT02.MomentLocal
