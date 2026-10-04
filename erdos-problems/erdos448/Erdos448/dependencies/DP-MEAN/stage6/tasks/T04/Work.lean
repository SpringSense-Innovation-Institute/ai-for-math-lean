module

import all Mathlib.Basic.Real.Basic
public import Erdos448.dependencies.«DP-MEAN».stage6.shared.TaskInterfaces

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.DPMean.TaskT04

open Erdos448.DPMean

noncomputable section

lemma mem_inclusiveNatDomain_iff {x : ℝ} (hx : 0 ≤ x) {n : ℕ} :
    n ∈ inclusiveNatDomain x ↔ 0 < n ∧ (n : ℝ) ≤ x := by
  simp [inclusiveNatDomain, Nat.le_floor_iff hx, and_comm]

lemma mem_inclusivePrimeDomain_iff {x : ℝ} (hx : 0 ≤ x) {p : ℕ} :
    p ∈ inclusivePrimeDomain x ↔ Nat.Prime p ∧ (p : ℝ) ≤ x := by
  rw [inclusivePrimeDomain, Finset.mem_filter,
    mem_inclusiveNatDomain_iff hx]
  constructor
  · rintro ⟨⟨hp_pos, hp_le⟩, hp⟩
    exact ⟨hp, hp_le⟩
  · rintro ⟨hp, hp_le⟩
    exact ⟨⟨hp.pos, hp_le⟩, hp⟩

lemma factorization_eq_of_prime_coprime_decomposition
    {n p r m : ℕ} (hp : Nat.Prime p) (hr : 1 ≤ r)
    (hn : n = p ^ r * m) (hcop : Nat.Coprime p m) :
    n.factorization p = r := by
  subst n
  rw [Nat.factorization_mul_apply_of_coprime
    ((Nat.coprime_pow_left_iff (by omega) p m).2 hcop)]
  simp [hp.factorization_pow,
    Nat.factorization_eq_zero_of_not_dvd (hp.coprime_iff_not_dvd.mp hcop)]

lemma primePower_decomposition_unique
    {n p : ℕ} (hn : 0 < n) (hp : Nat.Prime p) (hpn : p ∣ n) :
    ∃! rm : ℕ × ℕ,
      1 ≤ rm.1 ∧ n = p ^ rm.1 * rm.2 ∧ Nat.Coprime p rm.2 := by
  let r := n.factorization p
  let m := ordCompl[p] n
  have hr : 1 ≤ r := (hp.dvd_iff_one_le_factorization hn.ne').mp hpn
  have hnm : n = p ^ r * m := (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  have hcop : Nat.Coprime p m := Nat.coprime_ordCompl hp hn.ne'
  refine ⟨(r, m), ⟨hr, hnm, hcop⟩, ?_⟩
  rintro ⟨r', m'⟩ ⟨hr', hnr'm', hcop'⟩
  have hr'eq : r' = r := by
    symm
    exact factorization_eq_of_prime_coprime_decomposition hp hr' hnr'm' hcop'
  subst r'
  apply Prod.ext
  · rfl
  · exact Nat.mul_left_cancel (Nat.pow_pos hp.pos) (hnr'm'.symm.trans hnm)

lemma log_eq_sum_primePowers
    {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : n ∈ inclusiveNatDomain x) :
    Real.log (n : ℝ) =
      ∑ p ∈ inclusivePrimeDomain x,
        if p ∣ n then Real.log (((p ^ n.factorization p : ℕ) : ℝ)) else 0 := by
  have hnpos : 0 < n := (mem_inclusiveNatDomain_iff hx).mp hn |>.1
  have hnle : (n : ℝ) ≤ x := (mem_inclusiveNatDomain_iff hx).mp hn |>.2
  rw [Real.log_nat_eq_sum_factorization]
  change (∑ p ∈ n.factorization.support,
      (n.factorization p : ℝ) * Real.log (p : ℝ)) = _
  calc
    (∑ p ∈ n.factorization.support,
        (n.factorization p : ℝ) * Real.log (p : ℝ)) =
        ∑ p ∈ n.factorization.support,
          Real.log (((p ^ n.factorization p : ℕ) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro p hp_mem
            simp [Nat.cast_pow, Real.log_pow]
    _ = ∑ p ∈ inclusivePrimeDomain x,
          if p ∣ n then Real.log (((p ^ n.factorization p : ℕ) : ℝ)) else 0 := by
      have hsets : n.factorization.support =
          (inclusivePrimeDomain x).filter (fun p => p ∣ n) := by
        ext p
        constructor
        · intro hp_mem
          have hpf : p ∈ n.primeFactors := by simpa using hp_mem
          have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hpf
          have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hpf
          have hpn : p ≤ n := Nat.le_of_dvd hnpos hpdvd
          exact Finset.mem_filter.mpr
            ⟨(mem_inclusivePrimeDomain_iff hx).2
              ⟨hpp, (mod_cast hpn : (p : ℝ) ≤ (n : ℝ)).trans hnle⟩,
              hpdvd⟩
        · intro hp_mem
          rcases Finset.mem_filter.mp hp_mem with ⟨hp_dom, hpdvd⟩
          have hpp : Nat.Prime p :=
            (mem_inclusivePrimeDomain_iff hx).mp hp_dom |>.1
          simpa using hpp.mem_primeFactors hpdvd hnpos.ne'
      rw [hsets, Finset.sum_filter]

lemma fixed_prime_reindex
    (h : ArithmeticFunction) (hmul : Multiplicative h)
    {x : ℝ} (hx : 0 ≤ x) {p : ℕ} (hp : Nat.Prime p) :
    (∑ n ∈ inclusiveNatDomain x,
      if p ∣ n then
        h n * Real.log (((p ^ n.factorization p : ℕ) : ℝ))
      else 0) =
    ∑ r ∈ inclusiveNatDomain x,
      ∑ m ∈ inclusiveNatDomain x,
        if Nat.Coprime p m ∧ ((((p ^ r) * m : ℕ) : ℝ) ≤ x) then
          h (p ^ r) * h m * Real.log ((((p ^ r : ℕ) : ℝ)))
        else 0 := by
  let D := inclusiveNatDomain x
  let A := D.filter (fun n => p ∣ n)
  let B := (D.product D).filter (fun rm =>
    Nat.Coprime p rm.2 ∧ ((((p ^ rm.1) * rm.2 : ℕ) : ℝ) ≤ x))
  have hreindex :
      (∑ n ∈ A, h n * Real.log (((p ^ n.factorization p : ℕ) : ℝ))) =
      ∑ rm ∈ B, h (p ^ rm.1) * h rm.2 *
        Real.log ((((p ^ rm.1 : ℕ) : ℝ))) := by
    apply Finset.sum_bij'
      (fun n _ => (n.factorization p, ordCompl[p] n))
      (fun rm _ => p ^ rm.1 * rm.2)
    · intro n hnA
      have hnD : n ∈ D := (Finset.mem_filter.mp hnA).1
      have hpdvd : p ∣ n := (Finset.mem_filter.mp hnA).2
      have hnpos : 0 < n := (mem_inclusiveNatDomain_iff hx).mp hnD |>.1
      have hnle : (n : ℝ) ≤ x := (mem_inclusiveNatDomain_iff hx).mp hnD |>.2
      have hrpos : 0 < n.factorization p := hp.factorization_pos_of_dvd hnpos.ne' hpdvd
      have hrlt : n.factorization p < n := Nat.factorization_lt p hnpos.ne'
      have hmpos : 0 < ordCompl[p] n := Nat.ordCompl_pos p hnpos.ne'
      have hmle : ordCompl[p] n ≤ n := Nat.ordCompl_le n p
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, Nat.coprime_ordCompl hp hnpos.ne', ?_⟩
      · exact (mem_inclusiveNatDomain_iff hx).2
          ⟨hrpos, (mod_cast hrlt.le : (n.factorization p : ℝ) ≤ (n : ℝ)).trans hnle⟩
      · exact (mem_inclusiveNatDomain_iff hx).2
          ⟨hmpos, (Nat.cast_le.mpr hmle).trans hnle⟩
      · simpa [Nat.ordProj_mul_ordCompl_eq_self n p] using hnle
    · intro rm hrmB
      rcases Finset.mem_filter.mp hrmB with ⟨hrmD, hcop, hprodle⟩
      rcases Finset.mem_product.mp hrmD with ⟨hrD, hmD⟩
      have hrpos : 0 < rm.1 := (mem_inclusiveNatDomain_iff hx).mp hrD |>.1
      have hmpos : 0 < rm.2 := (mem_inclusiveNatDomain_iff hx).mp hmD |>.1
      apply Finset.mem_filter.mpr
      refine ⟨(mem_inclusiveNatDomain_iff hx).2
        ⟨Nat.mul_pos (Nat.pow_pos hp.pos) hmpos, hprodle⟩, ?_⟩
      exact dvd_mul_of_dvd_left (dvd_pow_self p hrpos.ne') rm.2
    · intro n hnA
      exact Nat.ordProj_mul_ordCompl_eq_self n p
    · intro rm hrmB
      rcases Finset.mem_filter.mp hrmB with ⟨hrmD, hcop, hprodle⟩
      have hrpos : 1 ≤ rm.1 := (mem_inclusiveNatDomain_iff hx).mp
        (Finset.mem_product.mp hrmD).1 |>.1
      have hfac : (p ^ rm.1 * rm.2).factorization p = rm.1 :=
        factorization_eq_of_prime_coprime_decomposition hp hrpos rfl hcop
      apply Prod.ext
      · exact hfac
      · simp only [hfac]
        exact Nat.mul_div_cancel_left rm.2 (Nat.pow_pos hp.pos)
    · intro n hnA
      have hnD : n ∈ D := (Finset.mem_filter.mp hnA).1
      have hpdvd : p ∣ n := (Finset.mem_filter.mp hnA).2
      have hnpos : 0 < n := (mem_inclusiveNatDomain_iff hx).mp hnD |>.1
      have hrpos : 0 < n.factorization p := hp.factorization_pos_of_dvd hnpos.ne' hpdvd
      have hmpos : 0 < ordCompl[p] n := Nat.ordCompl_pos p hnpos.ne'
      change h n * Real.log (((p ^ n.factorization p : ℕ) : ℝ)) =
        h (p ^ n.factorization p) * h (ordCompl[p] n) *
          Real.log (((p ^ n.factorization p : ℕ) : ℝ))
      have hh_eq : h n = h (p ^ n.factorization p) * h (ordCompl[p] n) := by
        calc
          h n = h (ordProj[p] n * ordCompl[p] n) :=
            congrArg h (Nat.ordProj_mul_ordCompl_eq_self n p).symm
          _ = h (p ^ n.factorization p) * h (ordCompl[p] n) :=
            hmul.2 _ _ (Nat.pow_pos hp.pos) hmpos
              ((Nat.coprime_pow_left_iff hrpos p _).2
                (Nat.coprime_ordCompl hp hnpos.ne'))
      exact congrArg
        (fun y : ℝ => y * Real.log (((p ^ n.factorization p : ℕ) : ℝ))) hh_eq
  simpa [A, B, D, Finset.sum_filter, Finset.sum_product] using hreindex

lemma exact_primePower_reindex
    (h : ArithmeticFunction) (hh : NonnegativeMultiplicative h)
    (x : ℝ) (hx : 1 ≤ x) :
    weightedLogMean h x = primePowerCoprimeSum h x := by
  have hx0 : 0 ≤ x := hx.trans' zero_le_one
  unfold weightedLogMean primePowerCoprimeSum
  calc
    (∑ n ∈ inclusiveNatDomain x, h n * Real.log (n : ℝ)) =
        ∑ n ∈ inclusiveNatDomain x, h n *
          (∑ p ∈ inclusivePrimeDomain x,
            if p ∣ n then Real.log (((p ^ n.factorization p : ℕ) : ℝ)) else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [log_eq_sum_primePowers hx0 hn]
    _ = ∑ p ∈ inclusivePrimeDomain x,
          ∑ n ∈ inclusiveNatDomain x,
            if p ∣ n then
              h n * Real.log (((p ^ n.factorization p : ℕ) : ℝ))
            else 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hpdvd : p ∣ n <;> simp [hpdvd, Finset.mul_sum]
    _ = ∑ p ∈ inclusivePrimeDomain x,
          ∑ r ∈ inclusiveNatDomain x,
            ∑ m ∈ inclusiveNatDomain x,
              if Nat.Coprime p m ∧ ((((p ^ r) * m : ℕ) : ℝ) ≤ x) then
                h (p ^ r) * h m * Real.log ((((p ^ r : ℕ) : ℝ)))
              else 0 := by
      apply Finset.sum_congr rfl
      intro p hp_mem
      exact fixed_prime_reindex h hh.multiplicative hx0
        ((mem_inclusivePrimeDomain_iff hx0).mp hp_mem).1

@[expose] abbrev PublicTarget : Prop := Erdos448.DPMean.S6.T04Target

theorem publicTarget : PublicTarget := by
  intro h hh x hx
  refine
    { exact_identity := exact_primePower_reindex h hh x hx
      multiplicity_one := ?_ }
  intro n hn hnle p hp hpn
  exact primePower_decomposition_unique hn hp hpn

end

end Erdos448.DPMean.TaskT04
