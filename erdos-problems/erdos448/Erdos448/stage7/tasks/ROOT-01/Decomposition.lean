module

import all Mathlib.Basic.Real.Basic
public import Erdos448.stage7.tasks.«ROOT-01».Summability
public import Mathlib.Data.Nat.GCD.BigOperators

public section

set_option backward.isDefEq.respectTransparency false

namespace Erdos448.Stage7.ROOT01

open Erdos448.Stage4
open Erdos448.Stage4.Contracts
open Finset Nat
open scoped BigOperators

noncomputable section

@[expose] def commonPart (Ksh : PosNat) (n : ℕ) : ℕ :=
  (n.primeFactorsList.filter fun p => p ∈ Ksh.1.primeFactors).prod

@[expose] def awayPart (Ksh : PosNat) (n : ℕ) : ℕ :=
  (n.primeFactorsList.filter fun p => p ∉ Ksh.1.primeFactors).prod

lemma commonPart_pos (Ksh : PosNat) {n : ℕ} (hn : 0 < n) :
    0 < commonPart Ksh n := by
  unfold commonPart
  apply List.prod_pos
  intro p hp
  exact (Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_filter hp)).pos

lemma awayPart_pos (Ksh : PosNat) {n : ℕ} (hn : 0 < n) :
    0 < awayPart Ksh n := by
  unfold awayPart
  apply List.prod_pos
  intro p hp
  exact (Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_filter hp)).pos

lemma commonPart_mul_awayPart (Ksh : PosNat) {n : ℕ} (hn : 0 < n) :
    commonPart Ksh n * awayPart Ksh n = n := by
  rw [commonPart, awayPart]
  calc
    (n.primeFactorsList.filter fun p => p ∈ Ksh.1.primeFactors).prod *
        (n.primeFactorsList.filter fun p => p ∉ Ksh.1.primeFactors).prod =
        n.primeFactorsList.prod := by
      simpa using List.prod_map_filter_mul_prod_map_filter_not
        (fun p => p ∈ Ksh.1.primeFactors) id n.primeFactorsList
    _ = n := Nat.prod_primeFactorsList (Nat.ne_of_gt hn)

lemma commonPart_primeSupport (Ksh : PosNat) {n : ℕ} (hn : 0 < n) :
    HasPrimeSupportIn ⟨commonPart Ksh n, commonPart_pos Ksh hn⟩ Ksh := by
  intro p hp
  have hpPrime := Nat.prime_of_mem_primeFactors hp
  have hpDvd : p ∣ commonPart Ksh n := Nat.dvd_of_mem_primeFactors hp
  have hpFiltered : p ∈
      n.primeFactorsList.filter (fun q => q ∈ Ksh.1.primeFactors) := by
    apply mem_list_primes_of_dvd_prod (Nat.prime_iff.mp hpPrime)
    · intro q hq
      exact Nat.prime_iff.mp
        (Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_filter hq))
    · exact hpDvd
  exact of_decide_eq_true (List.mem_filter.mp hpFiltered).2

lemma commonPart_coprime_awayPart (Ksh : PosNat) (n : ℕ) :
    Nat.Coprime (commonPart Ksh n) (awayPart Ksh n) := by
  rw [commonPart, awayPart, Nat.coprime_list_prod_left_iff]
  intro p hp
  rw [Nat.coprime_list_prod_right_iff]
  intro q hq
  have hp' := List.mem_filter.mp hp
  have hq' := List.mem_filter.mp hq
  have hpK : p ∈ Ksh.1.primeFactors := of_decide_eq_true hp'.2
  have hqK : q ∉ Ksh.1.primeFactors := of_decide_eq_true hq'.2
  have hpPrime := Nat.prime_of_mem_primeFactorsList hp'.1
  have hqPrime := Nat.prime_of_mem_primeFactorsList hq'.1
  exact (Nat.coprime_primes hpPrime hqPrime).2 fun hpq =>
    hqK (hpq ▸ hpK)

lemma awayPart_coprime (Ksh : PosNat) (n : ℕ) :
    Nat.Coprime (awayPart Ksh n) Ksh.1 := by
  rw [awayPart, Nat.coprime_list_prod_left_iff]
  intro p hp
  have hp' := List.mem_filter.mp hp
  have hpNotK : p ∉ Ksh.1.primeFactors := of_decide_eq_true hp'.2
  have hpPrime := Nat.prime_of_mem_primeFactorsList hp'.1
  rw [hpPrime.coprime_iff_not_dvd]
  intro hpK
  exact hpNotK (Nat.mem_primeFactors.mpr
    ⟨hpPrime, hpK, Nat.ne_of_gt Ksh.2⟩)

lemma supported_coprime_of_coprime_K
    (Ksh d m : PosNat) (hdSupport : HasPrimeSupportIn d Ksh)
    (hmK : Nat.Coprime m.1 Ksh.1) : Nat.Coprime d.1 m.1 := by
  rw [← Nat.disjoint_primeFactors d.2.ne' m.2.ne']
  exact Finset.disjoint_left.mpr fun p hpd hpm =>
    (Finset.disjoint_left.mp hmK.disjoint_primeFactors) hpm (hdSupport hpd)

lemma split_unique
    (Ksh : PosNat) {n d m : ℕ} (hn : 0 < n) (hd : 0 < d) (hm : 0 < m)
    (hnEq : n = d * m)
    (hdSupport : HasPrimeSupportIn ⟨d, hd⟩ Ksh)
    (hmK : Nat.Coprime m Ksh.1) :
    commonPart Ksh n = d ∧ awayPart Ksh n = m := by
  have hdm : Nat.Coprime d m :=
    supported_coprime_of_coprime_K Ksh ⟨d, hd⟩ ⟨m, hm⟩ hdSupport hmK
  have hperm : List.Perm n.primeFactorsList
      (d.primeFactorsList ++ m.primeFactorsList) := by
    rw [hnEq]
    exact Nat.perm_primeFactorsList_mul_of_coprime hdm
  have hdAll : ∀ p ∈ d.primeFactorsList, p ∈ Ksh.1.primeFactors := by
    intro p hp
    exact hdSupport (Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hp)
  have hmNone : ∀ p ∈ m.primeFactorsList, p ∉ Ksh.1.primeFactors := by
    intro p hp hpK
    have hpPrime := Nat.prime_of_mem_primeFactorsList hp
    have hpm : p ∣ m := Nat.dvd_of_mem_primeFactorsList hp
    have hpKdvd : p ∣ Ksh.1 := Nat.dvd_of_mem_primeFactors hpK
    have hpOne : p ∣ 1 := by
      rw [← hmK.gcd_eq_one]
      exact Nat.dvd_gcd hpm hpKdvd
    exact hpPrime.not_dvd_one hpOne
  constructor
  · unfold commonPart
    calc
      (n.primeFactorsList.filter fun p => p ∈ Ksh.1.primeFactors).prod =
          ((d.primeFactorsList ++ m.primeFactorsList).filter
            fun p => p ∈ Ksh.1.primeFactors).prod :=
        (hperm.filter _).prod_eq
      _ = d.primeFactorsList.prod := by
        rw [List.filter_append,
          List.filter_eq_self.mpr (fun p hp => by simp [hdAll p hp]),
          List.filter_eq_nil_iff.mpr (fun p hp => by simp [hmNone p hp])]
        simp
      _ = d := Nat.prod_primeFactorsList (Nat.ne_of_gt hd)
  · unfold awayPart
    calc
      (n.primeFactorsList.filter fun p => p ∉ Ksh.1.primeFactors).prod =
          ((d.primeFactorsList ++ m.primeFactorsList).filter
            fun p => p ∉ Ksh.1.primeFactors).prod :=
        (hperm.filter _).prod_eq
      _ = m.primeFactorsList.prod := by
        rw [List.filter_append,
          List.filter_eq_nil_iff.mpr (fun p hp => by simp [hdAll p hp]),
          List.filter_eq_self.mpr (fun p hp => by simp [hmNone p hp])]
        simp
      _ = m := Nat.prod_primeFactorsList (Nat.ne_of_gt hm)

end

end Erdos448.Stage7.ROOT01
