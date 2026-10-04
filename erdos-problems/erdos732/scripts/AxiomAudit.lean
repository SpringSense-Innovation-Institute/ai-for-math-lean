module

public import Solution

open scoped Filter

example : ∃ c : ℝ, 0 < c ∧
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.exp (c * Real.sqrt (n : ℝ) * Real.log (n : ℝ))
        ≤ (Set.ncard {xs : List ℕ | ErdosProblems.P732.BlockCompatibleSequence n xs} : ℝ) :=
  ErdosProblems.P732.Palomar.erdos732_yes

#print axioms ErdosProblems.P732.Palomar.erdos732_yes
#print axioms ErdosProblems.P732.erdos732_yes
#print axioms ErdosProblems.P732.alon_exact_lower_bound_primePower
#print axioms ErdosProblems.P732.projectivePlane_of_primePower
