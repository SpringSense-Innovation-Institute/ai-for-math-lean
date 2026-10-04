module

public import LeanProject.ErdosProblems.P732.LowerBound

@[expose] public section

noncomputable section
open scoped Filter

/-- Alon's affirmative answer to Problem 1.2 (Erdős 732), with natural logarithm. -/
theorem ErdosProblems.P732.Palomar.erdos732_yes :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        Real.exp (c * Real.sqrt (n : ℝ) * Real.log (n : ℝ))
          ≤ (Set.ncard {xs : List ℕ | ErdosProblems.P732.BlockCompatibleSequence n xs} : ℝ) := by
  exact ErdosProblems.P732.erdos732_yes
