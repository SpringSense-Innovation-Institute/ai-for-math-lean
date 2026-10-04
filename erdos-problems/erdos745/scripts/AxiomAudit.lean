module

public import Solution

example : Erdos745.WrapUp.AtlasStatement := Erdos745.Palomar.sparseEvolution

open Filter
open Erdos745.WrapUp

-- The selected Palomar theorem itself exposes the absolute constant before M.
example : ∃ C : ℝ, 0 < C ∧ ∀ M : NatSeq, bareSuper M →
    ∀ᶠ n in atTop, |giantCenter M n - 4 * displacement M n| ≤
      C * (displacement M n ^ 2 / n) :=
  Erdos745.Palomar.sparseEvolution.2.2.2.1.1

-- The existing estimate uses the same explicit witness 12 for all sequences.
example : ∀ M : NatSeq, bareSuper M →
    ∀ᶠ n in atTop, |giantCenter M n - 4 * displacement M n| ≤
      (12 : ℝ) * (displacement M n ^ 2 / n) := by
  intro M hbare
  exact Proofs.Internal.W12_NEAR_Laws.super_center_bound Proofs.W03_RATE.result hbare

#print axioms Erdos745.WrapUp.Proofs.W12_NEAR.uniformCenterBound
#print axioms Erdos745.WrapUp.Proofs.Internal.W12_NEAR_Laws.super_center_bound
#print axioms Erdos745.WrapUp.Proofs.Internal.W12_NEAR_Laws.uniform_super_center_bound

#print axioms Erdos745.Palomar.sparseEvolution
#print axioms Erdos745.WrapUp.atlas
#print axioms Erdos745.WrapUp.Proofs.W01_ENUM.result
#print axioms Erdos745.WrapUp.Proofs.W02_KERNEL.result
#print axioms Erdos745.WrapUp.Proofs.W03_RATE.result
#print axioms Erdos745.WrapUp.Proofs.W04_TUPLES.result
#print axioms Erdos745.WrapUp.Proofs.W05_SUMS.result
#print axioms Erdos745.WrapUp.Proofs.W06_POISSON.result
#print axioms Erdos745.WrapUp.Proofs.W07_SUBCRIT.result
#print axioms Erdos745.WrapUp.Proofs.W08_CYCLIC.result
#print axioms Erdos745.WrapUp.Proofs.W09_TREE_MASS.result
#print axioms Erdos745.WrapUp.Proofs.W10_GIANT.result
#print axioms Erdos745.WrapUp.Proofs.W11_FIXED.result
#print axioms Erdos745.WrapUp.Proofs.W12_NEAR.result
#print axioms Erdos745.WrapUp.Proofs.W13_BROWNIAN.result
#print axioms Erdos745.WrapUp.Proofs.W14_EXPLORATION.result
#print axioms Erdos745.WrapUp.Proofs.W15_CRITICAL.result
