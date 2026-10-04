module

public import Erdos745.WrapUp.Proofs.W01_ENUM
public import Erdos745.WrapUp.Proofs.W02_KERNEL
public import Erdos745.WrapUp.Proofs.W03_RATE
public import Erdos745.WrapUp.Proofs.W04_TUPLES
public import Erdos745.WrapUp.Proofs.W05_SUMS
public import Erdos745.WrapUp.Proofs.W06_POISSON
public import Erdos745.WrapUp.Proofs.W07_SUBCRIT
public import Erdos745.WrapUp.Proofs.W08_CYCLIC
public import Erdos745.WrapUp.Proofs.W09_TREE_MASS
public import Erdos745.WrapUp.Proofs.W10_GIANT
public import Erdos745.WrapUp.Proofs.W11_FIXED
public import Erdos745.WrapUp.Proofs.W12_NEAR
public import Erdos745.WrapUp.Proofs.W13_BROWNIAN
public import Erdos745.WrapUp.Proofs.W14_EXPLORATION
public import Erdos745.WrapUp.Proofs.W15_CRITICAL

@[expose] public section

namespace Erdos745.WrapUp

/-- Combine the fixed-density, near-critical and critical laws. -/
theorem assembleAtlas (hfixed : FixedAtlasStatement) (hnear : RequiredNearAtlasStatement)
    (hcritical : CriticalStatement) : AtlasStatement := by
  -- Preserve the uniform witness before introducing any edge-sequence quantifier.
  exact ⟨hfixed.1, hfixed.2, hnear.1, ⟨hnear.2.1, hnear.2.2⟩, hcritical⟩

/-- Assemble the fixed-density and near-critical laws from their common inputs. -/
theorem fixedNearAtlas : FixedAtlasStatement ∧ RequiredNearAtlasStatement := by
  have hF : FiniteEnumerationStatement := Proofs.W01_ENUM.result
  have hR : RateStatement := Proofs.W03_RATE.result
  have hK : KernelBoundStatement := Proofs.W02_KERNEL.result hF
  have hT : TupleEstimatesStatement := Proofs.W04_TUPLES.result hF hR
  have hA : AnalyticSumsStatement := Proofs.W05_SUMS.result hF hR
  have hP : PoissonStatement := Proofs.W06_POISSON.result hF hR hT hA
  have hS : SubcriticalExclusionStatement := Proofs.W07_SUBCRIT.result hF hA
  have hC : CyclicStructureStatement := Proofs.W08_CYCLIC.result hF hK hR hT hA
  have hTree : TreeMassStatement := Proofs.W09_TREE_MASS.result hF hR hT hA
  have hG : GiantStatement := Proofs.W10_GIANT.result hF hR hT hA hC hTree
  exact ⟨Proofs.W11_FIXED.result hF hR hP hS hC hG,
    Proofs.W12_NEAR.result hF hR hP hS hC hG⟩

/-- Assemble the atlas from a critical-regime law. -/
theorem atlasOfCritical (hcritical : CriticalStatement) : AtlasStatement :=
  assembleAtlas fixedNearAtlas.1 fixedNearAtlas.2 hcritical

/-- Assemble the atlas from the graph exploration limit. -/
theorem atlasOfExploration (hExploration : ExplorationStatement) : AtlasStatement :=
  atlasOfCritical (Proofs.W15_CRITICAL.result Proofs.W13_BROWNIAN.result hExploration)

/-- The five-regime sparse evolution theorem. -/
theorem atlas : AtlasStatement :=
  atlasOfExploration
    (Proofs.W14_EXPLORATION.result Proofs.W01_ENUM.result Proofs.W13_BROWNIAN.result)

end Erdos745.WrapUp
