module

public import Erdos745.WrapUp.Exploration

@[expose] public section

/-!
Intermediate statements for finite enumeration, asymptotic estimates, Brownian
excursions and graph exploration. Proof modules establish these statements;
`Assembly.lean` combines them into the sparse evolution theorem.
-/
namespace Erdos745.WrapUp
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal
attribute [local instance] Classical.propDecidable
local instance : MeasurableSpace BrownianPath := borel BrownianPath

def noComplex {n : ℕ} (G : Graph n) : Prop :=
  ∀ S ∈ components G, edgesInside G S ≤ S.card

def cyclicAbove {n : ℕ} (G : Graph n) (h : ℝ) : Prop :=
  ∃ S ∈ components G, isUnicyclic G S ∧ h ≤ (S.card : ℝ)

def patternEvent {n : ℕ} (yes no : Graph n) (G : Graph n) : Prop :=
  yes ⊆ G ∧ Disjoint no G

def conditionalProbM (n M : ℕ) (H A : Graph n → Prop) : ℝ :=
  probM n M (fun G => H G ∧ A G) / probM n M H

def hypergeomMass (E R d y : ℕ) : ℝ :=
  if R ≤ E ∧ d ≤ E ∧ y ≤ d then
    (R.choose y : ℝ) * ((E - R).choose (d - y) : ℝ) / (E.choose d : ℝ)
  else 0

def growProb {n : ℕ} (G : Graph n) (t : ℕ) (A : Graph n → Prop) : ℝ :=
  let completions := (allGraphs n).filter (fun H => G ⊆ H ∧ H.card = G.card + t)
  ((completions.filter A).card : ℝ) / (completions.card : ℝ)

def rootedForestCount (k : ℕ) (roots : Finset (Fin k)) : ℕ :=
  ((allGraphs k).filter (fun G => ∀ S ∈ components G,
    isTree G S ∧ (S ∩ roots).card = 1)).card

def FiniteEnumerationStatement : Prop :=
  (∀ n M : ℕ, M ≤ capacity n → expectM n M (fun _ => 1) = 1) ∧
  (∀ (n M : ℕ) (yes no query : Graph n), M ≤ capacity n →
    Disjoint yes no → Disjoint query (yes ∪ no) →
    0 < probM n M (patternEvent yes no) → ∀ y : ℕ,
    conditionalProbM n M (patternEvent yes no) (fun G => (G ∩ query).card = y) =
      hypergeomMass (capacity n - yes.card - no.card) (M - yes.card) query.card y) ∧
  (∀ (n M t : ℕ) (A : Graph n → Prop), M + t ≤ capacity n →
    expectM n M (fun G => growProb G t A) = probM n (M + t) A) ∧
  (∀ (n : ℕ) (G query : Graph n) (t : ℕ), G.card + t ≤ capacity n →
    Disjoint G query →
    growProb G t (fun H => Disjoint H query) =
      ((capacity n - G.card - query.card).choose t : ℝ) /
        ((capacity n - G.card).choose t : ℝ) ∧
    growProb G t (fun H => Disjoint H query) ≤
      Real.exp (-(t : ℝ) * query.card / (capacity n : ℝ))) ∧
  (∀ n M k e : ℕ, M ≤ capacity n →
    expectM n M (fun G => (componentCount G k e : ℝ)) = componentFormula n M k e) ∧
  (∀ (n M q : ℕ) (ks : Fin q → ℕ), M ≤ capacity n →
    tupleMoment n M q ks = tupleFormula n M q ks) ∧
  (∀ n M q h : ℕ, M ≤ capacity n → 0 < h →
    expectM n M (fun G => (falling (treeCountGE G h) q : ℝ)) =
      ∑ ks : Fin q → Fin (n + 1),
        if ∀ i, h ≤ (ks i).val then tupleFormula n M q (fun i => (ks i).val) else 0) ∧
  (∀ (k : ℕ) (roots : Finset (Fin k)), rootedForestCount k roots =
    if roots.card = k then 1 else roots.card * k ^ (k - roots.card - 1)) ∧
  (∀ k : ℕ, 0 < k → connectedCount k (k - 1) = cayley k) ∧
  (∀ k : ℕ, 3 ≤ k → (connectedCount k k : ℝ) =
    ((k - 1).factorial : ℝ) / 2 *
      (Finset.range (k - 2)).sum (fun m =>
        (k : ℝ) ^ m / (m.factorial : ℝ))) ∧
  (∀ (n : ℕ) (G : Graph n) (i h : ℕ), 0 < i → 0 < h →
    (rankSize G i < h ↔ countGE G h ≤ i - 1)) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 3 ≤ k →
    (connectedCount k k : ℝ) ≤ C * Real.rpow (k : ℝ) ((k : ℝ) - 1 / 2)) ∧
  Tendsto (fun k : ℕ => (connectedCount k k : ℝ) /
    Real.rpow (k : ℝ) ((k : ℝ) - 1 / 2)) atTop (𝓝 (Real.sqrt (Real.pi / 8)))

def KernelBoundStatement : Prop :=
  ∃ A : ℝ, 1 < A ∧ ∀ k r : ℕ, 0 < k → 0 < r →
    (connectedCount k (k + r) : ℝ) ≤ A ^ r *
      Real.rpow (r : ℝ) (-(r : ℝ) / 2) *
      Real.rpow (k : ℝ) ((k : ℝ) + (3 * (r : ℝ) - 1) / 2)

def RateStatement : Prop :=
  (∀ x : ℝ, 0 < x → x ≠ 1 → 0 < rate x) ∧
  (∀ lam : ℝ, 1 < lam →
    0 < conjugate lam ∧ conjugate lam < 1 ∧
    conjugate lam * Real.exp (-conjugate lam) = lam * Real.exp (-lam) ∧
    rate (conjugate lam) = rate lam ∧
    ∀ y : ℝ, 0 < y → y < 1 → y * Real.exp (-y) = lam * Real.exp (-lam) →
      y = conjugate lam) ∧
  DifferentiableOn ℝ giantFraction (Set.Ioi 1) ∧
  ContinuousOn (deriv giantFraction) (Set.Ioi 1) ∧
  Tendsto (fun e : ℝ => deriv giantFraction (1 + e))
    (nhdsWithin 0 (Set.Ioi 0)) (𝓝 2) ∧
  ∃ C e0 : ℝ, 0 < C ∧ 0 < e0 ∧ e0 < 1 ∧
    ∀ e : ℝ, 0 < e → e < e0 →
      |rate (1 + e) - (e ^ 2 / 2 - e ^ 3 / 3)| ≤ C * e ^ 4 ∧
      |rate (1 - e) - (e ^ 2 / 2 + e ^ 3 / 3)| ≤ C * e ^ 4 ∧
      |conjugate (1 + e) - (1 - e + 2 * e ^ 2 / 3)| ≤ C * e ^ 3 ∧
      |giantFraction (1 + e) - (2 * e - 8 * e ^ 2 / 3)| ≤ C * e ^ 3

def treeLeading (n M k : ℕ) : ℝ :=
  if k = 0 then 0 else
    (n : ℝ) / degreeAt n M * (cayley k : ℝ) / (k.factorial : ℝ) *
      (degreeAt n M * Real.exp (-degreeAt n M)) ^ k

def tupleLeading (n M q : ℕ) (ks : Fin q → ℕ) : ℝ :=
  ∏ i, treeLeading n M (ks i)

def tupleGlobalBound (n M q : ℕ) (ks : Fin q → ℕ) (C kappa : ℝ) : Prop :=
  tupleMoment n M q ks ≤ C * (n : ℝ) ^ q *
    (∏ i, Real.rpow (ks i : ℝ) (-5 / 2 : ℝ)) *
    Real.exp (-kappa * ((degreeAt n M - 1) ^ 2 * (∑ i, (ks i : ℝ)) +
      (∑ i, (ks i : ℝ)) ^ 3 / (n : ℝ) ^ 2))

def tupleLocalBound (n M q : ℕ) (ks : Fin q → ℕ) (C : ℝ) : Prop :=
  let K : ℝ := ∑ i, (ks i : ℝ)
  0 < tupleMoment n M q ks ∧
  |Real.log (tupleMoment n M q ks / tupleLeading n M q ks)| ≤
    C * (K / n + |degreeAt n M - 1| * K ^ 2 / n + K ^ 3 / (n : ℝ) ^ 2)

def tupleTail (n M q power : ℕ) (B : ℝ) : ℝ :=
  ∑ ks : Fin q → Fin (n + 1),
    if (∀ i, 0 < (ks i).val) ∧ (∃ i, B * Real.log n < ((ks i).val : ℝ)) then
      (∏ i, (((ks i).val : ℝ) ^ power)) * tupleMoment n M q (fun i => (ks i).val)
    else 0

def TupleEstimatesStatement : Prop :=
  (∀ q : ℕ, 0 < q → ∃ C kappa : ℝ, 0 < C ∧ 0 < kappa ∧
    ∃ n0 : ℕ, ∀ (n M : ℕ) (ks : Fin q → ℕ), n0 ≤ n → M ≤ capacity n →
      1 / 2 ≤ degreeAt n M → degreeAt n M ≤ 3 / 2 → (∀ i, 0 < ks i) →
      tupleGlobalBound n M q ks C kappa ∧
      (((∑ i, (ks i : ℝ)) ≤ (n : ℝ) / 16) → tupleLocalBound n M q ks C)) ∧
  (∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, ∀ n M k l : ℕ,
    n0 ≤ n → M ≤ capacity n → 1 / 2 ≤ degreeAt n M → degreeAt n M ≤ 3 / 2 →
    0 < k → 0 < l → ((k + l : ℕ) : ℝ) ≤ (n : ℝ) / 16 →
      let pair : Fin 2 → ℕ := fun i => if i.val = 0 then k else l
      |Real.log (tupleMoment n M 2 pair /
        (tupleMoment n M 1 (fun _ => k) * tupleMoment n M 1 (fun _ => l)))| ≤
        C * (((k : ℝ) + l) / n + |degreeAt n M - 1| * k * l / n +
          (k : ℝ) * l * (k + l) / (n : ℝ) ^ 2)) ∧
  (∀ (lo hi B : ℝ) (q : ℕ), 0 < lo → lo ≤ hi → 0 < B → 0 < q →
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, ∀ (n M : ℕ) (ks : Fin q → ℕ),
      n0 ≤ n → M ≤ capacity n → lo ≤ degreeAt n M → degreeAt n M ≤ hi →
      (∀ i, 0 < ks i) → (∑ i, (ks i : ℝ)) ≤ B * Real.log n →
      0 < tupleMoment n M q ks ∧
      |Real.log (tupleMoment n M q ks / tupleLeading n M q ks)| ≤
        C * (∑ i, (ks i : ℝ)) ^ 2 / n) ∧
  (∀ (lo hi delta A : ℝ) (q power : ℕ), 0 < lo → lo ≤ hi → 0 < delta →
    0 < A → 0 < q → ∃ B : ℝ, 0 < B ∧ ∃ n0 : ℕ, ∀ n M : ℕ,
      n0 ≤ n → M ≤ capacity n → lo ≤ degreeAt n M → degreeAt n M ≤ hi →
      delta ≤ |degreeAt n M - 1| → tupleTail n M q power B ≤ Real.rpow (n : ℝ) (-A))

def rootedTerm (z : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else (k : ℝ) ^ (k - 1) * z ^ k / (k.factorial : ℝ)

def treeTail (a : ℝ) (h : ℕ) : ℝ :=
  ∑' k : ℕ, if h ≤ k ∧ 0 < k then
    Real.rpow (k : ℝ) (-5 / 2 : ℝ) * Real.exp (-a * k) else 0

def AnalyticSumsStatement : Prop :=
  (∀ lam : ℝ, 0 < lam → lam ≠ 1 →
    HasSum (rootedTerm (lam * Real.exp (-lam)))
      (if lam < 1 then lam else conjugate lam)) ∧
  (∀ beta : ℝ, -1 < beta → ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 0 < u → u ≤ 1 →
    Summable (fun k : ℕ => Real.rpow ((k + 1 : ℕ) : ℝ) beta *
      Real.exp (-u * (k + 1))) ∧
    (∑' k : ℕ, Real.rpow ((k + 1 : ℕ) : ℝ) beta * Real.exp (-u * (k + 1))) ≤
      C * Real.rpow u (-beta - 1)) ∧
  (∀ a : ℝ, 0 < a → Tendsto (fun h : ℕ => treeTail a h /
    (Real.rpow (h : ℝ) (-5 / 2 : ℝ) * Real.exp (-a * h) / (1 - Real.exp (-a))))
      atTop (𝓝 1)) ∧
  (∀ (aa Ls : RealSeq) (hs : NatSeq), (∀ᶠ n in atTop, 0 < aa n) →
    Tendsto aa atTop (𝓝 0) → Tendsto Ls atTop atTop →
    Tendsto (fun n => aa n * (hs n : ℝ) - Ls n) atTop (𝓝 0) →
    Tendsto (fun n => treeTail (aa n) (hs n) /
      (Real.rpow (aa n) (3 / 2 : ℝ) * Real.rpow (Ls n) (-5 / 2 : ℝ) * Real.exp (-Ls n)))
      atTop (𝓝 1))

def PoissonStatement : Prop :=
  (∀ (M : NatSeq) (X : (n : ℕ) → Graph n → ℕ) (nu : ℝ), admissible M → 0 ≤ nu →
    (∀ q : ℕ, 0 < q → Tendsto
      (fun n => expectM n (M n) (fun G => (falling (X n G) q : ℝ))) atTop (𝓝 (nu ^ q))) →
    ∀ j : ℕ, Tendsto (fun n => probM n (M n) (fun G => X n G ≤ j))
      atTop (𝓝 (poissonCDF nu j))) ∧
  (∀ (M : NatSeq) (lam : ℝ), admissible M → 0 < lam → lam ≠ 1 →
    Tendsto (degree M) atTop (𝓝 lam) → ∀ (ns h : NatSeq) (ell : ℝ), StrictMono ns →
    Tendsto (fun j => (h j : ℝ) - center M (ns j)) atTop (𝓝 ell) →
    ∀ q : ℕ, Tendsto (fun j => countCDF (ns j) (M (ns j)) (h j) q)
      atTop (𝓝 (poissonCDF (latticeRate lam ell) q))) ∧
  (∀ M : NatSeq, bareSub M ∨ bareSuper M → ∀ (r : ℝ) (q : ℕ),
    Tendsto (fun n => countCDF n (M n) ⌈nearThreshold M n r⌉₊ q)
      atTop (𝓝 (poissonCDF (nearRate r) q)))

def unicyclicLimit (lam : ℝ) : ℝ :=
  ∑' k : ℕ, if 3 ≤ k then
    (lam * Real.exp (-lam)) ^ k / 2 *
      (Finset.range (k - 2)).sum (fun m =>
        (k : ℝ) ^ m / (m.factorial : ℝ)) else 0

def SubcriticalExclusionStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n M : ℕ) (e : ℝ), 2 ≤ n → M ≤ capacity n →
    0 < e → 4 / (n : ℝ) ≤ e → degreeAt n M ≤ 1 - e →
    probM n M (fun G => ¬ noComplex G) ≤ C / ((n : ℝ) * e ^ 3)

def CyclicStructureStatement : Prop :=
  (∀ M : NatSeq, bareSub M ∨ bareSuper M →
    boundedBy (fun n => expectM n (M n) unicyclicMass) (fun n => (epsilon M n)⁻¹ ^ 2) ∧
    boundedBy (fun n => expectM n (M n) (fun G => (smallComplexCount G (largeCutoff n) : ℝ)))
      (fun n => (widthParameter M n)⁻¹) ∧
    ∀ r : ℝ, Tendsto (fun n => probM n (M n) (fun G => cyclicAbove G (nearThreshold M n r)))
      atTop (𝓝 0)) ∧
  (∀ (M : NatSeq) (lam : ℝ), admissible M → 0 < lam → lam ≠ 1 →
    Tendsto (degree M) atTop (𝓝 lam) →
    0 ≤ unicyclicLimit lam ∧
    Tendsto (fun n => expectM n (M n) unicyclicMass) atTop (𝓝 (unicyclicLimit lam)) ∧
    boundedBy (fun n => expectM n (M n) (fun G => (smallComplexCount G (largeCutoff n) : ℝ)))
      (fun n => (n : ℝ)⁻¹) ∧
    ∀ (ns h : NatSeq) (ell : ℝ), StrictMono ns →
    Tendsto (fun j => (h j : ℝ) - center M (ns j)) atTop (𝓝 ell) →
    Tendsto (fun j => probM (ns j) (M (ns j)) (fun G => cyclicAbove G (h j))) atTop (𝓝 0))

def treeMeanError (M : NatSeq) (n : ℕ) : ℝ :=
  expectM n (M n) (fun G => treeMassBelow G (largeCutoff n)) -
    (n : ℝ) * conjugate (degree M n) / degree M n

def TreeMassStatement : Prop :=
  (∀ M : NatSeq, bareSuper M →
    boundedBy (treeMeanError M) (fun n => (epsilon M n)⁻¹ ^ 2) ∧
    boundedBy (fun n => varianceM n (M n) (fun G => treeMassBelow G (largeCutoff n)))
      (fun n => (n : ℝ) / epsilon M n)) ∧
  (∀ (M : NatSeq) (lam : ℝ), admissible M → 1 < lam →
    Tendsto (degree M) atTop (𝓝 lam) →
    boundedBy (treeMeanError M) (fun _ => 1) ∧
    boundedBy (fun n => varianceM n (M n) (fun G => treeMassBelow G (largeCutoff n)))
      (fun n => (n : ℝ)))

def GiantStatement : Prop :=
  (∀ M : NatSeq, bareSuper M →
    tightScaled M (fun n G => largeMass G (largeCutoff n)) (giantCenter M)
      (fun n => Real.sqrt ((n : ℝ) / epsilon M n)) ∧
    tightScaled M (fun _ G => (rankSize G 1 : ℝ)) (giantCenter M)
      (fun n => Real.sqrt ((n : ℝ) / epsilon M n)) ∧
    Tendsto (fun n => probM n (M n) separatedStructure) atTop (𝓝 1)) ∧
  (∀ (M : NatSeq) (lam : ℝ), admissible M → 1 < lam →
    Tendsto (degree M) atTop (𝓝 lam) →
    tightScaled M (fun n G => largeMass G (largeCutoff n)) (giantCenter M)
      (fun n => Real.sqrt (n : ℝ)) ∧
    tightScaled M (fun _ G => (rankSize G 1 : ℝ)) (giantCenter M)
      (fun n => Real.sqrt (n : ℝ)) ∧
    Tendsto (fun n => probM n (M n) separatedStructure) atTop (𝓝 1))

def FixedAtlasStatement : Prop := fixedSubcriticalLaw ∧ fixedSupercriticalLaw


def RequiredNearAtlasStatement : Prop :=
  barelySubcriticalLaw ∧ barelySupercriticalLaw


def BrownianFoundationStatement : Prop :=
  (∃! mu : PathLaw, BrownianLaw mu) ∧
  ∀ mu : PathLaw, BrownianLaw mu → ∀ lam : ℝ,
    (∀ᵐ w ∂mu, GoodExcursionPath w lam) ∧
    ∀ i : ℕ, 0 < i → Measurable (fun w => excursionRankExtended w lam i) ∧
      ∀ᵐ w ∂mu, 0 < excursionRankExtended w lam i ∧ excursionRankExtended w lam i < ⊤

def ExplorationStatement : Prop :=
  ∃ Phi : ExplorationPaths, IsInterpolation Phi ∧
    ∀ (M : NatSeq) (lam : ℝ) (mu : PathLaw),
      criticalWindow M lam → BrownianLaw mu →
      WeakExploration M Phi lam mu ∧ ExplorationTails M lam

def CriticalStatement : Prop := criticalLaw


end
end Erdos745.WrapUp
