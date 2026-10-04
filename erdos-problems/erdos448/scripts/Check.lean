module

public import Solution

public section

open Filter Finset Set
open scoped Topology

example : ¬ (∀ epsilon : ℝ, 0 < epsilon →
    Tendsto (fun x : ℕ =>
      (Erdos448.Stage4.prefixCount (Erdos448.Stage4.strictEvent epsilon) x : ℝ) / x)
      atTop (nhds 1)) := Erdos448.negativeAnswer

#print axioms Erdos448.negativeAnswer
#print axioms Erdos448.WrapupFinal.negativeAnswer
