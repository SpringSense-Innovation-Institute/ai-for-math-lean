module

public import Erdos448.stage8.Integration

public section

/-- The strict small-divisor-ratio assertion does not hold for every epsilon. -/
theorem Erdos448.negativeAnswer : Erdos448.Stage4.NegativeAnswer := by
  exact Erdos448.WrapupFinal.negativeAnswer
