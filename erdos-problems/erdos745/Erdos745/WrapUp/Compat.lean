module

public import Mathlib

public section

/-- The legacy measurable-map probability instance, now supplied automatically by Mathlib. -/
theorem MeasureTheory.Measure.isProbabilityMeasure_map
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    {f : α → β} (_hf : AEMeasurable f μ) :
    MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.map f μ) := by
  infer_instance

/-- Continuity through Mathlib's explicit constructor for nonnegative reals. -/
@[fun_prop] theorem Erdos745.WrapUp.continuousNNRealMk
    {α : Type*} [TopologicalSpace α] (f : α → ℝ) (h : ∀ x, 0 ≤ f x)
    (hf : Continuous f) : Continuous (fun x => NNReal.mk (f x) (h x)) := by
  simpa only [NNReal.mk] using! hf.subtype_mk h
