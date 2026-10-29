module

public import ASDExplicitGamma.Native.OldSignedCoarseDirectionalMean

/-! Integrability of the actual fixed-frame directional and trace
observables on every source cell under the partial-insertion law. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Main Algsuperdiff.Section3
noncomputable section

/-- Every directional majorant entry is integrable for each actual cell. -/
theorem old_signed_coarse_directional_entry_integrable (M : ABKModel 2) (m : ℤ)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (Q : TriadicCube 2) (sigma : ℝ) (i j : Fin 2) :
    Integrable (fun a => oldSignedCoarseDirectionalMatrix Q a.toFun sigma i j)
      (mainInsertionCoefficientLaw M m t) := by
  let μ := mainInsertionCoefficientLaw M m t
  let oldSignedEntryProbability : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff
      (mainInsertion_partialInsertedCoefficient_measurable M m t).aemeasurable).2 inferInstance
  have hK := mainInsertionCoefficientLaw_integrable_blockMatEntry M m t ht Q (.inl i) (.inl j)
  have hD := mainInsertionCoefficientLaw_integrable_blockMatEntry M m t ht Q (.inr i) (.inr j)
  have hh := ((hK.const_mul sigma⁻¹).add (hD.const_mul sigma)).sub
    (integrable_const (2*(1 : Mat 2) i j) : Integrable (fun _ : RegCoeffField 2 => 2*(1 : Mat 2) i j) μ)
  simpa only [oldSignedCoarseDirectionalMatrix,blockMatEntry,Matrix.add_apply,Matrix.sub_apply,
    Matrix.smul_apply,smul_eq_mul,Pi.add_def,Pi.sub_def] using hh

/-- The actual directional quadratic form is integrable. -/
theorem old_signed_coarse_directional_integrable (M : ABKModel 2) (m : ℤ)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (Q : TriadicCube 2) (sigma : ℝ) (e : Vec 2) :
    Integrable (fun a => vecDot e (matVecMul (oldSignedCoarseDirectionalMatrix Q a.toFun sigma) e))
      (mainInsertionCoefficientLaw M m t) :=
  old_signed_quadratic_integrable _ _ (old_signed_coarse_directional_entry_integrable M m t ht Q sigma) e

/-- The fixed-frame four-load trace is exactly the directional matrix trace. -/
theorem old_signed_coarse_directional_trace (Q : TriadicCube 2) (a : CoeffField 2) (sigma : ℝ) :
    Matrix.trace (oldSignedCoarseDirectionalMatrix Q a sigma)=traceDefect (cubeSet Q) a sigma := by
  simp [oldSignedCoarseDirectionalMatrix,traceDefect,Matrix.trace_fin_two]
  ring

/-- The actual trace used by the expected half-trace identity is integrable. -/
theorem old_signed_coarse_trace_integrable (M : ABKModel 2) (m : ℤ)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (Q : TriadicCube 2) (sigma : ℝ) :
    Integrable (fun a => traceDefect (cubeSet Q) a.toFun sigma)
      (mainInsertionCoefficientLaw M m t) := by
  have hh := (old_signed_coarse_directional_entry_integrable M m t ht Q sigma 0 0).add
    (old_signed_coarse_directional_entry_integrable M m t ht Q sigma 1 1)
  simpa only [← old_signed_coarse_directional_trace,Matrix.trace_fin_two,Pi.add_def] using hh

end
end ASDExplicitGamma.Native
