-- Ported from GMCExplicitDelta Proofs/ProjPoincare/Geometry.lean (Apache-2.0).
module

public import ASDExplicitGamma.Triadic.Support.Localization.HaarDefs
public import ASDExplicitGamma.Triadic.Support.Contract.DerivedGeometry
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import ASDExplicitGamma.Triadic.Support.ProjectedPoincare.Scalar
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Coordinate slicing and integrability on triadic cubes. -/
@[expose] public section

open Homogenization MeasureTheory Set
open scoped ENNReal

namespace ASDExplicitGamma.Triadic.Support.ProjectedPoincare

variable {d n : ℕ}

theorem continuous_memLp_cube (Q : TriadicCube d) {f : Homogenization.Vec d → ℝ}
    (hf : Continuous f) (p : ℝ≥0∞) : MemLp f p (normalizedCubeMeasure Q) := by
  obtain ⟨C, hC⟩ := (isBounded_cubeSet Q).isCompact_closure.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  unfold normalizedCubeMeasure cubeMeasure
  apply Measure.ae_smul_measure
  apply (ae_restrict_iff' (measurableSet_cubeSet Q)).mpr
  exact Filter.Eventually.of_forall (fun x hx => hC x (subset_closure hx))

/-- Averaging over the remaining coordinates contracts the squared norm. -/
theorem cubeAverage_sq_le (Q : TriadicCube d) {f : Homogenization.Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    (cubeAverage Q f) ^ 2 ≤ cubeAverage Q (fun x => f x ^ 2) := by
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
  simpa [Measure.real, normalizedCubeMeasure_apply_univ] using
    integral_mul_sq_le hf (memLp_const (1 : ℝ))

end ASDExplicitGamma.Triadic.Support.ProjectedPoincare
