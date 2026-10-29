module

public import ASDExplicitGamma.Native.OldSignedCovarianceProductIntegral
public import ASDExplicitGamma.Scalar.FlatSourceC1Multiplier
public import ASDExplicitGamma.Triadic.HilbertHaarBasic

/-! Complete-Hilbert row testing with genuine Sobolev membership. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
noncomputable section

/-- A continuous Hilbert coefficient is essentially bounded on the actual
bounded parent domain, in its physical volume measure. -/
theorem parent_boundary_continuous_memLp_top_open {E : Type*}
    [NormedAddCommGroup E] (Q : TriadicCube 2) (b : Vec 2 → E) (hb : Continuous b) :
    MemLp b ⊤ (volume.restrict (openCubeSet Q)) := by
  let parentBoundaryRowFiniteOpenMeasure : IsFiniteMeasure (volume.restrict (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hU := isOpenBoundedConvexDomain_openCubeSet Q
  obtain ⟨C,hC⟩ := hU.isBoundedDomain.isBounded.isCompact_closure.exists_bound_of_continuousOn hb.continuousOn
  apply MemLp.of_bound hb.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem (isOpen_openCubeSet Q).measurableSet] with x hx
  exact hC x (subset_closure hx)

/-- Actual L∞ rows acting on actual L2 fields admit complete mode testing
against every L2 scalar test. No product-norm estimate is a premise. -/
theorem parent_boundary_bounded_row_test {X E I : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Countable I]
    (mu : Measure X) (e : HilbertBasis I ℝ E) (A B : X → E) (r : X → ℝ)
    (hA : MemLp A ⊤ mu) (hB : MemLp B 2 mu) (hr : MemLp r 2 mu) :
    HasSum (fun n => ∫ x,r x*inner ℝ (e n) (A x)*inner ℝ (e n) (B x) ∂mu)
      (∫ x,r x*inner ℝ (A x) (B x) ∂mu) := by
  have hprod : MemLp (fun x => ‖A x‖*‖B x‖) 2 mu := hA.norm.mul hB.norm
  have hi : Integrable (fun x => |r x| *‖A x‖*‖B x‖) mu := by
    have hh := hr.norm.integrable_mul hprod
    change Integrable (fun x => ‖r x‖ * (‖A x‖*‖B x‖)) mu at hh
    simpa only [Real.norm_eq_abs,mul_assoc] using hh
  exact old_signed_weighted_white_covariance_product mu e A B r
    hA.aestronglyMeasurable hB.aestronglyMeasurable hr.aestronglyMeasurable hi

/-- A scalar coordinate of a genuine C1 Hilbert row is genuinely C1. -/
theorem parent_boundary_row_coordinate_contDiff {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : Vec 2 → E) (hb : ContDiff ℝ 1 b) (z : E) :
    ContDiff ℝ 1 (fun x => inner ℝ z (b x)) :=
  (innerSL ℝ z).contDiff.comp hb

/-- Its derivative is the coordinate of the actual Hilbert row derivative. -/
theorem parent_boundary_row_coordinate_derivative {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : Vec 2 → E) (hb : ContDiff ℝ 1 b) (z : E) (x : Vec 2) (i : Fin 2) :
    (fderiv ℝ (fun y => inner ℝ z (b y)) x) (basisVec i) =
      inner ℝ z ((fderiv ℝ b x) (basisVec i)) := by
  have hh := (innerSL ℝ z).hasFDerivAt.comp x
    ((hb.differentiable (by norm_num)).differentiableAt.hasFDerivAt)
  change (fderiv ℝ ((innerSL ℝ z) ∘ b) x) (basisVec i)=_
  rw [hh.fderiv]
  rfl

end
end ASDExplicitGamma.Native
