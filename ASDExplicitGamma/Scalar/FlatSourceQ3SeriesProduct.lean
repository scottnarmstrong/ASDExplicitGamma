module

public import ASDExplicitGamma.Scalar.FlatSourceQ3SpatialWick
public import ASDExplicitGamma.Scalar.FlatSourceProductFatou
public import ASDExplicitGamma.Gaussian.H3SeriesCompletion
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! Pathwise L² convergence of the actual q3 scalar-times-projected-load product. -/

@[expose] public section

open MeasureTheory Filter Homogenization Set
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped ENNReal Topology

namespace ASDExplicitGamma.Scalar

local instance flatSourceProductOpenCubeFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

theorem flat_source_clamp_continuous (a b c d : ℝ)
    (hab : a < b) (hcd : c < d) :
    Continuous (lambda8CovarianceClamp a b c d hab hcd) := by
  exact Continuous.subtype_mk (by
    change Continuous (fun x : Vec 2 => fun i =>
      if i = 0 then max a (min (x i) b) else max c (min (x i) d))
    exact continuous_pi fun i => by
      fin_cases i
      · simpa using continuous_const.max ((continuous_apply 0).min continuous_const)
      · simpa using continuous_const.max ((continuous_apply 1).min continuous_const))
    (fun x => by
      change max a (min (x 0) b) ∈ Icc a b ∧
        max c (min (x 1) d) ∈ Icc c d
      exact ⟨⟨le_max_left _ _, max_le_iff.mpr ⟨hab.le, min_le_right _ _⟩⟩,
        ⟨le_max_left _ _, max_le_iff.mpr ⟨hcd.le, min_le_right _ _⟩⟩⟩)

/-- The actual scalar q3 field, restricted to the parent square and viewed in
L∞, is a continuous linear image of the source H³ realization. -/
noncomputable def flatSourceQ3ValueLInf
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (β : ℝ) (L : {l : ℝ // 0 < l}) :
    Q3H3Range a₀ b₀ c₀ d₀ β L →L[ℝ]
      Lp ℝ ∞ (volumeMeasureOn (openCubeSet Q)) := by
  let clamp : C(Vec 2, closedRectangle a₀ b₀ c₀ d₀) :=
    ⟨lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd,
      flat_source_clamp_continuous a₀ b₀ c₀ d₀ hab hcd⟩
  let h3ToBounded : C(closedRectangle a₀ b₀ c₀ d₀, ℝ) →L[ℝ]
      BoundedContinuousFunction (closedRectangle a₀ b₀ c₀ d₀) ℝ :=
    (ContinuousMap.linearIsometryBoundedOfCompact
      (closedRectangle a₀ b₀ c₀ d₀) ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  exact (BoundedContinuousFunction.toLp (∞ : ℝ≥0∞)
      (volumeMeasureOn (openCubeSet Q)) ℝ).comp
    ((BoundedContinuousFunction.compContinuousCLM ℝ ℝ clamp).comp
      (h3ToBounded.comp (q3H3RangeValue a₀ b₀ c₀ d₀ β L)))

/-- The actual local Dirichlet-projected q3 load is a continuous linear image
of the same H³ realization, with values in the physical vector L² space. -/
noncomputable def flatSourceQ3ProjectedL2
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀) (e : Vec 2)
    (β : ℝ) (L : {l : ℝ // 0 < l}) :
    Q3H3Range a₀ b₀ c₀ d₀ β L →L[ℝ] HilbertVectorL2 (openCubeSet Q) :=
  lambda8Q3ProjectedLoad (isOpenBoundedConvexDomain_openCubeSet Q)
    a₀ b₀ c₀ d₀ hab hcd e β L

/-- Along the source's almost-sure H³ convergence, the finite-mode scalar
field times the corresponding projected vector field converges in spatial
L² to the fixed physical representative. The two factors use the same
Gaussian partial sum, so no independence premise is involved. -/
theorem flat_source_q3_fixed_product_tendsto
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀) (e : Vec 2)
    (β : ℝ) (L : {l : ℝ // 0 < l}) :
    ∀ᵐ ω ∂standardGaussianInfinitePi,
      Tendsto
        (fun N => flatSourceQ3ValueLInf Q hab hcd β L
            (gaussianPartialSum
              (q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis) N ω) •
          flatSourceQ3ProjectedL2 Q hab hcd e β L
            (gaussianPartialSum
              (q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis) N ω))
        atTop
        (𝓝 (flatSourceQ3ValueLInf Q hab hcd β L
              (q3H3Series a₀ b₀ c₀ d₀ β L whiteBasis ω) •
            flatSourceQ3ProjectedL2 Q hab hcd e β L
              (q3H3Series a₀ b₀ c₀ d₀ β L whiteBasis ω))) := by
  filter_upwards [ae_tendsto_q3H3Series_full a₀ b₀ c₀ d₀ β L whiteBasis]
    with ω hω
  apply lp_product_tendsto_of_tendsto
    (volumeMeasureOn (openCubeSet Q))
  · exact (flatSourceQ3ValueLInf Q hab hcd β L).continuous.tendsto _ |>.comp hω.1
  · exact (flatSourceQ3ProjectedL2 Q hab hcd e β L).continuous.tendsto _ |>.comp hω.1

end ASDExplicitGamma.Scalar
