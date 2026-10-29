module

public import ASDExplicitGamma.Gaussian.Q3RemainderCameronMartin
public import ASDExplicitGamma.Gaussian.HilbertBasisVariance
public import ASDExplicitGamma.Gaussian.BasisIndependence
public import ASDExplicitGamma.Gaussian.BilinearCovariance
public import ASDExplicitGamma.Gaussian.SeriesLawVariance

/-! # Genuine remainder Cameron–Martin bases give the same auxiliary Gaussian law -/

@[expose] public section

open MeasureTheory Homogenization Set Filter
open scoped Topology RealInnerProductSpace ENNReal

namespace ASDExplicitGamma.Gaussian

section
variable (a b c d β : ℝ) (L : {l : ℝ // 0 < l}) (x₀ : closedRectangle a b c d)

noncomputable def q3RemainderRangeValue :
    Q3H3Range a b c d β L →L[ℝ] C(closedRectangle a b c d, ℝ) :=
  (centeringMap x₀).comp (q3H3RangeValue a b c d β L)

variable {ι : Type*} [Countable ι]
  (e : HilbertBasis ι ℝ (Q3RemainderCameronMartin a b c d β L x₀))

/-- Use a genuine covariance-Hilbert basis while keeping the proved ordinary Sobolev
Hilbert carrier for stochastic convergence. -/
noncomputable def q3CameronMartinDirections : ℕ → Q3H3Range a b c d β L :=
  gaussEnumerated (fun j => q3H3RangeFactor a b c d β L (e j : WhiteNoise))

theorem q3CameronMartinDirections_summable :
    Summable (fun j => ‖q3CameronMartinDirections a b c d β L x₀ e j‖ ^ 2) :=
  enumerated_summable_sq _ (q3H3RangeFactor_summable a b c d β L _
    (cameronMartin_orthonormal _ e e.orthonormal))

noncomputable def q3CameronMartinSeries : (ℕ → ℝ) → Q3H3Range a b c d β L :=
  @gaussianSeriesLimit (Q3H3Range a b c d β L) inferInstance
    (instQ3H3RangeInnerProductSpace a b c d β L) inferInstance inferInstance inferInstance inferInstance
    inferInstance (q3CameronMartinDirections a b c d β L x₀ e)
    (q3CameronMartinDirections_summable a b c d β L x₀ e)

/-- In particular every derivative observation has the same bracket in a genuine CM basis. -/
theorem q3RemainderCameronMartin_variance (hab : a < b) (hcd : c < d)
    (A : C(closedRectangle a b c d, ℝ) →L[ℝ] ℝ) :
    (∑' j, (A (q3RemainderRangeValue a b c d β L x₀
      (q3CameronMartinDirections a b c d β L x₀ e j))) ^ 2) =
    ∑' j, (A (q3RemainderRangeValue a b c d β L x₀
      (q3H3Directions a b c d β L whiteBasis j))) ^ 2 := by
  let T := q3RemainderRangeValue a b c d β L x₀
  change (∑' j, (A (T (gaussEnumerated (fun i => q3H3RangeFactor a b c d β L (e i : WhiteNoise)) j))) ^ 2) =
    ∑' j, (A (T (gaussEnumerated (fun i => q3H3RangeFactor a b c d β L (whiteBasis i)) j))) ^ 2
  rw [enumerated_tsum_apply _ (fun z => (A (T z)) ^ 2) (by simp),
    enumerated_tsum_apply _ (fun z => (A (T z)) ^ 2) (by simp)]
  let l := A.comp (q3RemainderValueFactor a b c d β L x₀)
  change (∑' j, (l (e j : WhiteNoise)) ^ 2) = ∑' j, (l (whiteBasis j)) ^ 2
  rw [cameronMartin_basis_variance (q3RemainderH3Factor a b c d β L x₀) e l,
    hilbertBasis_variance whiteBasis l]
  intro u hu
  change A (q3RemainderValueFactor a b c d β L x₀ u) = 0
  rw [(q3RemainderFactor_kernel a b c d β L x₀ hab hcd u).mp hu, map_zero]

/-- A genuine Cameron–Martin basis and the original factorization have the same value law. -/
theorem q3RemainderCameronMartin_series_law (hab : a < b) (hcd : c < d) :
    standardGaussianInfinitePi.map (fun ω => q3RemainderRangeValue a b c d β L x₀
      (q3CameronMartinSeries a b c d β L x₀ e ω)) =
    standardGaussianInfinitePi.map (fun ω => q3RemainderRangeValue a b c d β L x₀
      (q3H3Series a b c d β L whiteBasis ω)) := by
  apply @seriesLaw_eq_of_variance (Q3H3Range a b c d β L) (closedRectangle a b c d)
    inferInstance (instQ3H3RangeInnerProductSpace a b c d β L) inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (q3CameronMartinDirections a b c d β L x₀ e) (q3H3Directions a b c d β L whiteBasis)
    (q3CameronMartinDirections_summable a b c d β L x₀ e)
    (q3H3Directions_summable a b c d β L whiteBasis) (q3RemainderRangeValue a b c d β L x₀)
  exact q3RemainderCameronMartin_variance a b c d β L x₀ e hab hcd

/-- Every bounded bilinear trace, in particular every Hessian at an actual coefficient,
is unchanged when the covariance factor is replaced by a genuine full CM basis. -/
theorem q3RemainderCameronMartin_bilinear_trace (hab : a < b) (hcd : c < d)
    (B : C(closedRectangle a b c d, ℝ) →L[ℝ] C(closedRectangle a b c d, ℝ) →L[ℝ] ℝ) :
    (∑' j, B (q3RemainderRangeValue a b c d β L x₀ (q3CameronMartinDirections a b c d β L x₀ e j))
      (q3RemainderRangeValue a b c d β L x₀ (q3CameronMartinDirections a b c d β L x₀ e j))) =
    ∑' j, B (q3RemainderRangeValue a b c d β L x₀ (q3H3Directions a b c d β L whiteBasis j))
      (q3RemainderRangeValue a b c d β L x₀ (q3H3Directions a b c d β L whiteBasis j)) := by
  exact @bilinearTrace_eq_of_law (Q3H3Range a b c d β L) (Q3H3Range a b c d β L)
    C(closedRectangle a b c d, ℝ)
    inferInstance (instQ3H3RangeInnerProductSpace a b c d β L) inferInstance inferInstance inferInstance inferInstance
    inferInstance (instQ3H3RangeInnerProductSpace a b c d β L) inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    _ (q3CameronMartinDirections_summable a b c d β L x₀ e) (q3RemainderRangeValue a b c d β L x₀)
    _ (q3H3Directions_summable a b c d β L whiteBasis) (q3RemainderRangeValue a b c d β L x₀)
    (q3RemainderCameronMartin_series_law a b c d β L x₀ e hab hcd) B

/-- The source remainder generator and bracket agree for every genuine full CM basis
and the original working covariance factorization. -/
theorem q3RemainderCameronMartin_generator_and_bracket (hab : a < b) (hcd : c < d)
    (Φ : C(closedRectangle a b c d, ℝ) → ℝ) (hΦ : ContDiff ℝ 2 Φ)
    (x : C(closedRectangle a b c d, ℝ)) :
    let H := fun j => q3RemainderRangeValue a b c d β L x₀ (q3CameronMartinDirections a b c d β L x₀ e j)
    let H₀ := fun j => q3RemainderRangeValue a b c d β L x₀ (q3H3Directions a b c d β L whiteBasis j)
    (1 / 2 : ℝ) * modelCovarianceTrace Φ H x = (1 / 2 : ℝ) * modelCovarianceTrace Φ H₀ x ∧
      modelGradientSquareTrace Φ H x = modelGradientSquareTrace Φ H₀ x := by
  dsimp only
  constructor
  · congr 1
    unfold modelCovarianceTrace secondDirectionalDerivative
    simp_rw [second_fderiv_eq hΦ]
    exact q3RemainderCameronMartin_bilinear_trace a b c d β L x₀ e hab hcd
      (fderiv ℝ (fderiv ℝ Φ) x)
  · exact q3RemainderCameronMartin_variance a b c d β L x₀ e hab hcd (fderiv ℝ Φ x)

end
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3

end ASDExplicitGamma.Gaussian
