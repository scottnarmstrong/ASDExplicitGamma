module

public import ASDExplicitGamma.Gaussian.Q3ModelCovariance
public import ASDExplicitGamma.Gaussian.H3Representatives

/-! # Actual model-shell law of the ordinary-H³/C¹ Gaussian realization -/

@[expose] public section

open MeasureTheory ProbabilityTheory Homogenization Set
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

noncomputable def whiteBasisIndex : Set WhiteNoise :=
  Classical.choose (exists_hilbertBasis (𝕜 := ℝ) (E := WhiteNoise))

noncomputable def whiteBasis : HilbertBasis whiteBasisIndex ℝ WhiteNoise :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis (𝕜 := ℝ) (E := WhiteNoise)))

instance instWhiteBasisCountable : Countable whiteBasisIndex :=
  orthonormal_countable whiteBasis whiteBasis.orthonormal

/-- The actual physical shell law is the value marginal of the H³/C¹ series, for every
nondegenerate source rectangle and with no realization premise. -/
theorem shellMarginalLaw_eq_h3Series (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (k : ℤ) :
    (ShellField.shellMarginalLaw M.P k).toMeasure.map
        (shellFieldScalarRestriction (closedRectangle a b c d)) =
      standardGaussianInfinitePi.map (fun ω =>
        q3C1Series a b c d (q3ModelAmplitude M h k) (q3ModelLength k) whiteBasis ω 0) := by
  let β := q3ModelAmplitude M h k
  let L := q3ModelLength k
  let V := Q3H3Range a b c d β L
  let K := closedRectangle a b c d
  let v := q3H3Directions a b c d β L whiteBasis
  let hs := q3H3Directions_summable a b c d β L whiteBasis
  let T := q3H3RangeValue a b c d β L
  let C : K → K → ℝ := fun x y => β ^ 2 * q3Cov ((x.1 0 - y.1 0) / L.1) *
    q3Cov ((x.1 1 - y.1 1) / L.1)
  have hShell := @shellMarginalLaw_finite_observation M h hM k K
  have hKernel : ∀ x y : K, (∑' j, T (v j) x * T (v j) y) = C x y :=
    q3H3Directions_covariance a b c d β hab hcd L whiteBasis
  have hlaw := @shellFieldScalarRestriction_law_eq_gaussianSeries V
    inferInstance (instQ3H3RangeInnerProductSpace a b c d β L) inferInstance inferInstance
    inferInstance inferInstance inferInstance K inferInstance inferInstance inferInstance
    (ShellField.shellMarginalLaw M.P k).toMeasure inferInstance C v hs T hShell hKernel
  exact hlaw

/-- The same Sobolev realization on the actual completed cutoff carrier. -/
theorem actualShellLaw_eq_h3Series (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (k : ℤ) :
    (Cutoff.cutoffSampleLaw M).toMeasure.map (fun ω =>
      shellFieldScalarRestriction (closedRectangle a b c d) (ω.1 k)) =
      standardGaussianInfinitePi.map (fun ω =>
        q3C1Series a b c d (q3ModelAmplitude M h k) (q3ModelLength k) whiteBasis ω 0) := by
  have hh := shellMarginalLaw_eq_h3Series a b c d hab hcd M h hM k
  have hm := Model.map_freshShell_eq_shellMarginalLaw M (k - 1)
  simp only [sub_add_cancel] at hm
  rw [← hm, Measure.map_map (measurable_shellFieldScalarRestriction _)
    ((measurable_pi_apply k).comp measurable_subtype_coe)] at hh
  exact hh

/-- Only the fresh value is centered. The actual remainder law is the deterministic image
of the same H³/C¹ realization, so no center/remainder independence is introduced. -/
theorem actualRemainderLaw_eq_h3Series (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (k : ℤ)
    (x₀ : closedRectangle a b c d) :
    (Cutoff.cutoffSampleLaw M).toMeasure.map (fun ω =>
      centeringMap x₀ (shellFieldScalarRestriction (closedRectangle a b c d) (ω.1 k))) =
      standardGaussianInfinitePi.map (fun ω => centeringMap x₀
        (q3C1Series a b c d (q3ModelAmplitude M h k) (q3ModelLength k) whiteBasis ω 0)) := by
  have hh := congrArg (fun μ : Measure C(closedRectangle a b c d, ℝ) => μ.map (centeringMap x₀))
    (actualShellLaw_eq_h3Series a b c d hab hcd M h hM k)
  rw [Measure.map_map (centeringMap x₀).continuous.measurable
    (show Measurable (fun ω : Cutoff.CutoffSample 2 =>
      shellFieldScalarRestriction (closedRectangle a b c d) (ω.1 k)) from
      (measurable_shellFieldScalarRestriction _).comp ((measurable_pi_apply k).comp measurable_subtype_coe)),
    Measure.map_map (centeringMap x₀).continuous.measurable] at hh
  · exact hh
  · exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 =>
      C(closedRectangle a b c d, ℝ)) 0).continuous.comp_stronglyMeasurable
      (stronglyMeasurable_q3C1Series a b c d _ _ whiteBasis)).measurable

end ASDExplicitGamma.Gaussian
