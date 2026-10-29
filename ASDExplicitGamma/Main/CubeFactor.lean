module

public import ASDExplicitGamma.Main.CubeRestriction
public import ASDExplicitGamma.Gaussian.Q3ModelH3Realization
public import ASDExplicitGamma.Gaussian.ModelHeatResponse

/-! The actual smooth q3 covariance factor on the exact main trace square. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization ASDExplicitGamma.Gaussian MeasureTheory ProbabilityTheory Set
open Algsuperdiff.Section3
open scoped Topology

/-- The ordinary H3 factor space for this same physical square. -/
noncomputable abbrev MainCubeH3 (n : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l}) :=
  Q3H3Range (-mainCubeHalfSide n) (mainCubeHalfSide n)
    (-mainCubeHalfSide n) (mainCubeHalfSide n) b L

noncomputable instance mainCubeH3InnerProductSpace (n : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l}) :
    InnerProductSpace ℝ (MainCubeH3 n b L) :=
  instQ3H3RangeInnerProductSpace _ _ _ _ b L

noncomputable def mainCubeH3Value (n : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l}) :
    MainCubeH3 n b L →L[ℝ] C(closure (cubeSet (originCube 2 n)), ℝ) :=
  (mainCubeRestriction n).comp (q3H3RangeValue _ _ _ _ b L)

noncomputable def mainCubeQ3Directions (n : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l}) : ℕ → MainCubeH3 n b L :=
  q3H3Directions _ _ _ _ b L whiteBasis

theorem mainCubeQ3Directions_summable (n : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l}) :
    Summable (fun j => ‖mainCubeQ3Directions n b L j‖^2) :=
  q3H3Directions_summable _ _ _ _ b L whiteBasis

/-- The series uses the named inherited ordinary-H3 inner product explicitly. -/
noncomputable def mainCubeQ3Series (n : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l}) :
    (ℕ → ℝ) → C(closure (cubeSet (originCube 2 n)), ℝ) :=
  @gaussianSeriesLimitE (MainCubeH3 n b L) C(closure (cubeSet (originCube 2 n)), ℝ)
    inferInstance (mainCubeH3InnerProductSpace n b L) inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (mainCubeQ3Directions n b L) (mainCubeQ3Directions_summable n b L) (mainCubeH3Value n b L)

/-- The value of a factor direction is exactly the actual global convolution. -/
theorem mainCubeH3Value_factor (n : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l})
    (u : WhiteNoise) (x : closure (cubeSet (originCube 2 n))) :
    mainCubeH3Value n b L
      (q3H3RangeFactor (-mainCubeHalfSide n) (mainCubeHalfSide n)
        (-mainCubeHalfSide n) (mainCubeHalfSide n) b L u) x =
      q3Convolution b L h3Zero u x.1 := by
  have hs : -mainCubeHalfSide n < mainCubeHalfSide n := by
    have h : 0 < mainCubeHalfSide n := by unfold mainCubeHalfSide cubeScaleFactor; positivity
    linarith only [h]
  exact q3H3RangeValue_factor _ _ _ _ b hs hs L u _

/-- The actual fresh shell on the main square has precisely the H3-series
law with the physical model amplitude and length. No realization is assumed. -/
theorem main_actual_fresh_cube_factor_law (n : ℤ) (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (m : ℤ) :
    let b := q3ModelAmplitude M h (m+1)
    let L := q3ModelLength (m+1)
    (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun omega : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction (closure (cubeSet (originCube 2 n))) (omega.1 (m+1))) =
      standardGaussianInfinitePi.map (mainCubeQ3Series n b L) := by
  intro b L
  have hs : -mainCubeHalfSide n < mainCubeHalfSide n := by
    have hpos : 0 < mainCubeHalfSide n := by unfold mainCubeHalfSide cubeScaleFactor; positivity
    linarith only [hpos]
  have hlaw := actualShellLaw_eq_h3Series (-mainCubeHalfSide n) (mainCubeHalfSide n)
    (-mainCubeHalfSide n) (mainCubeHalfSide n) hs hs M h hM (m+1)
  have hmap := congrArg (Measure.map (mainCubeRestriction n)) hlaw
  have hseries : Measurable (fun omega =>
      q3C1Series (-mainCubeHalfSide n) (mainCubeHalfSide n)
        (-mainCubeHalfSide n) (mainCubeHalfSide n) b L whiteBasis omega 0) :=
    (measurable_pi_apply (0 : Fin 3)).comp
      (stronglyMeasurable_q3C1Series _ _ _ _ b L whiteBasis).measurable
  have hsample : Measurable (fun omega : Cutoff.CutoffSample 2 =>
      shellFieldScalarRestriction (closedRectangle (-mainCubeHalfSide n) (mainCubeHalfSide n)
        (-mainCubeHalfSide n) (mainCubeHalfSide n)) (omega.1 (m+1))) :=
    (measurable_shellFieldScalarRestriction _).comp
      ((measurable_pi_apply (m+1)).comp measurable_subtype_coe)
  rw [Measure.map_map (mainCubeRestriction n).continuous.measurable hsample,
    Measure.map_map (mainCubeRestriction n).continuous.measurable hseries] at hmap
  convert hmap using 1 <;> rfl

end ASDExplicitGamma.Main
