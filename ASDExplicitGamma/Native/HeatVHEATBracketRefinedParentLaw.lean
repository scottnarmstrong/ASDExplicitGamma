module

public import ASDExplicitGamma.Native.HeatVHEATRefinedShellLaw
public import ASDExplicitGamma.Main.CubeFactor
public import ASDExplicitGamma.Triadic.DiagMesh
import ASDExplicitGamma.Triadic.PoincareCell

/-! The common actual shell law on the refined carrier, obtained by
restricting the canonical q3 source law on its containing parent cube. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open ASDExplicitGamma.Triadic
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ProbabilityTheory
open scoped Topology

set_option linter.constructorNameAsVariable false in
/- Every depth-ten carrier child lies in the containing parent cube. -/
theorem nativeHeatQ3RefinedCarrierDomain_subset_parent (m : ℤ) :
    nativeHeatQ3RefinedCarrierDomain m ⊆
      closure (cubeSet (originCube 2 (m + 10))) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  let Q := originCube 2 (m + 10)
  let C := nativeHeatQ3RefinedCarrierChild m i
  let k := nativeHeatQ3RefinedChildDigits (finProdFinEquiv.symm i)
  have hcorner (a : Fin 2) :
      cubeCorner C a = cubeCorner Q a + (k a).val * diagMeshRadius Q 10 := by
    change cubeCorner (Triadic.diagMeshCell Q 10
      (nativeHeatQ3RefinedChildDigits (finProdFinEquiv.symm i))) a = _
    exact Triadic.diagMeshCell_corner Q 10 _ a
  have hside : cubeScaleFactor C = diagMeshRadius Q 10 := by
    change cubeScaleFactor (Triadic.diagMeshCell Q 10
      (nativeHeatQ3RefinedChildDigits (finProdFinEquiv.symm i))) = _
    exact Triadic.diagMeshCell_side Q 10 _
  have htile : cubeScaleFactor Q = (3 : ℝ) ^ 10 * diagMeshRadius Q 10 := by
    rw [Triadic.diagMeshRadius]
    field_simp
  have hlower (a : Fin 2) : cubeCorner Q a ≤ cubeCorner C a := by
    rw [hcorner]
    exact le_add_of_nonneg_right
      (mul_nonneg (Nat.cast_nonneg _) (Triadic.diagMeshRadius_pos Q 10).le)
  have hupper (a : Fin 2) :
      cubeCorner C a + cubeScaleFactor C ≤ cubeCorner Q a + cubeScaleFactor Q := by
    have hk : ((k a).val : ℝ) + 1 ≤ (3 : ℝ) ^ 10 := by
      exact_mod_cast Nat.succ_le_of_lt (k a).isLt
    have hmul := mul_le_mul_of_nonneg_right hk
      (Triadic.diagMeshRadius_pos Q 10).le
    rw [hcorner, hside]
    calc
      cubeCorner Q a + (k a).val * diagMeshRadius Q 10 + diagMeshRadius Q 10 =
          cubeCorner Q a + (((k a).val : ℝ) + 1) * diagMeshRadius Q 10 := by ring
      _ ≤ cubeCorner Q a + (3 : ℝ) ^ 10 * diagMeshRadius Q 10 :=
        by nlinarith [hmul]
      _ = cubeCorner Q a + cubeScaleFactor Q := by rw [← htile]
  have hcube : cubeSet C ⊆ cubeSet Q := by
    rw [Triadic.cubeSet_eq_box C, Triadic.cubeSet_eq_box Q]
    intro y hy
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico] at hy ⊢
    intro a
    rcases hy a with ⟨hylo, hyhi⟩
    exact ⟨(hlower a).trans hylo, lt_of_lt_of_le hyhi (hupper a)⟩
  exact closure_mono hcube hxi

/-- Restrict a continuous parent-cube field to the full refined carrier. -/
noncomputable def nativeHeatQ3RefinedCarrierParentRestrict (m : ℤ) :
    C(closure (cubeSet (originCube 2 (m + 10))), ℝ) →L[ℝ]
      C(nativeHeatQ3RefinedCarrierDomain m, ℝ) := by
  let e : nativeHeatQ3RefinedCarrierDomain m →
      closure (cubeSet (originCube 2 (m + 10))) :=
    fun x => ⟨x.1, nativeHeatQ3RefinedCarrierDomain_subset_parent m x.2⟩
  exact ContinuousMap.compCLM ℝ ℝ ⟨e, continuous_subtype_val.subtype_mk _⟩

/-- The actual factor for one physical refined shell has the law of the
canonical q3 source field restricted from the parent cube. This is a joint
law on the whole carrier, so restrictions to different children keep their
actual common-noise correlations. -/
theorem nativeHeatQ3RefinedCarrierFreshShellParentLaw
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (d : Fin 9) :
    let F := nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m
    (standardGaussianInfinitePi.map
      (gaussianSeriesLimitE (F.squareSummable d) (F.factor d))) =
      (standardGaussianInfinitePi.map
        (mainCubeQ3Series (m + 10)
          (q3ModelAmplitude M h
            (nativeHeatQ3RefinedCarrierPhysicalShells m d))
          (q3ModelLength
            (nativeHeatQ3RefinedCarrierPhysicalShells m d)))).map
        (nativeHeatQ3RefinedCarrierParentRestrict m) := by
  classical
  let F := nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m
  let parent := closure (cubeSet (originCube 2 (m + 10)))
  let K := nativeHeatQ3RefinedCarrierDomain m
  let label := nativeHeatQ3RefinedCarrierPhysicalShells m d
  let r := nativeHeatQ3RefinedCarrierParentRestrict m
  have hF := F.law d
  have hparent : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction parent (ω.1 label)) =
      standardGaussianInfinitePi.map
        (mainCubeQ3Series (m + 10)
          (q3ModelAmplitude M h label) (q3ModelLength label)) := by
    simpa [parent, label, Int.sub_add_cancel] using
      (main_actual_fresh_cube_factor_law (m + 10) M h hM (label - 1))
  have hparentK := congrArg (Measure.map r) hparent
  have hm : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      shellFieldScalarRestriction parent (ω.1 label)) :=
    (measurable_shellFieldScalarRestriction parent).comp
      ((measurable_pi_apply label).comp measurable_subtype_coe)
  rw [Measure.map_map r.continuous.measurable hm] at hparentK
  have hsame : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 =>
        r (shellFieldScalarRestriction parent (ω.1 label))) =
      (Cutoff.cutoffSampleLaw M).toMeasure.map
        (fun ω : Cutoff.CutoffSample 2 =>
          shellFieldScalarRestriction K (ω.1 label)) := by
    congr 1
  change (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction K (ω.1 label)) = _ at hF
  dsimp only [F, label, K, r] at hF hparentK ⊢
  exact hF.symm.trans (hsame.symm.trans hparentK)

end ASDExplicitGamma.Native
