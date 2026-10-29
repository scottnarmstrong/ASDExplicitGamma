module

public import ASDExplicitGamma.Native.HeatVHEATDriftSourceClocks
public import ASDExplicitGamma.Native.ParentBoundaryModelScales
public import ASDExplicitGamma.Native.HeatRefinedGridProfile
public import ASDExplicitGamma.Native.HeatRefinedOverlapSeries
public import ASDExplicitGamma.Inverse.PureFluxGeneratorBankScales

/-! The actual refined source profile is bounded by the configured shell
profile, uniformly over the parent scale. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization Gaussian Triadic Inverse Variational ASDExplicitGamma.Numerics.Native
open Algsuperdiff.Section3
open scoped BigOperators
noncomputable section

private theorem nativeHeatQ3RefinedCarrierGridRatios (m : ℤ)
    (d : Fin 9) :
    cubeScaleFactor (originCube 2 m) /
        (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1 =
      (heatRefinedRho d.val : ℝ) ∧
    diagMeshRadius (originCube 2 m) (pureFluxBankSourceDepth (d.val + 2)) /
        (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1 =
      (heatRefinedDelta d.val : ℝ) := by
  have hrho := parent_boundary_model_length_ratio m (d.val + 2)
  have hdepth :
      (d.val + 2) + pureFluxBankSourceDepth (d.val + 2) =
        max (d.val + 2) 5 := by
    simp only [pureFluxBankSourceDepth]
    omega
  have hmesh :
      diagMeshRadius (originCube 2 m) (pureFluxBankSourceDepth (d.val + 2)) /
          (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1 =
        (1 / 3 : ℝ) ^ max (d.val + 2) 5 := by
    calc
      _ = (cubeScaleFactor (originCube 2 m) /
          (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1) /
          (3 : ℝ) ^ pureFluxBankSourceDepth (d.val + 2) := by
            simp only [diagMeshRadius]
            ring
      _ = ((1 / 3 : ℝ) ^ (d.val + 2)) /
          (3 : ℝ) ^ pureFluxBankSourceDepth (d.val + 2) := by rw [hrho]
      _ = (1 / 3 : ℝ) ^
          ((d.val + 2) + pureFluxBankSourceDepth (d.val + 2)) := by
            rw [div_eq_mul_inv, inv_eq_one_div, ← one_div_pow]
            rw [← pow_add]
      _ = (1 / 3 : ℝ) ^ max (d.val + 2) 5 := by rw [hdepth]
  constructor
  · simpa [heatRefinedRho] using hrho
  · simpa [heatRefinedDelta] using hmesh

/-- The finite nine-shell coefficient multiplying the child bank row is
bounded by `E9 * SB`; no carrier or child enumeration is used. -/
theorem nativeHeatQ3RefinedCarrierSourceProfileSum_le_SB
    (M : ABKModel 2) (h : ℝ) (m : ℤ)
    (hstate : nativeInductionState M h (m + 1)) :
    (∑ d : Fin 9,
      heatVHEATDriftVariance M h (m + 1) d *
        q3GridOverlapFactor 10 (d.val + 2) *
        (lemmaVH2Bn
          (cubeScaleFactor (originCube 2 m) /
            (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1)
          (diagMeshRadius (originCube 2 m)
            (pureFluxBankSourceDepth (d.val + 2)) /
            (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1) ^ 2)) ≤
      heatVHEATDriftE9 M * (nativeHeatSB : ℝ) := by
  have hsum (d : Fin 9) :
      heatVHEATDriftVariance M h (m + 1) d *
        q3GridOverlapFactor 10 (d.val + 2) *
        (lemmaVH2Bn
          (cubeScaleFactor (originCube 2 m) /
            (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1)
          (diagMeshRadius (originCube 2 m)
            (pureFluxBankSourceDepth (d.val + 2)) /
            (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1) ^ 2) ≤
      heatVHEATDriftE9 M *
        (q3GridOverlapFactor 10 (d.val + 2) *
          (lemmaVH2Bn
            (heatRefinedRho d.val : ℝ)
            (heatRefinedDelta d.val : ℝ)) ^ 2) := by
    have hv := heatVHEATDrift_source_variance_le M h (m + 1) hstate d
    have hgeom := nativeHeatQ3RefinedCarrierGridRatios m d
    have hprofile :
        0 ≤ q3GridOverlapFactor 10 (d.val + 2) *
          (lemmaVH2Bn
            (heatRefinedRho d.val : ℝ)
            (heatRefinedDelta d.val : ℝ)) ^ 2 := by
      have hov : 0 ≤ heatRefinedOverlap d.val := by
        unfold heatRefinedOverlap
        positivity
      have hbn : 0 ≤ lemmaVH2Bn
          (heatRefinedRho d.val : ℝ) (heatRefinedDelta d.val : ℝ) := by
        unfold lemmaVH2Bn heatRefinedRho heatRefinedDelta lemmaVH2C1 lemmaVH2C2 lemmaVH2A2
        positivity
      rw [heat_refined_grid_overlap]
      exact mul_nonneg (by exact_mod_cast hov) (sq_nonneg _)
    calc
      _ = heatVHEATDriftVariance M h (m + 1) d *
          (q3GridOverlapFactor 10 (d.val + 2) *
            (lemmaVH2Bn
              (heatRefinedRho d.val : ℝ)
              (heatRefinedDelta d.val : ℝ)) ^ 2) := by
            rw [hgeom.1, hgeom.2]
            ring
      _ ≤ heatVHEATDriftE9 M *
          (q3GridOverlapFactor 10 (d.val + 2) *
            (lemmaVH2Bn
              (heatRefinedRho d.val : ℝ)
              (heatRefinedDelta d.val : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_right hv.2 hprofile
  let profile : ℕ → ℝ := fun n =>
    q3GridOverlapFactor 10 (n + 2) *
      (lemmaVH2Bn (heatRefinedRho n : ℝ) (heatRefinedDelta n : ℝ)) ^ 2
  have hprofile_nonneg (n : ℕ) : 0 ≤ profile n := by
    dsimp [profile]
    have hov : 0 ≤ heatRefinedOverlap n := by
      unfold heatRefinedOverlap
      positivity
    have hbn : 0 ≤ lemmaVH2Bn (heatRefinedRho n : ℝ) (heatRefinedDelta n : ℝ) := by
      unfold lemmaVH2Bn heatRefinedRho heatRefinedDelta lemmaVH2C1 lemmaVH2C2 lemmaVH2A2
      positivity
    rw [heat_refined_grid_overlap]
    exact mul_nonneg (by exact_mod_cast hov) (sq_nonneg _)
  have hfinite :
      (∑ d : Fin 9,
        profile d.val) ≤ nativeHeatSB := by
    have hs : Summable profile := by
      simpa only [profile, heat_refined_grid_overlap] using
        heat_refined_Bn_profile_control.1
    have hle :
        (∑ n ∈ Finset.range 9, profile n) ≤ ∑' n : ℕ, profile n :=
      hs.sum_le_tsum (Finset.range 9) (fun n _ => hprofile_nonneg n)
    calc
      _ = ∑ n ∈ Finset.range 9, profile n := by
            exact (Fin.sum_univ_eq_sum_range (fun n : ℕ => profile n) 9).symm
      _ ≤ _ := hle
      _ ≤ _ := by
        simpa only [profile, heat_refined_grid_overlap] using
          heat_refined_Bn_profile_control.2
  have he9 : 0 ≤ heatVHEATDriftE9 M := by
    unfold heatVHEATDriftE9
    exact mul_nonneg (mul_nonneg (by norm_num) M.shellPrefix.gamma_pos.le)
      (Real.rpow_pos_of_pos (by norm_num) _).le
  calc
    _ ≤ ∑ d : Fin 9,
        heatVHEATDriftE9 M *
          (q3GridOverlapFactor 10 (d.val + 2) *
            (lemmaVH2Bn
              (heatRefinedRho d.val : ℝ)
              (heatRefinedDelta d.val : ℝ)) ^ 2) :=
      Finset.sum_le_sum (fun d _ => hsum d)
    _ = heatVHEATDriftE9 M *
        (∑ d : Fin 9,
          q3GridOverlapFactor 10 (d.val + 2) *
            (lemmaVH2Bn
              (heatRefinedRho d.val : ℝ)
              (heatRefinedDelta d.val : ℝ)) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_left hfinite
        he9

end
end ASDExplicitGamma.Native
