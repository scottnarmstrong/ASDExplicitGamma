module

public import ASDExplicitGamma.Native.HeatVHEATRefinedThetaProfile
public import ASDExplicitGamma.Native.HeatVHEATSourceCarrierGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedShellLawGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceClocksGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceProfilesGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceTransportGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceGeometryGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceBankGen
public import ASDExplicitGamma.Native.HeatVHEATDriftBankIdentityGen
public import ASDExplicitGamma.Native.HeatVHEATDriftBankMeasurableGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceIntegrandGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceNormsGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceExpectationGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedCoefficientsGen
public import ASDExplicitGamma.Native.HeatVHEATDriftConfiguredCoefficientsGen
public import ASDExplicitGamma.Native.HeatVHEATDriftConfiguredExpectationGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedProfileGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedExpectationGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedPhysicalGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedBindingGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceObserverGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedActualGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedAssemblyGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedRowGen
public import ASDExplicitGamma.Native.Q3GridOverlapGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedSupportGeometryGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedGeometryGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedObservationGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedParentLawGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedSourceMapGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanVarianceGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedRemainderGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanChildBoundGen
public import ASDExplicitGamma.Native.HeatVHEATBracketMeanRieszSupportGen
public import ASDExplicitGamma.Native.HeatVHEATBracketParentRieszGen
public import ASDExplicitGamma.Native.HeatVHEATBracketMeanDerivativeGen
public import ASDExplicitGamma.Native.HeatVHEATBracketMeanDerivativeCLMGen
public import ASDExplicitGamma.Native.HeatVHEATBracketMeanRieszIdentityGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanRieszIdentityGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanAverageProfilesGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanBracketGen
public import ASDExplicitGamma.Native.HeatVHEATBracketSourceCarrierGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedDriftAssemblyGen
public import ASDExplicitGamma.Native.HeatVHEATSourceBracketGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedFinalAssemblyGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedThetaPointwiseGen

/-! The `ns`-shell generalization of `HeatVHEATRefinedThetaProfile`. -/

@[expose] public section


namespace ASDExplicitGamma.Native

open Homogenization Gaussian Triadic Inverse Variational ASDExplicitGamma.Numerics.Native
open Algsuperdiff.Section3
open scoped BigOperators
noncomputable section

variable (ns : ℕ) [NeZero ns]

private theorem nativeHeatQ3RefinedCarrierGridRatios_Gen (m : ℤ)
    (d : Fin ns) :
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
theorem nativeHeatQ3RefinedCarrierSourceProfileSum_le_SB_Gen
    (M : ABKModel 2) (h : ℝ) (m : ℤ)
    (hstate : nativeInductionState M h (m + 1)) :
    (∑ d : Fin ns,
      (heatVHEATDriftVarianceGen ns) M h (m + 1) d *
        q3GridOverlapFactor 10 (d.val + 2) *
        (lemmaVH2Bn
          (cubeScaleFactor (originCube 2 m) /
            (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1)
          (diagMeshRadius (originCube 2 m)
            (pureFluxBankSourceDepth (d.val + 2)) /
            (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1) ^ 2)) ≤
      (heatVHEATDriftEGen ns) M * (nativeHeatSB : ℝ) := by
  have hsum (d : Fin ns) :
      (heatVHEATDriftVarianceGen ns) M h (m + 1) d *
        q3GridOverlapFactor 10 (d.val + 2) *
        (lemmaVH2Bn
          (cubeScaleFactor (originCube 2 m) /
            (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1)
          (diagMeshRadius (originCube 2 m)
            (pureFluxBankSourceDepth (d.val + 2)) /
            (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1) ^ 2) ≤
      (heatVHEATDriftEGen ns) M *
        (q3GridOverlapFactor 10 (d.val + 2) *
          (lemmaVH2Bn
            (heatRefinedRho d.val : ℝ)
            (heatRefinedDelta d.val : ℝ)) ^ 2) := by
    have hv := (heatVHEATDrift_source_variance_le_Gen ns) M h (m + 1) hstate d
    have hgeom := (nativeHeatQ3RefinedCarrierGridRatios_Gen ns) m d
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
      _ = (heatVHEATDriftVarianceGen ns) M h (m + 1) d *
          (q3GridOverlapFactor 10 (d.val + 2) *
            (lemmaVH2Bn
              (heatRefinedRho d.val : ℝ)
              (heatRefinedDelta d.val : ℝ)) ^ 2) := by
            rw [hgeom.1, hgeom.2]
            ring
      _ ≤ (heatVHEATDriftEGen ns) M *
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
      (∑ d : Fin ns,
        profile d.val) ≤ nativeHeatSB := by
    have hs : Summable profile := by
      simpa only [profile, heat_refined_grid_overlap] using
        heat_refined_Bn_profile_control.1
    have hle :
        (∑ n ∈ Finset.range ns, profile n) ≤ ∑' n : ℕ, profile n :=
      hs.sum_le_tsum (Finset.range ns) (fun n _ => hprofile_nonneg n)
    calc
      _ = ∑ n ∈ Finset.range ns, profile n := by
            exact (Fin.sum_univ_eq_sum_range (fun n : ℕ => profile n) ns)
      _ ≤ _ := hle
      _ ≤ _ := by
        simpa only [profile, heat_refined_grid_overlap] using
          heat_refined_Bn_profile_control.2
  have he9 : 0 ≤ (heatVHEATDriftEGen ns) M := by
    unfold heatVHEATDriftEGen
    exact mul_nonneg (mul_nonneg (by norm_num) M.shellPrefix.gamma_pos.le)
      (Real.rpow_pos_of_pos (by norm_num) _).le
  calc
    _ ≤ ∑ d : Fin ns,
        (heatVHEATDriftEGen ns) M *
          (q3GridOverlapFactor 10 (d.val + 2) *
            (lemmaVH2Bn
              (heatRefinedRho d.val : ℝ)
              (heatRefinedDelta d.val : ℝ)) ^ 2) :=
      Finset.sum_le_sum (fun d _ => hsum d)
    _ = (heatVHEATDriftEGen ns) M *
        (∑ d : Fin ns,
          q3GridOverlapFactor 10 (d.val + 2) *
            (lemmaVH2Bn
              (heatRefinedRho d.val : ℝ)
              (heatRefinedDelta d.val : ℝ)) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_left hfinite
        he9

end
end ASDExplicitGamma.Native
