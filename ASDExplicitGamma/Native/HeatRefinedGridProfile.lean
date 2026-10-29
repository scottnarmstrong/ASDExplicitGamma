module

public import ASDExplicitGamma.Native.HeatRefinedOverlapSeries
public import ASDExplicitGamma.Native.Q3GridOverlap
public import ASDExplicitGamma.Triadic.DiagInterpolant

/-! Identification of the refined rational profile with the actual depth-ten grid. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open ASDExplicitGamma.Numerics.Native
noncomputable section

/-- Source shell `n+1` is observed two scales below its wave length; its
mesh depth is `3-n`, with natural subtraction. -/
theorem heat_refined_grid_ratios (n : ℕ) :
    cubeScaleFactor (originCube 2 (-10)) / (q3GridKernelScale 10 (n+2)).1 =
      (heatRefinedRho n:ℝ) ∧
    diagMeshRadius (originCube 2 (-10)) (3-n) / (q3GridKernelScale 10 (n+2)).1 =
      (heatRefinedDelta n:ℝ) := by
  have hscale : cubeScaleFactor (originCube 2 (-10)) = ((3:ℝ)^10)⁻¹ := by
    simp [cubeScaleFactor,originCube,zpow_neg]
  have hfirst : cubeScaleFactor (originCube 2 (-10)) /
      (q3GridKernelScale 10 (n+2)).1 = (heatRefinedRho n:ℝ) := by
    rw [hscale]
    unfold q3GridKernelScale heatRefinedRho
    push_cast
    rw [div_pow,one_pow]
    field_simp
  refine ⟨hfirst, ?_⟩
  have hexp : n+2+(3-n)=max (n+2) 5 := by omega
  unfold diagMeshRadius
  rw [div_right_comm,hfirst]
  unfold heatRefinedRho heatRefinedDelta
  push_cast
  rw [←hexp]
  simp only [div_pow,one_pow,pow_add]
  field_simp

/-- The actual support multiplicity has exactly the certified refined factor. -/
theorem heat_refined_grid_overlap (n : ℕ) :
    q3GridOverlapFactor 10 (n+2) = (heatRefinedOverlap n:ℝ) := by
  unfold q3GridOverlapFactor heatRefinedOverlap
  push_cast
  rw [←pow_mul,mul_comm (8-n) 2,pow_mul]
  norm_num only [show (3:ℝ)^2=9 by norm_num]
  rw [div_pow,one_pow,one_div]

/-- The complete actual refined geometry is summable. -/
theorem heat_refined_grid_profile_summable :
    Summable (fun n : ℕ => q3GridOverlapFactor 10 (n+2)*
      (lemmaVH2Bn
        (cubeScaleFactor (originCube 2 (-10))/(q3GridKernelScale 10 (n+2)).1)
        (diagMeshRadius (originCube 2 (-10)) (3-n)/(q3GridKernelScale 10 (n+2)).1))^2) := by
  simpa only [heat_refined_grid_overlap,(heat_refined_grid_ratios _).1,
    (heat_refined_grid_ratios _).2] using heat_refined_Bn_profile_control.1

/-- The source depth-ten, shell-dependent-mesh coefficient fits the literal
configured budget, including all positive shells. -/
theorem heat_refined_grid_profile_tsum_le :
    (∑' n : ℕ,q3GridOverlapFactor 10 (n+2)*
      (lemmaVH2Bn
        (cubeScaleFactor (originCube 2 (-10))/(q3GridKernelScale 10 (n+2)).1)
        (diagMeshRadius (originCube 2 (-10)) (3-n)/(q3GridKernelScale 10 (n+2)).1))^2)
      ≤ (nativeHeatSB:ℝ) := by
  simpa only [heat_refined_grid_overlap,(heat_refined_grid_ratios _).1,
    (heat_refined_grid_ratios _).2] using heat_refined_Bn_profile_tsum_le

end
end ASDExplicitGamma.Native
