module

public import ASDExplicitGamma.Native.ParentBoundaryCommonKernelProfile

/-! The exact source finite shell clocks bound the actual common-center generator coefficient. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Algsuperdiff.Section3
noncomputable section

/-- The source finite second/fourth spatial covariance program, retaining
each shell's actual height before summation. -/
def parentBoundaryCommonSourceSpatialClock (gamma : ℝ) (height r p : ℕ) : ℝ :=
  ∑ i : Fin height,nativeSourceShellClock gamma (i.val+1)*(1/3:ℝ)^((r+(i.val+1))*p)

/-- The descendant ratio in the source kernel is exactly the triadic depth,
independently of the location of the common source square. -/
theorem parent_boundary_common_descendant_scale_ratio
    {P Q : TriadicCube 2} {d : ℕ} (hQ : Q ∈ descendantsAtDepth P d) :
    cubeScaleFactor Q/cubeScaleFactor P=(1/3:ℝ)^d := by
  rw [cubeScaleFactor_eq_div_pow_of_mem_descendantsAtDepth hQ,one_div_pow]
  have hP : 0 < cubeScaleFactor P := zpow_pos (by norm_num : (0:ℝ)<3) _
  field_simp

/-- The literal source finite shell program bounds the actual complete
common-center heat coefficient on every actual descendant, with exact
triadic population depth and starting/observed true-frame ratio. -/
theorem parent_boundary_common_shell_sum_source_kernel
    (M : ABKModel 2) (h : ℝ) {P Q : TriadicCube 2} {d : ℕ}
    (hQ : Q ∈ descendantsAtDepth P d) (n : ℤ) (r : ℕ) (hP : P.scale=n-(r:ℤ))
    (hstate : nativeInductionState M h n) (height : ℕ) :
    (∑ i : Fin height,parentBoundaryCommonShellCoefficient M h P Q n height i) ≤
      ((Annealed.sigmaBar M n:ℝ)/(Annealed.sigmaBar M Q.scale:ℝ))^2*
        parentBoundaryCommonKernelProfile (parentBoundaryCommonSourceSpatialClock M.gamma height r 2)
          (parentBoundaryCommonSourceSpatialClock M.gamma height r 4) ((1/3:ℝ)^d) := by
  have hk := parent_boundary_common_shell_sum_kernel M h P Q n height
  rw [parent_boundary_common_descendant_scale_ratio hQ] at hk
  apply hk.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact parent_boundary_common_kernel_profile_mono
    (parent_boundary_common_spatial_clock_cap M h P n r hP hstate height 2)
    (parent_boundary_common_spatial_clock_cap M h P n r hP hstate height 4) (by positivity)

end
end ASDExplicitGamma.Native
