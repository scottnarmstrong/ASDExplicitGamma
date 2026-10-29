module

public import ASDExplicitGamma.Native.ParentBoundaryCommonShellShape
public import ASDExplicitGamma.Native.ParentBoundaryBandEnergy

/-! Actual normalized common-source spatial clocks and their exact native shell bounds. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Algsuperdiff.Section3
noncomputable section

/-- Exact translated-source-square length ratio at every shell height. -/
theorem parent_boundary_common_model_length_ratio
    (P : TriadicCube 2) (n : ℤ) (r s : ℕ) (hP : P.scale=n-(r:ℤ)) :
    cubeScaleFactor P/(q3ModelLength (n+(s:ℤ))).val=(1/3:ℝ)^(r+s) := by
  have hscale : cubeScaleFactor P=cubeScaleFactor (originCube 2 (n-(r:ℤ))) := by
    change (3:ℝ)^P.scale=(3:ℝ)^(n-(r:ℤ))
    rw [hP]
  have hi : n+(s:ℤ)=(n-(r:ℤ))+((r+s:ℕ):ℤ) := by omega
  rw [hscale,hi,parent_boundary_model_length_ratio]

/-- Literal finite normalized covariance clock, retaining each physical
shell amplitude and its own source-square length ratio. -/
def parentBoundaryCommonSpatialClock (M : ABKModel 2) (h : ℝ) (P : TriadicCube 2)
    (n : ℤ) (height p : ℕ) : ℝ :=
  ∑ i : Fin height,(q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))^2*
    (cubeScaleFactor P/(q3ModelLength (n+((i.val+1:ℕ):ℤ))).val)^p

/-- The precise source finite shell program bounds the actual normalized
spatial clock, with every shell height retained before summation. -/
theorem parent_boundary_common_spatial_clock_cap
    (M : ABKModel 2) (h : ℝ) (P : TriadicCube 2) (n : ℤ) (r : ℕ)
    (hP : P.scale=n-(r:ℤ)) (hstate : nativeInductionState M h n) (height p : ℕ) :
    parentBoundaryCommonSpatialClock M h P n height p ≤
      ∑ i : Fin height,nativeSourceShellClock M.gamma (i.val+1)*(1/3:ℝ)^((r+(i.val+1))*p) := by
  unfold parentBoundaryCommonSpatialClock
  apply Finset.sum_le_sum
  intro i _
  rw [parent_boundary_common_model_length_ratio P n r (i.val+1) hP,←pow_mul]
  have hv : (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))^2 ≤
      nativeSourceShellClock M.gamma (i.val+1) := by
    simpa only [div_pow] using native_source_shell_variance_le_clock M h n (i.val+1) (i.val+1) hstate le_rfl
  exact mul_le_mul_of_nonneg_right hv (by positivity)

/-- Normalization by the true frame commutes with the actual full A-column
coefficient. No frame ratio or spatial scale is rounded. -/
theorem parent_boundary_common_row_coefficient_div
    (P Q : TriadicCube 2) (b sigma : ℝ) (hsigma : 0 < sigma) (L : {l : ℝ // 0 < l}) :
    parentBoundaryCommonRowCoefficient P Q (b/sigma) L 0=
      parentBoundaryCommonRowCoefficient P Q b L 0/sigma := by
  rw [parent_boundary_common_row_coefficient_shape,parent_boundary_common_row_coefficient_shape,
    abs_div,abs_of_pos hsigma]
  ring

end
end ASDExplicitGamma.Native
