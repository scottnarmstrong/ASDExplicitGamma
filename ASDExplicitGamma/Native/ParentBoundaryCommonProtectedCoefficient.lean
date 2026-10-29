module

public import ASDExplicitGamma.Native.ParentBoundaryCommonSourceKernel

/-! Physical covariance coefficients in the exact protected source-bank frame. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Algsuperdiff.Section3
noncomputable section

/-- Actual physical per-shell p20 coefficient when the inverse bank is
anchored at protected label m rather than the observed square's own label. -/
def parentBoundaryCommonProtectedShellCoefficient (M : ABKModel 2) (h : ℝ)
    (P Q : TriadicCube 2) (m n : ℤ) (height : ℕ) (i : Fin height) : ℝ :=
  let J := n+((i.val+1:ℕ):ℤ)
  let sigma : ℝ := Annealed.sigmaBar M n
  let b := q3ModelAmplitude M h J
  let L := q3ModelLength J
  let A := parentBoundaryCommonRowCoefficient P Q b L 0
  let kappa := lemmaVH2Bn (cubeScaleFactor P/L.val) (diagMeshRadius Q 0/L.val)
  sigma⁻¹^2*(sigma/(Annealed.sigmaBar M m:ℝ))^2*((232/125:ℝ)*A^2+38*b^2*kappa^2)

/-- Nonnegativity of every actual protected-shell coefficient. -/
theorem parent_boundary_common_protected_coefficient_nonneg
    (M : ABKModel 2) (h : ℝ) (P Q : TriadicCube 2) (m n : ℤ) (height : ℕ) (i : Fin height) :
    0 ≤ parentBoundaryCommonProtectedShellCoefficient M h P Q m n height i := by
  unfold parentBoundaryCommonProtectedShellCoefficient
  dsimp only
  positivity

/-- Exact change of the bank's completed label; the physical covariance
and starting response frame are unchanged. -/
theorem parent_boundary_common_protected_coefficient_eq
    (M : ABKModel 2) (h : ℝ) (P Q : TriadicCube 2) (m n : ℤ) (height : ℕ) (i : Fin height) :
    parentBoundaryCommonProtectedShellCoefficient M h P Q m n height i=
      ((Annealed.sigmaBar M Q.scale:ℝ)/(Annealed.sigmaBar M m:ℝ))^2*
        parentBoundaryCommonShellCoefficient M h P Q n height i := by
  unfold parentBoundaryCommonProtectedShellCoefficient parentBoundaryCommonShellCoefficient
  dsimp only
  field_simp [(Annealed.sigmaBar_characterization M Q.scale).1.ne',
    (Annealed.sigmaBar_characterization M m).1.ne']

/-- The ACTUAL protected coefficient sum has the exact source kernel
profile, without an extra fixed source-offset frame loss. -/
theorem parent_boundary_common_protected_sum_source_kernel
    (M : ABKModel 2) (h : ℝ) {P Q : TriadicCube 2} {d : ℕ}
    (hQ : Q ∈ descendantsAtDepth P d) (m n : ℤ) (r : ℕ) (hP : P.scale=n-(r:ℤ))
    (hstate : nativeInductionState M h n) (height : ℕ) :
    (∑ i : Fin height,parentBoundaryCommonProtectedShellCoefficient M h P Q m n height i) ≤
      ((Annealed.sigmaBar M n:ℝ)/(Annealed.sigmaBar M m:ℝ))^2*
        parentBoundaryCommonKernelProfile (parentBoundaryCommonSourceSpatialClock M.gamma height r 2)
          (parentBoundaryCommonSourceSpatialClock M.gamma height r 4) ((1/3:ℝ)^d) := by
  simp_rw [parent_boundary_common_protected_coefficient_eq]
  rw [←Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left
    (parent_boundary_common_shell_sum_source_kernel M h hQ n r hP hstate height)
    (sq_nonneg ((Annealed.sigmaBar M Q.scale:ℝ)/(Annealed.sigmaBar M m:ℝ)))
  apply hh.trans_eq
  field_simp [(Annealed.sigmaBar_characterization M Q.scale).1.ne',
    (Annealed.sigmaBar_characterization M m).1.ne']

end
end ASDExplicitGamma.Native
