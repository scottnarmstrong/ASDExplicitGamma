module

public import ASDExplicitGamma.Native.ParentBoundaryCommonPowerExpectation
public import ASDExplicitGamma.Native.ParentBoundaryCommonCubeShellHeat

/-! Actual root-compatible differential inequality on every common-centered descendant. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Algsuperdiff.Section3
noncomputable section

/-- Literal actual twentieth moment in the starting native frame. -/
def parentBoundaryCommonTraceMoment (M : ABKModel 2) {P Q : TriadicCube 2} {d : ℕ}
    (hQ : Q ∈ descendantsAtDepth P d) (n : ℤ) (height : ℕ) (t : ℝ) : ℝ :=
  parentBoundaryCommonCubeAverage M hQ n height
    (fun x => (squareTrace Q M.nu (Annealed.sigmaBar M n) x)^(20:ℝ)) t

/-- The actual moment is nonnegative, including its possible zero case. -/
theorem parent_boundary_common_trace_moment_nonneg
    (M : ABKModel 2) {P Q : TriadicCube 2} {d : ℕ}
    (hQ : Q ∈ descendantsAtDepth P d) (n : ℤ) (height : ℕ) (t : ℝ) :
    0 ≤ parentBoundaryCommonTraceMoment M hQ n height t :=
  integral_nonneg (fun ω => Real.rpow_nonneg
    (parent_boundary_common_square_trace_nonneg Q M.nu (Annealed.sigmaBar M n) M.nu_pos
      (Annealed.sigmaBar_characterization M n).1 (parentBoundaryCommonCubeObserved hQ n height t ω)) _)

end
end ASDExplicitGamma.Native
