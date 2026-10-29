module

public import ASDExplicitGamma.Native.ParentBoundaryBandResponse
public import ASDExplicitGamma.Native.ParentBoundaryBandDirectionalLaw
public import ASDExplicitGamma.Inverse.FullResponseTrace
public import ASDExplicitGamma.Inverse.StoppedDensitySumNorm

/-! Quantitative trace moments on the actual simultaneous-band source cells.
The reserve is paid against the full response on the same law. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Inverse Algsuperdiff.Section3 Gaussian Cold
open scoped ENNReal
noncomputable section

/-- Raw full-response profile at a specified refinement below the starting cube. -/
def parentBoundaryBandTraceCap (M : ABKModel 2) (height depth : ℕ) : ℝ :=
  4*((1009309/500000:ℝ)+M.gamma*(32474*((height:ℝ)+(depth:ℝ)+1)+11483216))*
    (3:ℝ)^((2*(height:ℝ)+4*(depth:ℝ)+4)*M.gamma)

/-- The raw reserve profile is nonnegative. -/
theorem parent_boundary_band_trace_cap_nonneg (M : ABKModel 2) (height depth : ℕ) :
    0≤parentBoundaryBandTraceCap M height depth := by
  have hg := M.shellPrefix.gamma_pos.le
  unfold parentBoundaryBandTraceCap
  positivity

/-- Actual physical trace positivity on any source cell. -/
theorem parent_boundary_band_trace_nonneg (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (t : ℝ) (U : TriadicCube 2) (omega : Cutoff.CutoffSample 2) :
    0≤traceDefect (cubeSet U)
      (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega)
      (Annealed.sigmaBar M n) := by
  obtain ⟨Lam,_,hEll⟩ := parent_boundary_band_elliptic_cube M n (n+(height:ℤ))
    (fun _ => Real.sqrt t) omega U
  exact traceDefect_nonneg_of_ellipticFieldOn_triCube M.nu_pos hEll
    (Annealed.sigmaBar_characterization M n).1

end
end ASDExplicitGamma.Native
