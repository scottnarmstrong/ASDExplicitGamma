module

public import ASDExplicitGamma.Native.ParentBoundaryBandTraceMoments
public import ASDExplicitGamma.Native.OldSignedDepthSeriesArithmetic

/-! Summability of the complete simultaneous-band depth budgets, including
the actual population reserve and the unchanged observer frame. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Scalar Inverse Algsuperdiff.Section3
noncomputable section

/-- The full-response profile factors into its fixed-depth part, an affine
depth polynomial and the exact physical-frame geometric growth. -/
theorem parent_boundary_band_trace_cap_factor (M : ABKModel 2) (height r j : ℕ) :
    parentBoundaryBandTraceCap M height (r+j)=
      4*((1009309/500000:ℝ)+M.gamma*(32474*((height:ℝ)+(r:ℝ)+1)+11483216)+
        (32474*M.gamma)*(j:ℝ))*
        (3:ℝ)^((2*(height:ℝ)+4*(r:ℝ)+4)*M.gamma)*(3:ℝ)^(4*M.gamma*(j:ℝ)) := by
  unfold parentBoundaryBandTraceCap
  push_cast
  have he : (2*(height:ℝ)+4*((r:ℝ)+(j:ℝ))+4)*M.gamma=
      (2*(height:ℝ)+4*(r:ℝ)+4)*M.gamma+4*M.gamma*(j:ℝ) := by ring
  rw [he,Real.rpow_add (by norm_num : (0:ℝ)<3)]
  ring

end
end ASDExplicitGamma.Native
