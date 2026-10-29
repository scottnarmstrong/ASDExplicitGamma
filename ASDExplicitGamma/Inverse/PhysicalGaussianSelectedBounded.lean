module

public import ASDExplicitGamma.Inverse.PhysicalGaussianHeightWave
public import ASDExplicitGamma.Inverse.StoppedSelectedBoundedFamily

/-! The actual bounded-candidate physical wave terms W₀ and W₁ of the source. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- Exact bounded-candidate part of source W_j, with z_s=Hs+2-40. -/
def physicalSelectedWaveFiniteBudget (γ p : ℝ) (H0 : ℕ) (j : Fin 2) : ℝ :=
  40*(2*p+2)*(12:ℝ)^(1/p:ℝ)*((H0:ℝ)-27)^j.val*(3:ℝ)^(4*γ*((H0:ℝ)-27))

end
end ASDExplicitGamma.Inverse
