module

public import ASDExplicitGamma.Inverse.PhysicalGaussianSelectedBounded
public import ASDExplicitGamma.Inverse.PhysicalGaussianHeightWave
public import ASDExplicitGamma.Inverse.StoppedSelectedWaveExactFamily
public import ASDExplicitGamma.Inverse.PhysicalGaussianReconstruction
public import ASDExplicitGamma.Inverse.StoppedSelectedFamilyIdentity

/-! The actual selected physical bounds for the wave terms W₀ and W₁, without moment or independence premises. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- Literal full-series source W_j in (9.4), including its twelve-candidate term. -/
def physicalSelectedWaveExactBudget (γ p : ℝ) (H0 : ℕ) (j : Fin 2) : ℝ :=
  physicalSelectedWaveFiniteBudget γ p H0 j+40*(4*p+2)*selectedWaveExactTail γ p H0 j

/-- Complete geometric majorant of W_j, keeping the exact first tail term. -/
def physicalSelectedWaveBudget (γ p : ℝ) (H0 : ℕ) (j : Fin 2) : ℝ :=
  physicalSelectedWaveFiniteBudget γ p H0 j+40*(4*p+2)*selectedWaveTailBudget γ p H0 j

end
end ASDExplicitGamma.Inverse
