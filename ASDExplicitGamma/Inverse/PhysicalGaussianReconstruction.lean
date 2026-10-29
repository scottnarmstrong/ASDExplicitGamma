module

public import ASDExplicitGamma.Inverse.PhysicalGaussianHeightWave

/-! Exact reconstruction of the physical wave from the normalized height clocks. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3
noncomputable section

/-- Extracting the layer clock is exactly reversible, pointwise on the actual
sample space. No norm or stochastic premise is needed. -/
theorem physical_height_wave_reconstruction (A : ABKModel 2) (Q : TriadicCube 2) (N : ℤ)
    (H0 : ℕ) (a c : ℝ) (weights : (ℕ × ℕ) → ℤ → ℝ) (layer H : ℕ) (ω : Cutoff.CutoffSample 2) :
    (3:ℝ)^(4*A.gamma*(localizationProfileDepth (layer+1):ℝ))*
      physicalHeightWave A Q N H0 a c weights layer H ω =
        physicalResetWave A Q N H0 a c weights (H-H0,layer) ω := by
  have hr : (3:ℝ)^(4*A.gamma*(localizationProfileDepth (layer+1):ℝ))*
      (3:ℝ)^(-4*A.gamma*(localizationProfileDepth (layer+1):ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
    convert Real.rpow_zero 3 using 1
    congr 1
    ring
  unfold physicalHeightWave
  rw [← mul_assoc,hr,one_mul]

end
end ASDExplicitGamma.Inverse
