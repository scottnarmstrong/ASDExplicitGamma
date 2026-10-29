module

public import ASDExplicitGamma.Inverse.PhysicalGaussianResetWave

/-! Actual height-indexed physical waves, with the deterministic layer clock extracted exactly. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- The physical reset wave with its exact layer factor removed. -/
def physicalHeightWave (A : ABKModel 2) (Q : TriadicCube 2) (N : ℤ) (H0 : ℕ)
    (a c : ℝ) (weights : (ℕ × ℕ) → ℤ → ℝ) (layer H : ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (3:ℝ)^(-4*A.gamma*(localizationProfileDepth (layer+1):ℝ))*
    physicalResetWave A Q N H0 a c weights (H-H0,layer) ω

/-- The two source height weights z_h^j, j=0,1, on the actual physical wave. -/
def physicalHeightWeightedWave (A : ABKModel 2) (Q : TriadicCube 2) (N : ℤ) (H0 : ℕ)
    (a c : ℝ) (weights : (ℕ × ℕ) → ℤ → ℝ) (layer : ℕ) (j : Fin 2) (H : ℕ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  ((H:ℝ)-38)^j.val*physicalHeightWave A Q N H0 a c weights layer H ω

/-- Exact x=f_k+z_h identity at every candidate height. -/
theorem physical_height_abscissa_eq (H0 : ℕ) (hH : 38 ≤ H0) (H : ℕ) (hH0 : H0 ≤ H) (layer : ℕ) :
    (localizationResetAbscissa (H0-38) (H-H0) layer:ℝ) =
      ((H:ℝ)-38)+(localizationProfileDepth (layer+1):ℝ) := by
  have hi : (localizationResetAbscissa (H0-38) (H-H0) layer:ℤ) =
      (H:ℤ)-38+(localizationProfileDepth (layer+1):ℤ) := by
    unfold localizationResetAbscissa
    omega
  exact_mod_cast hi

theorem physical_height_wave_measurable (A : ABKModel 2) (Q : TriadicCube 2) (N : ℤ) (H0 : ℕ)
    (a c : ℝ) (weights : (ℕ × ℕ) → ℤ → ℝ) (layer H : ℕ) :
    Measurable (physicalHeightWave A Q N H0 a c weights layer H) :=
  measurable_const.mul (physical_reset_wave_measurable A Q N H0 a c weights _)

theorem physical_height_weighted_wave_measurable (A : ABKModel 2) (Q : TriadicCube 2) (N : ℤ) (H0 : ℕ)
    (a c : ℝ) (weights : (ℕ × ℕ) → ℤ → ℝ) (layer : ℕ) (j : Fin 2) (H : ℕ) :
    Measurable (physicalHeightWeightedWave A Q N H0 a c weights layer j H) :=
  measurable_const.mul (physical_height_wave_measurable A Q N H0 a c weights layer H)

end
end ASDExplicitGamma.Inverse
