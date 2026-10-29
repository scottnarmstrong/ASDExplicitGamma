module

public import ASDExplicitGamma.Cold.HarmonicCutoffRecovery
public import ASDExplicitGamma.Cold.SquarePartitionProjection

/-! # Cutoff comparison uses actual integrated energies on each own cell -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Set
open ASDExplicitGamma.Triadic
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- Spatial average monotonicity on the actual open square. -/
theorem square_volumeAverage_mono_ae (R : TriadicCube 2) {f g : Vec 2 → ℝ}
    (hf : IntegrableOn f (openCubeSet R)) (hg : IntegrableOn g (openCubeSet R))
    (hfg : f ≤ᵐ[volume.restrict (openCubeSet R)] g) :
    volumeAverage (openCubeSet R) f ≤ volumeAverage (openCubeSet R) g := by
  unfold volumeAverage
  exact mul_le_mul_of_nonneg_left (integral_mono_ae hf hg hfg)
    (inv_nonneg.mpr ENNReal.toReal_nonneg)

end ASDExplicitGamma.Cold
