module

public import ASDExplicitGamma.Inverse.SelectedGaussian
public import ASDExplicitGamma.Inverse.PhysicalGaussianAllOrderTail
public import ASDExplicitGamma.Inverse.AssemblyWaveReconstruction
public import ASDExplicitGamma.Triadic.PoincareCell

/-! Actual clocked wave payments on a layer, with the full-stop index. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Triadic
open ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- The physical-wave part of the scalar trace envelope on one layer. -/
def assemblyTraceWaveLayer (M : ABKModel 2) (Q : TriadicCube 2)
    (k : ℕ) (p : ℝ) (N : ℤ) (weights : ℤ → ℝ) (i : ℕ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  rootAssemblyClock M.gamma (resetQ3StoppedHeight M Q k ω) (i+1)*
    Real.sqrt (bankLayerWeight i)*
      physicalMissingWave M (layerOldCutoff Q.scale (resetQ3StoppedHeight M Q k ω) (i+1))
        Q.scale N (cubeCorner Q 0) (cubeCorner Q 1)
        (sourceBandWeights (protectedOldLabel Q.scale (orderBand p)) weights) ω

end
end ASDExplicitGamma.Inverse
