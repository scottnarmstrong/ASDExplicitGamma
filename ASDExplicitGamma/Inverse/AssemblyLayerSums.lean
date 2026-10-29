module

public import ASDExplicitGamma.Inverse.RootEnergyAssembly
public import ASDExplicitGamma.Inverse.HybridActiveSum
public import ASDExplicitGamma.Inverse.HybridIdentitySum
public import ASDExplicitGamma.Inverse.StoppedPastDiameterFinite

/-! Root energy enlarged to complete deterministic Whitney layers. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal
noncomputable section

/-- The complete nonnegative inverse energy majorant on a deterministic
Whitney partition, before any moment estimate or height selection. -/
def assemblyInverseLayerMajorant (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (ω : Cutoff.CutoffSample 2) (q : Vec 2) : ℝ≥0∞ :=
  ENNReal.ofReal rootAssemblySensitivity *
    ((∑' n : ℕ, ENNReal.ofReal (∑ P ∈ whitneyRootLayer Q H n,
      rootAssemblyClock M.gamma H n * (volume (cubeSet P)).toReal /
        (volume (cubeSet Q)).toReal * fullMatrixQuadratic (toFullBlockVec (0,q))
          (clippedCellMatrix M (P.scale+40) P resetAllOrderTau ω))) +
      ENNReal.ofReal (rootResponseEnvelope (6*resetAllOrderTau)) *
        ∑' n : ℕ, ENNReal.ofReal (rootAssemblyClock M.gamma H n *
          (planarGradientCharge 40+1) *
          ((∑ e : Fin 3, ∫ x in rootLayerCarrier Q H n,
            (layerResolutionDiameter M Q H resetAllOrderTau (waveGateEta .allOrder)
              n e ω x)^2)/(volume (cubeSet Q)).toReal) * dotProduct q q))

end
end ASDExplicitGamma.Inverse
