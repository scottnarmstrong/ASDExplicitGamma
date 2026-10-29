module

public import ASDExplicitGamma.Native.OldSignedPhysicalPotential
public import ASDExplicitGamma.Scalar.Lambda8Q3ParentOscillation

/-! The whole-plane projected modes have actual H1 potentials on every
source square, with their exact physical kernel gradients. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian
noncomputable section

/-- The physical whole-plane mode potential restricted to the actual square. -/
def oldSignedProjectedModePotentialH1 (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (w : WhiteNoise) (j : Fin 2) : H1Function (openCubeSet Q) :=
  H1Function.ofContDiffOnIsOpenBoundedConvexDomain (isOpenBoundedConvexDomain_openCubeSet Q)
    (old_signed_physical_mode_potential_contDiff b L w j)

/-- The H1 representative has the actual spectral-kernel gradient, with
the correct shell-length normalization at every point. -/
theorem old_signed_projected_mode_potential_grad (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (w : WhiteNoise) (j i : Fin 2) (x : Vec 2) :
    (oldSignedProjectedModePotentialH1 Q b L w j).grad x i =
      inner ℝ w (oldSignedProjectedWhiteKernel b L (L.1⁻¹ • x) i j) := by
  change (fderiv ℝ (oldSignedPhysicalModePotential b L w j) x) (basisVec i)=_
  rw [(old_signed_physical_mode_potential_hasFDerivAt b L w j x).fderiv]
  fin_cases i <;> simp [oldSignedPhysicalModeDerivative,basisVec_apply]

end
end ASDExplicitGamma.Native
