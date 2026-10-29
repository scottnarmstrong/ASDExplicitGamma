module

public import ASDExplicitGamma.Scalar.OldHessianTrialConcreteTrial
public import ASDExplicitGamma.Native.OldSignedEnergyPairingAlgebra

/-! Exact source removal in the original weighted complementary projection. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Main
noncomputable section

/-- Orthogonality removes the projection only on the source side while
retaining the original fine receiver. -/
theorem old_hessian_residual_source_cross (Q : TriadicCube 2) (fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F G : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G) :
    oldSignedEnergyPairing Q nu sigma k
      (oldSignedLocalResidual Q fine nu sigma hnu hsigma k F hF)
      (oldSignedLocalResidual Q fine nu sigma hnu hsigma k G hG)=
    oldSignedEnergyPairing Q nu sigma k F
      (oldSignedLocalResidual Q fine nu sigma hnu hsigma k G hG) := by
  rw [old_signed_energy_pairing_symm Q nu sigma k,
    old_signed_local_residual_pairing Q fine nu sigma hnu hsigma k G F hG hF,
    old_signed_energy_pairing_symm Q nu sigma k]

/-- The actual mixed residual and original Z have the literal source/Z
cross, before its affine and oscillatory reciprocal decomposition. -/
theorem old_hessian_actual_residual_source_cross (Q : TriadicCube 2) (coarse fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (i : Fin 2) :
    oldSignedEnergyPairing Q nu sigma k
      (oldHessianMixedBottomResidual Q coarse fine nu sigma hnu hsigma k b L n i)
      (oldSignedPatchedMinus Q fine nu sigma hnu hsigma k b L n i)=
    oldSignedEnergyPairing Q nu sigma k
      (oldHessianMixedBottomSource Q coarse fine nu sigma hnu hsigma k b L n i)
      (oldSignedPatchedMinus Q fine nu sigma hnu hsigma k b L n i) :=
  old_hessian_residual_source_cross Q fine nu sigma hnu hsigma k _ _
    (old_hessian_mixed_bottom_source_memL2 Q coarse fine nu sigma hnu hsigma k b L n i)
    (old_signed_flat_minus_block_memL2 Q b L n i)

end
end ASDExplicitGamma.Scalar
