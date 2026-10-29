module

public import ASDExplicitGamma.Scalar.OldHessianTrialConcreteTrial
public import ASDExplicitGamma.Native.OldSignedActualTrialExpansion
public import ASDExplicitGamma.Native.OldSignedEnergyPairingAlgebra

/-! The physical bottom-load Hessian is below the fully expanded mixed trial
`R_mix - lambda Z`, with every signed cross term retained. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian
noncomputable section

/-- Left scalar homogeneity of the actual normalized energy pairing. -/
theorem old_hessian_energy_pairing_smul_left (Q : TriadicCube 2) (nu sigma : ℝ)
    (k : ResponseCoefficient (openCubeSet Q)) (c : ℝ) (F G : Vec 2 → BlockVec 2) :
    oldSignedEnergyPairing Q nu sigma k (c • F) G = c * oldSignedEnergyPairing Q nu sigma k F G := by
  unfold oldSignedEnergyPairing
  rw [← volumeAverage_smul]
  apply congrArg (volumeAverage (openCubeSet Q))
  funext x
  exact blockVecDot_smul_left c (F x) _

/-- Right scalar homogeneity of the actual normalized energy pairing. -/
theorem old_hessian_energy_pairing_smul_right (Q : TriadicCube 2) (nu sigma : ℝ)
    (k : ResponseCoefficient (openCubeSet Q)) (c : ℝ) (F G : Vec 2 → BlockVec 2) :
    oldSignedEnergyPairing Q nu sigma k F (c • G) = c * oldSignedEnergyPairing Q nu sigma k F G := by
  rw [old_signed_energy_pairing_symm,old_hessian_energy_pairing_smul_left,
    old_signed_energy_pairing_symm]

/-- Mode-by-mode trial inequality for the original bottom load. -/
theorem old_hessian_mode_trial (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (i : Fin 2) (lam : ℝ) :
    let E := oldSignedEnergyPairing Q nu sigma k
    let C := oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
    let S := oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (0,basisVec i)
    let R := oldHessianMixedBottomResidual Q coarse (coarse+1) nu sigma hnu hsigma k b L n i
    let Z := oldSignedPatchedMinus Q (coarse+1) nu sigma hnu hsigma k b L n i
    oldSignedPhysicalHessian Q nu sigma hnu hsigma k (0,basisVec i) b L n ≤
      E R R+lam^2*E Z Z-2*lam*E R Z+2*E S (C R)-2*lam*E S (C Z) := by
  intro E C S R Z
  have hR : MemBlockL2 (openCubeSet Q) R :=
    old_hessian_mixed_bottom_residual_memL2 Q coarse (coarse+1) nu sigma hnu hsigma k b L n i
  have hZ : MemBlockL2 (openCubeSet Q) Z :=
    (old_hessian_fine_minus_variation Q (coarse+1) nu sigma hnu hsigma k b L n i).1
  have hS : MemBlockL2 (openCubeSet Q) S := Lp.memLp S
  have hh := old_hessian_actual_mixed_bottom_trial Q coarse (coarse+1) nu sigma hnu hsigma k b L n i lam
  rw [old_signed_trial_value_fields] at hh
  have hlZ : MemBlockL2 (openCubeSet Q) (lam • Z) := hZ.const_smul lam
  have he := old_signed_bottom_field_trial_expansion Q nu sigma hnu hsigma k b L n hS hR hlZ
  refine hh.trans_eq ?_
  change E (R-lam • Z) (R-lam • Z)+2*E S (C (R-lam • Z))=_
  rw [he,old_hessian_energy_pairing_smul_left,old_hessian_energy_pairing_smul_right,
    old_hessian_energy_pairing_smul_right,map_smul,old_hessian_energy_pairing_smul_right]
  ring

end
end ASDExplicitGamma.Scalar
