module

public import ASDExplicitGamma.Native.OldSignedPatchProjection

/-! Projection bounds obtained from the genuine compatible difference,
with its exact energy still retained for paired trace cancellation. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic
noncomputable section

/-- Subtract the actual affine patch and apply the inverse-depth maximum
bound. This statement serves both the ordinary and reciprocal comparison. -/
theorem old_signed_patch_projection_bound (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (S : Vec 2 → BlockVec 2) (hS : ScalarCompatible (openCubeSet Q) S) :
    let R := oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P) (memLp_const P)
    (∑ i, energy Q (cubeProjection Q depth (fun x => (S x).1 i-P.1 i))) ≤
      lemmaVInverseDepthMax Q (responseFramePlanarCoefficientField nu sigma k) depth *
        oldSignedEnergyPairing Q nu sigma k (S-R) (S-R) := by
  intro R
  let D := S-R
  have hc : ScalarCompatible (openCubeSet Q) D := old_signed_compatible_sub hS
    (old_signed_patch_compatible Q depth nu sigma hnu hsigma k P)
  let W : BlockState 2 := ⟨fun x => (D x).1,fun x => (D x).2⟩
  have hh := compatible_projectionEnergy_bound
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
      nu sigma hnu hsigma k) W hc.2.1 hc.2.2 hc.1 depth
  have hmean : cubeAverage Q (blockPairingIntegrand
      (responseFramePlanarCoefficientField nu sigma k) W W)=oldSignedEnergyPairing Q nu sigma k D D := by
    rw [cubeAverage_eq_integralAverage_openCubeSet]
    rfl
  rw [hmean] at hh
  have he : (∑ i,energy Q (cubeProjection Q depth (fun x => W.potential x i)))=
      ∑ i,energy Q (cubeProjection Q depth (fun x => (S x).1 i-P.1 i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (energy Q) (old_signed_patch_projection_eq Q depth nu sigma hnu hsigma k P S hS.1 i)
  rw [he] at hh
  exact hh

end
end ASDExplicitGamma.Native
