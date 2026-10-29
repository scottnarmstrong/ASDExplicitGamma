module

public import ASDExplicitGamma.Scalar.UpperCellEnergyPrincipalResponse
public import ASDExplicitGamma.Variational.AdapterConstantSkew
public import Homogenization.CoarseGraining.CoarseBounds.AeBridge

/-! Exact constant-skew gauge of the physical principal projection. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response Variational MeasureTheory
noncomputable section

/-- The projected constant-load energy is twice the literal variational infimum. -/
theorem upper_cell_constant_projection_twice_mu
    (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    let D := scalarFrameRealization Q nu sigma hnu hsigma k
    let S := scalarProjectionResidual Q nu sigma hnu hsigma k
      (blockVecToHilbertBlockL2Const (U := openCubeSet Q) P)
    D.energyBilin S S = 2*Mu (openCubeSet Q) P
      (responseFramePlanarCoefficientField nu sigma k) := by
  dsimp only
  rw [upper_cell_constant_projection_eq_minimizer]
  have hm := lemmaV_canonical_muCandidate_eq_Mu (isOpenBoundedConvexDomain_openCubeSet Q)
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
      nu sigma hnu hsigma k)
    (show 0 < (volume (openCubeSet Q)).toReal by
      rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) P
  change (scalarFrameRealization Q nu sigma hnu hsigma k).muCandidate P = _ at hm
  rw [← hm]
  generalize scalarFrameRealization Q nu sigma hnu hsigma k = D
  change _ = 2*quadraticEnergy D.energyBilin (D.minimizerMap P)
  unfold quadraticEnergy
  ring

/-- Removing the normalized constant skew g from a physical coefficient
requires the exact load transform (p,q) -> (p,q-g J p). -/
theorem upper_cell_principal_constant_gauge
    (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (g : ℝ) (P : BlockVec 2) :
    let shifted := k + BoundedContinuousFunction.const (closure (openCubeSet Q)) (sigma*g)
    let Dnew := scalarFrameRealization Q nu sigma hnu hsigma shifted
    let Dold := scalarFrameRealization Q nu sigma hnu hsigma k
    let Snew := scalarProjectionResidual Q nu sigma hnu hsigma shifted
      (blockVecToHilbertBlockL2Const (U := openCubeSet Q) P)
    let Sold := scalarProjectionResidual Q nu sigma hnu hsigma k
      (blockVecToHilbertBlockL2Const (U := openCubeSet Q) (constantSkewLoad g P))
    Dnew.energyBilin Snew Snew = Dold.energyBilin Sold Sold := by
  dsimp only
  rw [upper_cell_constant_projection_twice_mu,
    upper_cell_constant_projection_twice_mu]
  congr 1
  have he : responseFramePlanarCoefficientField nu sigma
      (k + BoundedContinuousFunction.const (closure (openCubeSet Q)) (sigma*g)) =ᵐ[
        volume.restrict (openCubeSet Q)]
      (fun x => responsePlanarCoefficient (nu/sigma) (responseCoefficientExtension k x/sigma+g)) := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    simp only [responseFramePlanarCoefficientField]
    rw [responseCoefficientExtension_add_on _ _ hx,
      responseCoefficientExtension_eq
        (BoundedContinuousFunction.const (closure (openCubeSet Q)) (sigma*g)) hx]
    simp only [BoundedContinuousFunction.const_apply]
    congr 1
    field_simp [hsigma.ne']
  rw [Mu_congr_of_ae_eq he, Mu_constantSkew (nu/sigma) (div_pos hnu hsigma)]
  rfl

/-- Exact gauged upper load. Only the stationary potential correction remains
in its bottom coordinate after subtracting the fresh mean skew. -/
theorem upper_cell_gauged_upper_load (g : ℝ) (e w : Vec 2) :
    constantSkewLoad g (e, g • matVecMul responsePlanarJ e + w) = (e,w) := by
  change (e, (g • matVecMul responsePlanarJ e + w) - g • matVecMul responsePlanarJ e) = (e,w)
  rw [add_sub_cancel_left]

end
end ASDExplicitGamma.Scalar
