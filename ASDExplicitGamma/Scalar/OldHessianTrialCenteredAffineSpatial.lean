module

public import ASDExplicitGamma.Scalar.OldHessianTrialCenteredModeColumns
public import ASDExplicitGamma.Scalar.OldHessianTrialAffineReceiverColumns
public import ASDExplicitGamma.Scalar.OldHessianTrialBrokenModePairing

/-! Actual centered-source/original-affine-receiver pairing before expectation. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Signed physical pairing of one centered source and original affine
minus receiver, retaining its actual fine-cell dependence. -/
def oldHessianCenteredAffineSpatialTerm (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (p : whiteBasisIndex×Fin 2) : ℝ :=
  oldSignedCellAverage Q (coarse+1) (fun U => cubeAverage U.val (fun x =>
    vecDot (oldHessianMinusAffineSpatialColumn Q (coarse+1) nu sigma hnu hsigma k b L p U x)
      (oldHessianCenteredModeColumn Q coarse nu sigma hnu hsigma k b L p U.val x)))

/-- Complete signed affine residual pairing: actual source convergence and
regularity are proved internally; a pointwise receiver convergence input is
consumed here and supplied by the stochastic bank in the physical export. -/
theorem old_hessian_centered_affine_spatial_pairing (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (hreceiver : Summable (oldHessianMinusAffineSpatialEnergy Q (coarse+1) nu sigma hnu hsigma k b L)) :
    Summable (oldHessianCenteredAffineSpatialTerm Q coarse nu sigma hnu hsigma k b L) ∧
      |∑' p,oldHessianCenteredAffineSpatialTerm Q coarse nu sigma hnu hsigma k b L p|≤
        Real.sqrt (oldHessianCenteredSpatialEnergy Q coarse nu sigma hnu hsigma k b L)*
          Real.sqrt (∑' p,oldHessianMinusAffineSpatialEnergy Q (coarse+1) nu sigma hnu hsigma k b L p) := by
  let G := oldHessianMinusAffineSpatialColumn Q (coarse+1) nu sigma hnu hsigma k b L
  let F := fun p (U : OldSignedCellIndex Q (coarse+1)) =>
    oldHessianCenteredModeColumn Q coarse nu sigma hnu hsigma k b L p U.val
  have hG p U i := old_hessian_minus_affine_spatial_column_memLp Q (coarse+1) nu sigma hnu hsigma k b L p U i
  have hF p (U : OldSignedCellIndex Q (coarse+1)) i :=
    (old_hessian_centered_mode_regular Q coarse nu sigma hnu hsigma k b L p U.val U.property i).1
  have hpos p (U : OldSignedCellIndex Q (coarse+1)) i :=
    (old_hessian_centered_mode_regular Q coarse nu sigma hnu hsigma k b L p U.val U.property i).2
  have hsource := old_hessian_centered_mode_series Q coarse nu sigma hnu hsigma k b L
  have hFs : Summable (fun p => oldSignedCellAverage Q (coarse+1)
      (fun U => vectorPositiveHaarEnergy U.val (F p U))) := by
    have hs : Summable (fun p => oldHessianCenteredModeEnergy Q coarse nu sigma hnu hsigma k b L p) := hsource.1
    simp_rw [old_hessian_centered_mode_energy_average] at hs
    exact hs
  have hh := old_hessian_broken_mode_pairing Q (coarse+1) G F hG hF hpos hreceiver hFs
  have he : (∑' p,oldSignedCellAverage Q (coarse+1) (fun U => vectorPositiveHaarEnergy U.val (F p U)))=
      oldHessianCenteredSpatialEnergy Q coarse nu sigma hnu hsigma k b L := by
    dsimp only [F]
    simp_rw [←old_hessian_centered_mode_energy_average]
    exact hsource.2
  rw [he] at hh
  exact ⟨hh.1,hh.2.trans_eq (by
    dsimp only [G,oldHessianMinusAffineSpatialEnergy]
    exact mul_comm _ _)⟩

end
end ASDExplicitGamma.Scalar
