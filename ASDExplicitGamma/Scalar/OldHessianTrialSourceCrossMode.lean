module

public import ASDExplicitGamma.Scalar.OldHessianTrialSourceCellCrossSplit
public import ASDExplicitGamma.Scalar.OldHessianTrialPatchedSourcePairing
public import ASDExplicitGamma.Scalar.OldHessianTrialFullAffineSplit

/-! Exact signed affine/oscillatory decomposition of the actual trial cross. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Main
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The genuine original source/oscillatory receiver cross for two loads. -/
def oldHessianSourceOscillationSpatialMode (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) : ℝ :=
  oldSignedCellAverage Q (coarse+1) (fun U => ∑ i : Fin 2,cubeAverage U.val (fun x => vecDot
    (oldHessianMinusOscillationColumn Q (coarse+1) nu sigma hnu hsigma k b L (n,i) U x)
    (oldHessianFullModeColumn Q coarse nu sigma hnu hsigma k b L (n,i) x)))

/-- Exact mode identity with both source signs and the original fine Z.
In particular the affine term has positive 2lambda and the actual signed
oscillatory source term has negative 2lambda in the trial expansion. -/
theorem old_hessian_source_cross_mode (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (lam : ℝ) :
    -(2*lam)*(∑ i : Fin 2,oldSignedEnergyPairing Q nu sigma k
      (oldHessianMixedBottomResidual Q coarse (coarse+1) nu sigma hnu hsigma k b L n i)
      (oldSignedPatchedMinus Q (coarse+1) nu sigma hnu hsigma k b L n i))=
      (2*lam)*oldHessianFullAffineSpatialMode Q coarse nu sigma hnu hsigma k b L n-
      (2*lam)*oldHessianSourceOscillationSpatialMode Q coarse nu sigma hnu hsigma k b L n := by
  let A := fun (i : Fin 2) (U : OldSignedCellIndex Q (coarse+1)) => cubeAverage U.val (fun x => vecDot
    (oldHessianMinusAffineSpatialColumn Q (coarse+1) nu sigma hnu hsigma k b L (n,i) U x)
    (oldHessianFullModeColumn Q coarse nu sigma hnu hsigma k b L (n,i) x))
  let O := fun (i : Fin 2) (U : OldSignedCellIndex Q (coarse+1)) => cubeAverage U.val (fun x => vecDot
    (oldHessianMinusOscillationColumn Q (coarse+1) nu sigma hnu hsigma k b L (n,i) U x)
    (oldHessianFullModeColumn Q coarse nu sigma hnu hsigma k b L (n,i) x))
  have he (i : Fin 2) : oldSignedEnergyPairing Q nu sigma k
      (oldHessianMixedBottomResidual Q coarse (coarse+1) nu sigma hnu hsigma k b L n i)
      (oldSignedPatchedMinus Q (coarse+1) nu sigma hnu hsigma k b L n i)=
      oldSignedCellAverage Q (coarse+1) (fun U => A i U+O i U) := by
    rw [old_hessian_actual_source_pairing_partition]
    apply congrArg (oldSignedCellAverage Q (coarse+1))
    funext U
    exact old_hessian_source_cell_cross_split Q coarse nu sigma hnu hsigma k b L (n,i) U
  have hA : oldHessianFullAffineSpatialMode Q coarse nu sigma hnu hsigma k b L n=
      -(oldSignedCellAverage Q (coarse+1) (fun U => ∑ i : Fin 2,A i U)) := by
    unfold oldHessianFullAffineSpatialMode
    dsimp only [A]
    unfold oldSignedCellAverage
    simp only [vecDot,Pi.neg_apply,mul_neg,Finset.sum_neg_distrib,cubeAverage_eq_integral_normalizedCubeMeasure,integral_neg]
  simp_rw [he,old_signed_cell_average_add]
  rw [Finset.sum_add_distrib,←old_signed_cell_average_sum,←old_signed_cell_average_sum,hA]
  change -(2*lam)*(_+_)=(2*lam)*(-_)-(2*lam)*(oldSignedCellAverage Q (coarse+1) (fun U => ∑ i : Fin 2,O i U))
  ring

end
end ASDExplicitGamma.Scalar
