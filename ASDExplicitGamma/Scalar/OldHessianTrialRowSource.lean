module

public import ASDExplicitGamma.Native.OldSignedSourceMultiplier
public import ASDExplicitGamma.Native.OldSignedShearGauge

/-! The complete unchanged fine source row for arbitrary genuine H10
potentials, including the actual mixed coarse split v-phi. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Main Triadic Gaussian Inverse Variational
noncomputable section

/-- The fine localized source has genuine positive-Haar convergence on each
physical fine cell. This applies to the actual v-phi without any estimate. -/
theorem old_hessian_localized_row_positive (n : ℤ) (fine : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (u : H10Function (openCubeSet (originCube 2 n)))
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) fine)
    (j : whiteBasisIndex) (i : Fin 2) :
    Summable (fun k : ℕ => (Real.sqrt 3)^(k+1)*energy U (cubeIncrement U (k+1)
      (fun x => (oldSignedLocalizedPotentialShear (diagInterpolant (originCube 2 n) fine)
        (mainQ3DirectionW2 (originCube 2 n) b L (whiteBasis j)).value u.toH1Function x).2 i))) := by
  simpa only [old_signed_zero_affine_potential,oldSignedLocalizedPotentialShear,Pi.neg_apply] using
    old_signed_q3_row_positive n b L fine 0 u U hU j i

/-- The literal signed pure-second source has exactly the original complete
Gaussian row energy. No cell boundary or constant mode is removed. -/
theorem old_hessian_localized_row_energy_eq (n : ℤ) (fine : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (u : H10Function (openCubeSet (originCube 2 n)))
    (j : whiteBasisIndex) :
    descendantsAverage (originCube 2 n) fine (fun U => vectorPositiveHaarEnergy U
      (fun x => (oldSignedLocalizedPotentialShear (diagInterpolant (originCube 2 n) fine)
        (mainQ3DirectionW2 (originCube 2 n) b L (whiteBasis j)).value u.toH1Function x).2)) =
      pureFluxMainQ3RowEnergy n b 1 L fine 0 u j := by
  simp only [pureFluxMainQ3RowEnergy,pureFluxMainQ3BasisFrameMultiplier,inv_one,one_smul,
    old_signed_zero_affine_potential]
  apply congrArg (descendantsAverage (originCube 2 n) fine)
  funext U
  simp only [oldSignedLocalizedPotentialShear,vectorPositiveHaarEnergy,Pi.neg_apply,primalEnergy_neg]

/-- The complete fine source row obeys A² times the complete fine broken
weak energy of its actual potential, before stochastic source bounds enter. -/
theorem old_hessian_localized_row_energy (n : ℤ) (fine : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (u : H10Function (openCubeSet (originCube 2 n))) :
    let E := fun j => descendantsAverage (originCube 2 n) fine (fun U => vectorPositiveHaarEnergy U
      (fun x => (oldSignedLocalizedPotentialShear (diagInterpolant (originCube 2 n) fine)
        (mainQ3DirectionW2 (originCube 2 n) b L (whiteBasis j)).value u.toH1Function x).2))
    Summable E ∧ (∑' j,E j) ≤ oldSignedSourceMultiplier (originCube 2 n) fine b L^2*
      lemmaVTiledWeakEnergy (originCube 2 n) fine u.toH1Function.grad := by
  intro E
  have he : E=pureFluxMainQ3RowEnergy n b 1 L fine 0 u :=
    funext (old_hessian_localized_row_energy_eq n fine b L u)
  rw [he]
  simpa only [old_signed_zero_affine_potential] using old_signed_q3_row_energy_bound n b L fine 0 u

end
end ASDExplicitGamma.Scalar
