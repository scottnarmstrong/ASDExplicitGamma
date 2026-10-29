module

public import ASDExplicitGamma.Main.PartialInsertion
public import ASDExplicitGamma.Variational.AdapterMu

/-! The actual OLD-frame inverse trace as a polynomially controlled C2 heat test. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Variational
open Algsuperdiff.Section3

/-- The physical lower-right trace in a fixed deterministic frame. -/
noncomputable def mainInverseObservable (n : ℤ) (nu sigma : ℝ) :
    C(closure (cubeSet (originCube 2 n)), ℝ) → ℝ := fun k =>
  sigma * Matrix.trace (coarseBlockMatrix (cubeSet (originCube 2 n))
    (responsePlanarCoefficientField nu
      (ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ k))).lowerRight

/-- The inverse test is precisely the sum of the two pure-flux variational energies. -/
theorem mainInverseObservable_eq_twoLoad (n : ℤ) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    mainInverseObservable n nu sigma k =
      ∑ i : Fin 2, responseFrameEnergyObservable (measurableSet_cubeSet (originCube 2 n))
        (volume_cubeSet_toReal_pos (originCube 2 n)) nu sigma hnu hsigma (0, Pi.single i 1)
        (ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ k) := by
  simp_rw [responseFrameEnergyObservable_eq_frameCoarseQuadratic]
  simp [mainInverseObservable, frameMatrix, Matrix.trace, Matrix.diag_apply,
    blockVecDot, blockMatVecMul, vecDot, matVecMul, Fin.sum_univ_two]
  ring

/-- The two-load inverse trace has exactly the C2 polynomial control required
by the Gaussian heat theorem, at fixed positive molecular viscosity. -/
theorem mainInverseObservable_hasPolynomiallyBoundedC2Derivatives (n : ℤ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma) :
    Gaussian.HasPolynomiallyBoundedC2Derivatives (mainInverseObservable n nu sigma) := by
  let L := (ContinuousMap.linearIsometryBoundedOfCompact
    (closure (cubeSet (originCube 2 n))) ℝ ℝ).toLinearIsometry
  let E (i : Fin 2) : C(closure (cubeSet (originCube 2 n)), ℝ) → ℝ := fun k =>
    responseFrameEnergyObservable (measurableSet_cubeSet (originCube 2 n))
      (volume_cubeSet_toReal_pos (originCube 2 n)) nu sigma hnu hsigma (0, Pi.single i 1) (L k)
  have hE (i : Fin 2) : Gaussian.HasPolynomiallyBoundedC2Derivatives (E i) :=
    Gaussian.hasPolynomiallyBoundedC2Derivatives_comp_isometry L
      (responseFrameEnergyObservable_hasPolynomiallyBoundedC2Derivatives
        (measurableSet_cubeSet (originCube 2 n)) (volume_cubeSet_toReal_pos (originCube 2 n))
        nu sigma hnu hsigma (0, Pi.single i 1))
  have heq : mainInverseObservable n nu sigma = fun k => E 0 k + E 1 k := by
    funext k
    simpa only [Fin.sum_univ_two, E, L, LinearIsometryEquiv.coe_toLinearIsometry] using
      mainInverseObservable_eq_twoLoad n nu sigma hnu hsigma k
  rw [heq]
  exact Gaussian.hasPolynomiallyBoundedC2Derivatives_add (hE 0) (hE 1)

/-- The literal model inverse trace, in the completed OLD true frame. -/
noncomputable def mainInsertionInverseTrace (M : ABKModel 2) (m n : ℤ) (t : ℝ)
    (omega : Cutoff.CutoffSample 2) : ℝ :=
  (Annealed.sigmaBar M m : ℝ) * Matrix.trace
    (coarseBlockMatrix (cubeSet (originCube 2 n)) (Model.partialInsertedCoefficient M m t omega).toFun).lowerRight

end ASDExplicitGamma.Main
