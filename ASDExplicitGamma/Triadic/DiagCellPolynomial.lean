module

public import ASDExplicitGamma.Triadic.DiagCellMoments
public import ASDExplicitGamma.Triadic.PlanarPositiveGradient

/-! Genuine smooth H¹ witnesses and exact gradients for the local bilinear cells. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

theorem diagBilinearPolynomial_explicit (Q : TriadicCube 2) (c : Fin 4 → ℝ) (x : Vec 2) :
    diagBilinearPolynomial Q c x = c 0 + c 1 * diagCenteredCoordinate Q 0 x +
      c 2 * diagCenteredCoordinate Q 1 x +
      c 3 * diagCenteredCoordinate Q 0 x * diagCenteredCoordinate Q 1 x := by
  simp [diagBilinearPolynomial, diagBilinearBasis, Fin.sum_univ_succ]
  ring

theorem diagBilinearPolynomial_contDiff (Q : TriadicCube 2) (c : Fin 4 → ℝ) :
    ContDiff ℝ 1 (diagBilinearPolynomial Q c) := by
  have heq := funext (diagBilinearPolynomial_explicit Q c)
  rw [heq]
  unfold diagCenteredCoordinate
  fun_prop

/-- A genuine H¹ cell polynomial, with its actual classical weak derivative. -/
def diagBilinearH1 (Q : TriadicCube 2) (c : Fin 4 → ℝ) : H1Function (openCubeSet Q) :=
  H1Function.ofContDiffOnIsOpenBoundedConvexDomain (isOpenBoundedConvexDomain_openCubeSet Q)
    (diagBilinearPolynomial_contDiff Q c)

@[simp] theorem diagBilinearH1_toFun (Q : TriadicCube 2) (c : Fin 4 → ℝ) :
    (diagBilinearH1 Q c).toFun = diagBilinearPolynomial Q c := rfl

theorem diagCenteredCoordinate_hasFDerivAt (Q : TriadicCube 2) (i : Fin 2) (x : Vec 2) :
    HasFDerivAt (diagCenteredCoordinate Q i)
      ((cubeScaleFactor Q)⁻¹ • (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ)) x := by
  convert (((hasFDerivAt_apply (𝕜 := ℝ) i x).sub_const (cubeCorner Q i)).const_mul
    (cubeScaleFactor Q)⁻¹).sub_const (1/2) using 1
  funext y
  unfold diagCenteredCoordinate
  ring

/-- Exact derivative, including the mixed centered term. -/
theorem diagBilinearH1_grad (Q : TriadicCube 2) (c : Fin 4 → ℝ) (x : Vec 2) (i : Fin 2) :
    (diagBilinearH1 Q c).grad x i =
      if i = 0 then (c 1 + c 3 * diagCenteredCoordinate Q 1 x) / cubeScaleFactor Q
      else (c 2 + c 3 * diagCenteredCoordinate Q 0 x) / cubeScaleFactor Q := by
  have h0 := diagCenteredCoordinate_hasFDerivAt Q 0 x
  have h1 := diagCenteredCoordinate_hasFDerivAt Q 1 x
  have hp := (((hasFDerivAt_const (c 0) x).add (h0.const_mul (c 1))).add
    (h1.const_mul (c 2))).add ((h0.const_mul (c 3)).mul h1)
  change (fderiv ℝ (diagBilinearPolynomial Q c) x) (basisVec i) = _
  have hfun : diagBilinearPolynomial Q c =
      (((fun _ : Vec 2 => c 0) + fun y => c 1 * diagCenteredCoordinate Q 0 y) +
        fun y => c 2 * diagCenteredCoordinate Q 1 y) +
        (fun y => c 3 * diagCenteredCoordinate Q 0 y) * diagCenteredCoordinate Q 1 := by
    funext y
    exact diagBilinearPolynomial_explicit Q c y
  rw [hfun, hp.fderiv]
  fin_cases i <;> simp [basisVec] <;> ring

/-- Values determine the weak gradient on a cell, without assuming a trace. -/
theorem diagH1_grad_eq_polynomial (Q : TriadicCube 2) (u : H1Function (openCubeSet Q))
    (c : Fin 4 → ℝ) (hu : Set.EqOn u.toFun (diagBilinearPolynomial Q c) (openCubeSet Q))
    (i : Fin 2) :
    (fun x => u.grad x i) =ᵐ[volume.restrict (openCubeSet Q)]
      (fun x => (diagBilinearH1 Q c).grad x i) := by
  apply HasWeakPartialDerivOn.ae_eq (isOpen_openCubeSet Q)
    (locallyIntegrableOn_of_locallyIntegrable_restrict
      ((u.gradMemL2 i).locallyIntegrable (by norm_num)))
    (locallyIntegrableOn_of_locallyIntegrable_restrict
      (((diagBilinearH1 Q c).gradMemL2 i).locallyIntegrable (by norm_num)))
  · exact u.hasWeakGradient i
  · intro φ hφ hs hsub
    rw [← (diagBilinearH1 Q c).hasWeakGradient i φ hφ hs hsub]
    apply setIntegral_congr_fun (measurableSet_openCubeSet Q)
    intro x hx
    exact congrArg (fun v => v * (fderiv ℝ φ x) (basisVec i)) (hu hx)

end

end ASDExplicitGamma.Triadic
