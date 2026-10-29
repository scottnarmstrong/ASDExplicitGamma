module

public import ASDExplicitGamma.Triadic.SensitivityODEPath

/-! Pointwise response derivative estimates along the sensitivity path. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory ASDExplicitGamma.Response
open Homogenization.Book.Ch02 Homogenization.Book.Ch04
open Algsuperdiff.Frozen.Section24

noncomputable section

/-- The pointwise response derivative is controlled by the root sensitivity
coefficient and the root inverse-lambda, uniformly over descendants. -/
theorem sensitivity_descendant_responseJ_deriv_abs_le
    {Q R : TriadicCube 2} {j : ℕ}
    (ν : ℝ) (hν : 0 < ν) (k kH : ResponseCoefficient (openCubeSet Q))
    (h : PlanarW2Infinity Q)
    (hkH : responseCoefficientExtension kH =ᵐ[
      volume.restrict (openCubeSet Q)] h.value.toFun)
    (hR : R ∈ descendantsAtDepth Q j) (q : Vec 2)
    (u : ℝ) (hu : 0 < u) (hu4 : u ≤ 1 / 4) (t : ℝ) :
    |deriv (fun τ => responseJ (Book.Ch02.cubeDomain R)
      (sensitivityBookCoeffOn R ν hν
        (sensitivityResponseCoefficientPath
          (sensitivityResponseCoefficientRestrict k hR)
          (sensitivityResponseCoefficientRestrict kH hR) τ)) 0 q) t| ≤
      sensitivityB2 * sensitivityDsharp Q h *
        (Book.Ch02.lambdaSqFinite Q u 2
          (sensitivityPathFamily ν hν k kH t))⁻¹ *
        responseJ (Book.Ch02.cubeDomain R)
          (sensitivityBookCoeffOn R ν hν
            (sensitivityResponseCoefficientPath
              (sensitivityResponseCoefficientRestrict k hR)
              (sensitivityResponseCoefficientRestrict kH hR) t)) 0 q := by
  let kR := sensitivityResponseCoefficientRestrict k hR
  let kHR := sensitivityResponseCoefficientRestrict kH hR
  let hlocal := h.restrict hR
  let kt := sensitivityResponseCoefficientPath kR kHR t
  let a := sensitivityBookCoeffOn R ν hν kt
  let D := sensitivityDsharp R hlocal
  let L := (Book.Ch02.lambdaSqFinite R u 2
    (sensitivityCoefficientFamily ν hν kt))⁻¹
  let y := responseJ (Book.Ch02.cubeDomain R) a 0 q
  have hlocalDeriv := sensitivity_coarse_derivative_inverseBlock_bound
    R ν hν kt hlocal u hu hu4 q
  have hDsharp : 0 ≤ D := by
    dsimp [D, sensitivityDsharp, sensitivityD1, sensitivityD2]
    have hK : 0 ≤ sensitivityKappaH := by
      unfold sensitivityKappaH planarC0 planarC1
      positivity
    exact add_nonneg
      (mul_nonneg (mul_nonneg (cubeScaleFactor_pos' R).le
        (Real.sqrt_nonneg _)) (by
          unfold planarGradientLInf planarW1ValueLInf
          exact ENNReal.toReal_nonneg))
      (mul_nonneg hK
        (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)) (by
          unfold planarHessianFrobeniusLInf planarW1DerivativeFrobeniusLInf
          exact ENNReal.toReal_nonneg)))
  have hL : 0 ≤ L := by
    dsimp [L]
    exact inv_nonneg.mpr
      (Book.Ch02.lambdaSq_finite_nonneg R
        (sensitivityCoefficientFamily ν hν kt) hu (by norm_num))
  have hB : 0 ≤ sensitivityB2 := by
    unfold sensitivityB2
    positivity
  have hY : 0 ≤ y := by
    exact Book.Ch02.responseJ_nonneg (Book.Ch02.cubeDomain R) a 0 q
  have hquad : blockVecDot (0, -q)
      (blockMatVecMul
        (Algsuperdiff.Frozen.Section24.coarseMatrixDerivative
          (Book.Ch02.cubeDomain R) a (sensitivityMatrixDirection hlocal)) (0, -q)) =
      vecDot q (matVecMul
        (Algsuperdiff.Frozen.Section24.coarseMatrixDerivative
          (Book.Ch02.cubeDomain R) a (sensitivityMatrixDirection hlocal)).lowerRight q) := by
    calc
      _ = vecDot (-q) (matVecMul
          (Algsuperdiff.Frozen.Section24.coarseMatrixDerivative
            (Book.Ch02.cubeDomain R) a (sensitivityMatrixDirection hlocal)).lowerRight (-q)) := by
        simp only [blockVecDot, blockMatVecMul, matVecMul_zero, zero_add,
          vecDot_zero_left]
      _ = _ := by
        rw [Homogenization.matVecMul_neg, Homogenization.vecDot_neg_left,
          Homogenization.vecDot_neg_right]
        simp
  have hresponse : vecDot q (matVecMul
      (Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain R) a) q) = 2 * y :=
    Algsuperdiff.Section24.Sensitivity.Provider.Lambda.vecDot_matVecMul_sigmaStarInvCoarse
      (Book.Ch02.cubeDomain R) a q
  have hlocal' : |vecDot q (matVecMul
      (Algsuperdiff.Frozen.Section24.coarseMatrixDerivative
        (Book.Ch02.cubeDomain R) a (sensitivityMatrixDirection hlocal)).lowerRight q)| ≤
      sensitivityB2 * D * L * (2 * y) := by
    have hh := hlocalDeriv
    dsimp [D, L, a, kt, sensitivitySkewMatrixDirection,
      Book.Ch02.coarseBlockMatrix_lowerRight] at hh ⊢
    rw [hresponse] at hh
    exact hh
  have hhalf : (1 / 2 : ℝ) * |vecDot q (matVecMul
      (Algsuperdiff.Frozen.Section24.coarseMatrixDerivative
        (Book.Ch02.cubeDomain R) a (sensitivityMatrixDirection hlocal)).lowerRight q)| ≤
      (1 / 2 : ℝ) * (sensitivityB2 * D * L * (2 * y)) :=
    mul_le_mul_of_nonneg_left hlocal' (by norm_num)
  have hprod := sensitivityDsharp_mul_descendant_lambda_inv_le
    ν hν k kH h hR u hu hu4 t
  have hcoeff : 0 ≤ sensitivityB2 * D * L :=
    mul_nonneg (mul_nonneg hB hDsharp) hL
  have hcoeffRoot : sensitivityB2 * D * L ≤
      sensitivityB2 * sensitivityDsharp Q h *
        (Book.Ch02.lambdaSqFinite Q u 2
          (sensitivityPathFamily ν hν k kH t))⁻¹ := by
    have hprod' : D * L ≤ sensitivityDsharp Q h *
        (Book.Ch02.lambdaSqFinite Q u 2
          (sensitivityPathFamily ν hν k kH t))⁻¹ := by
      simpa [D, L, kt, kR, kHR, hlocal] using hprod
    calc
      sensitivityB2 * D * L = sensitivityB2 * (D * L) := by ring
      _ ≤ sensitivityB2 * (sensitivityDsharp Q h *
          (Book.Ch02.lambdaSqFinite Q u 2
            (sensitivityPathFamily ν hν k kH t))⁻¹) :=
        mul_le_mul_of_nonneg_left hprod' hB
      _ = _ := by ring
  have hpathDeriv := sensitivity_descendant_responseJ_hasDerivAt
    ν hν k kH h hkH hR q t
  rw [hpathDeriv.deriv]
  have hquadPath : blockVecDot (0, -q)
      (blockMatVecMul
        (Algsuperdiff.Frozen.Section24.coarseMatrixDerivative
          (Book.Ch02.cubeDomain R)
          (sensitivityBookCoeffOn R ν hν
            (sensitivityResponseCoefficientPath kR kHR t))
          (sensitivitySkewMatrixDirection hlocal).1) (0, -q)) =
      vecDot q (matVecMul
        (Algsuperdiff.Frozen.Section24.coarseMatrixDerivative
          (Book.Ch02.cubeDomain R)
          (sensitivityBookCoeffOn R ν hν
            (sensitivityResponseCoefficientPath kR kHR t))
          (sensitivitySkewMatrixDirection hlocal).1).lowerRight q) := by
    simpa [a, kt, kR, kHR, hlocal, sensitivitySkewMatrixDirection] using hquad
  calc
    |(1 / 2 : ℝ) * blockVecDot (0, -q) (blockMatVecMul
        (Algsuperdiff.Frozen.Section24.coarseMatrixDerivative
          (Book.Ch02.cubeDomain R)
          (sensitivityBookCoeffOn R ν hν
            (sensitivityResponseCoefficientPath kR kHR t))
          (sensitivitySkewMatrixDirection hlocal).1) (0, -q))| =
      (1 / 2 : ℝ) * |vecDot q (matVecMul
        (Algsuperdiff.Frozen.Section24.coarseMatrixDerivative
          (Book.Ch02.cubeDomain R)
          (sensitivityBookCoeffOn R ν hν
            (sensitivityResponseCoefficientPath kR kHR t))
          (sensitivitySkewMatrixDirection hlocal).1).lowerRight q)| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), hquadPath]
    _ ≤ (1 / 2 : ℝ) * (sensitivityB2 * D * L * (2 * y)) := hhalf
    _ = sensitivityB2 * D * L * y := by ring
    _ ≤ (sensitivityB2 * sensitivityDsharp Q h *
        (Book.Ch02.lambdaSqFinite Q u 2
          (sensitivityPathFamily ν hν k kH t))⁻¹) * y :=
      mul_le_mul_of_nonneg_right hcoeffRoot hY
    _ = _ := by rfl


end

end ASDExplicitGamma.Triadic
