module

public import ASDExplicitGamma.Triadic.SensitivityODELambda
public import Homogenization.Book.Ch02.Theorems.BlockCoarseMatrix
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The matrix-valued part of the coarse-sensitivity path. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory ASDExplicitGamma.Response
open Homogenization.Book.Ch02

noncomputable section

/-- Subtract the actual cube mean from a Sobolev sensitivity direction. -/
def sensitivityMeanZeroW2Direction {Q : TriadicCube 2}
    (h : PlanarW2Infinity Q) : PlanarW2Infinity Q where
  value := h.value - h1ConstantOnCube Q (cubeAverage Q h.value.toFun)
  value_memLp_top := by
    have hc : MemLp (fun _ : Vec 2 => cubeAverage Q h.value.toFun) ⊤
        (volume.restrict (openCubeSet Q)) := memLp_const _
    have hm := h.value_memLp_top.sub hc
    change MemLp ((h.value -
      h1ConstantOnCube Q (cubeAverage Q h.value.toFun)).toFun) ⊤ _
    rw [H1Function.sub_toFun, h1ConstantOnCube_toFun]
    exact hm
  gradient := h.gradient
  gradient_eq := by
    intro i
    rw [H1Function.sub_grad, h1ConstantOnCube_grad]
    simpa using h.gradient_eq i

theorem sensitivityMeanZeroW2Direction_mean {Q : TriadicCube 2}
    (h : PlanarW2Infinity Q) :
    cubeAverage Q (sensitivityMeanZeroW2Direction h).value.toFun = 0 := by
  simp only [sensitivityMeanZeroW2Direction, H1Function.sub_toFun,
    h1ConstantOnCube_toFun]
  rw [cubeAverage_sub_const_of_memLp_two Q h.value.memL2_normalizedCubeMeasure]
  ring

theorem sensitivityDsharp_meanZeroW2Direction {Q : TriadicCube 2}
    (h : PlanarW2Infinity Q) :
    sensitivityDsharp Q (sensitivityMeanZeroW2Direction h) =
      sensitivityDsharp Q h := by
  unfold sensitivityDsharp sensitivityD1 sensitivityD2
  rfl

/-- The centered Sobolev representative is realized by adding the corresponding
constant to the bounded-continuous path representative. -/
theorem sensitivityMeanZeroW2Direction_responseRepresentative
    {Q : TriadicCube 2} (kH : ResponseCoefficient (openCubeSet Q))
    (h : PlanarW2Infinity Q)
    (hkH : responseCoefficientExtension kH =ᵐ[
      volume.restrict (openCubeSet Q)] h.value.toFun) :
    let g := -(cubeAverage Q h.value.toFun)
    responseCoefficientExtension
        (kH + BoundedContinuousFunction.const (closure (openCubeSet Q)) g) =ᵐ[
      volume.restrict (openCubeSet Q)]
        (sensitivityMeanZeroW2Direction h).value.toFun := by
  dsimp
  filter_upwards [hkH, ae_restrict_mem (measurableSet_openCubeSet Q)] with x hxrep hx
  rw [responseCoefficientExtension_add_on kH
    (BoundedContinuousFunction.const (closure (openCubeSet Q))
      (-(cubeAverage Q h.value.toFun))) hx,
    responseCoefficientExtension_eq
      (BoundedContinuousFunction.const (closure (openCubeSet Q))
        (-(cubeAverage Q h.value.toFun))) hx, hxrep]
  simp only [sensitivityMeanZeroW2Direction, H1Function.sub_toFun,
    h1ConstantOnCube_toFun]
  simp only [BoundedContinuousFunction.const_apply]
  ring

/-- The full coarse quadratic form at time `t` along the coefficient path. -/
def sensitivityCoarseMatrixPathQuadratic {Q : TriadicCube 2}
    (ν : ℝ) (hν : 0 < ν) (k kH : ResponseCoefficient (openCubeSet Q))
    (P : BlockVec 2) (t : ℝ) : ℝ :=
  blockVecDot P (blockMatVecMul
    (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
      (sensitivityBookCoeffOn Q ν hν
        (sensitivityResponseCoefficientPath k kH t))) P)

theorem sensitivityCoarseMatrixPathQuadratic_nonneg {Q : TriadicCube 2}
    (ν : ℝ) (hν : 0 < ν) (k kH : ResponseCoefficient (openCubeSet Q))
    (P : BlockVec 2) (t : ℝ) :
    0 ≤ sensitivityCoarseMatrixPathQuadratic ν hν k kH P t := by
  by_cases hP : P = 0
  · simp [sensitivityCoarseMatrixPathQuadratic, hP, blockMatVecMul,
      blockVecDot, matVecMul, vecDot]
  · have hpos := (Book.Ch02.blockCoarseMatrixTheory
      (Book.Ch02.cubeDomain Q)
      (sensitivityBookCoeffOn Q ν hν
        (sensitivityResponseCoefficientPath k kH t))).block_matrix_posDef P hP
    exact hpos.le

/-- Differentiating the full quadratic form gives the full derivative-matrix
quadratic form. -/
theorem sensitivityCoarseMatrixPathQuadratic_hasDerivAt {Q : TriadicCube 2}
    (ν : ℝ) (hν : 0 < ν) (k kH : ResponseCoefficient (openCubeSet Q))
    (h : PlanarW2Infinity Q)
    (hkH : responseCoefficientExtension kH =ᵐ[
      volume.restrict (openCubeSet Q)] h.value.toFun)
    (P : BlockVec 2) (t : ℝ) :
    HasDerivAt (sensitivityCoarseMatrixPathQuadratic ν hν k kH P)
      (blockVecDot P (blockMatVecMul
        (Algsuperdiff.Frozen.Section24.coarseMatrixDerivative
          (Book.Ch02.cubeDomain Q)
          (sensitivityBookCoeffOn Q ν hν
            (sensitivityResponseCoefficientPath k kH t))
          (sensitivityMatrixDirection h)) P)) t := by
  let aτ := fun τ : ℝ => sensitivityBookCoeffOn Q ν hν
    (sensitivityResponseCoefficientPath k kH τ)
  let Aτ := fun τ : ℝ => Book.Ch02.coarseBlockMatrix
    (Book.Ch02.cubeDomain Q) (aτ τ)
  let g := sensitivitySkewMatrixDirection h
  have hpath (τ : ℝ) : Book.Ch02.CoeffOn.AEEq (aτ τ)
      (Algsuperdiff.Frozen.Section24.perturbCoeffOn
        (Book.Ch02.cubeDomain Q) (sensitivityBookCoeffOn Q ν hν k) g τ) := by
    exact sensitivityBookCoeffOn_path_aeeq Q ν hν k h kH hkH τ
  have hresp :=
    Algsuperdiff.Section24.Sensitivity.Provider.Response.hasDerivAt_responseJ_perturbCoeffOn_pair
      (by norm_num : 2 ≤ 2) (Book.Ch02.cubeDomain Q)
      (sensitivityBookCoeffOn Q ν hν k) g P.1 (-P.2) t
  have hresponseFun :
      (fun τ => Book.Ch02.responseJ (Book.Ch02.cubeDomain Q) (aτ τ)
        P.1 (-P.2)) =
      (fun τ => Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
        (Algsuperdiff.Frozen.Section24.perturbCoeffOn
          (Book.Ch02.cubeDomain Q) (sensitivityBookCoeffOn Q ν hν k) g τ)
        P.1 (-P.2)) := by
    funext τ
    exact Book.Ch02.responseJ_eq_ofAEEq (hpath τ) P.1 (-P.2)
  rw [← hresponseFun] at hresp
  have hD := sensitivity_coarseMatrixDerivative_eq_of_aeeq
    (aτ t)
    (Algsuperdiff.Frozen.Section24.perturbCoeffOn
      (Book.Ch02.cubeDomain Q) (sensitivityBookCoeffOn Q ν hν k) g t)
    (hpath t) g.1
  rw [← hD] at hresp
  have hformula (τ : ℝ) :
      blockVecDot P (blockMatVecMul (Aτ τ) P) =
        2 * Book.Ch02.responseJ (Book.Ch02.cubeDomain Q) (aτ τ)
          P.1 (-P.2) + 2 * vecDot P.1 (-P.2) := by
    have h := Homogenization.Internal.Ch02.BookCh02.responseJ_eq_block_quadratic
      (Book.Ch02.cubeDomain Q) (aτ τ) P.1 (-P.2)
    have hneg : (-P.1, -P.2) = -P := rfl
    rw [hneg] at h
    have hmv : blockMatVecMul (Aτ τ) (-P) =
        -blockMatVecMul (Aτ τ) P := by
      cases P
      ext i <;> simp [blockMatVecMul, matVecMul_neg] <;> ring
    have hquad : blockVecDot (-P) (blockMatVecMul (Aτ τ) (-P)) =
        blockVecDot P (blockMatVecMul (Aτ τ) P) := by
      rw [hmv]
      have hleft : blockVecDot (-P) (-blockMatVecMul (Aτ τ) P) =
          blockVecDot P (blockMatVecMul (Aτ τ) P) := by
        cases P
        simp [blockVecDot, vecDot_neg_left, vecDot_neg_right,
          vecDot_add_right]
        ring
      exact hleft
    rw [hquad] at h
    linarith
  let f : ℝ → ℝ := fun τ => Book.Ch02.responseJ
    (Book.Ch02.cubeDomain Q) (aτ τ) P.1 (-P.2)
  have hfun : sensitivityCoarseMatrixPathQuadratic ν hν k kH P =
      fun τ => 2 * f τ + 2 * vecDot P.1 (-P.2) := by
    funext τ
    exact hformula τ
  rw [hfun]
  have hmul := hresp.const_mul 2
  have hadd := hmul.add_const (2 * vecDot P.1 (-P.2))
  convert hadd using 1
  · have hp : (P.1, - -P.2) = P := by cases P; simp
    rw [hp]
    change blockVecDot P (blockMatVecMul
      (Algsuperdiff.Frozen.Section24.coarseMatrixDerivative
        (Book.Ch02.cubeDomain Q)
        (sensitivityBookCoeffOn Q ν hν
          (sensitivityResponseCoefficientPath k kH t))
        (sensitivityMatrixDirection h)) P) =
      2 * ((1 / 2 : ℝ) * blockVecDot P (blockMatVecMul
        (Algsuperdiff.Frozen.Section24.coarseMatrixDerivative
          (Book.Ch02.cubeDomain Q)
          (sensitivityBookCoeffOn Q ν hν
            (sensitivityResponseCoefficientPath k kH t))
          (sensitivityMatrixDirection h)) P))
    ring

/-- The centered A-form derivative controls this actual matrix quadratic
form, with the literal inverse-lambda path coefficient. -/
theorem sensitivityCoarseMatrixPathQuadratic_deriv_abs_le {Q : TriadicCube 2}
    (ν : ℝ) (hν : 0 < ν) (k kH : ResponseCoefficient (openCubeSet Q))
    (h : PlanarW2Infinity Q)
    (hkH : responseCoefficientExtension kH =ᵐ[
      volume.restrict (openCubeSet Q)] h.value.toFun)
    (hmean : cubeAverage Q h.value.toFun = 0)
    {u : ℝ} (hu : 0 < u) (hu4 : u ≤ 1 / 4)
    (P : BlockVec 2) (t : ℝ) :
    |deriv (sensitivityCoarseMatrixPathQuadratic ν hν k kH P) t| ≤
      sensitivityA2 * sensitivityDsharp Q h *
        sensitivityPathLambdaInverse ν hν k kH u t *
        sensitivityCoarseMatrixPathQuadratic ν hν k kH P t := by
  have hvar := sensitivity_coarse_derivative_A_bound Q ν hν
    (sensitivityResponseCoefficientPath k kH t) h hmean u hu hu4 P.1 P.2
  rw [(sensitivityCoarseMatrixPathQuadratic_hasDerivAt
    ν hν k kH h hkH P t).deriv]
  simpa [sensitivityCoarseMatrixPathQuadratic, sensitivityPathFamily,
    sensitivityPathLambdaInverse, sensitivityResponseCoefficientPath] using hvar

end

end ASDExplicitGamma.Triadic
