module

public import ASDExplicitGamma.Triadic.SensitivityODEMatrix
public import ASDExplicitGamma.Numerics.Enclosures
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Integrating the matrix-valued coarse-sensitivity path. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory ASDExplicitGamma.Response
open Homogenization.Book.Ch02

noncomputable section

/-- Scalar multiplication of a doubled block matrix, componentwise. -/
def sensitivityBlockScale {d : ℕ} (c : ℝ) (A : BlockMat d) : BlockMat d :=
  { upperLeft := c • A.upperLeft
    upperRight := c • A.upperRight
    lowerLeft := c • A.lowerLeft
    lowerRight := c • A.lowerRight }

theorem sensitivityBlockScale_quadratic {d : ℕ} (c : ℝ) (A : BlockMat d)
    (P : BlockVec d) :
    blockVecDot P (blockMatVecMul (sensitivityBlockScale c A) P) =
      c * blockVecDot P (blockMatVecMul A P) := by
  cases P with
  | mk p q =>
      simp only [sensitivityBlockScale, blockMatVecMul, blockVecDot,
        smul_matVecMul, vecDot_add_right, vecDot_smul_right]
      ring

/-- Exact integral of the rational coefficient appearing after Bihari. -/
theorem sensitivity_rational_rate_integral {A B x : ℝ}
    (hB : 0 < B) (hx : 0 ≤ x) (hsmall : B * x < 1) :
    (∫ t in (0 : ℝ)..1, A * x / (1 - B * x * t)) =
      -(A / B) * Real.log (1 - B * x) := by
  let F : ℝ → ℝ := fun t => -(A / B) * Real.log (1 - B * x * t)
  let r : ℝ → ℝ := fun t => A * x / (1 - B * x * t)
  have harg (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
      0 < 1 - B * x * t := by
    have ht0 : 0 ≤ t := by
      rcases Set.mem_uIcc.mp ht with h | h <;> linarith
    have ht1 : t ≤ 1 := by
      rcases Set.mem_uIcc.mp ht with h | h <;> linarith
    have hBx : 0 ≤ B * x := mul_nonneg hB.le hx
    have hprod := mul_nonneg hBx (sub_nonneg.mpr ht1)
    nlinarith
  have hderiv (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
      HasDerivAt F (r t) t := by
    have hlin : HasDerivAt (fun s : ℝ => 1 - B * x * s) (-(B * x)) t := by
      convert (hasDerivAt_const t (1 : ℝ)).sub
        ((hasDerivAt_id t).const_mul (B * x)) using 1
      · funext s
        simp
      · ring
    have hlog := hlin.log (ne_of_gt (harg t ht))
    have hscale := hlog.const_mul (-(A / B))
    convert hscale using 1
    dsimp [r]
    field_simp [hB.ne', (harg t ht).ne']
  have hlincont : Continuous (fun t : ℝ => 1 - B * x * t) := by fun_prop
  have hargne (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
      1 - B * x * t ≠ 0 := (harg t ht).ne'
  have hrcont : ContinuousOn r (Set.uIcc (0 : ℝ) 1) := by
    exact continuousOn_const.div hlincont.continuousOn hargne
  have hint : IntervalIntegrable r volume 0 1 :=
    hrcont.intervalIntegrable (μ := volume)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simpa [F, r, Real.log_one, sub_eq_add_neg, mul_assoc] using hFTC

/-- Two-sided Loewner integration for a zero-mean direction. -/
theorem sensitivityCoarseMatrixPath_loewner_meanZero {Q : TriadicCube 2}
    (ν : ℝ) (hν : 0 < ν) (k kH : ResponseCoefficient (openCubeSet Q))
    (h : PlanarW2Infinity Q)
    (hkH : responseCoefficientExtension kH =ᵐ[
      volume.restrict (openCubeSet Q)] h.value.toFun)
    (hmean : cubeAverage Q h.value.toFun = 0)
    {u : ℝ} (hu : 0 < u) (hu4 : u ≤ 1 / 4)
    (hsmall : sensitivityB2 * sensitivityDsharp Q h *
      sensitivityPathLambdaInverse ν hν k kH u 0 < 1) :
    BlockMatLoewnerLE
      (sensitivityBlockScale
        ((1 - sensitivityB2 * sensitivityDsharp Q h *
        sensitivityPathLambdaInverse ν hν k kH u 0) ^
          (sensitivityA2 / sensitivityB2))
        (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
          (sensitivityBookCoeffOn Q ν hν k)))
      (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
        (sensitivityBookCoeffOn Q ν hν (sensitivityResponseCoefficientPath k kH 1))) ∧
    BlockMatLoewnerLE
      (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
        (sensitivityBookCoeffOn Q ν hν (sensitivityResponseCoefficientPath k kH 1)))
      (sensitivityBlockScale
        ((1 - sensitivityB2 * sensitivityDsharp Q h *
        sensitivityPathLambdaInverse ν hν k kH u 0) ^
          (-(sensitivityA2 / sensitivityB2)))
        (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
          (sensitivityBookCoeffOn Q ν hν k))) := by
  let f : ℝ → ℝ := sensitivityPathLambdaInverse ν hν k kH u
  let A : ℝ := sensitivityA2
  let B : ℝ := sensitivityB2
  let D : ℝ := sensitivityDsharp Q h
  let x : ℝ := D * f 0
  let C : ℝ := B * D * f 0
  have hA : 0 ≤ A := by dsimp [A, sensitivityA2]; positivity
  have hB : 0 < B := by dsimp [B, sensitivityB2]; positivity
  have hD : 0 ≤ D := by dsimp [D]; exact sensitivityDsharp_nonneg Q h
  have hf0 : 0 ≤ f 0 := by
    exact sensitivityPathLambdaInverse_nonneg ν hν k kH hu 0
  have hC : 0 ≤ C := by dsimp [C, B, D]; positivity
  have hx : 0 ≤ x := by dsimp [x]; exact mul_nonneg hD hf0
  have hsmallC : C < 1 := by simpa [C, B, D] using hsmall
  have hfcont : Continuous f := by
    dsimp [f]
    exact sensitivityPathLambdaInverse_continuous ν hν k kH h hkH hu hu4
  have hfnonneg : ∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ f t := by
    intro t _ _
    exact sensitivityPathLambdaInverse_nonneg ν hν k kH hu t
  have hratio : ∀ t, 0 ≤ t → t ≤ 1 →
      f t ≤ Real.exp (∫ τ in (0 : ℝ)..t, (B * D) * f τ) * f 0 := by
    intro t ht0 ht1
    have h := sensitivityPathLambdaInverse_ratio_variable ν hν k kH h hkH
      hu hu4 hfcont (t₁ := 0) (t₂ := t) (by linarith)
    simpa [f, B, D, mul_assoc] using h
  have hpoint : ∀ t, 0 ≤ t → t ≤ 1 →
      f t ≤ f 0 / (1 - C * t) := by
    intro t ht0 ht1
    have h := sensitivity_bihari_upper_envelope_at hfcont
      (mul_nonneg (by dsimp [B, sensitivityB2]; positivity) hD)
      hfnonneg hratio (by simpa [C, B, D, mul_assoc] using hsmall)
      ht0 ht1
    simpa [C, x, B, D, mul_assoc, mul_left_comm, mul_comm] using h
  let δ : ℝ := (1 - C) / 2
  let den : ℝ → ℝ := fun t => max δ (1 - C * t)
  let c : ℝ → ℝ := fun t => A * x / den t
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hc : Continuous c := by
    apply continuous_const.div
    · have hdencont : Continuous den := by
        dsimp [den]
        exact continuous_const.max
          (continuous_const.sub (continuous_const.mul continuous_id))
      exact hdencont
    · intro t
      exact (lt_of_lt_of_le hδ (le_max_left _ _)).ne'
  have hden (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
      den t = 1 - C * t := by
    have hprod := mul_nonneg hC (sub_nonneg.mpr ht1)
    have hlow : 1 - C ≤ 1 - C * t := by nlinarith
    have hδle : δ ≤ 1 - C * t := by dsimp [δ]; linarith
    simp [den, max_eq_right hδle]
  have hdenPos (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
      0 < 1 - C * t := by
    have hprod := mul_nonneg hC (sub_nonneg.mpr ht1)
    nlinarith [hsmallC]
  have hcoeff (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
      A * D * f t ≤ A * x / (1 - C * t) := by
    have hf := hpoint t ht0 ht1
    have hmul := mul_le_mul_of_nonneg_left hf (mul_nonneg hA hD)
    calc
      A * D * f t ≤ A * D * (f 0 / (1 - C * t)) := by
        simpa [mul_assoc] using hmul
      _ = A * x / (1 - C * t) := by
        dsimp [x]
        field_simp [(hdenPos t ht0 ht1).ne']
  -- The scalar Grönwall argument is applied separately to each load pair.
  have hquadLoewner (P : BlockVec 2) :
      (1 - C) ^ (A / B) *
          sensitivityCoarseMatrixPathQuadratic ν hν k kH P 0 ≤
        sensitivityCoarseMatrixPathQuadratic ν hν k kH P 1 ∧
      sensitivityCoarseMatrixPathQuadratic ν hν k kH P 1 ≤
        (1 - C) ^ (-(A / B)) *
          sensitivityCoarseMatrixPathQuadratic ν hν k kH P 0 := by
    let zpath : ℝ → ℝ := sensitivityCoarseMatrixPathQuadratic ν hν k kH P
    have hzpath (t : ℝ) : 0 ≤ zpath t := by
      exact sensitivityCoarseMatrixPathQuadratic_nonneg ν hν k kH P t
    have hzt (t : ℝ) : HasDerivAt zpath (deriv zpath t) t := by
      have hraw := sensitivityCoarseMatrixPathQuadratic_hasDerivAt
        ν hν k kH h hkH P t
      change HasDerivAt
        (sensitivityCoarseMatrixPathQuadratic ν hν k kH P)
        (deriv (sensitivityCoarseMatrixPathQuadratic ν hν k kH P) t) t
      rw [hraw.deriv]
      exact hraw
    have hdy (t : ℝ) : |deriv zpath t| ≤ A * D * f t * zpath t := by
      simpa [A, D, f, zpath] using
        sensitivityCoarseMatrixPathQuadratic_deriv_abs_le ν hν k kH h hkH
          hmean hu hu4 P t
    have hprod (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
        A * D * f t * zpath t ≤ c t * zpath t := by
      have h := mul_le_mul_of_nonneg_right (hcoeff t ht0 ht1) (hzpath t)
      simpa [c, den, hden t ht0 ht1, mul_assoc] using h
    have hupper (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
        deriv zpath t ≤ c t * zpath t := by
      calc
        deriv zpath t ≤ |deriv zpath t| := le_abs_self _
        _ ≤ A * D * f t * zpath t := hdy t
        _ ≤ c t * zpath t := hprod t ht0 ht1
    have hlower (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
        -(c t * zpath t) ≤ deriv zpath t := by
      have habs := abs_le.mp (hdy t)
      have hprod' := hprod t ht0 ht1
      exact le_trans (neg_le_neg hprod') habs.1
    have hgronUp := sensitivity_exp_integral_of_hasDerivAt_le
      hzt hc hupper (by norm_num : (0 : ℝ) ≤ 1)
    have hgronDown := sensitivity_le_exp_integral_mul_of_neg_hasDerivAt_le
      hzt hc hlower (by norm_num : (0 : ℝ) ≤ 1)
    let I := ∫ t in (0 : ℝ)..1, c t
    have hInt : I = -(A / B) * Real.log (1 - C) := by
      have hEq : I = ∫ t in (0 : ℝ)..1, A * x / (1 - C * t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht0 : 0 ≤ t := by
          rcases Set.mem_uIcc.mp ht with h | h <;> linarith
        have ht1 : t ≤ 1 := by
          rcases Set.mem_uIcc.mp ht with h | h <;> linarith
        simp [c, hden t ht0 ht1]
      rw [hEq]
      have hBx : B * x = C := by dsimp [B, x, C]; ring
      have hsmallBx : B * x < 1 := by rw [hBx]; exact hsmallC
      have hrate := sensitivity_rational_rate_integral
        (A := A) (B := B) (x := x) hB hx hsmallBx
      rw [hBx] at hrate
      simpa [C] using hrate
    have hZ : 0 < 1 - C := by linarith
    have hfactorUp : Real.exp I = (1 - C) ^ (-(A / B)) := by
      rw [hInt, Real.rpow_def_of_pos hZ]
      congr 1
      ring
    have hfactorDown : Real.exp (-I) = (1 - C) ^ (A / B) := by
      rw [hInt, Real.rpow_def_of_pos hZ]
      congr 1
      ring
    constructor
    · have h := hgronDown
      have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos (-I)).le
      calc
        (1 - C) ^ (A / B) * zpath 0 = Real.exp (-I) * zpath 0 := by rw [hfactorDown]
        _ ≤ Real.exp (-I) * (Real.exp I * zpath 1) := hm
        _ = zpath 1 := by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero]; ring
    · change zpath 1 ≤ Real.exp I * zpath 0 at hgronUp
      simpa [zpath, I, hfactorUp] using hgronUp
  let A0 := Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
    (sensitivityBookCoeffOn Q ν hν k)
  let A1 := Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
    (sensitivityBookCoeffOn Q ν hν (sensitivityResponseCoefficientPath k kH 1))
  have hbase (P : BlockVec 2) :
      sensitivityCoarseMatrixPathQuadratic ν hν k kH P 0 =
        blockVecDot P (blockMatVecMul A0 P) := by
    simp [sensitivityCoarseMatrixPathQuadratic, A0, sensitivityResponseCoefficientPath]
  have hend (P : BlockVec 2) :
      sensitivityCoarseMatrixPathQuadratic ν hν k kH P 1 =
        blockVecDot P (blockMatVecMul A1 P) := by
    rfl
  constructor
  · intro P
    have h := (hquadLoewner P).1
    rw [hbase P, hend P] at h
    change (1 / 2 : ℝ) * blockVecDot P
        (blockMatVecMul (sensitivityBlockScale ((1 - C) ^ (A / B)) A0) P) ≤
      (1 / 2 : ℝ) * blockVecDot P (blockMatVecMul A1 P)
    rw [sensitivityBlockScale_quadratic]
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left h
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
  · intro P
    have h := (hquadLoewner P).2
    rw [hbase P, hend P] at h
    change (1 / 2 : ℝ) * blockVecDot P (blockMatVecMul A1 P) ≤
      (1 / 2 : ℝ) * blockVecDot P
        (blockMatVecMul (sensitivityBlockScale ((1 - C) ^ (-(A / B))) A0) P)
    rw [sensitivityBlockScale_quadratic]
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left h
      (by norm_num : (0 : ℝ) ≤ 1 / 2)

end

end ASDExplicitGamma.Triadic
