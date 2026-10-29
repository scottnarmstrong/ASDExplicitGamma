module

public import ASDExplicitGamma.Triadic.SensitivityODELoewner
public import ASDExplicitGamma.Triadic.HilbertPoincareNumerics
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Explicit scalar and matrix caps for the planar sensitivity ODE. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory ASDExplicitGamma.Response

noncomputable section

def sensitivityCloc : ℝ := 1.1106

def sensitivityCA : ℝ := 0.8722

def sensitivityCLambda : ℝ := 0.9004

theorem sensitivityB2_lt_45016 : sensitivityB2 < (0.45016 : ℝ) := by
  have hsqrt : Real.sqrt 2 < (1.414214 : ℝ) := by
    apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1.414214)).2
    norm_num
  have hpi := ASDExplicitGamma.Numerics.pi_enclosure.1
  have hprod : (1.414214 : ℝ) < 0.45016 * 3.14159265358979323846 := by
    norm_num
  unfold sensitivityB2
  apply (div_lt_iff₀ Real.pi_pos).2
  calc
    Real.sqrt 2 < 1.414214 := hsqrt
    _ < 0.45016 * 3.14159265358979323846 := hprod
    _ < 0.45016 * Real.pi := by gcongr

theorem sensitivityA2_lt_62915 : sensitivityA2 < (0.62915 : ℝ) := by
  have hC0 := planarC0_decimal_bounds.2
  have hB := sensitivityB2_lt_45016
  have hC0nonneg : 0 ≤ planarC0 := by
    unfold planarC0
    exact Real.sqrt_nonneg _
  have hC0sq := (sq_le_sq₀ hC0nonneg
      (by norm_num : 0 ≤ (0.439510742 : ℝ))).2 hC0.le
  have hBnonneg : 0 ≤ sensitivityB2 := by unfold sensitivityB2; positivity
  have hBsq := (sq_le_sq₀ hBnonneg
      (by norm_num : 0 ≤ (0.45016 : ℝ))).2 hB.le
  have hsum : planarC0 ^ 2 + sensitivityB2 ^ 2 < (0.62915 : ℝ) ^ 2 := by
    nlinarith
  unfold sensitivityA2
  exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 0.62915)).2 hsum

/-- The chord bound for the logarithm on the interval `[1/2,1]`. -/
theorem sensitivity_log_one_sub_chord {y : ℝ}
    (hy0 : 0 ≤ y) (hyhalf : y ≤ 1 / 2) :
    -Real.log (1 - y) ≤ 2 * y * Real.log 2 := by
  let a : ℝ := 1 - 2 * y
  let b : ℝ := 2 * y
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hab : a + b = 1 := by dsimp [a, b]; ring
  have hhalf : (1 / 2 : ℝ) = 2⁻¹ := by norm_num
  have hconc := strictConcaveOn_log_Ioi.concaveOn
  have hchord := hconc.2 (by norm_num : (1 : ℝ) ∈ Set.Ioi 0)
    (by norm_num : (1 / 2 : ℝ) ∈ Set.Ioi 0) ha hb hab
  have harg : a * 1 + b * (1 / 2 : ℝ) = 1 - y := by
    dsimp [a, b]
    ring
  have hlog : -(2 * y * Real.log 2) ≤ Real.log (1 - y) := by
    calc
      -(2 * y * Real.log 2) = a * Real.log 1 + b * Real.log (1 / 2 : ℝ) := by
        rw [Real.log_one, hhalf, Real.log_inv]
        dsimp [a, b]
        ring
      _ ≤ Real.log (a * 1 + b * (1 / 2 : ℝ)) := by
        simpa only [smul_eq_mul] using hchord
      _ = Real.log (1 - y) := by rw [harg]
  linarith

theorem sensitivityA2_log_two_cap :
    2 * sensitivityA2 * Real.log 2 ≤ sensitivityCA := by
  have hA := sensitivityA2_lt_62915
  have hlog := ASDExplicitGamma.Numerics.log_two_enclosure.2
  calc
    2 * sensitivityA2 * Real.log 2 ≤ 2 * 0.62915 * Real.log 2 := by
      nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
    _ ≤ 2 * 0.62915 * 0.693147180559946 := by
      exact mul_le_mul_of_nonneg_left hlog (by norm_num)
    _ ≤ sensitivityCA := by norm_num [sensitivityCA]

theorem sensitivity_scalar_factor_cap {x : ℝ}
    (hx0 : 0 ≤ x) (hxloc : x ≤ sensitivityCloc) :
    1 / (1 - sensitivityB2 * x) ≤ 1 + sensitivityCLambda * x := by
  have hB := sensitivityB2_lt_45016
  have hB0 : 0 ≤ sensitivityB2 := by unfold sensitivityB2; positivity
  have hlam : 0 < sensitivityCLambda := by norm_num [sensitivityCLambda]
  have hprod : sensitivityB2 * (1 + sensitivityCLambda * x) ≤
      sensitivityCLambda := by
    calc
      sensitivityB2 * (1 + sensitivityCLambda * x) ≤
          0.45016 * (1 + sensitivityCLambda * x) :=
        mul_le_mul_of_nonneg_right hB.le (by positivity)
      _ ≤ 0.45016 * (1 + sensitivityCLambda * sensitivityCloc) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        nlinarith [mul_le_mul_of_nonneg_left hxloc hlam.le]
      _ ≤ sensitivityCLambda := by norm_num [sensitivityCLambda, sensitivityCloc]
  have hBx : sensitivityB2 * x < 1 / 2 := by
    calc
      sensitivityB2 * x ≤ 0.45016 * sensitivityCloc := by
        calc
          sensitivityB2 * x ≤ 0.45016 * x :=
            mul_le_mul_of_nonneg_right hB.le hx0
          _ ≤ 0.45016 * sensitivityCloc :=
            mul_le_mul_of_nonneg_left hxloc (by norm_num)
      _ < 1 / 2 := by norm_num [sensitivityCloc]
  have hden : 0 < 1 - sensitivityB2 * x := by linarith
  have hmul : 1 ≤ (1 + sensitivityCLambda * x) *
      (1 - sensitivityB2 * x) := by
    calc
      1 ≤ 1 + x * (sensitivityCLambda -
          sensitivityB2 * (1 + sensitivityCLambda * x)) :=
        le_add_of_nonneg_right (mul_nonneg hx0 (sub_nonneg.mpr hprod))
      _ = (1 + sensitivityCLambda * x) *
          (1 - sensitivityB2 * x) := by ring
  exact (div_le_iff₀ hden).2 hmul

theorem sensitivity_matrix_factor_cap {x : ℝ}
    (hx0 : 0 ≤ x) (hxloc : x ≤ sensitivityCloc) :
    (1 - sensitivityB2 * x) ^ (-(sensitivityA2 / sensitivityB2)) ≤
      Real.exp (sensitivityCA * x) := by
  have hB := sensitivityB2_lt_45016
  have hB0 : 0 < sensitivityB2 := by unfold sensitivityB2; positivity
  have hA0 : 0 ≤ sensitivityA2 := by unfold sensitivityA2; positivity
  have hBx : sensitivityB2 * x ≤ 1 / 2 := by
    calc
      sensitivityB2 * x ≤ 0.45016 * sensitivityCloc := by
        calc
          sensitivityB2 * x ≤ 0.45016 * x :=
            mul_le_mul_of_nonneg_right hB.le hx0
          _ ≤ 0.45016 * sensitivityCloc :=
            mul_le_mul_of_nonneg_left hxloc (by norm_num)
      _ ≤ 1 / 2 := by norm_num [sensitivityCloc]
  have hden : 0 < 1 - sensitivityB2 * x := by linarith
  have hlog := sensitivity_log_one_sub_chord
    (mul_nonneg hB0.le hx0) hBx
  have hlogexp :
      -(sensitivityA2 / sensitivityB2) *
          Real.log (1 - sensitivityB2 * x) ≤ sensitivityCA * x := by
    have hscaled := mul_le_mul_of_nonneg_left hlog
      (div_nonneg hA0 hB0.le)
    calc
      -(sensitivityA2 / sensitivityB2) *
          Real.log (1 - sensitivityB2 * x) =
        (sensitivityA2 / sensitivityB2) *
          (-Real.log (1 - sensitivityB2 * x)) := by ring
      _ ≤ (sensitivityA2 / sensitivityB2) *
          (2 * (sensitivityB2 * x) * Real.log 2) := hscaled
      _ = (2 * sensitivityA2 * Real.log 2) * x := by
        field_simp [hB0.ne']
      _ ≤ sensitivityCA * x :=
        mul_le_mul_of_nonneg_right sensitivityA2_log_two_cap hx0
  rw [Real.rpow_def_of_pos hden]
  apply Real.exp_le_exp.mpr
  calc
    Real.log (1 - sensitivityB2 * x) *
        (-(sensitivityA2 / sensitivityB2)) =
      -(sensitivityA2 / sensitivityB2) *
        Real.log (1 - sensitivityB2 * x) := mul_comm _ _
    _ ≤ sensitivityCA * x := hlogexp

/-- The full coarse-sensitivity ODE, with the source numerical caps and the
mean-zero representative constructed internally. -/
theorem sensitivity_coarse_sensitivity_ode_caps {Q : TriadicCube 2}
    (ν : ℝ) (hν : 0 < ν) (k kH : ResponseCoefficient (openCubeSet Q))
    (h : PlanarW2Infinity Q)
    (hkH : responseCoefficientExtension kH =ᵐ[
      volume.restrict (openCubeSet Q)] h.value.toFun)
    {u : ℝ} (hu : 0 < u) (hu4 : u ≤ 1 / 4)
    (hsmall : sensitivityB2 * sensitivityDsharp Q h *
      sensitivityPathLambdaInverse ν hν k kH u 0 < 1)
    (hloc : sensitivityDsharp Q h *
      sensitivityPathLambdaInverse ν hν k kH u 0 ≤ sensitivityCloc) :
    sensitivityPathLambdaInverse ν hν k kH u 1 ≤
      sensitivityPathLambdaInverse ν hν k kH u 0 *
        (1 + sensitivityCLambda * (sensitivityDsharp Q h *
          sensitivityPathLambdaInverse ν hν k kH u 0)) ∧
    BlockMatLoewnerLE
      (sensitivityBlockScale
        ((1 - sensitivityB2 * sensitivityDsharp Q h *
          sensitivityPathLambdaInverse ν hν k kH u 0) ^
            (sensitivityA2 / sensitivityB2))
        (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
          (sensitivityBookCoeffOn Q ν hν k)))
      (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
        (sensitivityBookCoeffOn Q ν hν
          (sensitivityResponseCoefficientPath k
            (kH + BoundedContinuousFunction.const (closure (openCubeSet Q))
              (-(cubeAverage Q h.value.toFun))) 1))) ∧
    BlockMatLoewnerLE
      (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
        (sensitivityBookCoeffOn Q ν hν
          (sensitivityResponseCoefficientPath k
            (kH + BoundedContinuousFunction.const (closure (openCubeSet Q))
              (-(cubeAverage Q h.value.toFun))) 1)))
      (sensitivityBlockScale
        (Real.exp (sensitivityCA * (sensitivityDsharp Q h *
          sensitivityPathLambdaInverse ν hν k kH u 0)))
        (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
          (sensitivityBookCoeffOn Q ν hν k))) := by
  let h₀ := sensitivityMeanZeroW2Direction h
  let g := -(cubeAverage Q h.value.toFun)
  let kH₀ := kH + BoundedContinuousFunction.const (closure (openCubeSet Q)) g
  have hmean₀ : cubeAverage Q h₀.value.toFun = 0 := by
    exact sensitivityMeanZeroW2Direction_mean h
  have hkH₀ : responseCoefficientExtension kH₀ =ᵐ[
      volume.restrict (openCubeSet Q)] h₀.value.toFun := by
    simpa [h₀, kH₀, g] using
      sensitivityMeanZeroW2Direction_responseRepresentative kH h hkH
  have hD₀ : sensitivityDsharp Q h₀ = sensitivityDsharp Q h := by
    exact sensitivityDsharp_meanZeroW2Direction h
  have hshift : sensitivityPathLambdaInverse ν hν k kH₀ u 0 =
      sensitivityPathLambdaInverse ν hν k kH u 0 := by
    exact sensitivityPathLambdaInverse_constant_direction_shift
      ν hν k kH g (u := u) (t := 0)
  have hsmall₀ : sensitivityB2 * sensitivityDsharp Q h₀ *
      sensitivityPathLambdaInverse ν hν k kH₀ u 0 < 1 := by
    rw [hD₀, hshift]
    exact hsmall
  have hmatrix := sensitivityCoarseMatrixPath_loewner_meanZero
    ν hν k kH₀ h₀ hkH₀ hmean₀ hu hu4 hsmall₀
  have hX0 : 0 ≤ sensitivityDsharp Q h *
      sensitivityPathLambdaInverse ν hν k kH u 0 :=
    mul_nonneg (sensitivityDsharp_nonneg Q h)
      (sensitivityPathLambdaInverse_nonneg ν hν k kH hu 0)
  have hscalarCap := sensitivity_scalar_factor_cap hX0 hloc
  have hscalar := sensitivityPathLambdaInverse_rational_envelope
    ν hν k kH h hkH hu hu4 hsmall
  have hscalarCap' :
      (1 - sensitivityB2 * (sensitivityDsharp Q h *
        sensitivityPathLambdaInverse ν hν k kH u 0))⁻¹ ≤
        1 + sensitivityCLambda * (sensitivityDsharp Q h *
          sensitivityPathLambdaInverse ν hν k kH u 0) := by
    simpa only [one_div] using hscalarCap
  have hscalarResult : sensitivityPathLambdaInverse ν hν k kH u 1 ≤
      sensitivityPathLambdaInverse ν hν k kH u 0 *
        (1 + sensitivityCLambda * (sensitivityDsharp Q h *
          sensitivityPathLambdaInverse ν hν k kH u 0)) := by
    calc
      sensitivityPathLambdaInverse ν hν k kH u 1 ≤
          sensitivityPathLambdaInverse ν hν k kH u 0 /
            (1 - sensitivityB2 * sensitivityDsharp Q h *
              sensitivityPathLambdaInverse ν hν k kH u 0) := hscalar
      _ = sensitivityPathLambdaInverse ν hν k kH u 0 *
            (1 - sensitivityB2 * sensitivityDsharp Q h *
              sensitivityPathLambdaInverse ν hν k kH u 0)⁻¹ := by ring
      _ ≤ sensitivityPathLambdaInverse ν hν k kH u 0 *
            (1 + sensitivityCLambda * (sensitivityDsharp Q h *
              sensitivityPathLambdaInverse ν hν k kH u 0)) := by
        apply mul_le_mul_of_nonneg_left _
          (sensitivityPathLambdaInverse_nonneg ν hν k kH hu 0)
        simpa [mul_assoc] using hscalarCap'
  let A₀ := Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
    (sensitivityBookCoeffOn Q ν hν k)
  let A₁ := Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
    (sensitivityBookCoeffOn Q ν hν
      (sensitivityResponseCoefficientPath k kH₀ 1))
  have hmatrixLo : BlockMatLoewnerLE
      (sensitivityBlockScale
        ((1 - sensitivityB2 * sensitivityDsharp Q h *
          sensitivityPathLambdaInverse ν hν k kH u 0) ^
            (sensitivityA2 / sensitivityB2)) A₀) A₁ := by
    have hs := hmatrix.1
    rw [hD₀, hshift] at hs
    change BlockMatLoewnerLE
      (sensitivityBlockScale
        ((1 - sensitivityB2 * sensitivityDsharp Q h *
          sensitivityPathLambdaInverse ν hν k kH u 0) ^
            (sensitivityA2 / sensitivityB2)) A₀) A₁
    exact hs
  have hfactorCap := sensitivity_matrix_factor_cap hX0 hloc
  have hmatrixHiFactor :
      (1 - sensitivityB2 * sensitivityDsharp Q h₀ *
        sensitivityPathLambdaInverse ν hν k kH₀ u 0) ^
          (-(sensitivityA2 / sensitivityB2)) ≤
        Real.exp (sensitivityCA * (sensitivityDsharp Q h *
          sensitivityPathLambdaInverse ν hν k kH u 0)) := by
    rw [hD₀, hshift]
    simpa [mul_assoc] using hfactorCap
  have hmatrixHi : BlockMatLoewnerLE A₁
      (sensitivityBlockScale
        (Real.exp (sensitivityCA * (sensitivityDsharp Q h *
          sensitivityPathLambdaInverse ν hν k kH u 0))) A₀) := by
    intro P
    have hq₀ : 0 ≤ blockVecDot P (blockMatVecMul A₀ P) := by
      have h := sensitivityCoarseMatrixPathQuadratic_nonneg
        ν hν k kH₀ P 0
      change 0 ≤ blockVecDot P (blockMatVecMul
        (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
          (sensitivityBookCoeffOn Q ν hν
            (sensitivityResponseCoefficientPath k kH₀ 0))) P) at h
      have hpath0 : sensitivityResponseCoefficientPath k kH₀ 0 = k := by
        simp [sensitivityResponseCoefficientPath]
      rw [hpath0] at h
      change 0 ≤ blockVecDot P (blockMatVecMul A₀ P) at h
      exact h
    have hfactorq := mul_le_mul_of_nonneg_right hmatrixHiFactor hq₀
    have hupper := hmatrix.2 P
    change (1 / 2 : ℝ) *
        blockVecDot P (blockMatVecMul A₁ P) ≤
      (1 / 2 : ℝ) * blockVecDot P
        (blockMatVecMul
          (sensitivityBlockScale
            ((1 - sensitivityB2 * sensitivityDsharp Q h₀ *
              sensitivityPathLambdaInverse ν hν k kH₀ u 0) ^
                (-(sensitivityA2 / sensitivityB2))) A₀) P) at hupper
    rw [sensitivityBlockScale_quadratic] at hupper
    change (1 / 2 : ℝ) *
        blockVecDot P (blockMatVecMul A₁ P) ≤
      (1 / 2 : ℝ) * blockVecDot P
        (blockMatVecMul
          (sensitivityBlockScale
            (Real.exp (sensitivityCA * (sensitivityDsharp Q h *
              sensitivityPathLambdaInverse ν hν k kH u 0))) A₀) P)
    rw [sensitivityBlockScale_quadratic]
    calc
      (1 / 2 : ℝ) * blockVecDot P (blockMatVecMul A₁ P) ≤
          (1 / 2 : ℝ) *
            ((1 - sensitivityB2 * sensitivityDsharp Q h₀ *
              sensitivityPathLambdaInverse ν hν k kH₀ u 0) ^
                (-(sensitivityA2 / sensitivityB2)) *
              blockVecDot P (blockMatVecMul A₀ P)) := hupper
      _ ≤ (1 / 2 : ℝ) *
          (Real.exp (sensitivityCA * (sensitivityDsharp Q h *
            sensitivityPathLambdaInverse ν hν k kH u 0)) *
            blockVecDot P (blockMatVecMul A₀ P)) :=
        mul_le_mul_of_nonneg_left hfactorq (by norm_num)
  exact ⟨hscalarResult, hmatrixLo, hmatrixHi⟩

end

end ASDExplicitGamma.Triadic
