module

public import ASDExplicitGamma.Triadic.SensitivityODENumerics

/-! The small branch of the all-event principal comparison, with its literal source slope. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response Triadic MeasureTheory
noncomputable section

/-- On the source small-event interval, the exponential sensitivity payment
is bounded by the prescribed affine factor. -/
theorem upper_cell_small_exponential_le {x : ℝ} (hx : 0 ≤ x) (hxsmall : x ≤ 2/5) :
    Real.exp (sensitivityCA*x) ≤ 1+(5/4:ℝ)*x := by
  have hcx : sensitivityCA*x ≤ x := by
    have hh := mul_le_mul_of_nonneg_right
      (show sensitivityCA ≤ 1 by norm_num [sensitivityCA]) hx
    simpa only [one_mul] using hh
  have hden : 0 < 2-x := by linarith
  apply (Real.exp_le_exp.mpr hcx).trans
  apply (Real.exp_le_two_add_div_two_sub hx (by linarith)).trans
  apply (div_le_iff₀ hden).mpr
  have hp := mul_nonneg hx (show 0 ≤ (1/2:ℝ)-(5/4:ℝ)*x by linarith)
  nlinarith only [hp]

/-- The actual centered coarse matrix obeys the source 5/4 small-event
comparison. The local-domain and ODE smallness hypotheses are discharged
from the one explicit source event Theta*F<=2/5. -/
theorem upper_cell_small_centered_matrix {Q : TriadicCube 2}
    (nu : ℝ) (hnu : 0 < nu) (k kH : ResponseCoefficient (openCubeSet Q))
    (h : PlanarW2Infinity Q)
    (hkH : responseCoefficientExtension kH =ᵐ[volume.restrict (openCubeSet Q)] h.value.toFun)
    {u : ℝ} (hu : 0 < u) (hu4 : u ≤ 1/4)
    (hsmall : sensitivityDsharp Q h * sensitivityPathLambdaInverse nu hnu k kH u 0 ≤ 2/5) :
    BlockMatLoewnerLE
      (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
        (sensitivityBookCoeffOn Q nu hnu
          (sensitivityResponseCoefficientPath k
            (kH + BoundedContinuousFunction.const (closure (openCubeSet Q))
              (-(cubeAverage Q h.value.toFun))) 1)))
      (sensitivityBlockScale
        (1+(5/4:ℝ)*(sensitivityDsharp Q h * sensitivityPathLambdaInverse nu hnu k kH u 0))
        (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
          (sensitivityBookCoeffOn Q nu hnu k))) := by
  let x := sensitivityDsharp Q h * sensitivityPathLambdaInverse nu hnu k kH u 0
  have hx : 0 ≤ x := mul_nonneg (sensitivityDsharp_nonneg Q h)
    (sensitivityPathLambdaInverse_nonneg nu hnu k kH hu 0)
  have hB : sensitivityB2*x < 1 := by
    have hh := mul_le_mul_of_nonneg_left hsmall
      (show 0 ≤ sensitivityB2 by unfold sensitivityB2; positivity)
    have hcap := sensitivityB2_lt_45016
    dsimp only [x] at *
    nlinarith only [hh,hcap]
  have hloc : x ≤ sensitivityCloc := hsmall.trans (by norm_num [sensitivityCloc])
  have hc := (sensitivity_coarse_sensitivity_ode_caps nu hnu k kH h hkH hu hu4
    (by simpa only [x,mul_assoc] using hB) hloc).2.2
  intro P
  have hq : 0 ≤ blockVecDot P (blockMatVecMul
      (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
        (sensitivityBookCoeffOn Q nu hnu k)) P) := by
    simpa only [sensitivityCoarseMatrixPathQuadratic, sensitivityResponseCoefficientPath,
      zero_smul, add_zero] using
      sensitivityCoarseMatrixPathQuadratic_nonneg nu hnu k kH P 0
  have hp := hc P
  rw [sensitivityBlockScale_quadratic] at hp ⊢
  have hs := mul_le_mul_of_nonneg_right (upper_cell_small_exponential_le hx hsmall) hq
  exact hp.trans (mul_le_mul_of_nonneg_left hs (by norm_num))

end
end ASDExplicitGamma.Scalar
