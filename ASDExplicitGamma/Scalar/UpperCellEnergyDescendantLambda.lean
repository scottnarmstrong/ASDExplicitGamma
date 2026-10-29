module

public import ASDExplicitGamma.Scalar.UpperCellEnergyOldLambda
public import ASDExplicitGamma.Scalar.UpperCellEnergyHistoryEnvelope

/-! The explicit descendant decay retained in the upper-cell depth choice. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Response Variational Native Triadic
noncomputable section

/-- At quarter lambda exponent, restriction saves exactly one half power of
three per generation after paying the inverse-lambda descendant weight. -/
theorem upper_cell_descendant_weight_decay (Q : TriadicCube 2) (j : ℕ) :
    (3:ℝ)^(-(j:ℤ)) *
      Book.Ch02.multiscaleDescendantWeight Q (Q.scale-(j:ℤ)) (1/4) =
        ((Real.sqrt 3)^j)⁻¹ := by
  have hw : Book.Ch02.multiscaleDescendantWeight Q (Q.scale-(j:ℤ)) (1/4) =
      (3:ℝ)^((1/2:ℝ)*(j:ℝ)) := by
    unfold Book.Ch02.multiscaleDescendantWeight
    congr 1
    push_cast
    ring
  have hz : (3:ℝ)^(-(j:ℤ)) = (3:ℝ)^(-(j:ℝ)) := by
    rw [←Real.rpow_intCast]
    congr 1
    simp
  rw [hw,hz,←Real.rpow_add (by norm_num : (0:ℝ)<3)]
  rw [show -(j:ℝ)+(1/2:ℝ)*(j:ℝ) = -((1/2:ℝ)*(j:ℝ)) by ring,
    Real.rpow_neg (by norm_num : (0:ℝ)≤3),Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3),
    ←Real.sqrt_eq_rpow]

/-- The local smallness parameter decays geometrically, including the exact
factor discarded by the uniform descendant comparison. -/
theorem upper_cell_descendant_lambda_decay
    {Q R : TriadicCube 2} {j : ℕ}
    (nu : ℝ) (hnu : 0<nu) (k kH : ResponseCoefficient (openCubeSet Q))
    (h : PlanarW2Infinity Q) (hR : R ∈ descendantsAtDepth Q j) (t : ℝ) :
    sensitivityDsharp R (h.restrict hR) *
      sensitivityPathLambdaInverse nu hnu
        (sensitivityResponseCoefficientRestrict k hR)
        (sensitivityResponseCoefficientRestrict kH hR) (1/4) t ≤
      (sensitivityDsharp Q h * sensitivityPathLambdaInverse nu hnu k kH (1/4) t) /
        (Real.sqrt 3)^j := by
  let F := sensitivityPathFamily nu hnu k kH t
  have hs : R ∈ descendantsAtScale Q (Q.scale-(j:ℤ)) := by
    rw [descendantsAtScale_eq_descendantsAtDepth Q (by omega)]
    simpa using hR
  have hl := Book.Ch02.descendant_lambdaSq_finite_inv_le F hs
    (by norm_num : (0:ℝ)<1/4) (by norm_num : (1:ℝ)≤2)
  have he := sensitivityPathFamily_descendant_lambda_eq nu hnu k kH hR (1/4) t
  have hl' : sensitivityPathLambdaInverse nu hnu
      (sensitivityResponseCoefficientRestrict k hR)
      (sensitivityResponseCoefficientRestrict kH hR) (1/4) t ≤
      Book.Ch02.multiscaleDescendantWeight Q (Q.scale-(j:ℤ)) (1/4) *
        sensitivityPathLambdaInverse nu hnu k kH (1/4) t := by
    unfold sensitivityPathLambdaInverse
    rw [he]
    exact hl
  have hd := sensitivityDsharp_descendant_le h hR
  have hw : 0 ≤ Book.Ch02.multiscaleDescendantWeight Q (Q.scale-(j:ℤ)) (1/4) := by
    unfold Book.Ch02.multiscaleDescendantWeight
    exact Real.rpow_nonneg (by norm_num) _
  have hr := sensitivityPathLambdaInverse_nonneg nu hnu k kH
    (by norm_num : (0:ℝ)<1/4) t
  calc
    _ ≤ sensitivityDsharp R (h.restrict hR) *
        (Book.Ch02.multiscaleDescendantWeight Q (Q.scale-(j:ℤ)) (1/4) *
          sensitivityPathLambdaInverse nu hnu k kH (1/4) t) :=
      mul_le_mul_of_nonneg_left hl' (sensitivityDsharp_nonneg _ _)
    _ ≤ ((3:ℝ)^(-(j:ℤ))*sensitivityDsharp Q h) *
        (Book.Ch02.multiscaleDescendantWeight Q (Q.scale-(j:ℤ)) (1/4) *
          sensitivityPathLambdaInverse nu hnu k kH (1/4) t) :=
      mul_le_mul_of_nonneg_right hd (mul_nonneg hw hr)
    _ = (sensitivityDsharp Q h * sensitivityPathLambdaInverse nu hnu k kH (1/4) t) *
        ((3:ℝ)^(-(j:ℤ))*Book.Ch02.multiscaleDescendantWeight Q (Q.scale-(j:ℤ)) (1/4)) := by ring
    _ = _ := by
      rw [upper_cell_descendant_weight_decay]
      exact (div_eq_mul_inv _ _).symm

end
end ASDExplicitGamma.Scalar
