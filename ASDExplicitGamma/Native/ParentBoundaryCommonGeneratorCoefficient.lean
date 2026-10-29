module

public import ASDExplicitGamma.Native.ParentBoundaryCommonCenterHilbertBound
public import ASDExplicitGamma.Native.ParentBoundaryCommonDistinctRow
public import ASDExplicitGamma.Inverse.PureFluxFeedbackCoefficient

/-! OLD common-center covariance coefficients, with the source's 1.856 bound. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Main Triadic Variational Inverse
noncomputable section

/-- The operator feedback row is nonnegative and no larger than the full
Hilbert--Schmidt source column at the same common center and child mesh. -/
theorem parent_boundary_common_covariance_rows_order
    (P Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l}) (m : ℕ) :
    0 ≤ parentBoundaryCommonFeedbackCoefficient P Q b L m ∧
      parentBoundaryCommonFeedbackCoefficient P Q b L m ≤
        parentBoundaryCommonRowCoefficient P Q b L m := by
  have hm := (diagMeshRadius_pos Q m).le
  constructor
  · unfold parentBoundaryCommonFeedbackCoefficient
    positivity
  · have hg : (78/5:ℝ)*b^2/L.val^2 ≤ (156/5:ℝ)*b^2/L.val^2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num : (78/5:ℝ) ≤ 156/5) (sq_nonneg b))
        (sq_nonneg L.val)
    have hh : (23244/25:ℝ)*b^2/L.val^4 ≤ (46488/25:ℝ)*b^2/L.val^4 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num : (23244/25:ℝ) ≤ 46488/25) (sq_nonneg b))
        (by positivity)
    unfold parentBoundaryCommonFeedbackCoefficient parentBoundaryCommonRowCoefficient
    exact add_le_add
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hg) (by positivity)))
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hh) (by positivity))

/-- The literal OLD coefficient 1.856 bounds the positive feedback branch.
This uses D_f=63/50, independently of the main constants. -/
theorem parent_boundary_common_covariance_mu_cap
    (A B : ℝ) (hB : 0 ≤ B) (hBA : B ≤ A) :
    pureFluxCovarianceMu A B ≤ (232/125:ℝ)*A^2 := by
  apply pureFlux_covariance_mu_le_of_certificate
  · nlinarith only [sq_nonneg A]
  · have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB hBA 2) (sq_nonneg A)
    nlinarith only [hh,sq_nonneg (A^2)]

/-- Applied to the actual common-center source rows, the source's 1.856
constant retains the exact parent-radius / child-mesh geometry. -/
theorem parent_boundary_common_covariance_mu
    (P Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l}) (m : ℕ) :
    pureFluxCovarianceMu (parentBoundaryCommonRowCoefficient P Q b L m)
      (parentBoundaryCommonFeedbackCoefficient P Q b L m) ≤
      (232/125:ℝ)*(parentBoundaryCommonRowCoefficient P Q b L m)^2 := by
  exact parent_boundary_common_covariance_mu_cap _ _
    (parent_boundary_common_covariance_rows_order P Q b L m).1
    (parent_boundary_common_covariance_rows_order P Q b L m).2

/-- Scalar closure of the actual source-minus-projection Hessian identity,
for arbitrary common-center covariance row coefficients. -/
theorem parent_boundary_common_source_feedback_scalar
    (A D c B g S C Z x y E : ℝ) (hB : 0 ≤ B)
    (hidentity : g = S+2*C-Z) (hZ : 0 ≤ Z)
    (hsource : S ≤ B*c^2*A^2*x^2)
    (hfeedback : C ≤ (63/50:ℝ)*B*c^2*A*D*x*y)
    (hpair : x^2+y^2 ≤ B*E) :
    g ≤ c^2*pureFluxCovarianceMu A D*B^2*E := by
  have hscale : 0 ≤ B*c^2 := mul_nonneg hB (sq_nonneg c)
  have hmu := (pureFlux_covariance_mu_lower A D).1
  have hquad := pureFlux_covariance_quadratic_bound A D x y
  calc
    g ≤ B*c^2*(A^2*x^2+2*(63/50:ℝ)*A*D*x*y) := by
      rw [hidentity]
      nlinarith only [hsource,hfeedback,hZ]
    _ ≤ B*c^2*(pureFluxCovarianceMu A D*(x^2+y^2)) :=
      mul_le_mul_of_nonneg_left hquad hscale
    _ ≤ B*c^2*(pureFluxCovarianceMu A D*(B*E)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpair hmu) hscale
    _ = _ := by ring

end
end ASDExplicitGamma.Native
