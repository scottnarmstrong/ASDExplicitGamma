module

public import ASDExplicitGamma.Native.ParentBoundaryCommonCubeFrame
public import ASDExplicitGamma.Native.VanishingBracket
public import ASDExplicitGamma.Gaussian.SquareTrace

/-! Sharp Young restoration for one shared physical center on arbitrary cubes. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Triadic Algsuperdiff.Section3
noncomputable section

private theorem parent_common_shear_young_scalar
    (T D z g eta : ℝ) (hT : 0 ≤ T) (hD : 0 ≤ D) (hz : z^2 ≤ D*T) (heta : 0 < eta) :
    T+2*g*z+g^2*D+4 ≤ (1+eta)*(T+4)+(1+1/eta)*g^2*D := by
  have habs : |z| ≤ Real.sqrt T*Real.sqrt D := by
    have hs : (Real.sqrt T*Real.sqrt D)^2=T*D := by
      rw [mul_pow,Real.sq_sqrt hT,Real.sq_sqrt hD]
    have hn := mul_nonneg (Real.sqrt_nonneg T) (Real.sqrt_nonneg D)
    nlinarith only [hz,hs,sq_abs z,abs_nonneg z,hn]
  have hl : g*z ≤ |g| *(Real.sqrt T*Real.sqrt D) :=
    (le_abs_self (g*z)).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left habs (abs_nonneg _))
  have hs := sq_nonneg (eta*Real.sqrt T-|g| *Real.sqrt D)
  have hy : 2*g*z ≤ eta*T+g^2*D/eta := by
    apply (mul_le_mul_iff_right₀ heta).mp
    have hc : eta*(g^2*D/eta)=g^2*D := by field_simp
    rw [mul_add,hc]
    simp only [sub_sq,mul_pow,Real.sq_sqrt hT,Real.sq_sqrt hD,sq_abs] at hs
    have hscaled := mul_le_mul_of_nonneg_left hl heta.le
    nlinarith only [hscaled,hs]
  have hreserve : 0 ≤ 4*eta := mul_nonneg (by norm_num) heta.le
  calc
    _ ≤ T+(eta*T+g^2*D/eta)+g^2*D+4 := by linarith only [hy]
    _ ≤ T+(eta*T+g^2*D/eta)+g^2*D+4+4*eta := le_add_of_nonneg_right hreserve
    _ = _ := by ring

/-- Actual bounded-coefficient constant-shear restoration with an arbitrary
positive Young parameter. The trace, inverse and discriminant are proved
from the same physical minimizers. -/
theorem parent_boundary_response_trace_shear_young
    (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (cubeSet Q)) (g eta : ℝ) (heta : 0 < eta) :
    traceDefect (cubeSet Q) (fun x => responsePlanarCoefficient nu (responseCoefficientExtension k x+g)) sigma+4 ≤
      (1+eta)*(traceDefect (cubeSet Q) (responsePlanarCoefficientField nu k) sigma+4)+
        (1+1/eta)*(g/sigma)^2*
          Matrix.trace (frameMatrix sigma (coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField nu k))).lowerRight := by
  have hr := nativeTraceShearDefectRows Q nu sigma hnu hsigma k
  dsimp only at hr
  rw [hr.2.2.2 g]
  have hb := parent_common_shear_young_scalar _ _ _ g eta hr.1 hr.2.1.le hr.2.2.1 heta
  exact hb.trans_eq (by rw [div_pow]; ring)

/-- The closed-cell physical trace equals the open-cell normalized trace
on the same restricted compact field. -/
theorem parent_boundary_common_cell_trace_eq
    {P Q : TriadicCube 2} {d : ℕ} (hQ : Q ∈ descendantsAtDepth P d)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (f : C(closure (cubeSet P),ℝ)) :
    squareTrace Q nu sigma (parentBoundaryCommonOpenCellCoefficient hQ f)=
      traceDefect (cubeSet Q) (responsePlanarCoefficientField nu (parentBoundaryCellCoefficient hQ f)) sigma := by
  let k := parentBoundaryCellCoefficient hQ f
  have he : responseFramePlanarCoefficientField nu sigma (parentBoundaryCommonOpenCellCoefficient hQ f)=ᵐ[
      volume.restrict (openCubeSet Q)] responseFramePlanarCoefficientField nu sigma k := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    rw [responseFramePlanarCoefficientField_apply,responseFramePlanarCoefficientField_apply,
      parent_boundary_common_open_cell_coefficient_value hQ f hx,
      parent_boundary_cell_coefficient_value hQ f (openCubeSet_subset_cubeSet Q hx)]
  have hmat := coarseBlockMatrix_congr_of_ae_eq he
  rw [←coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q,
    ←coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q] at hmat
  unfold squareTrace traceDefect
  rw [hmat,response_coarseMatrix_frame_eq (measurableSet_cubeSet Q) nu sigma hnu hsigma k]
  simp only [frameMatrix,inv_one,one_mul,Matrix.trace_smul,smul_eq_mul]
  rfl

end
end ASDExplicitGamma.Native
