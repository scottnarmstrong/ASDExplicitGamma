module

public import ASDExplicitGamma.Native.OldSignedCovarianceIntegral
public import ASDExplicitGamma.Native.OldSignedProjectedKernelBounds

/-! Integrated covariance contraction for actual physical q3 modes and an
arbitrary integrable old spatial multiplier on the same observation square. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
noncomputable section

/-- The complete signed physical white contraction commutes with spatial
integration against the actual old multiplier. Its domination is supplied
from the proved q3 kernel energies, not assumed as an estimate. -/
theorem old_signed_physical_integrated_covariance (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (i j : Fin 2) (r : Vec 2 → ℝ)
    (hr : IntegrableOn r (openCubeSet Q)) :
    HasSum (fun n : whiteBasisIndex => ∫ x in openCubeSet Q,
      r x*q3Convolution b L h3Zero (whiteBasis n) x*
        inner ℝ (whiteBasis n) (oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j) ∂volume)
      ((-(b^2/2)*(if i=j then 1 else 0))*(∫ x in openCubeSet Q,r x ∂volume)) := by
  let A := q3Section b L h3Zero
  let B := fun x : Vec 2 => oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j
  have hA : Continuous A := q3Section_continuous b L h3Zero
  have hx : Continuous (fun x : Vec 2 => L.1⁻¹ • x) :=
    continuous_id.const_smul (L.1⁻¹)
  have hB : Continuous B := (old_signed_rotated_white_continuous b L i j).comp hx
  have hm : AEStronglyMeasurable (fun x => |r x| *(‖A x‖^2+‖B x‖^2))
      (volumeMeasureOn (openCubeSet Q)) :=
    hr.aestronglyMeasurable.norm.mul
      ((hA.aestronglyMeasurable.norm.pow 2).add (hB.aestronglyMeasurable.norm.pow 2))
  have hi : Integrable (fun x => |r x| *(‖A x‖^2+‖B x‖^2))
      (volumeMeasureOn (openCubeSet Q)) := by
    apply (hr.norm.mul_const (2*b^2)).mono' hm
    filter_upwards with x
    have hb := old_signed_rotated_white_norm_le b L (L.1⁻¹ • x) i j
    have ha : ‖A x‖^2=b^2 := old_signed_raw_white_norm_sq b L x
    have hs : ‖B x‖^2≤b^2 := by
      change ‖oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j‖^2≤b^2
      nlinarith only [hb,sq_abs b,norm_nonneg (oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j),
        abs_nonneg b]
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (abs_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _))),ha]
    simp only [Real.norm_eq_abs]
    nlinarith only [mul_le_mul_of_nonneg_left hs (abs_nonneg (r x))]
  have hh := old_signed_weighted_white_covariance (volumeMeasureOn (openCubeSet Q))
    whiteBasis A B r hA.aestronglyMeasurable hB.aestronglyMeasurable hr.aestronglyMeasurable hi
  have hp (x : Vec 2) : inner ℝ (A x) (B x)=-(b^2/2)*(if i=j then 1 else 0) := by
    have h := old_signed_rotated_white_point_covariance b L (L.1⁻¹ • x) i j
    have hx : L.1 • (L.1⁻¹ • x)=x := by
      rw [smul_smul,mul_inv_cancel₀ L.2.ne',one_smul]
    rw [hx] at h
    exact h
  simp_rw [hp] at hh
  rw [integral_mul_const] at hh
  simpa only [A,B,q3Convolution,mul_comm (∫ x in openCubeSet Q,r x ∂volume)] using hh

end
end ASDExplicitGamma.Native
