module

public import ASDExplicitGamma.Native.OldSignedCovarianceProductIntegral
public import ASDExplicitGamma.Native.OldSignedRemainderCovariance

/-! Complete physical harmonic covariance tested by an actual spatial L2
field. The test and the remainder retain all their joint dependence. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
noncomputable section

private instance oldSignedRemainderCovarianceHolderTwoTwoOne : ENNReal.HolderTriple 2 2 1 :=
  ⟨by simpa only [inv_one] using ENNReal.inv_two_add_inv_two⟩

/-- The complete harmonic-mode sum passes outside its spatial pairing
with any genuine L2 test, including the actual reciprocal-gradient error. -/
theorem old_signed_remainder_covariance_integral (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (plus : Bool) (a : Fin 2 × Fin 2)
    (r : Vec 2 → ℝ) (hr : MemLp r 2 (normalizedCubeMeasure Q)) :
    HasSum (fun n : whiteBasisIndex => ∫ x,r x*
      q3Convolution b L h3Zero (whiteBasis n) x*
        oldSignedRemainderCoordinate Q b L plus n a x ∂normalizedCubeMeasure Q)
      (∫ x,r x*oldSignedRemainderScalarCovariance Q b L plus a x ∂normalizedCubeMeasure Q) := by
  let F := oldSignedRemainderKernel Q b L plus a
  have hf := F.memL2_normalized Q
  have hn x : ‖q3Section b L h3Zero x‖=|b| := by
    apply (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg b)).mp
    rw [old_signed_raw_white_norm_sq,sq_abs]
  have hrabs : MemLp (fun x => |r x|) 2 (normalizedCubeMeasure Q) := by
    simpa only [Real.norm_eq_abs] using hr.norm
  have hi0 : Integrable (fun x => |r x| *‖F.toFun x‖) (normalizedCubeMeasure Q) :=
    hrabs.integrable_mul hf.norm
  have hi : Integrable (fun x => |r x| *‖q3Section b L h3Zero x‖*‖F.toFun x‖)
      (normalizedCubeMeasure Q) := by
    have he : (fun x => |r x| *‖q3Section b L h3Zero x‖*‖F.toFun x‖)=
        (fun x => |b| *(|r x| *‖F.toFun x‖)) := by
      funext x
      rw [hn]
      ring
    rw [he]
    exact hi0.const_mul _
  have hs := old_signed_weighted_white_covariance_product (normalizedCubeMeasure Q)
    whiteBasis (q3Section b L h3Zero) F.toFun r
    (q3Section_continuous b L h3Zero).aestronglyMeasurable
    hf.aestronglyMeasurable hr.aestronglyMeasurable hi
  apply hs.congr_fun
  intro n
  apply integral_congr_ae
  filter_upwards [old_signed_remainder_kernel_coefficient Q b L plus a n] with x hx
  change r x*q3Convolution b L h3Zero (whiteBasis n) x*
    oldSignedRemainderCoordinate Q b L plus n a x=
      r x*inner ℝ (whiteBasis n) (q3Section b L h3Zero x)*
        inner ℝ (whiteBasis n) ((oldSignedRemainderKernel Q b L plus a).toFun x)
  rw [hx]
  rfl

end
end ASDExplicitGamma.Native
