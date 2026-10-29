module

public import ASDExplicitGamma.Native.OldSignedRemainderKernel
public import ASDExplicitGamma.Native.OldSignedWhiteRow
public import ASDExplicitGamma.Native.OldSignedRowProductBounds

/-! Literal complete physical white covariance contractions of the two
harmonic remainders. Mode identities hold almost everywhere on the actual
source cube; no independence or finite-rank stationarity is asserted. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main ASDExplicitGamma.Triadic
noncomputable section

/-- The scalar covariance before the fixed output rotation J. -/
def oldSignedRemainderScalarCovariance (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (plus : Bool) (a : Fin 2 × Fin 2) (x : Vec 2) : ℝ :=
  inner ℝ (q3Section b L h3Zero x) ((oldSignedRemainderKernel Q b L plus a).toFun x)

/-- Every white coefficient is the corresponding original physical
harmonic mode, with almost-everywhere equality in the source measure. -/
theorem old_signed_remainder_kernel_coefficient (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (plus : Bool) (a : Fin 2 × Fin 2) (n : whiteBasisIndex) :
    (fun x => inner ℝ (whiteBasis n) ((oldSignedRemainderKernel Q b L plus a).toFun x))
      =ᵐ[normalizedCubeMeasure Q] oldSignedRemainderCoordinate Q b L plus n a := by
  have hh := old_signed_h1_kernel_coefficient Q whiteBasis
    (fun j => oldSignedRemainderCoordinate Q b L plus j a)
    (old_signed_coordinate_value_summable Q _
      (old_signed_remainder_coordinate_value_trace Q b L plus).summable a)
    (old_signed_coordinate_derivative_summable Q _
      (old_signed_remainder_coordinate_gradient_bound Q b L plus).1 a) n
  unfold normalizedCubeMeasure cubeMeasure
  apply Measure.ae_smul_measure
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  exact hh

/-- The complete covariance mode series converges to the actual contracted
kernel, jointly in the coefficient and the harmonic field. -/
theorem old_signed_remainder_scalar_covariance_hasSum (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (plus : Bool) (a : Fin 2 × Fin 2) :
    ∀ᵐ x ∂normalizedCubeMeasure Q,HasSum (fun n : whiteBasisIndex =>
      q3Convolution b L h3Zero (whiteBasis n) x *
        oldSignedRemainderCoordinate Q b L plus n a x)
      (oldSignedRemainderScalarCovariance Q b L plus a x) := by
  have hc : ∀ᵐ x ∂normalizedCubeMeasure Q,∀ n,
      inner ℝ (whiteBasis n) ((oldSignedRemainderKernel Q b L plus a).toFun x)=
        oldSignedRemainderCoordinate Q b L plus n a x := by
    rw [ae_all_iff]
    exact old_signed_remainder_kernel_coefficient Q b L plus a
  filter_upwards [hc] with x hx
  have hs := whiteBasis.hasSum_inner_mul_inner (q3Section b L h3Zero x)
    ((oldSignedRemainderKernel Q b L plus a).toFun x)
  apply hs.congr_fun
  intro n
  rw [real_inner_comm (whiteBasis n),hx n]
  rfl

end
end ASDExplicitGamma.Native
