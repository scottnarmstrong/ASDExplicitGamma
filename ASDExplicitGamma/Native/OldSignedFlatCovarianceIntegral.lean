module

public import ASDExplicitGamma.Native.OldSignedRotatedCovarianceIntegral

/-! Complete exact covariance of actual finite-square flat fields. The
signed bulk is retained, and the harmonic term remains an actual joint
spatial pairing with the original test field. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main ASDExplicitGamma.Triadic
open ASDExplicitGamma.Response
noncomputable section

/-- Every actual finite flat covariance mode splits into its whole-plane
bulk and harmonic terms under the spatial integral. Integrability is proved
before invoking linearity of the integral. -/
theorem old_signed_flat_covariance_integral_split (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (plus : Bool) (n : whiteBasisIndex) (i k : Fin 2)
    (r : Vec 2 → ℝ) (hr : MemLp r 2 (normalizedCubeMeasure Q)) :
    (∫ x,r x*q3Convolution b L h3Zero (whiteBasis n) x*
      matVecMul responsePlanarJ (fun l => oldSignedFlatCoordinate Q b L plus n (i,l) x) k
        ∂normalizedCubeMeasure Q)=
      (∫ x,r x*q3Convolution b L h3Zero (whiteBasis n) x*
        inner ℝ (whiteBasis n) (oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) k i)
          ∂normalizedCubeMeasure Q)+
      ∫ x,r x*q3Convolution b L h3Zero (whiteBasis n) x*
        matVecMul responsePlanarJ (fun l => oldSignedRemainderCoordinate Q b L plus n (i,l) x) k
          ∂normalizedCubeMeasure Q := by
  have hp : MemLp (fun x => inner ℝ (whiteBasis n)
      (oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) k i)) 2 (normalizedCubeMeasure Q) :=
    (main_continuous_memLp_top Q (continuous_const.inner
      ((old_signed_rotated_white_continuous b L k i).comp (continuous_id.const_smul (L.1⁻¹))))).mono_exponent (by simp)
  have hh : MemLp (fun x => matVecMul responsePlanarJ
      (fun l => oldSignedRemainderCoordinate Q b L plus n (i,l) x) k) 2 (normalizedCubeMeasure Q) := by
    rw [←old_signed_output_remainder_h1_toFun]
    exact (oldSignedOutputRemainderH1 Q b L plus n i k).memL2_normalizedCubeMeasure
  have hiP := old_signed_physical_mode_pairing_integrable Q b L n r _ hr hp
  have hiH := old_signed_physical_mode_pairing_integrable Q b L n r _ hr hh
  have he : (fun x => r x*q3Convolution b L h3Zero (whiteBasis n) x*
      matVecMul responsePlanarJ (fun l => oldSignedFlatCoordinate Q b L plus n (i,l) x) k)=
      (fun x => r x*q3Convolution b L h3Zero (whiteBasis n) x*
        inner ℝ (whiteBasis n) (oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) k i))+
      (fun x => r x*q3Convolution b L h3Zero (whiteBasis n) x*
        matVecMul responsePlanarJ (fun l => oldSignedRemainderCoordinate Q b L plus n (i,l) x) k) := by
    funext x
    rw [old_signed_flat_output_decomposition]
    simp only [Pi.add_apply]
    ring
  rw [he]
  exact integral_add hiP hiH

/-- Exact complete covariance identity for either actual finite-square
flat family. This is the local signed cancellation underlying AN (6.3). -/
theorem old_signed_flat_covariance_integral (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (plus : Bool) (i k : Fin 2)
    (r : Vec 2 → ℝ) (hr : MemLp r 2 (normalizedCubeMeasure Q)) :
    HasSum (fun n : whiteBasisIndex => ∫ x,r x*
      q3Convolution b L h3Zero (whiteBasis n) x*
        matVecMul responsePlanarJ (fun l => oldSignedFlatCoordinate Q b L plus n (i,l) x) k
          ∂normalizedCubeMeasure Q)
      ((-(b^2/2)*(if k=i then 1 else 0))*(∫ x,r x ∂normalizedCubeMeasure Q)+
        ∫ x,r x*oldSignedRemainderCovarianceField Q b L plus i x k ∂normalizedCubeMeasure Q) := by
  have hs := (old_signed_physical_normalized_covariance Q b L k i r hr).add
    (old_signed_rotated_remainder_covariance_integral Q b L plus i k r hr)
  apply hs.congr_fun
  intro n
  exact old_signed_flat_covariance_integral_split Q b L plus n i k r hr

end
end ASDExplicitGamma.Native
