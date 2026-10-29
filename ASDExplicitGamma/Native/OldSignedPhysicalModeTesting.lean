module

public import ASDExplicitGamma.Native.OldSignedRemainderCovarianceIntegral
public import ASDExplicitGamma.Native.OldSignedPhysicalCovarianceIntegral

/-! Integrability and exact normalized bulk contraction for actual
physical modes tested against spatial L2 fields. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main ASDExplicitGamma.Triadic
noncomputable section

private instance oldSignedPhysicalModeTestingHolderTwoTwoOne : ENNReal.HolderTriple 2 2 1 :=
  ⟨by simpa only [inv_one] using ENNReal.inv_two_add_inv_two⟩

/-- Multiplication by an actual physical white mode preserves spatial L2
on the cube; its boundedness is supplied by actual continuity. -/
theorem old_signed_physical_mode_mul_memLp (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (f : Vec 2 → ℝ)
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    MemLp (fun x => q3Convolution b L h3Zero (whiteBasis n) x*f x)
      2 (normalizedCubeMeasure Q) := by
  have hp := main_continuous_memLp_top Q
    (q3Convolution_continuous b L h3Zero (whiteBasis n))
  exact hp.mul hf

/-- Every actual scalar mode pairing with two genuine L2 spatial fields
is integrable, before any complete-mode interchange. -/
theorem old_signed_physical_mode_pairing_integrable (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (r f : Vec 2 → ℝ)
    (hr : MemLp r 2 (normalizedCubeMeasure Q)) (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    Integrable (fun x => r x*q3Convolution b L h3Zero (whiteBasis n) x*f x)
      (normalizedCubeMeasure Q) := by
  have hi := hr.integrable_mul (old_signed_physical_mode_mul_memLp Q b L n f hf)
  convert hi using 1
  funext x
  change r x*q3Convolution b L h3Zero (whiteBasis n) x*f x=
    r x*(q3Convolution b L h3Zero (whiteBasis n) x*f x)
  ring

/-- Exact signed bulk covariance in the source normalized measure. -/
theorem old_signed_physical_normalized_covariance (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (i j : Fin 2) (r : Vec 2 → ℝ)
    (hr : MemLp r 2 (normalizedCubeMeasure Q)) :
    HasSum (fun n : whiteBasisIndex => ∫ x,r x*
      q3Convolution b L h3Zero (whiteBasis n) x*
        inner ℝ (whiteBasis n) (oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j)
          ∂normalizedCubeMeasure Q)
      ((-(b^2/2)*(if i=j then 1 else 0))*(∫ x,r x ∂normalizedCubeMeasure Q)) := by
  have hs := (old_signed_physical_integrated_covariance Q b L i j r
    (integrableOn_open_of_memLp hr)).mul_left (cubeVolume Q)⁻¹
  have he : (cubeVolume Q)⁻¹*((-(b^2/2)*(if i=j then 1 else 0))*
      (∫ x in openCubeSet Q,r x))=
      (-(b^2/2)*(if i=j then 1 else 0))*(∫ x,r x ∂normalizedCubeMeasure Q) := by
    rw [integral_normalized_eq_open]
    ring
  rw [he] at hs
  apply hs.congr_fun
  intro n
  exact integral_normalized_eq_open Q _

end
end ASDExplicitGamma.Native
