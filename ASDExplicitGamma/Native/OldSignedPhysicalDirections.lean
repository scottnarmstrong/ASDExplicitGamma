module

public import ASDExplicitGamma.Native.OldSignedPhysicalCoefficient
public import ASDExplicitGamma.Gaussian.Q3Directions

/-! The physical OLD directions sigma psi are the actual main-cube q3
heat directions at amplitude sigma b, with the same white-mode family. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Inverse
noncomputable section

/-- Multiplying the physical shell amplitude multiplies its actual q3
convolution by exactly the same scalar. -/
theorem old_signed_q3_mul_amplitude (sigma b : ℝ) (L : {l : ℝ // 0<l})
    (w : WhiteNoise) (x : Vec 2) :
    q3Convolution (sigma*b) L h3Zero w x=sigma*q3Convolution b L h3Zero w x := by
  rw [q3Convolution_eq_integral,q3Convolution_eq_integral]
  have he : (fun y => q3SectionFunction (sigma*b) L h3Zero x y*w y)=
      fun y => sigma*(q3SectionFunction b L h3Zero x y*w y) := by
    funext y
    unfold q3SectionFunction
    ring
  rw [he,integral_const_mul]

/-- The actual padded main-cube direction is exactly the OLD physical
coefficient sigma psi on the closed observation square. -/
theorem old_signed_physical_direction_eq (m : ℤ) (sigma b : ℝ)
    (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) :
    pureFluxMainCubeQ3ResponseCoefficient m (sigma*b) L
      (@Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex) n)=
      oldSignedPhysicalCoefficient (originCube 2 m) sigma b L n := by
  ext x
  let y : closure (cubeSet (originCube 2 m)) :=
    ⟨x.1,closure_mono (openCubeSet_subset_cubeSet (originCube 2 m)) x.2⟩
  change mainCubeH3Value m (sigma*b) L
    (mainCubeQ3Directions m (sigma*b) L
      (@Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex) n))
      y=
    sigma*q3Convolution b L h3Zero (whiteBasis n) x.1
  rw [mainCubeH3Value_direction]
  change q3Convolution (sigma*b) L h3Zero
    (gaussEnumerated whiteBasis
      (@Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex) n)) x.1=_
  rw [enumerated_encode,old_signed_q3_mul_amplitude]

end
end ASDExplicitGamma.Native
