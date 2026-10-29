module

public import ASDExplicitGamma.Native.OldSignedQ1SetupReadable
public import ASDExplicitGamma.Native.ParentBoundaryModelScales

/-! Exact dimensionless q1 mesh scales at the actual one-shell physical length. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Main Triadic Algsuperdiff.Section3 Numerics.Native
noncomputable section

/-- The depth-five cell to fresh-shell ratio is exactly 3^-6. -/
theorem old_signed_q1_mesh_length_ratio (n : ℤ) :
    (cubeScaleFactor (originCube 2 n)/3^5)/(q3ModelLength (n+1)).val=(1/729:ℝ) := by
  have hh := parent_boundary_model_length_ratio n 1
  norm_num only [Nat.cast_one,pow_one] at hh
  calc
    _ = (cubeScaleFactor (originCube 2 n)/(q3ModelLength (n+1)).val)/3^5 := by ring
    _ = (1/3:ℝ)/3^5 := by rw [hh]
    _ = _ := by norm_num

/-- The second mesh moment retains its exact physical variance factor. -/
theorem old_signed_q1_mesh_second (n : ℤ) (b : ℝ) :
    (cubeScaleFactor (originCube 2 n)/3^5)^2*b^2/(q3ModelLength (n+1)).val^2=
      b^2*(1/531441:ℝ) := by
  calc
    _ = ((cubeScaleFactor (originCube 2 n)/3^5)/(q3ModelLength (n+1)).val)^2*b^2 := by ring
    _ = _ := by rw [old_signed_q1_mesh_length_ratio]; ring

/-- The fourth mesh moment has the matching exact 3^-24 factor. -/
theorem old_signed_q1_mesh_fourth (n : ℤ) (b : ℝ) :
    (cubeScaleFactor (originCube 2 n)/3^5)^4*b^2/(q3ModelLength (n+1)).val^4=
      b^2*(1/282429536481:ℝ) := by
  calc
    _ = ((cubeScaleFactor (originCube 2 n)/3^5)/(q3ModelLength (n+1)).val)^4*b^2 := by ring
    _ = _ := by rw [old_signed_q1_mesh_length_ratio]; ring

/-- The actual second mesh moment fits the identical frozen A2 field,
proportionally in theta, with no assumed coefficient bound. -/
theorem old_signed_q1_model_second_moment
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) :
    let b := q3ModelAmplitude M h (n+1)/(Annealed.sigmaBar M n:ℝ)
    (cubeScaleFactor (originCube 2 n)/3^5)^2*b^2/(q3ModelLength (n+1)).val^2≤
      theta M*(nativeSetupQ1001FieldsR.getD 1 0) := by
  intro b
  rw [old_signed_q1_mesh_second,old_signed_q1_setup_readable_01]
  have hh := mul_le_mul_of_nonneg_right (old_signed_q1_model_variance M h hg n hstate)
    (by norm_num : (0:ℝ)≤1/531441)
  exact hh.trans_eq (by ring)

end
end ASDExplicitGamma.Native
