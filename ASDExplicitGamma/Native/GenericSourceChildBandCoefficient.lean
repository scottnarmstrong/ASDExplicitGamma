module

public import ASDExplicitGamma.Native.GenericSourceChildBandHeat
public import ASDExplicitGamma.Native.GenericSourceBandCoefficient

/-! The refined child-cube scalar is the actual simultaneous attenuated field,
with completed old cutoff `n` and observation scale `n-1`. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Algsuperdiff.Frozen.Assumptions
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic ASDExplicitGamma.Response
noncomputable section

/-- The simultaneous compact scalar is exactly the scalar entry of the
actual attenuated coefficient, retaining every shell in the finite band. -/
theorem native_source_child_band_scalar_apply (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (x : closure (cubeSet (originCube 2 (n-1)))) :
    nativeSourceChildBandScalar n height t ω x =
      attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω x 1 0 := by
  let K := closure (cubeSet (originCube 2 (n-1)))
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 (n-1))).isCompact_closure
  simp only [nativeSourceChildBandScalar,ContinuousMap.add_apply,ContinuousMap.smul_apply,
    modelBand,ContinuousMap.sum_apply,smul_eq_mul]
  rw [olderField_apply_eq_coefficientCutoff K M ell n hK ω x]
  rw [Finset.mul_sum]
  have hsum := native_source_band_index_sum n height
    (fun j => Real.sqrt t*(shellFieldScalarRestriction K (ω.1 j) x))
  rw [hsum]
  simp only [attenuatedCoefficient,Matrix.add_apply,Matrix.sum_apply,
    Matrix.smul_apply,smul_eq_mul]
  rfl

/-- On the observation cube, the simultaneous compact source scalar gives
precisely the actual attenuated physical coefficient with its fixed `M.nu`. -/
theorem native_source_child_band_coefficient_on_cube (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) (x : Vec 2) (hx : x ∈ cubeSet (originCube 2 (n-1))) :
    responsePlanarCoefficientField M.nu
      (ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet (originCube 2 (n-1)))) ℝ ℝ
        (nativeSourceChildBandScalar n height t ω)) x =
      attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω x := by
  rw [responsePlanarCoefficientField,responseCoefficientExtension_eq _ hx,
    ContinuousMap.linearIsometryBoundedOfCompact_apply_apply,native_source_child_band_scalar_apply]
  exact native_source_planar_of_symm M.nu _ (native_source_band_attenuated_symm M n height t ω x)

end
end ASDExplicitGamma.Native
