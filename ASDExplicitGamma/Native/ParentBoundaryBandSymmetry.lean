module

public import ASDExplicitGamma.Native.GenericSourceBandFrame
public import ASDExplicitGamma.Model.CellSymmetry

/-! Exact whole-sample symmetries of an arbitrary finite attenuated band.
The same action moves the completed OLD field and every fresh shell. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Algsuperdiff.Frozen.Assumptions
open Inverse
noncomputable section

/-- Rotation about a physical center acts on the entire actual sample. -/
def parentBoundarySampleRotateAbout (c : Vec 2) (R : Mat 2) (hR : IsSignedPermutationMatrix R) :
    Cutoff.CutoffSample 2 → Cutoff.CutoffSample 2 :=
  Cutoff.translateCutoffSample (-c) ∘ Cutoff.rotateCutoffSample R hR ∘ Cutoff.translateCutoffSample c

/-- The finite weighted coefficient commutes with translation of the same
whole sample; no old/fresh or cross-cell independence is asserted. -/
theorem parent_boundary_band_translate (M : ABKModel 2) (n J : ℤ) (weights : ℤ → ℝ)
    (z : Vec 2) (omega : Cutoff.CutoffSample 2) (x : Vec 2) :
    attenuatedCoefficient M n J weights (Cutoff.translateCutoffSample z omega) x=
      attenuatedCoefficient M n J weights omega (x+z) := by
  simp [attenuatedCoefficient,Cutoff.coefficientCutoff_translateCutoffSample,
    Cutoff.translateCutoffSample_val,ShellField.translateSequence_apply,ShellField.translate_apply,
    translateReg_apply]

/-- Every physical common-noise covariance transforms with the whole band
under a signed coordinate permutation. -/
theorem parent_boundary_band_rotate (M : ABKModel 2) (n J : ℤ) (weights : ℤ → ℝ)
    (R : Mat 2) (hR : IsSignedPermutationMatrix R) (omega : Cutoff.CutoffSample 2) (x : Vec 2) :
    attenuatedCoefficient M n J weights (Cutoff.rotateCutoffSample R hR omega) x=
      matTranspose R*attenuatedCoefficient M n J weights omega (matVecMul R x)*R := by
  simp [attenuatedCoefficient,Cutoff.coefficientCutoff_rotateCutoffSample,
    Cutoff.rotateCutoffSample_val,ShellField.rotateSequence_apply,ShellField.rotate_apply,
    rotateReg_apply,Matrix.mul_add,Matrix.add_mul,Finset.mul_sum,Finset.sum_mul]

/-- The actual cutoff law is preserved by the same centered rotation of
every shell. This is whole-sequence J3, not independent cell rotations. -/
theorem parent_boundary_band_rotate_about_preserving (M : ABKModel 2)
    (c : Vec 2) (R : Mat 2) (hR : IsSignedPermutationMatrix R) :
    MeasurePreserving (parentBoundarySampleRotateAbout c R hR)
      (Cutoff.cutoffSampleLaw M).toMeasure (Cutoff.cutoffSampleLaw M).toMeasure := by
  have ht (z : Vec 2) : MeasurePreserving (Cutoff.translateCutoffSample z)
      (Cutoff.cutoffSampleLaw M).toMeasure (Cutoff.cutoffSampleLaw M).toMeasure :=
    ⟨Cutoff.measurable_translateCutoffSample z,Cutoff.map_translateCutoffSample_cutoffSampleLaw M z⟩
  have hr : MeasurePreserving (Cutoff.rotateCutoffSample R hR)
      (Cutoff.cutoffSampleLaw M).toMeasure (Cutoff.cutoffSampleLaw M).toMeasure :=
    ⟨Cutoff.measurable_rotateCutoffSample R hR,Cutoff.map_rotateCutoffSample_cutoffSampleLaw M R hR⟩
  exact (ht (-c)).comp (hr.comp (ht c))

end
end ASDExplicitGamma.Native
