module

public import ASDExplicitGamma.Main.ELinearXiHalf
public import ASDExplicitGamma.Main.ELinearPathwise
public import ASDExplicitGamma.Main.EOscillationCellHistoryTranslation
public import ASDExplicitGamma.Main.EOscillationDepthFiveProfile
public import ASDExplicitGamma.Main.AffineObserverFrame

/-! The local histories of the actual `L` group, computed from the frame
field of the root partial-insertion coefficient, are the translated root
histories used by the accepted bank and multiplier moments. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic
open Algsuperdiff.Section3.Cutoff
attribute [local irreducible] Homogenization.descendantsAtDepth

theorem main_partial_inserted_symmPart (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    symmPart (Model.partialInsertedCoefficient M m t ω x) = M.nu • (1 : Mat 2) := by
  have ha := Cutoff.symmPart_coefficientCutoff M.nu m ω x
  ext i j
  have hb := congrFun (congrFun ha i) j
  have hj := (ω.1 (m + 1)).skew_entry x i j
  change (Cutoff.coefficientCutoff M.nu m ω x i j +
    Cutoff.coefficientCutoff M.nu m ω x j i) / 2 = (M.nu • (1 : Mat 2)) i j at hb
  change ((Cutoff.coefficientCutoff M.nu m ω x i j + Real.sqrt t * ω.1 (m + 1) x i j) +
    (Cutoff.coefficientCutoff M.nu m ω x j i + Real.sqrt t * ω.1 (m + 1) x j i)) / 2 = _
  rw [hj]
  linarith

/-- On the open root cube, the frame field of the actual partial response is
the normalized partial-insertion coefficient. -/
theorem old_signed_partial_frame_eq_scaled_partial
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2) (x : Vec 2)
    (hx : x ∈ openCubeSet (originCube 2 m)) :
    oldSignedPartialFrameField M m 1 t ω x =
      (Annealed.sigmaBar M m : ℝ)⁻¹ •
        (Model.partialInsertedCoefficient M m t ω).toFun x := by
  let K : Set (Vec 2) := closure (cubeSet (originCube 2 m))
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 m)).isCompact_closure
  let xK : K := ⟨x, subset_closure (openCubeSet_subset_cubeSet (originCube 2 m) hx)⟩
  have hscalar := Gaussian.modelInsertedScalar_apply K M ell m hK t ω xK
  have hv : responseCoefficientExtension (oldSignedPartialResponseCoefficient m 1 t ω) x =
      (Model.partialInsertedCoefficient M m t ω).toFun x 1 0 := by
    unfold oldSignedPartialResponseCoefficient
    rw [show m + ((1:ℕ):ℤ) - 1 = m by omega]
    rw [pureFluxOpenResponseRestriction_value m _ hx]
    simpa [xK] using hscalar
  have hσ : (0:ℝ) < Annealed.sigmaBar M m := (Annealed.sigmaBar_characterization M m).1
  have hsym := main_partial_inserted_symmPart M m t ω x
  have hp := planar_coefficient_eq_of_symmPart M.nu _ hsym
  change responsePlanarCoefficient (M.nu / (Annealed.sigmaBar M m : ℝ))
      (responseCoefficientExtension (oldSignedPartialResponseCoefficient m 1 t ω) x / _) = _
  rw [hv]
  rw [← hp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [responsePlanarCoefficient, responsePlanarJ, Matrix.smul_apply] <;>
    field_simp [ne_of_gt hσ]

end ASDExplicitGamma.Main

namespace ASDExplicitGamma.Main

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic
open Algsuperdiff.Section3.Cutoff
attribute [local irreducible] Homogenization.descendantsAtDepth

end ASDExplicitGamma.Main
