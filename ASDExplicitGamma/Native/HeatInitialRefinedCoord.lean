module

public import ASDExplicitGamma.Native.HeatVHEATRefinedVector
public import ASDExplicitGamma.Native.HeatInitialDescendants
public import ASDExplicitGamma.Model.CutoffAction
public import ASDExplicitGamma.Scalar.LawShiftCarrier

/-! Physical child centers of the depth-ten carrier in canonical grid coordinates. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian Algsuperdiff.Section4.Provider.Annular Algsuperdiff.Frozen.Assumptions
open scoped ENNReal BigOperators

set_option linter.constructorNameAsVariable false

/-- The centre of a depth-ten child is the affine image of the canonical grid centre. -/
theorem nativeHeatQ3RefinedChildCube_center (Q : TriadicCube 2)
    (ij : Fin (3^10) × Fin (3^10)) :
    cubeCenter (nativeHeatQ3RefinedChildCube Q ij) =
      fun a => cubeCenter Q a + cubeScaleFactor Q *
        (q3GridCenterVector 10 ij a - (1 / 2 : ℝ)) := by
  let k := nativeHeatQ3RefinedChildDigits ij
  let C := Triadic.diagMeshCell Q 10 k
  have hcorner := Triadic.diagMeshCell_corner Q 10 k
  have hside := Triadic.diagMeshCell_side Q 10 k
  funext a
  fin_cases a
  · change cubeCenter C 0 = _
    rw [show cubeCenter C 0 = Triadic.cubeCorner C 0 +
        cubeScaleFactor C / 2 by
      simp [cubeCenter, Triadic.cubeCorner]
      ring,
      hcorner 0, hside]
    simp [k, nativeHeatQ3RefinedChildDigits, Triadic.cubeCorner, Triadic.diagMeshRadius,
      cubeCenter, cubeScaleFactor, q3GridCenterVector, q3GridCenterAxis]
    field_simp
    ring_nf
  · change cubeCenter C 1 = _
    rw [show cubeCenter C 1 = Triadic.cubeCorner C 1 +
        cubeScaleFactor C / 2 by
      simp [cubeCenter, Triadic.cubeCorner]
      ring,
      hcorner 1, hside]
    simp [k, nativeHeatQ3RefinedChildDigits, Triadic.cubeCorner, Triadic.diagMeshRadius,
      cubeCenter, cubeScaleFactor, q3GridCenterVector, q3GridCenterAxis]
    field_simp
    ring_nf

theorem nativeHeatQ3RefinedChildCube_center_scaled (Q : TriadicCube 2) (m : ℤ)
    (hscale : Q.scale = m + 10) (ij : Fin (3^10) × Fin (3^10)) :
    cubeCenter (nativeHeatQ3RefinedChildCube Q ij) =
      nativeHeatQ3ParentOrigin Q + (3 : ℝ) ^ (m + 10) • q3GridCenterVector 10 ij := by
  rw [nativeHeatQ3RefinedChildCube_center]
  funext a
  fin_cases a <;>
    simp [nativeHeatQ3ParentOrigin, Triadic.cubeCorner, cubeCenter,
      cubeScaleFactor, q3GridCenterVector, q3GridCenterAxis] <;>
    rw [← hscale] <;> ring_nf


/-- The actual fresh value at a depth-ten child centre, written shell by shell. -/
theorem nativeHeatQ3RefinedFreshRaw_eq_sum (m : ℤ) (ω : Cutoff.CutoffSample 2)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    nativeHeatQ3RefinedCarrierSourceFreshRaw m ω i =
      ∑ d : Fin 9, shellScalarValue (ω.1 (m + (d.val : ℤ) + 2))
        (cubeCenter (nativeHeatQ3RefinedCarrierChild m i)) := by
  classical
  unfold nativeHeatQ3RefinedCarrierSourceFreshRaw
    nativeHeatQ3RefinedCarrierSourceCenterMap childCenterMap
  simp only [ContinuousLinearMap.pi_apply, ContinuousMap.evalCLM_apply,
    Gaussian.modelBand, ContinuousMap.sum_apply]
  apply Finset.sum_congr rfl
  intro d _
  rfl

theorem nativeHeatQ3Refined_shiftedShellValue_eq_physical (M : ABKModel 2)
    (Q : TriadicCube 2) (m : ℤ) (hscale : Q.scale = m + 10)
    (ij : Fin (3^10) × Fin (3^10)) (d : Fin 9) (ω : Cutoff.CutoffSample 2) :
    shellScalarValue
      ((ASDExplicitGamma.Scalar.cutoffScaleShift M.gamma (m + 10)
        (Cutoff.translateCutoffSample (nativeHeatQ3ParentOrigin Q) ω)).val
        (((d.val + 2 : ℕ) : ℤ) - ((10 : ℕ) : ℤ)))
        (q3GridCenterVector 10 ij) =
    Real.rpow 3 (M.gamma * (-((m + 10 : ℤ) : ℝ))) *
      shellScalarValue (ω.1 (m + (d.val : ℤ) + 2))
        (cubeCenter (nativeHeatQ3RefinedChildCube Q ij)) := by
  let n : ℤ := m + 10
  have hindex : ((d.val + 2 : ℕ) : ℤ) - ((10 : ℕ) : ℤ) + n = m + (d.val : ℤ) + 2 := by
    dsimp [n]
    push_cast
    omega
  have hinv : (((3 : ℝ) ^ (-n))⁻¹) = (3 : ℝ) ^ n := by
    rw [zpow_neg]
    simp
  have hpoint : (((3 : ℝ) ^ (-n))⁻¹) • q3GridCenterVector 10 ij +
      nativeHeatQ3ParentOrigin Q = cubeCenter (nativeHeatQ3RefinedChildCube Q ij) := by
    rw [hinv, nativeHeatQ3RefinedChildCube_center_scaled Q m hscale ij]
    exact add_comm _ _
  have hraw :
      shellScalarValue
        ((ASDExplicitGamma.Scalar.cutoffScaleShift M.gamma n
          (Cutoff.translateCutoffSample (nativeHeatQ3ParentOrigin Q) ω)).val
          (((d.val + 2 : ℕ) : ℤ) - ((10 : ℕ) : ℤ)))
        (q3GridCenterVector 10 ij) =
      Real.rpow 3 (M.gamma * ((-n : ℤ) : ℝ)) *
        shellScalarValue
          (ω.1 (((d.val + 2 : ℕ) : ℤ) - ((10 : ℕ) : ℤ) + n))
          ((((3 : ℝ) ^ (-n))⁻¹) • q3GridCenterVector 10 ij +
            nativeHeatQ3ParentOrigin Q) := by
    simp [ASDExplicitGamma.Scalar.cutoffScaleShift,
      ASDExplicitGamma.Scalar.shellScaleShift,
      Cutoff.translateCutoffSample_val,
      ShellField.triadicScale_apply, ShellField.translateSequence_apply,
      ShellField.translate_apply, shellScalarValue, shellScalarEntry,
      n, smul_eq_mul]
  rw [hindex, hpoint] at hraw
  simpa [n] using hraw

/-- The translated, scale-shifted canonical band is the inverse-amplitude physical
fresh value at the child. -/
theorem nativeHeatQ3Refined_shiftedBand_eq_physical (M : ABKModel 2)
    (Q : TriadicCube 2) (m : ℤ) (hscale : Q.scale = m + 10)
    (ij : Fin (3^10) × Fin (3^10)) (ω : Cutoff.CutoffSample 2) :
    modelBand (nativeHeatQ3GridCenterSet 10)
        (fun d : Fin 9 => ((d.val + 2 : ℕ) : ℤ) - ((10 : ℕ) : ℤ))
        (ASDExplicitGamma.Scalar.cutoffScaleShift M.gamma (m + 10)
          (Cutoff.translateCutoffSample (nativeHeatQ3ParentOrigin Q) ω))
        (nativeHeatQ3GridCenterPoint 10 ij) =
      Real.rpow 3 (M.gamma * (-((m + 10 : ℤ) : ℝ))) *
        ∑ d : Fin 9, shellScalarValue (ω.1 (m + (d.val : ℤ) + 2))
          (cubeCenter (nativeHeatQ3RefinedChildCube Q ij)) := by
  classical
  simp only [Gaussian.modelBand, ContinuousMap.sum_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  exact nativeHeatQ3Refined_shiftedShellValue_eq_physical M Q m hscale ij d ω


theorem nativeHeatQ3Refined_rpow_mul_inv (M : ABKModel 2) (m : ℤ) :
    Real.rpow 3 (M.gamma * (-((m + 10 : ℤ) : ℝ))) *
      Real.rpow 3 (M.gamma * ((m + 10 : ℤ) : ℝ)) = 1 := by
  change (3 : ℝ) ^ (M.gamma * (-((m + 10 : ℤ) : ℝ))) *
    (3 : ℝ) ^ (M.gamma * ((m + 10 : ℤ) : ℝ)) = 1
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  have hzero : M.gamma * (-((m + 10 : ℤ) : ℝ)) +
      M.gamma * ((m + 10 : ℤ) : ℝ) = 0 := by ring
  rw [hzero]
  simp

/-- The actual fresh value at child `ij` is the amplitude times the canonical band at
the translated and scale-shifted sample. -/
theorem nativeHeatQ3RefinedFreshRaw_eq_scaled_band (M : ABKModel 2) (m : ℤ)
    (ω : Cutoff.CutoffSample 2) (ij : Fin (3^10) × Fin (3^10)) :
    nativeHeatQ3RefinedCarrierSourceFreshRaw m ω (finProdFinEquiv ij) =
      Real.rpow 3 (M.gamma * ((m + 10 : ℤ) : ℝ)) *
        modelBand (nativeHeatQ3GridCenterSet 10)
          (fun d : Fin 9 => ((d.val + 2 : ℕ) : ℤ) - ((10 : ℕ) : ℤ))
          (ASDExplicitGamma.Scalar.cutoffScaleShift M.gamma (m + 10)
            (Cutoff.translateCutoffSample
              (nativeHeatQ3ParentOrigin (originCube 2 (m + 10))) ω))
          (nativeHeatQ3GridCenterPoint 10 ij) := by
  classical
  let Q0 := originCube 2 (m + 10)
  have hscale : Q0.scale = m + 10 := by simp [Q0, originCube]
  have hband := nativeHeatQ3Refined_shiftedBand_eq_physical M Q0 m hscale ij ω
  have hfresh := nativeHeatQ3RefinedFreshRaw_eq_sum m ω (finProdFinEquiv ij)
  have hchild : nativeHeatQ3RefinedCarrierChild m (finProdFinEquiv ij) =
      nativeHeatQ3RefinedChildCube Q0 ij := by
    simp [nativeHeatQ3RefinedCarrierChild, Q0]
  rw [hfresh, hchild]
  rw [hband]
  have hAB := nativeHeatQ3Refined_rpow_mul_inv M m
  rw [← mul_assoc, mul_comm (Real.rpow 3 (M.gamma * ((m + 10 : ℤ) : ℝ))), hAB, one_mul]

end ASDExplicitGamma.Native
