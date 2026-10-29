module

public import ASDExplicitGamma.Main.EOscillationResponseHistory
public import ASDExplicitGamma.Main.EOscillationInverseHistoryAdapter
public import ASDExplicitGamma.Main.MultiplierMoments
public import ASDExplicitGamma.Native.HeatVHEATSourceHistoryTransport
public import ASDExplicitGamma.Native.HeatVHEATResponseTranslation
public import ASDExplicitGamma.Native.OldSignedHistoryCongr
public import ASDExplicitGamma.Gaussian.FixedNuPositive
public import ASDExplicitGamma.Scalar.CellTranslation
public import Homogenization.CoarseGraining.Translation
public import Homogenization.Geometry.TriadicCubeTranslation

/-! Translation of the actual OLD inverse and response histories from a
depth-five source cell to the origin cell at that scale. -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open scoped ENNReal

noncomputable section

private theorem main_eosc_cubeTranslationVector_descendant
    (z : Fin 2 → ℤ) (Q R : TriadicCube 2) (j : ℕ)
    (hR : R ∈ descendantsAtDepth Q j) :
    nativeHeatCubeTranslationVector (descendantTranslationShift j z) R =
      nativeHeatCubeTranslationVector z Q := by
  have hscale : R.scale = Q.scale - (j : ℤ) :=
    scale_eq_sub_of_mem_descendantsAtDepth hR
  have hpow : (3 : ℝ) ^ (j : ℤ) * (3 : ℝ) ^ (Q.scale - (j : ℤ)) =
      (3 : ℝ) ^ Q.scale := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    omega
  ext i
  simp only [nativeHeatCubeTranslationVector, descendantTranslationShift,
    Int.cast_mul, Int.cast_pow, Int.cast_ofNat, cubeScaleFactor]
  rw [hscale]
  have hnat : (3 : ℝ) ^ j = (3 : ℝ) ^ (j : ℤ) := by norm_cast
  rw [hnat]
  calc
    _ = (z i : ℝ) *
        ((3 : ℝ) ^ (j : ℤ) * (3 : ℝ) ^ (Q.scale - (j : ℤ))) := by ring
    _ = _ := by rw [hpow]

private theorem main_eosc_openCubeSet_translateCube
    (z : Fin 2 → ℤ) (Q : TriadicCube 2) :
    openCubeSet (translateCube z Q) =
      translateSet (nativeHeatCubeTranslationVector z Q) (openCubeSet Q) := by
  ext x
  rw [mem_translateSet_iff_sub_mem, mem_openCubeSet_translateCube_iff]
  rfl

/-- The full-response depth maximum is invariant under the exact translated
triadic cell and the inverse translate of its coefficient field. -/
theorem main_eosc_fullResponseDepthMax_translateCube
    (z : Fin 2 → ℤ) (Q : TriadicCube 2) (a : CoeffField 2) (j : ℕ) :
    fullResponseDepthMax (translateCube z Q)
        (translateCoeffField (-nativeHeatCubeTranslationVector z Q) a) j =
      fullResponseDepthMax Q a j := by
  classical
  unfold fullResponseDepthMax
  rw [descendantsAtDepth_translateCube z Q j]
  apply Book.Ch02.finsetSupReal_image
  intro R hR
  have hz := main_eosc_cubeTranslationVector_descendant z Q R j hR
  unfold fullResponseOperatorNorm
  rw [nativeHeat_cubeSet_translateCube_eq_responseTranslation]
  rw [hz, coarseBlockMatrix_translateSet_eq_translateCoeffField]
  have hcoeff : translateCoeffField (nativeHeatCubeTranslationVector z Q)
      (translateCoeffField (-nativeHeatCubeTranslationVector z Q) a) = a := by
    funext x
    simp [translateCoeffField]
  rw [hcoeff]

/-- The complete OLD full-response history is invariant under translation,
including its full infinite depth series. -/
theorem main_eosc_responseHistory_translateCube
    (z : Fin 2 → ℤ) (Q : TriadicCube 2) (a : CoeffField 2) :
    oldSignedResponseHistory (translateCube z Q)
        (translateCoeffField (-nativeHeatCubeTranslationVector z Q) a) =
      oldSignedResponseHistory Q a := by
  change (completeFullResponseHistory (translateCube z Q)
      (translateCoeffField (-nativeHeatCubeTranslationVector z Q) a)).toReal =
    (completeFullResponseHistory Q a).toReal
  apply congrArg ENNReal.toReal
  unfold completeFullResponseHistory
  apply congrArg (fun r : ℝ≥0∞ => ENNReal.ofReal (1-inverseHistoryDiscount) * r)
  apply tsum_congr
  intro j
  rw [main_eosc_fullResponseDepthMax_translateCube]

private theorem main_eosc_translateCube_origin_eq (U : TriadicCube 2) :
    translateCube U.index (originCube 2 U.scale) = U := by
  cases U
  simp only [translateCube, originCube, Pi.zero_apply, zero_add]

private theorem main_eosc_cubeTranslationVector_eq_triadicShift
    (U : TriadicCube 2) :
    nativeHeatCubeTranslationVector U.index (originCube 2 U.scale) =
      triadicCubeShift U := by
  ext i
  simp [nativeHeatCubeTranslationVector, triadicCubeShift, cubeScaleFactor,
    originCube]

/-- At every depth-five source cell, both OLD histories are the histories of
the origin-cell coefficient after translating the actual cutoff sample to
that cell. This is a pathwise identity with the translated sample; it does
not claim equality with the root history at the unshifted sample. -/
theorem main_eosc_local_histories_translate_origin
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (U : TriadicCube 2)
    (ω : CutoffSample 2) :
    oldSignedInverseHistory U
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (mainInsertionSkewCoefficient m t U ω)) =
      oldSignedInverseHistory (originCube 2 U.scale)
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (mainInsertionSkewCoefficient m t (originCube 2 U.scale)
            (Cutoff.translateCutoffSample (triadicCubeShift U) ω))) ∧
    oldSignedResponseHistory U
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (mainInsertionSkewCoefficient m t U ω)) =
      oldSignedResponseHistory (originCube 2 U.scale)
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (mainInsertionSkewCoefficient m t (originCube 2 U.scale)
            (Cutoff.translateCutoffSample (triadicCubeShift U) ω))) := by
  let Q : TriadicCube 2 := originCube 2 U.scale
  let z : Vec 2 := triadicCubeShift U
  let σ : ℝ := Annealed.sigmaBar M m
  let aU : CoeffField 2 := responseFramePlanarCoefficientField M.nu σ
    (mainInsertionSkewCoefficient m t U ω)
  let a0 : CoeffField 2 := responseFramePlanarCoefficientField M.nu σ
    (mainInsertionSkewCoefficient m t Q (Cutoff.translateCutoffSample z ω))
  let aBack : CoeffField 2 := translateCoeffField (-z) a0
  have hUcube : translateCube U.index Q = U := by
    simpa [Q] using main_eosc_translateCube_origin_eq U
  have hvec : nativeHeatCubeTranslationVector U.index Q = z := by
    simpa [Q, z] using main_eosc_cubeTranslationVector_eq_triadicShift U
  have hcube : openCubeSet U = translateSet z (openCubeSet Q) := by
    rw [← hUcube]
    rw [main_eosc_openCubeSet_translateCube]
    simp [hvec]
  have hσ : 0 < σ := by
    dsimp [σ]
    exact (Annealed.sigmaBar_characterization M m).1
  have hEllU : IsEllipticFieldOn (M.nu / σ)
      (((M.nu / σ) ^ 2 +
        (‖mainInsertionSkewCoefficient m t U ω‖ / σ) ^ 2) / (M.nu / σ))
      (openCubeSet U) aU := by
    dsimp [aU, σ]
    exact responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet U) M.nu (Annealed.sigmaBar M m : ℝ)
      M.nu_pos (Annealed.sigmaBar_characterization M m).1
      (mainInsertionSkewCoefficient m t U ω)
  have hEll0 : IsEllipticFieldOn (M.nu / σ)
      (((M.nu / σ) ^ 2 +
        (‖mainInsertionSkewCoefficient m t Q
          (Cutoff.translateCutoffSample z ω)‖ / σ) ^ 2) / (M.nu / σ))
      (openCubeSet Q) a0 := by
    dsimp [a0, Q, σ]
    exact responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet (originCube 2 U.scale)) M.nu
      (Annealed.sigmaBar M m : ℝ) M.nu_pos
      (Annealed.sigmaBar_characterization M m).1
      (mainInsertionSkewCoefficient m t (originCube 2 U.scale)
        (Cutoff.translateCutoffSample (triadicCubeShift U) ω))
  have hsetBack : translateSet (-z) (openCubeSet U) = openCubeSet Q := by
    ext x
    rw [mem_translateSet_iff_sub_mem, hcube, mem_translateSet_iff_sub_mem]
    simp [sub_eq_add_neg, add_assoc]
  have hEllBack : IsEllipticFieldOn _ _ (openCubeSet U) aBack :=
    fixedNu_field_translate (-z) (a := a0) (by
      rw [hsetBack]
      exact hEll0)
  have hcoef : aU =ᵐ[volumeMeasureOn (openCubeSet U)] aBack := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet U)] with x hx
    have hx0 : x - z ∈ openCubeSet Q := by
      rw [hcube, mem_translateSet_iff_sub_mem] at hx
      exact hx
    have hUval := main_eosc_response_frame_eq_scaled_partial
      M m t U ω x hx
    have h0val := main_eosc_response_frame_eq_scaled_partial
      M m t Q (Cutoff.translateCutoffSample z ω) (x - z) hx0
    have hpartial :
        (Model.partialInsertedCoefficient M m t
          (Cutoff.translateCutoffSample z ω)).toFun (x - z) =
        (Model.partialInsertedCoefficient M m t ω).toFun x := by
      rw [main_partialInsertedCoefficient_translate]
      simp [translateReg, sub_eq_add_neg, add_assoc]
    have hBackEval : aBack x =
        responseFramePlanarCoefficientField M.nu σ
          (mainInsertionSkewCoefficient m t Q
            (Cutoff.translateCutoffSample z ω)) (x-z) := by
      dsimp [aBack, a0]
      simp only [translateCoeffField]
      congr 1
    change responseFramePlanarCoefficientField M.nu σ
        (mainInsertionSkewCoefficient m t U ω) x = aBack x
    rw [hUval, hBackEval]
    have h0val' :
        responseFramePlanarCoefficientField M.nu σ
          (mainInsertionSkewCoefficient m t Q
            (Cutoff.translateCutoffSample z ω)) (x-z) =
        σ⁻¹ • (Model.partialInsertedCoefficient M m t
          (Cutoff.translateCutoffSample z ω)).toFun (x-z) := by
      simpa only [σ] using h0val
    rw [h0val', hpartial]
  have hInv := old_signed_inverse_history_congr U aU aBack hEllU hEllBack hcoef
  have hResp := old_signed_response_history_ennreal_congr U aU aBack hcoef
  have hInvShift := nativeHeat_lemmaVInverseHistory_translateCube
    U.index Q a0 ((3 : ℝ) ^ (1 / 4 : ℝ))
  have hRespShift := main_eosc_responseHistory_translateCube U.index Q a0
  have hback : aBack =
      translateCoeffField (-nativeHeatCubeTranslationVector U.index Q) a0 := by
    dsimp [aBack, z]
    rw [hvec]
  have hInvRoot : oldSignedInverseHistory U aBack = oldSignedInverseHistory Q a0 := by
    rw [← hUcube, hback]
    change lemmaVInverseHistory (translateCube U.index Q)
      (translateCoeffField (-nativeHeatCubeTranslationVector U.index Q) a0)
      ((3 : ℝ) ^ (1 / 4 : ℝ)) = _
    exact hInvShift
  have hRespRoot : oldSignedResponseHistory U aBack = oldSignedResponseHistory Q a0 := by
    rw [← hUcube, hback]
    exact hRespShift
  constructor
  · simpa [aU, a0, Q, σ] using hInv.trans hInvRoot
  · calc
      oldSignedResponseHistory U aU = oldSignedResponseHistory U aBack := by
        exact congrArg ENNReal.toReal hResp
      _ = oldSignedResponseHistory Q a0 := hRespRoot

/-- The two shifted root carriers retain their root L² caps on the cutoff
law, since whole-sample cutoff translations preserve that law. -/
theorem main_eosc_shifted_carrier_moments
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (U : TriadicCube 2) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let shift := fun ω : CutoffSample 2 =>
      Cutoff.translateCutoffSample (triadicCubeShift U) ω
    let B := fun ω =>
      (mainCutoffQ3SourceInverseBankMax M m t (shift ω)).toReal
    let M_U := mainPartialInsertedMultiplierHistory M m t ∘ shift
    MemLp B 2 μ ∧ lpNorm B 2 μ ≤ mainBeta ∧
      MemLp M_U 2 μ ∧
        lpNorm M_U 2 μ ≤ mainM0 (mainEnvelopeH (theta M) M.gamma t) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let shift : CutoffSample 2 → CutoffSample 2 := fun ω =>
    Cutoff.translateCutoffSample (triadicCubeShift U) ω
  let rootB : CutoffSample 2 → ℝ := fun ω =>
    (mainCutoffQ3SourceInverseBankMax M m t ω).toReal
  let B : CutoffSample 2 → ℝ := fun ω => rootB (shift ω)
  let rootM : CutoffSample 2 → ℝ := mainPartialInsertedMultiplierHistory M m t
  let M_U : CutoffSample 2 → ℝ := rootM ∘ shift
  have hmp : MeasurePreserving shift μ μ := by
    exact ⟨Cutoff.measurable_translateCutoffSample (triadicCubeShift U),
      Cutoff.map_translateCutoffSample_cutoffSampleLaw M (triadicCubeShift U)⟩
  have hBank := main_q3_source_inverse_bank_and_history M h hM hγ m
    (fun n hn => hpast n hn.le) t ht
  have hBrootMem : MemLp rootB 2 μ := by
    simpa only [rootB] using hBank.2.1
  have hBmem : MemLp B 2 μ := by
    change MemLp (rootB ∘ shift) 2 μ
    exact hBrootMem.comp_measurePreserving hmp
  have hBnorm : lpNorm B 2 μ = lpNorm rootB 2 μ := by
    change (eLpNorm (rootB ∘ shift) 2 μ).toReal =
      (eLpNorm rootB 2 μ).toReal
    rw [eLpNorm_comp_measurePreserving hBrootMem.aestronglyMeasurable hmp]
  have hBcap : lpNorm B 2 μ ≤ mainBeta := by
    rw [hBnorm]
    simpa only [rootB] using hBank.2.2.1
  have hMultiplier := main_multiplier_moments_of_main_envelope_h
    M h hM hγ m hpast t ht.1 ht.2
  have hMrootMem : MemLp rootM 2 μ := by
    simpa only [rootM] using hMultiplier.1.2
  have hMmem : MemLp M_U 2 μ := by
    change MemLp (rootM ∘ shift) 2 μ
    exact hMrootMem.comp_measurePreserving hmp
  have hMnorm : lpNorm M_U 2 μ = lpNorm rootM 2 μ := by
    change (eLpNorm (rootM ∘ shift) 2 μ).toReal =
      (eLpNorm rootM 2 μ).toReal
    rw [eLpNorm_comp_measurePreserving hMrootMem.aestronglyMeasurable hmp]
  have hMcap : lpNorm M_U 2 μ ≤ mainM0 (mainEnvelopeH (theta M) M.gamma t) := by
    rw [hMnorm]
    simpa only [rootM] using hMultiplier.1.1.2
  exact ⟨by simpa only [B] using hBmem,
    by simpa only [B] using hBcap,
    by simpa only [M_U, rootM, shift, μ] using hMmem,
    by simpa only [M_U, rootM, shift, μ] using hMcap⟩

end
end ASDExplicitGamma.Main
