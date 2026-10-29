/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Native.HeatVHEATRefinedThetaRows
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceBank
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceClocks

/-! The actual nine-shell VHEAT bracket row, transported to the correlated
bank and then controlled by the configured infinite shell profile. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Gaussian Inverse Response Variational Triadic
open Algsuperdiff.Section3 ASDExplicitGamma.Numerics.Native
open scoped ENNReal NNReal BigOperators
noncomputable section

/-- The actual nine-shell bracket row is dominated pointwise almost
everywhere by the complete correlated bank, with the sum of the nine
profile coefficients replaced by `E9 * SB`. -/
theorem nativeHeatQ3RefinedCarrierSourceRows_le_correlatedBank
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ l < m + 1, nativeInductionState M h l)
    (hstate : nativeInductionState M h (m + 1))
    (t : ℝ) (ht : t ≤ 1)
    (g : nativeHeatQ3RefinedCarrierIndex → (ℕ → ℝ) → ℝ) :
    ∀ᵐ z ∂nativeHeatRemainderJointLaw M,
      nativeHeatQ3RefinedCarrierSourceRows M h m t g z ≤
        4 * heatVHEATDriftE9 M * (nativeHeatSB : ℝ) *
          ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
            ∑ i : nativeHeatQ3RefinedCarrierIndex,
              let shift := heatVHEATDriftRefinedShift m i
              let R := heatRefinedTranslatedRare M (m + 1) 9 t shift z
              let T := heatVHEATDriftRefinedPhysicalTrace M m t g z i
              (3683 / 2500 + R) ^ 2 * T * (T + 4)) := by
  classical
  let σ : ℝ := Annealed.sigmaBar M (m + 1)
  let Q (i : nativeHeatQ3RefinedCarrierIndex) := nativeHeatQ3RefinedCarrierChild m i
  let shift (i : nativeHeatQ3RefinedCarrierIndex) := heatVHEATDriftRefinedShift m i
  let R (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) (i : nativeHeatQ3RefinedCarrierIndex) :=
    heatRefinedTranslatedRare M (m + 1) 9 t (shift i) z
  let T (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) (i : nativeHeatQ3RefinedCarrierIndex) :=
    heatVHEATDriftRefinedPhysicalTrace M m t g z i
  let B (z : Cutoff.CutoffSample 2 × (ℕ → ℝ))
      (i : nativeHeatQ3RefinedCarrierIndex) (d : Fin 9) :=
    lemmaVTileHistory (originCube 2 (Q i).scale)
      (pureFluxBankSourceDepth (d.val + 2))
      (responseFramePlanarCoefficientField M.nu σ
        (pureFluxOpenResponseRestriction (Q i).scale
          (nativeHeat_translateTriadicFieldToOrigin (Q i)
            (heatVHEATDriftRefinedChildField m t g z i))))
  let H (z : Cutoff.CutoffSample 2 × (ℕ → ℝ))
      (i : nativeHeatQ3RefinedCarrierIndex) (d : Fin 9) :=
    let Qi := Q i
    let A := nativeHeat_translateTriadicFieldToOrigin Qi
    let ki := pureFluxOpenResponseRestriction Qi.scale
      (A (heatVHEATDriftRefinedChildField m t g z i))
    let Bi := lemmaVTileHistory (originCube 2 Qi.scale)
      (pureFluxBankSourceDepth (d.val + 2))
      (responseFramePlanarCoefficientField M.nu σ ki)
    let Ti := modelTraceObservable Qi.scale M.nu σ
      (A (heatVHEATDriftRefinedChildField m t g z i))
    Bi ^ 2 * Ti * (Ti + 4)
  let C (d : Fin 9) : ℝ :=
    heatVHEATDriftVariance M h (m + 1) d *
      q3GridOverlapFactor 10 (d.val + 2) *
      (lemmaVH2Bn
        (cubeScaleFactor (originCube 2 m) /
          (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1)
        (diagMeshRadius (originCube 2 m)
          (pureFluxBankSourceDepth (d.val + 2)) /
          (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1)) ^ 2
  have hCeq (d : Fin 9) :
      4 * (q3ModelAmplitude M h (m + ((d.val + 2 : ℕ) : ℤ)) ^ 2 /
            (Annealed.sigmaBar M (m + 1) : ℝ) ^ 2) *
        q3GridOverlapFactor 10 (d.val + 2) *
        (lemmaVH2Bn
          (cubeScaleFactor (originCube 2 m) /
            (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1)
          (diagMeshRadius (originCube 2 m)
            (pureFluxBankSourceDepth (d.val + 2)) /
            (q3ModelLength (m + ((d.val + 2 : ℕ) : ℤ))).1)) ^ 2 = 4 * C d := by
    have hlabel : m + ((d.val + 2 : ℕ) : ℤ) =
        (m + 1) + ((d.val + 1 : ℕ) : ℤ) := by omega
    dsimp only [C, heatVHEATDriftVariance, σ]
    rw [hlabel]
    ring
  have hCnonneg (d : Fin 9) : 0 ≤ C d := by
    dsimp [C]
    have hv := (heatVHEATDrift_source_variance_le M h (m + 1) hstate d).1
    have hov : 0 ≤ q3GridOverlapFactor 10 (d.val + 2) := by
      have hh : 0 ≤ heatRefinedOverlap d.val := by
        unfold heatRefinedOverlap
        positivity
      rw [heat_refined_grid_overlap]
      exact_mod_cast hh
    exact mul_nonneg (mul_nonneg hv hov) (sq_nonneg _)
  have hprofile : (∑ d : Fin 9, C d) ≤ heatVHEATDriftE9 M * (nativeHeatSB : ℝ) := by
    simpa only [C] using nativeHeatQ3RefinedCarrierSourceProfileSum_le_SB M h m hstate
  have hbank := heatVHEATDrift_bank_family_ae_le M h hM hg (m + 1) 9 hpast t ht
    Finset.univ shift g
  have hbank' : ∀ᵐ z ∂nativeHeatRemainderJointLaw M,
      ∀ i : nativeHeatQ3RefinedCarrierIndex, ∀ d : Fin 9,
        B z i d ≤ (3683 / 2500 : ℝ) + R z i := by
    filter_upwards [hbank] with z hz
    intro i d
    have hrow := nativeHeatQ3RefinedCarrierRowHistory_le_bank M m t g z i d
    dsimp only [B, R, shift, Q]
    exact hrow.trans (hz i (Finset.mem_univ i) d)
  have hTnonneg (z : Cutoff.CutoffSample 2 × (ℕ → ℝ))
      (i : nativeHeatQ3RefinedCarrierIndex) : 0 ≤ T z i := by
    dsimp [T, heatVHEATDriftRefinedPhysicalTrace]
    rw [nativeHeatQ3RefinedCarrierChildTraceObservable_toOrigin
      (Q i) M.nu σ M.nu_pos (Annealed.sigmaBar_characterization M (m + 1)).1 _]
    exact modelTraceObservable_nonneg (Q i).scale M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M (m + 1)).1 _
  filter_upwards [hbank'] with z hz
  let G (i : nativeHeatQ3RefinedCarrierIndex) :=
    ((3683 / 2500 : ℝ) + R z i) ^ 2 * T z i * (T z i + 4)
  have hGnonneg (i : nativeHeatQ3RefinedCarrierIndex) : 0 ≤ G i := by
    dsimp [G]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (hTnonneg z i)) (by linarith [hTnonneg z i])
  have hrow (d : Fin 9) :
      (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
          (∑ i : nativeHeatQ3RefinedCarrierIndex, H z i d) ≤
      (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ * ∑ i, G i := by
    have hN : 0 ≤ (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ := by positivity
    apply mul_le_mul_of_nonneg_left _ hN
    apply Finset.sum_le_sum
    intro i hi
    have hBi0 : 0 ≤ B z i d :=
      lemmaVTileHistory_nonneg (originCube 2 (Q i).scale)
        (pureFluxBankSourceDepth (d.val + 2))
        (responseFramePlanarCoefficientField M.nu σ
          (pureFluxOpenResponseRestriction (Q i).scale
            (nativeHeat_translateTriadicFieldToOrigin (Q i)
              (heatVHEATDriftRefinedChildField m t g z i))))
    have hBi2 := pow_le_pow_left₀ hBi0 (hz i d) 2
    have hprod : 0 ≤ T z i * (T z i + 4) :=
      mul_nonneg (hTnonneg z i) (by linarith [hTnonneg z i])
    have hmul := mul_le_mul_of_nonneg_right hBi2 hprod
    have hmodelEq : modelTraceObservable (Q i).scale M.nu σ
        (nativeHeat_translateTriadicFieldToOrigin (Q i)
          (heatVHEATDriftRefinedChildField m t g z i)) = T z i := by
      dsimp [T, heatVHEATDriftRefinedPhysicalTrace]
      exact (nativeHeatQ3RefinedCarrierChildTraceObservable_toOrigin
        (Q i) M.nu σ M.nu_pos (Annealed.sigmaBar_characterization M (m + 1)).1 _).symm
    have hterm : H z i d ≤ G i := by
      simp only [H, G, Q]
      rw [hmodelEq]
      simpa only [mul_assoc] using hmul
    exact hterm
  have hrows : nativeHeatQ3RefinedCarrierSourceRows M h m t g z ≤
      4 * (∑ d : Fin 9, C d) *
        ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ * ∑ i, G i) := by
    dsimp only [nativeHeatQ3RefinedCarrierSourceRows,
      nativeHeatQ3RefinedCarrierSourceRowsForFields, σ]
    simp_rw [hCeq]
    have hfactor : 0 ≤ (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ * ∑ i, G i := by
      apply mul_nonneg (by positivity)
      exact Finset.sum_nonneg (fun i _ => hGnonneg i)
    calc
      _ = 4 * ∑ d : Fin 9, C d *
          ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
            ∑ i : nativeHeatQ3RefinedCarrierIndex, H z i d) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro d hd
            ring
      _ ≤ 4 * ∑ d : Fin 9, C d *
          ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ * ∑ i, G i) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            apply Finset.sum_le_sum
            intro d hd
            exact mul_le_mul_of_nonneg_left (hrow d) (hCnonneg d)
      _ = 4 * (∑ d : Fin 9, C d) *
          ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ * ∑ i, G i) := by
            rw [← Finset.sum_mul]
            ring
  have he9 : 0 ≤ heatVHEATDriftE9 M := by
    unfold heatVHEATDriftE9
    exact mul_nonneg (mul_nonneg (by norm_num) M.shellPrefix.gamma_pos.le)
      (Real.rpow_pos_of_pos (by norm_num) _).le
  have hSB : 0 ≤ (nativeHeatSB : ℝ) := by norm_num [nativeHeatSB]
  have hcommon : 0 ≤ (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ * ∑ i, G i := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun i _ => hGnonneg i)
  calc
    nativeHeatQ3RefinedCarrierSourceRows M h m t g z ≤
        4 * (∑ d : Fin 9, C d) *
          ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ * ∑ i, G i) := hrows
    _ ≤ 4 * (heatVHEATDriftE9 M * (nativeHeatSB : ℝ)) *
          ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ * ∑ i, G i) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hprofile (by norm_num)) hcommon
    _ = 4 * heatVHEATDriftE9 M * (nativeHeatSB : ℝ) *
          ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ * ∑ i,
            let Q := nativeHeatQ3RefinedCarrierChild m i
            let shift := heatVHEATDriftRefinedShift m i
            let R := heatRefinedTranslatedRare M (m + 1) 9 t shift z
            let T := heatVHEATDriftRefinedPhysicalTrace M m t g z i
            (3683 / 2500 + R) ^ 2 * T * (T + 4)) := by
          simp only [G, R, T, shift]
          ring

end
end ASDExplicitGamma.Native
