module

public import ASDExplicitGamma.Main.ObsLowerPairTrace
public import ASDExplicitGamma.Main.ObsLowerCoercivityPair
public import ASDExplicitGamma.Main.ObsLowerCoeff
public import ASDExplicitGamma.Main.ObsLowerPenalty
public import ASDExplicitGamma.Main.PathwiseHessianResponseCovariance

/-! Observer-level two-load covariance row with the explicit MA lower root at
`v = (|σ⁻¹| |b|)^2`, coercivity through the cell history `B` only. -/

@[expose] public section

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  ASDExplicitGamma.Native
open scoped BigOperators

namespace ASDExplicitGamma.Main

theorem obs_twoLoad_trace_lower_source_root
    (m : ℤ) (hobs : ℕ) (ν σ b B : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet (originCube 2 (m + hobs))))
    (P : Fin 2 → BlockVec 2)
    (r : Fin 2 → H10Function (openCubeSet (originCube 2 (m + hobs))))
    (u : Fin 2 → AHarmonicFunction (responseFramePlanarCoefficientField ν σ k)
      (openCubeSet (originCube 2 (m + hobs))))
    (w : Fin 2 → AHarmonicFunction
      (adjointCoeffField (responseFramePlanarCoefficientField ν σ k))
      (openCubeSet (originCube 2 (m + hobs))))
    (hrep : ∀ a, hilbertBlockL2ToBlockL2
        ((responseFrameMuOperatorSystemData
          (isOpenBoundedConvexDomain_openCubeSet (originCube 2 (m + hobs))).isOpen.measurableSet
          (volume_openCubeSet_originCube_toReal_pos (d := 2) (m + hobs))
          ν σ hν hσ k).toMuHilbertRealization.minimizerMap (P a)) =ᵐ[
          volumeMeasureOn (openCubeSet (originCube 2 (m + hobs)))]
        (fun x => (blockResponsePairHalfState
          (responseFramePlanarCoefficientField ν σ k) (u a) (w a)).eval x))
    (hgrad : ∀ a, (lemmaVAffinePotential
        (isOpenBoundedConvexDomain_openCubeSet (originCube 2 (m + hobs))) (P a).1 (r a)).grad =ᵐ[
          volumeMeasureOn (openCubeSet (originCube 2 (m + hobs)))]
        (blockResponsePairHalfState
          (responseFramePlanarCoefficientField ν σ k) (u a) (w a)).potential)
    (hB : 0 ≤ B)
    (hhist : ∀ U ∈ descendantsAtDepth (originCube 2 (m + hobs)) (hobs + 5),
      lemmaVInverseHistory U (responseFramePlanarCoefficientField ν σ k)
        ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤ B) :
    let Q := originCube 2 (m + hobs)
    let H (j : ℕ) := pureFluxMainCubeQ3ResponseCoefficient (m + hobs) b (q3ModelLength (m + 1)) j
    let hU := measurableSet_openCubeSet Q
    let hvol := volume_openCubeSet_originCube_toReal_pos (d := 2) (m + hobs)
    let E (a : Fin 2) := responseFrameEnergyObservable hU hvol ν σ hν hσ (P a)
    let Eall := fun k' => ∑ a : Fin 2, E a k'
    (1 / 2 : ℝ) * modelCovarianceTrace Eall H k ≥
      -(mainInverseMuMinusSource ((|σ⁻¹| * |b|) ^ 2) * (max 1 B) ^ 2 * ∑ a : Fin 2, E a k) := by
  classical
  intro Q H hU hvol E Eall
  have hpair := obs_twoLoad_response_covariance_trace_lower (m + hobs) (hobs + 5) ν σ b B
    hν hσ (q3ModelLength (m + 1)) k P r u w hrep hgrad hB hhist
  dsimp only at hpair
  have hKA := mainInverseKA_nonneg ((|σ⁻¹| * |b|) ^ 2)
  have hKB := mainInverseKB_nonneg ((|σ⁻¹| * |b|) ^ 2)
  have hcolEq := obs_colC_eq m hobs b σ
  have hrowEq := obs_rowC_eq m hobs b σ
  have hcol0 : 0 ≤ |σ⁻¹| * obsColumnCoefficient (originCube 2 (m + hobs)) (hobs + 5) b
      (q3ModelLength (m + 1)) := by rw [hcolEq]; exact hKA
  have hrow0 : 0 ≤ |σ⁻¹| * mainQ3RowConstant
      (diagMeshRadius (originCube 2 (m + hobs)) (hobs + 5)) b
      (q3ModelLength (m + 1)).1 := by rw [hrowEq]; exact hKB
  have hpen (a : Fin 2) :
      -(mainInverseMuMinusSource ((|σ⁻¹| * |b|) ^ 2) * (max 1 B) ^ 2 * E a k) ≤
        -2 * ((63 / 50 : ℝ) * B * |σ⁻¹| ^ 2 *
          obsColumnCoefficient (originCube 2 (m + hobs)) (hobs + 5) b
            (q3ModelLength (m + 1)) *
          mainQ3RowConstant (diagMeshRadius (originCube 2 (m + hobs)) (hobs + 5)) b
            (q3ModelLength (m + 1)).1 *
          Real.sqrt (lemmaVTiledWeakEnergy (originCube 2 (m + hobs)) (hobs + 5)
            (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet
              (originCube 2 (m + hobs))) (P a).1 (r a)).grad) *
          Real.sqrt (lemmaVTiledWeakEnergy (originCube 2 (m + hobs)) (hobs + 5)
            ((1 / 2 : ℝ) • ((w a).toH1 - (u a).toH1)).grad)) -
        (|σ⁻¹| * mainQ3RowConstant (diagMeshRadius (originCube 2 (m + hobs)) (hobs + 5)) b
            (q3ModelLength (m + 1)).1 * Real.sqrt B *
          Real.sqrt (lemmaVTiledWeakEnergy (originCube 2 (m + hobs)) (hobs + 5)
            ((1 / 2 : ℝ) • ((w a).toH1 - (u a).toH1)).grad)) ^ 2 := by
    have hbud := obs_response_pair_tiled_energy_le (m + hobs) (hobs + 5) ν σ hν hσ k (P a)
      (r a) (u a) (w a) (hrep a) (hgrad a) B hhist
    dsimp only at hbud
    have hEa : E a k = ‖responseFrameEnergyBaseMinimizer
        (measurableSet_openCubeSet (originCube 2 (m + hobs)))
        (volume_openCubeSet_originCube_toReal_pos (d := 2) (m + hobs)) ν σ hν hσ k (P a)‖ ^ 2 :=
      (main_response_energy_minimizer_norm_sq (m + hobs) ν σ hν hσ k (P a)).symm
    have hE0 : 0 ≤ E a k := by rw [hEa]; exact sq_nonneg _
    have hW0 := lemmaVTiledWeakEnergy_nonneg (originCube 2 (m + hobs)) (hobs + 5)
      (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet
        (originCube 2 (m + hobs))) (P a).1 (r a)).grad
    have hW1 := lemmaVTiledWeakEnergy_nonneg (originCube 2 (m + hobs)) (hobs + 5)
      ((1 / 2 : ℝ) • ((w a).toH1 - (u a).toH1)).grad
    have hmain := obs_penalty_le B
      (|σ⁻¹| * obsColumnCoefficient (originCube 2 (m + hobs)) (hobs + 5) b
        (q3ModelLength (m + 1)))
      (|σ⁻¹| * mainQ3RowConstant (diagMeshRadius (originCube 2 (m + hobs)) (hobs + 5)) b
        (q3ModelLength (m + 1)).1) _ _ (E a k)
      (mainInverseKA ((|σ⁻¹| * |b|) ^ 2)) (mainInverseKB ((|σ⁻¹| * |b|) ^ 2))
      hB hE0 hcol0 hrow0 hW0 hW1 hKA hKB hcolEq.le hrowEq.le (by rw [hEa]; exact hbud)
    have e1 : mainInverseMuMinus (mainInverseKA ((|σ⁻¹| * |b|) ^ 2))
        (mainInverseKB ((|σ⁻¹| * |b|) ^ 2)) =
        mainInverseMuMinusSource ((|σ⁻¹| * |b|) ^ 2) := rfl
    rw [e1] at hmain
    have e2 : -2 * ((63 / 50 : ℝ) * B * |σ⁻¹| ^ 2 *
          obsColumnCoefficient (originCube 2 (m + hobs)) (hobs + 5) b
            (q3ModelLength (m + 1)) *
          mainQ3RowConstant (diagMeshRadius (originCube 2 (m + hobs)) (hobs + 5)) b
            (q3ModelLength (m + 1)).1 * Real.sqrt (lemmaVTiledWeakEnergy (originCube 2 (m + hobs))
              (hobs + 5) (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet
              (originCube 2 (m + hobs))) (P a).1 (r a)).grad) *
          Real.sqrt (lemmaVTiledWeakEnergy (originCube 2 (m + hobs)) (hobs + 5)
            ((1 / 2 : ℝ) • ((w a).toH1 - (u a).toH1)).grad)) =
        -(2 * ((63 / 50 : ℝ) * B *
          (|σ⁻¹| * obsColumnCoefficient (originCube 2 (m + hobs)) (hobs + 5) b
            (q3ModelLength (m + 1))) *
          (|σ⁻¹| * mainQ3RowConstant (diagMeshRadius (originCube 2 (m + hobs)) (hobs + 5)) b
            (q3ModelLength (m + 1)).1) *
          Real.sqrt (lemmaVTiledWeakEnergy (originCube 2 (m + hobs)) (hobs + 5)
            (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet
              (originCube 2 (m + hobs))) (P a).1 (r a)).grad) *
          Real.sqrt (lemmaVTiledWeakEnergy (originCube 2 (m + hobs)) (hobs + 5)
            ((1 / 2 : ℝ) • ((w a).toH1 - (u a).toH1)).grad))) := by ring
    rw [sub_eq_add_neg, e2]
    have hmain' := hmain
    nlinarith [hmain']
  calc (1 / 2 : ℝ) * modelCovarianceTrace Eall H k ≥ _ := hpair
    _ ≥ ∑ a : Fin 2, (-(mainInverseMuMinusSource ((|σ⁻¹| * |b|) ^ 2) * (max 1 B) ^ 2 * E a k)) :=
      Finset.sum_le_sum (fun a _ => hpen a)
    _ = _ := by rw [Finset.sum_neg_distrib, Finset.mul_sum]

end ASDExplicitGamma.Main
