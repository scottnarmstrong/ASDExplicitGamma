module

public import ASDExplicitGamma.Main.ELinearObsCell
public import ASDExplicitGamma.Native.OldSignedDirectionalDepthMatrix
public import ASDExplicitGamma.Native.OldSignedSourceDirectionalModes
public import ASDExplicitGamma.Main.ThetaGeneratorELinearXiHalf
public import ASDExplicitGamma.Inverse.ParentGapCenteredDepth

/-! Translation covariance of the actual directional proxy of a cell. -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

private theorem e_linear_px_openCube_translate
    (z : Fin 2 → ℤ) (Q : TriadicCube 2) :
    openCubeSet (translateCube z Q) =
      translateSet (nativeHeatCubeTranslationVector z Q) (openCubeSet Q) := by
  ext x
  rw [mem_translateSet_iff_sub_mem, mem_openCubeSet_translateCube_iff]
  rfl

private theorem e_linear_px_translateCube_origin (U : TriadicCube 2) :
    translateCube U.index (originCube 2 U.scale) = U := by
  cases U
  simp only [translateCube, originCube, Pi.zero_apply, zero_add]

private theorem e_linear_px_vec_eq_shift (U : TriadicCube 2) :
    nativeHeatCubeTranslationVector U.index (originCube 2 U.scale) =
      triadicCubeShift U := by
  ext i
  simp [nativeHeatCubeTranslationVector, triadicCubeShift, cubeScaleFactor,
    originCube]

theorem descendantsAverage_translateCube_Th (z : Fin 2 → ℤ) (Q : TriadicCube 2) (j : ℕ)
    (F : TriadicCube 2 → ℝ) :
    descendantsAverage (translateCube z Q) j F =
      descendantsAverage Q j (fun R => F (translateCube (descendantTranslationShift j z) R)) := by
  classical
  unfold descendantsAverage
  dsimp only
  rw [descendantsAtDepth_translateCube z Q j]
  have hinj : Set.InjOn (translateCube (descendantTranslationShift j z))
      (descendantsAtDepth Q j : Set (TriadicCube 2)) :=
    (Homogenization.Book.Ch02.translateCube_injective _).injOn
  rw [Finset.card_image_of_injOn hinj, Finset.sum_image hinj]

theorem old_signed_coarse_translate_descendant_Th
    (z : Fin 2 → ℤ) (Q R : TriadicCube 2) (j : ℕ) (hR : R ∈ descendantsAtDepth Q j)
    (a : CoeffField 2) :
    coarseBlockMatrix (openCubeSet (translateCube (descendantTranslationShift j z) R))
        (translateCoeffField (-nativeHeatCubeTranslationVector z Q) a) =
      coarseBlockMatrix (openCubeSet R) a := by
  have hz : nativeHeatCubeTranslationVector (descendantTranslationShift j z) R =
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
      _ = (z i : ℝ) * ((3 : ℝ) ^ (j : ℤ) * (3 : ℝ) ^ (Q.scale - (j : ℤ))) := by ring
      _ = _ := by rw [hpow]
  have hopen : openCubeSet (translateCube (descendantTranslationShift j z) R) =
      translateSet (nativeHeatCubeTranslationVector (descendantTranslationShift j z) R)
        (openCubeSet R) := by
    ext x
    rw [mem_translateSet_iff_sub_mem, mem_openCubeSet_translateCube_iff]
    rfl
  rw [hopen, hz, coarseBlockMatrix_translateSet_eq_translateCoeffField]
  have hcoeff : translateCoeffField (nativeHeatCubeTranslationVector z Q)
      (translateCoeffField (-nativeHeatCubeTranslationVector z Q) a) = a := by
    funext x
    simp [translateCoeffField]
  rw [hcoeff]

theorem descendantsAverage_translateCube_congr_Th (z : Fin 2 → ℤ) (Q : TriadicCube 2)
    (j : ℕ) (F G : TriadicCube 2 → ℝ)
    (h : ∀ R ∈ descendantsAtDepth Q j,
      F (translateCube (descendantTranslationShift j z) R) = G R) :
    descendantsAverage (translateCube z Q) j F = descendantsAverage Q j G := by
  rw [descendantsAverage_translateCube_Th]
  unfold descendantsAverage
  dsimp only
  congr 1
  exact Finset.sum_congr rfl h

theorem old_signed_paired_depth_matrix_translateCube_Th
    (z : Fin 2 → ℤ) (Q : TriadicCube 2) (a : CoeffField 2) (j : ℕ) :
    oldSignedPairedDepthMatrix (translateCube z Q) j
        (translateCoeffField (-nativeHeatCubeTranslationVector z Q) a) =
      oldSignedPairedDepthMatrix Q j a := by
  have e1 : (fun i k => descendantsAverage (translateCube z Q) j (fun R =>
        (coarseBlockMatrix (openCubeSet R)
          (translateCoeffField (-nativeHeatCubeTranslationVector z Q) a)).upperLeft i k)) =
      fun i k => descendantsAverage Q j (fun R => (coarseBlockMatrix (openCubeSet R) a).upperLeft i k) := by
    funext i k
    exact descendantsAverage_translateCube_congr_Th z Q j _ _ (fun R hR => by
      rw [old_signed_coarse_translate_descendant_Th z Q R j hR a])
  have e2 : (fun i k => descendantsAverage (translateCube z Q) j (fun R =>
        (coarseBlockMatrix (openCubeSet R)
          (translateCoeffField (-nativeHeatCubeTranslationVector z Q) a)).lowerRight i k)) =
      fun i k => descendantsAverage Q j (fun R => (coarseBlockMatrix (openCubeSet R) a).lowerRight i k) := by
    funext i k
    exact descendantsAverage_translateCube_congr_Th z Q j _ _ (fun R hR => by
      rw [old_signed_coarse_translate_descendant_Th z Q R j hR a])
  unfold oldSignedPairedDepthMatrix descendantsAverageBlockMat descendantsAverageMat
  dsimp only
  rw [e1, e2]

theorem old_signed_directional_proxy_translateCube_Th
    (z : Fin 2 → ℤ) (Q : TriadicCube 2) (a : CoeffField 2) (e : Vec 2) :
    oldSignedDirectionalProxy (translateCube z Q)
        (translateCoeffField (-nativeHeatCubeTranslationVector z Q) a) e =
      oldSignedDirectionalProxy Q a e := by
  unfold oldSignedDirectionalProxy
  have hD (j : ℕ) := nativeHeat_lemmaVInverseDepthMax_translateCube z Q a j
  have hM (j : ℕ) := old_signed_paired_depth_matrix_translateCube_Th z Q a j
  have hD' : lemmaVInverseDepthMax (translateCube z Q)
      (translateCoeffField (-nativeHeatCubeTranslationVector z Q) a) =
      lemmaVInverseDepthMax Q a := funext hD
  rw [hD']
  simp only [hM]

/-- The corrector history of a source cell, from the root frame field, is the
corrector history of the origin cell at the translated sample. -/
theorem main_e_linear_obs_proxy_translate_Th
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : CutoffSample 2)
    (U : TriadicCube 2) (e : Vec 2) :
    oldSignedDirectionalProxy U (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) e =
      oldSignedDirectionalProxy (originCube 2 U.scale)
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (mainInsertionSkewCoefficient m t (originCube 2 U.scale)
            (Cutoff.translateCutoffSample (triadicCubeShift U) ω))) e := by
  let Q : TriadicCube 2 := originCube 2 U.scale
  let z : Vec 2 := triadicCubeShift U
  let σ : ℝ := Annealed.sigmaBar M m
  let aU : CoeffField 2 := responseFramePlanarCoefficientField M.nu σ
    (mainInsertionSkewCoefficient m t U ω)
  let a0 : CoeffField 2 := responseFramePlanarCoefficientField M.nu σ
    (mainInsertionSkewCoefficient m t Q (Cutoff.translateCutoffSample z ω))
  let aBack : CoeffField 2 := translateCoeffField (-z) a0
  have hUcube : translateCube U.index Q = U := e_linear_px_translateCube_origin U
  have hvec : nativeHeatCubeTranslationVector U.index Q = z := e_linear_px_vec_eq_shift U
  have hcube : openCubeSet U = translateSet z (openCubeSet Q) := by
    rw [← hUcube, e_linear_px_openCube_translate, hvec]
  have hEllU := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet U) M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M m).1
    (mainInsertionSkewCoefficient m t U ω)
  have hEll0 := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M m).1
    (mainInsertionSkewCoefficient m t Q (Cutoff.translateCutoffSample z ω))
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
    have hUval := main_eosc_response_frame_eq_scaled_partial M m t U ω x hx
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
            (Cutoff.translateCutoffSample z ω)) (x - z) := by
      dsimp [aBack, a0]
      simp only [translateCoeffField]
      congr 1
    change responseFramePlanarCoefficientField M.nu σ
        (mainInsertionSkewCoefficient m t U ω) x = aBack x
    rw [hUval, hBackEval]
    have h0val' :
        responseFramePlanarCoefficientField M.nu σ
          (mainInsertionSkewCoefficient m t Q
            (Cutoff.translateCutoffSample z ω)) (x - z) =
        σ⁻¹ • (Model.partialInsertedCoefficient M m t
          (Cutoff.translateCutoffSample z ω)).toFun (x - z) := by
      simpa only [σ] using h0val
    rw [h0val', hpartial]
  have hprox := old_signed_directional_proxy_congr U aU aBack hEllU hEllBack hcoef e
  have hback : aBack =
      translateCoeffField (-nativeHeatCubeTranslationVector U.index Q) a0 := by
    dsimp [aBack, z]
    rw [hvec]
  have hRoot : oldSignedDirectionalProxy U aBack e = oldSignedDirectionalProxy Q a0 e := by
    rw [← hUcube, hback]
    exact old_signed_directional_proxy_translateCube_Th U.index Q a0 e
  exact hprox.trans hRoot

/-- Annealed payment of the directional proxy of an arbitrary source cell of
scale `m-5`, summed over a square-summable load family, by half the explicit
`mainEnvelopeXi`. -/
theorem main_e_linear_obs_proxy_modes_payment_Th
    {I : Type*} [Countable I]
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (U : TriadicCube 2) (hscale : U.scale = m - 5)
    (E : I → Fin 2 → Vec 2) (hE : Summable (fun i => ∑ c : Fin 2, vecNormSq (E i c))) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let xi := mainEnvelopeXi
      ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2)
      M.gamma (theta M * mainSourceInversePrefix) (theta M) t
    let P := fun ω => ∑' i, ∑ c : Fin 2, oldSignedDirectionalProxy U
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
        (mainInsertionSkewCoefficient m t U ω)) (E i c)
    Integrable P μ ∧ (∫ ω, P ω ∂μ) ≤ xi / 2 * (∑' i, ∑ c : Fin 2, vecNormSq (E i c)) := by
  intro μ xi P
  let U0 := originCube 2 U.scale
  have hU0 : U0 ∈ descendantsAtDepth (originCube 2 m) 5 := by
    have h5 := ASDExplicitGamma.Inverse.originCube_mem_descendantsAtDepth' 2 m 5
    simpa only [U0, hscale, Nat.cast_ofNat] using h5
  have hstates : ∀ l ≤ m, nativeInductionState M h l :=
    fun l hl => hpast l (lt_of_le_of_lt hl hm)
  have hnat := old_signed_source_directional_modes_payment M h hM hγ m 5 le_rfl U0 hU0 t
    ⟨ht.1, ht.2⟩ hstates E hE
  have hxi := main_e_linear_source_history_half_xi_Th M h hM hγ N hpast m hm t ht U0 hU0
  have hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU0
  let P0 : CutoffSample 2 → ℝ := fun ω => ∑' i, ∑ c : Fin 2, oldSignedDirectionalProxy U0
    (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
      (mainInsertionSkewCoefficient m t U0 ω)) (E i c)
  have hP0eq : (fun ω => ∑' i, ∑ c : Fin 2, oldSignedDirectionalProxy U0
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
        (oldSignedCellCoefficient (originCube 2 m) U0 hsub
          (oldSignedPartialResponseCoefficient m 1 t ω))) (E i c)) = P0 := by
    funext ω
    apply tsum_congr
    intro i
    apply Finset.sum_congr rfl
    intro c _
    have hEllC := responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet U0) M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
      (Annealed.sigmaBar_characterization M m).1
      (oldSignedCellCoefficient (originCube 2 m) U0 hsub
        (oldSignedPartialResponseCoefficient m 1 t ω))
    have hEllU := responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet U0) M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 (mainInsertionSkewCoefficient m t U0 ω)
    apply old_signed_directional_proxy_congr U0 _ _ hEllC hEllU
    have h1 := old_signed_cell_frame_coefficient_ae (originCube 2 m) U0 hsub M.nu
      (Annealed.sigmaBar M m : ℝ) (oldSignedPartialResponseCoefficient m 1 t ω)
    have h2 : oldSignedPartialFrameField M m 1 t ω =ᵐ[volumeMeasureOn (openCubeSet U0)]
        responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (mainInsertionSkewCoefficient m t U0 ω) := by
      filter_upwards [ae_restrict_mem (measurableSet_openCubeSet U0)] with x hx
      rw [old_signed_partial_frame_eq_scaled_partial M m t ω x (hsub hx),
        main_eosc_response_frame_eq_scaled_partial M m t U0 ω x hx]
    exact h1.trans h2
  dsimp only at hnat
  rw [hP0eq] at hnat
  have hshift : P = fun ω => P0 (Cutoff.translateCutoffSample (triadicCubeShift U) ω) := by
    funext ω
    apply tsum_congr
    intro i
    apply Finset.sum_congr rfl
    intro c _
    exact main_e_linear_obs_proxy_translate_Th M m t ω U (E i c)
  have hmp : MeasurePreserving (fun ω : CutoffSample 2 =>
      Cutoff.translateCutoffSample (triadicCubeShift U) ω) μ μ :=
    ⟨Cutoff.measurable_translateCutoffSample (triadicCubeShift U),
      Cutoff.map_translateCutoffSample_cutoffSampleLaw M (triadicCubeShift U)⟩
  have hbudget : (1 - inverseHistoryDiscount ^ 2) *
      ∑' j : ℕ, inverseHistoryDiscount ^ (2 * j) * oldSignedSourceHistoryBudget M m U0 t j ≤
        xi / 2 := by
    change _ ≤ mainEnvelopeXi _ _ _ _ _ / 2
    linarith
  have hnn : 0 ≤ ∑' i, ∑ c : Fin 2, vecNormSq (E i c) :=
    tsum_nonneg (fun i => Finset.sum_nonneg (fun c _ => vecNormSq_nonneg _))
  rw [hshift]
  refine ⟨hmp.integrable_comp_of_integrable hnat.1, ?_⟩
  have hi := integral_map (μ := μ) (φ := fun ω : CutoffSample 2 =>
      Cutoff.translateCutoffSample (triadicCubeShift U) ω) hmp.measurable.aemeasurable
    (by rw [hmp.map_eq]; exact hnat.1.1)
  rw [hmp.map_eq] at hi
  rw [← hi]
  exact hnat.2.trans (mul_le_mul_of_nonneg_right hbudget hnn)

end

end ASDExplicitGamma.Main
