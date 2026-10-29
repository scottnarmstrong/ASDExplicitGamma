/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.SmoothFeedbackMaximizerMeasurable
public import ASDExplicitGamma.Scalar.SmoothFeedbackForcedFeedback

/-! Measurability of the joint smooth feedback `F_w²` of the actual OLD maximizers
in the OLD sample. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native
open Algsuperdiff.Section3
open scoped BigOperators

noncomputable section

/-- The indicator of a cell times the `i`th basis vector. -/
def indVec (R : TriadicCube 2) (i : Fin 2) : Vec 2 → Vec 2 :=
  (openCubeSet R).indicator (fun _ => basisVec i)

theorem indVec_memL2 (Q R : TriadicCube 2) (i : Fin 2) :
    MemVectorL2 (openCubeSet Q) (indVec R i) := by
  unfold indVec
  have hc : MemLp (fun _ : Vec 2 => basisVec i) 2 (volumeMeasureOn (openCubeSet Q)) :=
    memLp_const _
  exact hc.indicator (isOpen_openCubeSet R).measurableSet

theorem pairing_indicator (Q R : TriadicCube 2) (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (F : Vec 2 → BlockVec 2) (i : Fin 2) :
    scalarSourcePairing (openCubeSet Q) (indVec R i) F =
      ((volume (openCubeSet R)).toReal / (volume (openCubeSet Q)).toReal) *
        cubeAverage R (fun x => (F x).1 i) := by
  have hvolR : (volume (openCubeSet R)).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]; exact (cubeVolume_pos R).ne'
  have hmeasR := (isOpen_openCubeSet R).measurableSet
  rw [← forcedSource_volumeAverage_eq_cubeAverage R]
  unfold scalarSourcePairing volumeAverage
  have hpt : (fun x => vecDot (indVec R i x) (F x).1) =
      (openCubeSet R).indicator (fun x => (F x).1 i) := by
    funext x
    by_cases hx : x ∈ openCubeSet R
    · simp only [indVec, Set.indicator, hx, if_true, vecDot, basisVec, Fin.sum_univ_two]
      fin_cases i <;> simp
    · simp [indVec, Set.indicator, hx, vecDot]
  rw [hpt, integral_indicator hmeasR, Measure.restrict_restrict hmeasR,
    Set.inter_eq_left.mpr hRQ]
  field_simp

theorem ofBlockVec_sub (X Y : BlockVec 2) :
    HilbertBlockVec.ofBlockVec (X - Y) =
      HilbertBlockVec.ofBlockVec X - HilbertBlockVec.ofBlockVec Y := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i
  · simp [HilbertBlockVec.ofBlockVec, HilbertVec.ofVec, WithLp.toLp_sub]
  · simp [HilbertBlockVec.ofBlockVec, HilbertVec.ofVec, WithLp.toLp_sub]

theorem toH_sub {U : Set (Vec 2)} {F G : Vec 2 → BlockVec 2} (hF : MemBlockL2 U F)
    (hG : MemBlockL2 U G) :
    toHilbertBlockL2OfBlockField (hF.sub hG) =
      toHilbertBlockL2OfBlockField hF - toHilbertBlockL2OfBlockField hG := by
  apply Lp.ext
  filter_upwards [coeFn_toHilbertBlockL2OfBlockField (hF.sub hG),
    coeFn_toHilbertBlockL2OfBlockField hF, coeFn_toHilbertBlockL2OfBlockField hG,
    Lp.coeFn_sub (toHilbertBlockL2OfBlockField hF) (toHilbertBlockL2OfBlockField hG)]
    with x h1 h2 h3 h4
  rw [h1, h4]
  simp only [Pi.sub_apply, h2, h3]
  simp [hilbertifyBlockField, ofBlockVec_sub]

theorem flux_indicator (Q R : TriadicCube 2) (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (a : CoeffField 2) (F : Vec 2 → BlockVec 2) (i : Fin 2) :
    volumeAverage (openCubeSet Q) (fun x => blockVecDot (((0 : Vec 2), indVec R i x) : BlockVec 2)
        (blockMatVecMul (blockCoeffField a x) (F x))) =
      ((volume (openCubeSet R)).toReal / (volume (openCubeSet Q)).toReal) *
        cubeAverage R (fun x => (blockMatVecMul (blockCoeffField a x) (F x)).2 i) := by
  have hvolR : (volume (openCubeSet R)).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]; exact (cubeVolume_pos R).ne'
  have hmeasR := (isOpen_openCubeSet R).measurableSet
  rw [← forcedSource_volumeAverage_eq_cubeAverage R]
  unfold volumeAverage
  have hpt : (fun x => blockVecDot (((0 : Vec 2), indVec R i x) : BlockVec 2)
        (blockMatVecMul (blockCoeffField a x) (F x))) =
      (openCubeSet R).indicator
        (fun x => (blockMatVecMul (blockCoeffField a x) (F x)).2 i) := by
    funext x
    by_cases hx : x ∈ openCubeSet R
    · simp only [indVec, Set.indicator, hx, if_true, blockVecDot, vecDot, basisVec,
        Fin.sum_univ_two]
      fin_cases i <;> simp
    · simp [indVec, Set.indicator, hx, blockVecDot, vecDot]
  rw [hpt, integral_indicator hmeasR, Measure.restrict_restrict hmeasR,
    Set.inter_eq_left.mpr hRQ]
  field_simp

theorem measurable_tsum_of_nonneg'' {Ω : Type*} [MeasurableSpace Ω] (g : ℕ → Ω → ℝ)
    (hm : ∀ j, Measurable (g j)) (hn : ∀ j ω, 0 ≤ g j ω)
    (hs : ∀ ω, Summable (fun j => g j ω)) : Measurable (fun ω => ∑' j, g j ω) := by
  have hE : Measurable fun ω => ∑' j, ENNReal.ofReal (g j ω) :=
    Measurable.ennreal_tsum fun j => (hm j).ennreal_ofReal
  have : (fun ω => ∑' j, g j ω) = fun ω => (∑' j, ENNReal.ofReal (g j ω)).toReal := by
    funext ω
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => hn j ω) (hs ω),
      ENNReal.toReal_ofReal (tsum_nonneg fun j => hn j ω)]
  rw [this]
  exact hE.ennreal_toReal

/-- The weak-Haar energy of a measurable family of `L²` fields is measurable, when all
the cell averages are. -/
theorem weak_measurable {Ω : Type*} [MeasurableSpace Ω] (U : TriadicCube 2)
    (a : Ω → Vec 2 → Vec 2)
    (hmem : ∀ ω (l : Fin 2), MemLp (fun x => a ω x l) 2 (normalizedCubeMeasure U))
    (hmeas : ∀ (R : TriadicCube 2) (j : ℕ), R ∈ descendantsAtDepth U j → ∀ l : Fin 2,
      Measurable (fun ω => cubeAverage R (fun x => a ω x l))) :
    Measurable (fun ω => vectorWeakHaarEnergy U (a ω)) := by
  classical
  have hfun : (fun ω => vectorWeakHaarEnergy U (a ω)) = fun ω =>
      (1 - (Real.sqrt 3)⁻¹) * ∑' j : ℕ, (Real.sqrt 3)⁻¹ ^ j *
        forcedSource_meanLevel U j (a ω) := by
    funext ω
    exact forcedSource_weakEnergy_eq_meanSeries U (hmem ω)
  rw [hfun]
  refine Measurable.const_mul ?_ _
  have hlev (j : ℕ) : Measurable fun ω => forcedSource_meanLevel U j (a ω) := by
    unfold forcedSource_meanLevel descendantsAverage
    refine Measurable.const_mul (Finset.measurable_sum _ fun R hR => ?_) _
    simp only [vecNormSq, vecDot]
    exact Finset.measurable_sum _ fun l _ => (hmeas R j hR l).mul (hmeas R j hR l)
  refine measurable_tsum_of_nonneg'' _ (fun j => (hlev j).const_mul _) (fun j ω => ?_)
    (fun ω => forcedSource_meanLevel_series_summable U (hmem ω))
  refine mul_nonneg (pow_nonneg (by positivity) _) ?_
  unfold forcedSource_meanLevel descendantsAverage
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun R _ => ?_)
  simp only [vecNormSq, vecDot]
  exact Finset.sum_nonneg fun l _ => mul_self_nonneg _

section Averages

variable (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (w : Vec 2 → Vec 2)
  (hw : MemVectorL2 (openCubeSet Q) w)
  (Z : Cutoff.CutoffSample 2 → Vec 2 → BlockVec 2)
  (hZ : ∀ ω, IsScalarOldMaximizer Q M.nu (Annealed.sigmaBar M m : ℝ)
    (oldCutoffSkewCoefficient m Q ω) w (Z ω))

include hw hZ

theorem avg_potential_measurable (R : TriadicCube 2) (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (l : Fin 2) :
    Measurable (fun ω => cubeAverage R (fun x => (Z ω x).1 l - w x l)) := by
  classical
  letI finiteCell : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  letI : IsSeparable (volumeMeasureOn (openCubeSet Q)) := inferInstance
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  letI : SecondCountableTopology (HilbertBlockL2 (openCubeSet Q)) := inferInstance
  have hζ := maximizer_class_measurable M m Q w hw Z hZ
  let F : Vec 2 → BlockVec 2 := fun x => (w x, 0)
  have hF : MemBlockL2 (openCubeSet Q) F := memBlockL2_blockField hw MemLp.zero
  have hvolR : (volume (openCubeSet R)).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]; exact (cubeVolume_pos R).ne'
  have hvolQ : (volume (openCubeSet Q)).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]; exact (cubeVolume_pos Q).ne'
  let ℓ := pairingCLM (openCubeSet Q) (indVec_memL2 Q R l)
  have hmeas : Measurable fun ω => ((volume (openCubeSet Q)).toReal /
      (volume (openCubeSet R)).toReal) *
      ℓ (toHilbertBlockL2OfBlockField (hZ ω).1.1 - toHilbertBlockL2OfBlockField hF) :=
    (ℓ.continuous.measurable.comp (hζ.sub_const _)).const_mul _
  convert hmeas using 1
  funext ω
  have h1 := pairing_indicator Q R hRQ (Z ω - F) l
  have h2 : ℓ (toHilbertBlockL2OfBlockField (hZ ω).1.1 - toHilbertBlockL2OfBlockField hF) =
      scalarSourcePairing (openCubeSet Q) (indVec R l) (Z ω - F) := by
    rw [← toH_sub (hZ ω).1.1 hF]
    exact pairingCLM_eq _ _
  rw [h2, h1]
  have : cubeAverage R (fun x => (Z ω x).1 l - w x l) =
      cubeAverage R (fun x => ((Z ω - F) x).1 l) := by
    congr 1
  rw [this]
  field_simp

theorem avg_flux_measurable (U R : TriadicCube 2) (hUQ : openCubeSet U ⊆ openCubeSet Q)
    (hRU : openCubeSet R ⊆ openCubeSet U) (l : Fin 2) :
    Measurable (fun ω => cubeAverage R (fun x => (scalarCoefficientFlux
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
        (oldSignedCellCoefficient Q U hUQ (oldCutoffSkewCoefficient m Q ω))) (Z ω) x).2 l)) := by
  classical
  letI finiteCell : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  letI : IsSeparable (volumeMeasureOn (openCubeSet Q)) := inferInstance
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  letI : SecondCountableTopology (HilbertBlockL2 (openCubeSet Q)) := inferInstance
  have hσ : 0 < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).property
  have hζ := maximizer_class_measurable M m Q w hw Z hZ
  have hB : Measurable fun ω : Cutoff.CutoffSample 2 =>
      (scalarFrameRealization Q M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ
        (oldCutoffSkewCoefficient m Q ω)).energyBilin :=
    measurable_oldCutoff_scalarFrameEnergyBilin m Q M.nu (Annealed.sigmaBar M m : ℝ)
      M.nu_pos hσ
  have hRQ : openCubeSet R ⊆ openCubeSet Q := hRU.trans hUQ
  let T : Vec 2 → BlockVec 2 := fun x => ((0 : Vec 2), indVec R l x)
  have hT : MemBlockL2 (openCubeSet Q) T :=
    memBlockL2_blockField (memVectorL2_const 0) (indVec_memL2 Q R l)
  have hmeas : Measurable fun ω => ((volume (openCubeSet Q)).toReal /
      (volume (openCubeSet R)).toReal) *
      (scalarFrameRealization Q M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ
        (oldCutoffSkewCoefficient m Q ω)).energyBilin
        (toHilbertBlockL2OfBlockField (hZ ω).1.1) (toHilbertBlockL2OfBlockField hT) :=
    ((hB.clm_apply hζ).clm_apply measurable_const).const_mul _
  convert hmeas using 1
  funext ω
  have hvolR : (volume (openCubeSet R)).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]; exact (cubeVolume_pos R).ne'
  have hvolQ : (volume (openCubeSet Q)).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]; exact (cubeVolume_pos Q).ne'
  rw [scalar_frame_bilinear_field Q M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ
    (oldCutoffSkewCoefficient m Q ω) (hZ ω).1.1 hT]
  have h1 := flux_indicator Q R hRQ
    (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
      (oldCutoffSkewCoefficient m Q ω)) (Z ω) l
  have h2 : cubeAverage R (fun x => (scalarCoefficientFlux
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
        (oldSignedCellCoefficient Q U hUQ (oldCutoffSkewCoefficient m Q ω))) (Z ω) x).2 l) =
      cubeAverage R (fun x => (blockMatVecMul (blockCoeffField
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (oldCutoffSkewCoefficient m Q ω)) x) (Z ω x)).2 l) := by
    rw [← forcedSource_volumeAverage_eq_cubeAverage R, ← forcedSource_volumeAverage_eq_cubeAverage R]
    apply forcedSource_volumeAverage_congr_ae
    filter_upwards [ae_restrict_mem (isOpen_openCubeSet R).measurableSet] with x hx
    have hco : responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
        (oldSignedCellCoefficient Q U hUQ (oldCutoffSkewCoefficient m Q ω)) x =
        responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (oldCutoffSkewCoefficient m Q ω) x := by
      unfold responseFramePlanarCoefficientField
      rw [old_signed_cell_coefficient_extension_eq Q U hUQ _ (hRU hx)]
    simp only [scalarCoefficientFlux, blockCoeffField, hco]
  rw [h2]
  change _ = _ * volumeAverage (openCubeSet Q) (fun x => blockVecDot (T x) _)
  rw [h1]
  field_simp

end Averages

theorem measurable_cellAverage' {Ω : Type*} [MeasurableSpace Ω] (Q : TriadicCube 2)
    (depth : ℕ) {f : Ω → OldSignedCellIndex Q depth → ℝ} (h : ∀ U, Measurable (fun ω => f ω U)) :
    Measurable (fun ω => oldSignedCellAverage Q depth (f ω)) := by
  unfold oldSignedCellAverage
  exact (Finset.measurable_sum _ (fun U _ => h U)).const_mul _

/-- `F_w²` of the actual OLD maximizers is a measurable function of the OLD sample. -/
theorem FwStar_measurable {ι : Type*} (S : Finset ι) (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (depth : ℕ) (u : ι → H10Function (openCubeSet Q))
    (Z : Cutoff.CutoffSample 2 → ι → Vec 2 → BlockVec 2)
    (hZ : ∀ ω i, IsScalarOldMaximizer Q M.nu (Annealed.sigmaBar M m : ℝ)
      (oldCutoffSkewCoefficient m Q ω) (fun x => (u i).toH1Function.grad x) (Z ω i)) :
    Measurable (fwStar S M m Q depth u Z) := by
  classical
  have hσ : 0 < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).property
  unfold fwStar
  refine Finset.measurable_sum S fun i _ => ?_
  refine measurable_cellAverage' Q depth fun U => ?_
  have hUQ := openCubeSet_subset_of_mem_descendantsAtDepth U.property
  have hw : MemVectorL2 (openCubeSet Q) (fun x => (u i).toH1Function.grad x) :=
    (u i).toH1Function.grad_memVectorL2
  have hwU : MemVectorL2 (openCubeSet U.val) (fun x => (u i).toH1Function.grad x) :=
    hw.mono_measure (Measure.restrict_mono_set volume hUQ)
  have hZU (ω : Cutoff.CutoffSample 2) : MemBlockL2 (openCubeSet U.val) (Z ω i) :=
    (hZ ω i).1.1.mono_measure (Measure.restrict_mono_set volume hUQ)
  refine Measurable.add ?_ ?_
  · refine weak_measurable U.val
      (fun ω x j => (Z ω i x).1 j - (u i).toH1Function.grad x j) ?_ ?_
    · intro ω l
      exact memLp_coord ((memVectorL2_fst_of_memBlockL2 (hZU ω)).sub hwU) l
    · intro R j hR l
      exact avg_potential_measurable M m Q (fun x => (u i).toH1Function.grad x) hw
        (fun ω => Z ω i) (fun ω => hZ ω i) R
        ((openCubeSet_subset_of_mem_descendantsAtDepth hR).trans hUQ) l
  · refine weak_measurable U.val
      (fun ω x => (scalarCoefficientFlux
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (oldSignedCellCoefficient Q U.val hUQ (oldCutoffSkewCoefficient m Q ω))) (Z ω i) x).2)
      ?_ ?_
    · intro ω l
      have hEllU := responseFramePlanarCoefficientField_isElliptic
        (measurableSet_openCubeSet U.val) M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ
        (oldSignedCellCoefficient Q U.val hUQ (oldCutoffSkewCoefficient m Q ω))
      exact memLp_coord (memVectorL2_snd_of_memBlockL2
        (scalar_coefficient_flux_memL2 U.val _ hEllU (hZU ω))) l
    · intro R j hR l
      exact avg_flux_measurable M m Q (fun x => (u i).toH1Function.grad x) hw
        (fun ω => Z ω i) (fun ω => hZ ω i) U.val R hUQ
        (openCubeSet_subset_of_mem_descendantsAtDepth hR) l

end

end ASDExplicitGamma.Scalar
