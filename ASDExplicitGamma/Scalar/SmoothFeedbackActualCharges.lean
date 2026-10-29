/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.SmoothFeedbackActualAgg

/-! `L¹` and Hölder-range bounds of the actual charges `P_K`, `P_D`, `R_K`,
`E_lift` from the cell histories. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native ASDExplicitGamma.Main ASDExplicitGamma.Inverse
open Algsuperdiff.Section3
open scoped BigOperators ENNReal
attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

section Charges

variable {ι : Type*} (S : Finset ι) (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
  (u : ι → H10Function (openCubeSet Q))

theorem blockVecDot_top_self (w : Vec 2) :
    blockVecDot ((w, 0) : BlockVec 2) (w, 0) = vecNormSq w := by
  simp [blockVecDot, vecNormSq, vecDot]

theorem blockVecDot_bottom_self (w : Vec 2) :
    blockVecDot ((0, w) : BlockVec 2) (0, w) = vecNormSq w := by
  simp [blockVecDot, vecNormSq, vecDot]

theorem Wmean_le_Omega2 :
    ∑ i ∈ S, oldSignedCellAverage Q 134 (fun U => vecNormSq (cellMean Q u i U.val)) ≤
      omega2 S Q u := by
  unfold omega2
  exact Finset.sum_le_sum fun i _ => cellMeanSq_le Q 134 _
    (u i).toH1Function.grad_memVectorL2

theorem cell_top_load_le
    (H : ∀ i, HasWeakHessianOn (openCubeSet Q) (u i).toH1Function)
    (ω : Cutoff.CutoffSample 2) (i : ι) (U : OldSignedCellIndex Q 134) :
    oldSignedEnergyPairing U.val M.nu (Annealed.sigmaBar M m : ℝ)
      (oldSignedCellCoefficient Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
        (oldCutoffSkewCoefficient m Q ω))
      (oldSignedCellResidual Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
        M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).property
        (oldCutoffSkewCoefficient m Q ω) (topLoad Q u i) (topLoad_memL2 Q u i))
      (oldSignedCellResidual Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
        M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).property
        (oldCutoffSkewCoefficient m Q ω) (topLoad Q u i) (topLoad_memL2 Q u i)) ≤
      (vecNormSq (cellMean Q u i U.val) + vectorPositiveHaarEnergy U.val
        (fun x j => (u i).toH1Function.grad x j -
          cubeAverage U.val (fun y => (u i).toH1Function.grad y j))) *
        cellResponseHistory M m U.val ω := by
  have hadm := smooth_feedback_h2_projected_source_admissible Q U.val
    (openCubeSet_subset_of_mem_descendantsAtDepth U.property) (u i) (H i)
  have h1 := cell_top_energy_le M m Q U.val
    (openCubeSet_subset_of_mem_descendantsAtDepth U.property) ω
    (fun x j => (u i).toH1Function.grad x j) hadm.2.1 hadm.1
    (topLoad Q u i) (topLoad_memL2 Q u i) (fun x => rfl)
  have h3 := vectorPositive_split U.val (fun x j => (u i).toH1Function.grad x j) hadm.1
  rw [h3] at h1
  rw [mul_comm]
  exact h1

theorem cell_centered_load_le
    (H : ∀ i, HasWeakHessianOn (openCubeSet Q) (u i).toH1Function)
    (ω : Cutoff.CutoffSample 2) (i : ι) (U : OldSignedCellIndex Q 134) :
    oldSignedEnergyPairing U.val M.nu (Annealed.sigmaBar M m : ℝ)
      (oldSignedCellCoefficient Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
        (oldCutoffSkewCoefficient m Q ω))
      (oldSignedCellResidual Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
        M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).property
        (oldCutoffSkewCoefficient m Q ω) (centeredLoad Q u i U.val)
        (centeredLoad_memL2 Q u i U.val))
      (oldSignedCellResidual Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
        M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).property
        (oldCutoffSkewCoefficient m Q ω) (centeredLoad Q u i U.val)
        (centeredLoad_memL2 Q u i U.val)) ≤
      vectorPositiveHaarEnergy U.val
        (fun x j => (u i).toH1Function.grad x j -
          cubeAverage U.val (fun y => (u i).toH1Function.grad y j)) *
        cellResponseHistory M m U.val ω := by
  have hadm := smooth_feedback_h2_projected_source_admissible Q U.val
    (openCubeSet_subset_of_mem_descendantsAtDepth U.property) (u i) (H i)
  have h1 := cell_top_energy_le M m Q U.val
    (openCubeSet_subset_of_mem_descendantsAtDepth U.property) ω
    (fun x j => (u i).toH1Function.grad x j - cubeAverage U.val
      (fun y => (u i).toH1Function.grad y j)) hadm.2.2.2 hadm.2.2.1
    (centeredLoad Q u i U.val) (centeredLoad_memL2 Q u i U.val) (fun x => rfl)
  rw [mul_comm]
  exact h1

end Charges

section Agg

variable {ι : Type*} (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
  (hγ : M.gamma ≤ gammaZero) (m : ℤ) (hpast : ∀ n ≤ m, nativeInductionState M h n)
  (Q : TriadicCube 2) (hQ : Q.scale = m + 129) (S : Finset ι)
  (u : ι → H10Function (openCubeSet Q))

include hM hγ hpast hQ

theorem PK_Lq :
    Integrable (pK' S M m Q 134 u) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    eLpNorm (pK' S M m Q 134 u) (ENNReal.ofReal (128 / 127))
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (mStar' M * omega2 S Q u / (1 - 76 / 100)) := by
  have hag := agg_charge M h hM hγ m hpast Q hQ S
    (fun i U => vecNormSq (cellMean Q u i U.val)) (fun _ _ => vecNormSq_nonneg _)
    (K := 1 / (24 / 100)) (by norm_num) (PK_measurable S M m Q 134 u)
    (PK_nonneg S M m Q 134 u) (fun ω => by
      unfold pK'
      refine Finset.sum_le_sum fun i _ => cellAverage_le_of_le Q 134
        (fun U => vecNormSq_nonneg _) (fun U => ?_)
      have := cellMat_quad_le M m Q 134 U ω ((cellMean Q u i U.val, 0) : BlockVec 2)
      rw [blockVecDot_top_self] at this
      refine this.trans (le_of_eq ?_)
      ring)
  obtain ⟨hi, -, hq⟩ := hag
  refine ⟨hi, hq.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hW := Wmean_le_Omega2 S Q u
  have hm0 := mStar_nonneg M
  have : (∑ i ∈ S, ((descendantsAtDepth Q 134).card : ℝ)⁻¹ *
      ∑ U : OldSignedCellIndex Q 134, vecNormSq (cellMean Q u i U.val)) ≤ omega2 S Q u :=
    hW
  calc 1 / (24 / 100) * mStar' M * _ ≤ 1 / (24 / 100) * mStar' M * omega2 S Q u :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

theorem PD_integrable :
    Integrable (pD S M m Q 134 u) (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hag := agg_charge M h hM hγ m hpast Q hQ S
    (fun i U => vecNormSq (cellMean Q u i U.val)) (fun _ _ => vecNormSq_nonneg _)
    (K := 1 / (24 / 100)) (by norm_num) (PD_measurable S M m Q 134 u)
    (PD_nonneg S M m Q 134 u) (fun ω => by
      unfold pD
      refine Finset.sum_le_sum fun i _ => cellAverage_le_of_le Q 134
        (fun U => vecNormSq_nonneg _) (fun U => ?_)
      have := cellMat_quad_le M m Q 134 U ω ((0, cellMean Q u i U.val) : BlockVec 2)
      rw [blockVecDot_bottom_self] at this
      refine this.trans (le_of_eq ?_)
      ring)
  exact hag.1

theorem RK_Lq
    (H : ∀ i, HasWeakHessianOn (openCubeSet Q) (u i).toH1Function) :
    Integrable (rK' S M m Q 134 u) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω, rK' S M m Q 134 u ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      mStar' M * deltaSq' S Q 134 u ∧
    eLpNorm (rK' S M m Q 134 u) (ENNReal.ofReal (128 / 127))
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (mStar' M * deltaSq' S Q 134 u) := by
  have hag := agg_charge M h hM hγ m hpast Q hQ S
    (fun i U => vectorPositiveHaarEnergy U.val
      (fun x j => (u i).toH1Function.grad x j -
        cubeAverage U.val (fun y => (u i).toH1Function.grad y j)))
    (fun _ _ => vectorPositiveHaarEnergy_nonneg _ _)
    (K := 1) zero_le_one (RK_measurable S M m Q 134 u)
    (RK_nonneg S M m Q 134 u) (fun ω => by
      unfold rK'
      refine Finset.sum_le_sum fun i _ => cellAverage_le_of_le Q 134
        (fun U => vectorPositiveHaarEnergy_nonneg _ _) (fun U => ?_)
      have := cell_centered_load_le M m Q u H ω i U
      refine this.trans (le_of_eq ?_)
      ring)
  have hsum : (∑ i ∈ S, ((descendantsAtDepth Q 134).card : ℝ)⁻¹ *
      ∑ U : OldSignedCellIndex Q 134, vectorPositiveHaarEnergy U.val
        (fun x j => (u i).toH1Function.grad x j -
          cubeAverage U.val (fun y => (u i).toH1Function.grad y j))) =
      deltaSq' S Q 134 u := rfl
  obtain ⟨hi, hI, hq⟩ := hag
  rw [hsum] at hI hq
  refine ⟨hi, ?_, ?_⟩
  · simpa using hI
  · simpa using hq

theorem Elift_Lq
    (H : ∀ i, HasWeakHessianOn (openCubeSet Q) (u i).toH1Function) :
    eLpNorm (elift S M m Q 134 u) (ENNReal.ofReal (128 / 127))
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (mStar' M * (omega2 S Q u + deltaSq' S Q 134 u)) := by
  have hag := agg_charge M h hM hγ m hpast Q hQ S
    (fun i U => vecNormSq (cellMean Q u i U.val) + vectorPositiveHaarEnergy U.val
      (fun x j => (u i).toH1Function.grad x j -
        cubeAverage U.val (fun y => (u i).toH1Function.grad y j)))
    (fun _ _ => add_nonneg (vecNormSq_nonneg _) (vectorPositiveHaarEnergy_nonneg _ _))
    (K := 1) zero_le_one (Elift_measurable S M m Q 134 u)
    (Elift_nonneg S M m Q 134 u) (fun ω => by
      unfold elift
      refine Finset.sum_le_sum fun i _ => cellAverage_le_of_le Q 134
        (fun U => add_nonneg (vecNormSq_nonneg _) (vectorPositiveHaarEnergy_nonneg _ _))
        (fun U => ?_)
      have := cell_top_load_le M m Q u H ω i U
      refine this.trans (le_of_eq ?_)
      ring)
  obtain ⟨-, -, hq⟩ := hag
  refine hq.trans (ENNReal.ofReal_le_ofReal ?_)
  have hW := Wmean_le_Omega2 S Q u
  have hsum : (∑ i ∈ S, ((descendantsAtDepth Q 134).card : ℝ)⁻¹ *
      ∑ U : OldSignedCellIndex Q 134, (vecNormSq (cellMean Q u i U.val) +
        vectorPositiveHaarEnergy U.val
        (fun x j => (u i).toH1Function.grad x j -
          cubeAverage U.val (fun y => (u i).toH1Function.grad y j)))) =
      (∑ i ∈ S, oldSignedCellAverage Q 134 (fun U => vecNormSq (cellMean Q u i U.val))) +
        deltaSq' S Q 134 u := by
    unfold deltaSq' oldSignedCellAverage
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_add, Finset.sum_add_distrib]
  rw [hsum]
  have hm0 := mStar_nonneg M
  calc 1 * mStar' M * _ ≤ 1 * mStar' M * (omega2 S Q u + deltaSq' S Q 134 u) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

end Agg

section RD

variable {ι : Type*} (S : Finset ι) (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
  (u : ι → H10Function (openCubeSet Q))

theorem RD_le_Bdsq
    (H : ∀ i, HasWeakHessianOn (openCubeSet Q) (u i).toH1Function)
    (hcenter : ∀ i, ∀ U : TriadicCube 2, U ∈ descendantsAtDepth Q 134 →
      ScalarPositiveHaarAdmissible U (fun x j =>
        (u i).toH1Function.grad x j -
          cubeAverage U (fun y => (u i).toH1Function.grad y j)))
    (ω : Cutoff.CutoffSample 2) :
    rD S M m Q 134 u hcenter ω ≤ bhist M m Q 134 ω * deltaSq' S Q 134 u := by
  classical
  have hB0 := Bhist_nonneg M m Q 134 ω
  unfold rD deltaSq'
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hcell (U : OldSignedCellIndex Q 134) :
      (oldSignedEnergyPairing U.val M.nu (Annealed.sigmaBar M m : ℝ)
        (oldSignedCellCoefficient Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          (oldCutoffSkewCoefficient m Q ω))
        (scalarResidualField U.val M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
          (Annealed.sigmaBar M m).property
          (oldSignedCellCoefficient Q U.val
            (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
            (oldCutoffSkewCoefficient m Q ω))
          (toHilbertBlockL2OfBlockField
            (upper_cell_reset_bottom_load_memL2 U.val
              (hcenter i U.val U.property).memLp)))
        (scalarResidualField U.val M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
          (Annealed.sigmaBar M m).property
          (oldSignedCellCoefficient Q U.val
            (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
            (oldCutoffSkewCoefficient m Q ω))
          (toHilbertBlockL2OfBlockField
            (upper_cell_reset_bottom_load_memL2 U.val
              (hcenter i U.val U.property).memLp)))) ≤
      bhist M m Q 134 ω * vectorPositiveHaarEnergy U.val
        (fun x j => (u i).toH1Function.grad x j -
          cubeAverage U.val (fun y => (u i).toH1Function.grad y j)) := by
    have hadm := smooth_feedback_h2_projected_source_admissible Q U.val
      (openCubeSet_subset_of_mem_descendantsAtDepth U.property) (u i) (H i)
    have h1 := cell_bottom_energy_le M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
      (Annealed.sigmaBar M m).property Q U.val
      (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
      (oldCutoffSkewCoefficient m Q ω)
      (fun x j => (u i).toH1Function.grad x j - cubeAverage U.val
        (fun y => (u i).toH1Function.grad y j)) hadm.2.2.1
    have h2 := smooth_feedback_source_history_maximum_member_le Q 134 M.nu
      (Annealed.sigmaBar M m : ℝ) (oldCutoffSkewCoefficient m Q ω) U.val U.property
    have h4 := vectorPositiveHaarEnergy_nonneg U.val (fun x j =>
      (u i).toH1Function.grad x j - cubeAverage U.val (fun y => (u i).toH1Function.grad y j))
    exact h1.trans (mul_le_mul_of_nonneg_right h2 h4)
  have hav := old_signed_cell_average_mono Q 134 hcell
  rw [old_signed_cell_average_mul] at hav
  exact hav

theorem RD_bounds
    (H : ∀ i, HasWeakHessianOn (openCubeSet Q) (u i).toH1Function)
    (hcenter : ∀ i, ∀ U : TriadicCube 2, U ∈ descendantsAtDepth Q 134 →
      ScalarPositiveHaarAdmissible U (fun x j =>
        (u i).toH1Function.grad x j -
          cubeAverage U (fun y => (u i).toH1Function.grad y j)))
    {b : ℝ} (hb : 0 ≤ b)
    (hBq : eLpNorm (fun ω => bhist M m Q 134 ω) 128
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal b) :
    Integrable (rD S M m Q 134 u hcenter) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω, rD S M m Q 134 u hcenter ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      b * deltaSq' S Q 134 u := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hBm := Bhist_measurable M m Q
  have hBi : Integrable (fun ω => bhist M m Q 134 ω) μ := by
    have hmem : MemLp (fun ω => bhist M m Q 134 ω) 128 μ :=
      memLp_iff.mpr (hBq.trans_lt ENNReal.ofReal_lt_top)
    exact hmem.integrable (by norm_num)
  have hBint : (∫ ω, bhist M m Q 134 ω ∂μ) ≤ b := by
    have := integral_mul_le_128 (μ := μ) hBm measurable_const
      (fun ω => Bhist_nonneg M m Q 134 ω) (fun _ => zero_le_one) hb zero_le_one hBq
      (by
        rw [eLpNorm_const _ (by simp) (IsProbabilityMeasure.ne_zero μ)]
        simp)
    simpa using this
  have hd : 0 ≤ deltaSq' S Q 134 u :=
    Finset.sum_nonneg fun i _ => old_signed_cell_average_nonneg Q 134 _
      fun U => vectorPositiveHaarEnergy_nonneg _ _
  have hmaj : Integrable (fun ω => bhist M m Q 134 ω * deltaSq' S Q 134 u) μ :=
    hBi.mul_const _
  refine ⟨?_, ?_⟩
  · refine hmaj.mono' (RD_measurable S M m Q 134 u hcenter).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_of_nonneg (RD_nonneg S M m Q 134 u hcenter ω)]
    exact RD_le_Bdsq S M m Q u H hcenter ω
  · have hI := (RD_measurable S M m Q 134 u hcenter)
    calc (∫ ω, rD S M m Q 134 u hcenter ω ∂μ)
        ≤ ∫ ω, bhist M m Q 134 ω * deltaSq' S Q 134 u ∂μ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall
            (RD_nonneg S M m Q 134 u hcenter)) hmaj
            (Filter.Eventually.of_forall (RD_le_Bdsq S M m Q u H hcenter))
      _ = (∫ ω, bhist M m Q 134 ω ∂μ) * deltaSq' S Q 134 u := integral_mul_const _ _
      _ ≤ b * deltaSq' S Q 134 u := mul_le_mul_of_nonneg_right hBint hd

end RD

end

end ASDExplicitGamma.Scalar
