/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.SmoothFeedbackActualMeasurable
public import ASDExplicitGamma.Scalar.SmoothFeedbackTraceCap

/-! Nonnegativity, measurability of `𝓑`, and integrability of the actual
smooth-feedback charges. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native ASDExplicitGamma.Main ASDExplicitGamma.Inverse
open Algsuperdiff.Section3
open scoped BigOperators ENNReal
attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

theorem Bhist_measurable (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) :
    Measurable (fun ω => bhist M m Q 134 ω) := by
  classical
  let I := descendantsAtDepth Q 89
  let fam : TriadicCube 2 → Finset (TriadicCube 2) := fun i => descendantsAtDepth i 45
  let w := bankPartialInsertionWeights m 1 0
  have hBnn (x : Cutoff.CutoffSample 2) : 0 ≤ bhist M m Q 134 x :=
    smooth_feedback_source_history_maximum_nonneg Q 134 M.nu (Annealed.sigmaBar M m : ℝ) _
  have hGm : Measurable (inverseBankGroupedHistory I fam M m (m + 40) w) :=
    history_finite_max_measurable _ _ (fun i => history_finite_max_measurable _ _
      (fun U => bank_root_inverse_history_measurable U.1 M m (m + 40) w))
  have : (fun x => bhist M m Q 134 x) =
      fun x => (inverseBankGroupedHistory I fam M m (m + 40) w x).toReal := by
    funext x
    rw [← Bhist_eq_grouped M m Q x, ENNReal.toReal_ofReal (hBnn x)]
  rw [this]
  exact hGm.ennreal_toReal

theorem Bhist_nonneg (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (depth : ℕ)
    (ω : Cutoff.CutoffSample 2) : 0 ≤ bhist M m Q depth ω :=
  smooth_feedback_source_history_maximum_nonneg Q depth M.nu
    (Annealed.sigmaBar M m : ℝ) _

section Nonneg

variable {ι : Type*} (S : Finset ι) (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
  (depth : ℕ) (u : ι → H10Function (openCubeSet Q))

theorem cellMat_quad_nonneg (U : OldSignedCellIndex Q depth) (ω : Cutoff.CutoffSample 2)
    (P : BlockVec 2) :
    0 ≤ blockVecDot P (blockMatVecMul (cellMat M m Q depth U ω) P) := by
  unfold cellMat
  rw [← old_signed_affine_energy U.val M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
    (Annealed.sigmaBar M m).property
    (oldSignedCellCoefficient Q U.val
      (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
      (oldCutoffSkewCoefficient m Q ω)) P]
  exact old_signed_energy_pairing_nonneg U.val M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
    (Annealed.sigmaBar M m).property _ _

theorem PK_nonneg (ω : Cutoff.CutoffSample 2) : 0 ≤ pK' S M m Q depth u ω :=
  Finset.sum_nonneg fun i _ => old_signed_cell_average_nonneg Q depth _
    fun U => cellMat_quad_nonneg M m Q depth U ω _

theorem PD_nonneg (ω : Cutoff.CutoffSample 2) : 0 ≤ pD S M m Q depth u ω :=
  Finset.sum_nonneg fun i _ => old_signed_cell_average_nonneg Q depth _
    fun U => cellMat_quad_nonneg M m Q depth U ω _

theorem RK_nonneg (ω : Cutoff.CutoffSample 2) : 0 ≤ rK' S M m Q depth u ω :=
  Finset.sum_nonneg fun i _ => old_signed_cell_average_nonneg Q depth _
    fun U => old_signed_energy_pairing_nonneg U.val M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
      (Annealed.sigmaBar M m).property _ _

theorem Elift_nonneg (ω : Cutoff.CutoffSample 2) : 0 ≤ elift S M m Q depth u ω :=
  Finset.sum_nonneg fun i _ => old_signed_cell_average_nonneg Q depth _
    fun U => old_signed_energy_pairing_nonneg U.val M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
      (Annealed.sigmaBar M m).property _ _

variable (hcenter : ∀ i, ∀ U : TriadicCube 2, U ∈ descendantsAtDepth Q depth →
      ScalarPositiveHaarAdmissible U (fun x j =>
        (u i).toH1Function.grad x j -
          cubeAverage U (fun y => (u i).toH1Function.grad y j)))

theorem RD_nonneg (ω : Cutoff.CutoffSample 2) : 0 ≤ rD S M m Q depth u hcenter ω :=
  Finset.sum_nonneg fun i _ => old_signed_cell_average_nonneg Q depth _
    fun U => old_signed_energy_pairing_nonneg U.val M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
      (Annealed.sigmaBar M m).property _ _

end Nonneg

section Pair

variable {ι : Type*} (S : Finset ι) (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
  (depth : ℕ) (u : ι → H10Function (openCubeSet Q))

theorem cell_pair_eq (U : OldSignedCellIndex Q depth) (ω : Cutoff.CutoffSample 2)
    (w : Vec 2) :
    blockVecDot ((w, 0) : BlockVec 2) (blockMatVecMul (cellMat M m Q depth U ω) (w, 0)) +
      blockVecDot ((0, w) : BlockVec 2) (blockMatVecMul (cellMat M m Q depth U ω) (0, w)) -
      2 * vecNormSq w = smoothFeedbackPairCharge M m U.val w ω := by
  rw [cellMat_eq_A, smooth_feedback_block_top_quadratic,
    smooth_feedback_block_bottom_quadratic]
  rfl

theorem Apair_nonneg (ω : Cutoff.CutoffSample 2) : 0 ≤ apair S M m Q depth u ω :=
  Finset.sum_nonneg fun i _ => old_signed_cell_average_nonneg Q depth _ fun U => by
    rw [cell_pair_eq]
    exact (smooth_feedback_cell_pair_charge_bounds M m U.val _ ω).1

theorem Apair_le_trace (ω : Cutoff.CutoffSample 2) :
    apair S M m Q depth u ω ≤ ∑ i ∈ S, oldSignedCellAverage Q depth (fun U =>
      smoothFeedbackCellT M m U.val ω * vecNormSq (cellMean Q u i U.val)) := by
  refine Finset.sum_le_sum fun i _ => old_signed_cell_average_mono Q depth fun U => ?_
  rw [cell_pair_eq]
  exact (smooth_feedback_cell_pair_charge_bounds M m U.val _ ω).2

theorem Apair_integrable :
    Integrable (apair S M m Q depth u) (Cutoff.cutoffSampleLaw M).toMeasure := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hT (U : TriadicCube 2) : Integrable (fun ω => smoothFeedbackCellT M m U ω) μ :=
    Cold.coldNativeCellTrace_integrable M m U
  have hg : Integrable (fun ω => ∑ i ∈ S, oldSignedCellAverage Q depth (fun U =>
      smoothFeedbackCellT M m U.val ω * vecNormSq (cellMean Q u i U.val))) μ := by
    refine integrable_finsetSum _ (fun i _ => ?_)
    unfold oldSignedCellAverage
    exact (integrable_finsetSum _ (fun U _ => (hT U.val).mul_const _)).const_mul _
  refine hg.mono' (Apair_measurable S M m Q depth u).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_of_nonneg (Apair_nonneg S M m Q depth u ω)]
  exact Apair_le_trace S M m Q depth u ω

theorem Theta_nonneg (ω : Cutoff.CutoffSample 2) : 0 ≤ theta'' S M m Q depth u ω :=
  Finset.sum_nonneg fun i _ => old_signed_cell_average_nonneg Q depth _ fun U =>
    smooth_feedback_cell_directional_gamma_nonneg M m U.val _ ω

/-- The directional Gram of every side-`(m-5)` cell is integrable. -/
theorem directional_gamma_integrable
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (U : TriadicCube 2) (hU : U.scale = m - 5) (e : Vec 2) :
    Integrable (fun ω => smoothFeedbackCellDirectionalGamma M m U e ω)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let O : TriadicCube 2 := originCube 2 (m - ((5 : ℕ) : ℤ))
  have hO : O ∈ descendantsAtDepth (originCube 2 m) 5 :=
    ASDExplicitGamma.Inverse.originCube_mem_descendantsAtDepth' 2 m 5
  have hrow := Main.main_envelope_xi_depth5_actual_law
    M h hM hγ N hpast m hm
  have hlocal := hrow 0 ⟨by norm_num, by norm_num⟩ O hO (0 : Fin 4)
  have hThetaInt : Integrable
      (fun ω : Cutoff.CutoffSample 2 => mixedOldTheta M m O 0 ω) μ := by
    simpa [μ] using hlocal.1
  have hIntO : Integrable
      (fun ω => smoothFeedbackCellDirectionalGamma M m O e ω) μ :=
    smooth_feedback_directional_gamma_integrable_of_theta_integrable
      M hγ m O hO e hThetaInt
  have hscale : originCube 2 U.scale = O := by
    rw [hU]
    simp only [O]
    norm_num
  have hfun : (fun ω => smoothFeedbackCellDirectionalGamma M m U e ω) =
      (fun ω => smoothFeedbackCellDirectionalGamma M m
          (originCube 2 U.scale) e ω) ∘
        (MeasurableEquiv.vadd (triadicCubeShift U) :
          Cutoff.CutoffSample 2 ≃ᵐ Cutoff.CutoffSample 2) := by
    funext ω
    exact smooth_feedback_cell_directional_gamma_translate_origin M m U e ω
  rw [hfun, hscale]
  exact ((MeasureTheory.measurePreserving_vadd (triadicCubeShift U) μ
    ).integrable_comp_emb (MeasurableEquiv.vadd (triadicCubeShift U) :
      Cutoff.CutoffSample 2 ≃ᵐ Cutoff.CutoffSample 2).measurableEmbedding).2 hIntO

end Pair

end

end ASDExplicitGamma.Scalar
