/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.SmoothFeedbackLoadModes
public import ASDExplicitGamma.Scalar.SmoothFeedbackGapSourceForce
public import ASDExplicitGamma.Scalar.SmoothFeedbackLambda8Source
public import ASDExplicitGamma.Main.HilbertFiniteCoordinates
public import ASDExplicitGamma.Native.OldSignedCenteredPositive

/-! The centered quarter-order positive Haar energy of a vector field is the
Hilbert circulant positive energy used by the one-load oscillation input. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Triadic
open ASDExplicitGamma.Native ASDExplicitGamma.Main
open ASDExplicitGamma.Gaussian
open Algsuperdiff.Section3
open scoped BigOperators
attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

theorem vector_positive_centered_eq_hilbert_circ
    (U : TriadicCube 2) (F : Vec 2 → Vec 2) (hF : ScalarQuarterHaarAdmissible U F) :
    vectorPositiveHaarEnergy U
        (fun x j => F x j - cubeAverage U (fun y => F y j)) =
      hilbertPositiveCircHaarNorm U ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
        (fun x => HilbertVec.ofVec (F x)) ^ 2 := by
  classical
  have hq : (3 : ℝ) ^ (2 * (1 / 4 : ℝ)) = Real.sqrt 3 := by
    rw [show 2 * (1 / 4 : ℝ) = (1 / 2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow]
  have hcoord (j : Fin 2) : MemLp (fun x => F x j) 2 (normalizedCubeMeasure U) :=
    (memLp_pi_iff.mp hF.memLp) j
  let G : Vec 2 → EuclideanSpace ℝ (Fin 2) := fun x => HilbertVec.ofVec (F x)
  have hG : MemLp G 2 (normalizedCubeMeasure U) := by
    apply (memLp_piLp_iff).2
    intro a
    exact hcoord a
  have hseries : Summable (fun k => (Real.sqrt 3) ^ (k + 1) *
      hilbertEnergy U (hilbertCubeIncrement U (k + 1) G)) := by
    have he (k : ℕ) : (Real.sqrt 3) ^ (k + 1) *
        hilbertEnergy U (hilbertCubeIncrement U (k + 1) G) =
        ∑ i : Fin 2, (Real.sqrt 3) ^ (k + 1) *
          energy U (cubeIncrement U (k + 1) (fun x => F x i)) := by
      rw [main_hilbertEnergy_euclidean U (hilbertCubeIncrement_memLp U (k + 1) G),
        Finset.mul_sum]
      simp_rw [← main_hilbertIncrement_coordinate U hG]
      rfl
    simp_rw [he]
    exact summable_sum fun i _ => hF.increments i
  have hraw := main_hilbertPrimalEnergy_euclidean U hG hseries
  have hroot0 : hilbertEnergy U (hilbertCubeIncrement U 0 G) =
      ∑ a : Fin 2, (cubeAverage U (fun x => F x a)) ^ 2 := by
    have h := main_hilbertEnergy_euclidean U (hilbertCubeIncrement_memLp U 0 G)
    simp_rw [← main_hilbertIncrement_coordinate U hG 0] at h
    simpa only [cubeIncrement_zero, energy_projection_zero] using h
  have hcircNonneg : 0 ≤ hilbertPrimalCircEnergy U ((3 : ℝ) ^ (2 * (1 / 4 : ℝ))) G := by
    unfold hilbertPrimalCircEnergy
    apply tsum_nonneg
    intro k
    exact mul_nonneg (pow_nonneg (by positivity) _) (hilbertEnergy_nonneg U _)
  rw [hilbertPositiveCircHaarNorm, Real.sq_sqrt hcircNonneg]
  have hcirc : hilbertPrimalCircEnergy U ((3 : ℝ) ^ (2 * (1 / 4 : ℝ))) G =
      hilbertPrimalEnergy U (Real.sqrt 3) G -
        hilbertEnergy U (hilbertCubeIncrement U 0 G) := by
    rw [hq]
    simp only [hilbertPrimalEnergy, hilbertPrimalCircEnergy]
    ring
  rw [hcirc, hraw, hroot0]
  simp only [vectorPositiveHaarEnergy]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact old_signed_primal_sub_mean U (Real.sqrt 3) (fun x => F x j) (hcoord j)

/-- Finite-rank one-load inputs for the actual q3 mode family: `Ω² ≤ v/2` and
`δ² ≤ δₙ² v` with `v = h² 3^{2γk}`. -/
theorem lambda8_mode_family_inputs
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (e : Vec 2) (he : Book.Ch02.vecNorm e = 1) (k : ℤ)
    (S : Finset whiteBasisIndex) :
    let Q : TriadicCube 2 := originCube 2 (k + 128)
    let u : whiteBasisIndex → H10Function (openCubeSet Q) :=
      fun n => lambda8Q3ParentModePotential M h e k n
    (∑ n ∈ S, volumeAverage (openCubeSet Q)
        (fun x => vecNormSq ((u n).toH1Function.grad x))) ≤
      (1 / 2 : ℝ) * (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) ∧
    (∑ n ∈ S, oldSignedCellAverage Q 134 (fun U =>
        vectorPositiveHaarEnergy U.val
          (fun x j => (u n).toH1Function.grad x j -
            cubeAverage U.val (fun y => (u n).toH1Function.grad y j)))) ≤
      lambda8DeltaN ^ 2 * (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) := by
  classical
  intro Q u
  constructor
  · have hmodes := lambda8_mode_energy_sum_le M h hM e he k
    have hvolpos : 0 < (volume (openCubeSet Q)).toReal :=
      volume_openCubeSet_originCube_toReal_pos (d := 2) (k + 128)
    have hnorm (n : whiteBasisIndex) :
        ‖(u n).toH1Function.gradToHilbertVectorL2‖ ^ 2 =
          ∫ x in openCubeSet Q, vecNormSq ((u n).toH1Function.grad x) := by
      rw [← real_inner_self_eq_norm_sq]
      exact inner_toHilbertVectorL2OfVecField_eq_integral _ _
    have havg (n : whiteBasisIndex) :
        volumeAverage (openCubeSet Q) (fun x => vecNormSq ((u n).toH1Function.grad x)) =
          (volume (openCubeSet Q)).toReal⁻¹ *
            ‖(u n).toH1Function.gradToHilbertVectorL2‖ ^ 2 := by
      rw [hnorm]
      rfl
    simp_rw [havg]
    rw [← Finset.mul_sum]
    calc _ ≤ (volume (openCubeSet Q)).toReal⁻¹ *
          ∑' n, ‖(u n).toH1Function.gradToHilbertVectorL2‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hvolpos.le)
          exact hmodes.1.sum_le_tsum S (fun n _ => sq_nonneg _)
      _ ≤ (volume (openCubeSet Q)).toReal⁻¹ * ((volume (openCubeSet Q)).toReal *
          ((h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) / 2)) :=
          mul_le_mul_of_nonneg_left hmodes.2 (inv_nonneg.mpr hvolpos.le)
      _ = _ := by
        rw [← mul_assoc, inv_mul_cancel₀ hvolpos.ne', one_mul]
        ring
  · have hosc := lambda8Q3_one_load_delta_sq_le M h e he k
    have hcell (n : whiteBasisIndex) :
        oldSignedCellAverage Q 134 (fun U =>
          vectorPositiveHaarEnergy U.val
            (fun x j => (u n).toH1Function.grad x j -
              cubeAverage U.val (fun y => (u n).toH1Function.grad y j))) =
        lambda8Q3ParentModeOscillation M h e k n := by
      unfold lambda8Q3ParentModeOscillation
      rw [← old_signed_cell_average_eq_descendantsAverage]
      unfold oldSignedCellAverage
      congr 1
      apply Finset.sum_congr rfl
      intro U _
      have hadm := (smooth_feedback_h2_projected_source_admissible Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property) (u n)
        (lambda8Q3GaussianModeParentHessian Q (q3ModelAmplitude M h k)
          (q3ModelLength k) (-(matVecMul ASDExplicitGamma.Response.responsePlanarJ e)) n)).1
      exact vector_positive_centered_eq_hilbert_circ U.val _ hadm
    simp_rw [hcell]
    have hnn (n : whiteBasisIndex) : 0 ≤ lambda8Q3ParentModeOscillation M h e k n := by
      unfold lambda8Q3ParentModeOscillation descendantsAverage
      positivity
    calc _ ≤ ∑' n, lambda8Q3ParentModeOscillation M h e k n :=
          hosc.1.sum_le_tsum S (fun n _ => hnn n)
      _ ≤ _ := hosc.2


end

end ASDExplicitGamma.Scalar
