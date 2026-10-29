/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.SmoothFeedbackActualGapBound
public import ASDExplicitGamma.Scalar.SmoothFeedbackGammaMeasurability

/-! Measurability in the OLD sample of the actual smooth-feedback charges. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native ASDExplicitGamma.Main
open Algsuperdiff.Section3
open scoped BigOperators ENNReal
attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

theorem measurable_cellAverage {Ω : Type*} [MeasurableSpace Ω] (Q : TriadicCube 2)
    (depth : ℕ) {f : Ω → OldSignedCellIndex Q depth → ℝ} (h : ∀ U, Measurable (fun ω => f ω U)) :
    Measurable (fun ω => oldSignedCellAverage Q depth (f ω)) := by
  unfold oldSignedCellAverage
  exact (Finset.measurable_sum _ (fun U _ => h U)).const_mul _

theorem cellA_upperLeft_measurable (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2)
    (i j : Fin 2) :
    Measurable (fun ω => (smoothFeedbackCellA M m U ω).upperLeft i j) := by
  change Measurable fun ω => Cold.coldNativeResponse M m U ω (Sum.inl i) (Sum.inl j)
  exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
    (Cold.coldNativeResponse_measurable M m U))

theorem cellA_lowerRight_measurable (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2)
    (i j : Fin 2) :
    Measurable (fun ω => (smoothFeedbackCellA M m U ω).lowerRight i j) := by
  change Measurable fun ω => Cold.coldNativeResponse M m U ω (Sum.inr i) (Sum.inr j)
  exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
    (Cold.coldNativeResponse_measurable M m U))

theorem cellMat_top_quad_measurable (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (depth : ℕ) (U : OldSignedCellIndex Q depth) (w : Vec 2) :
    Measurable (fun ω => blockVecDot ((w, 0) : BlockVec 2)
      (blockMatVecMul (cellMat M m Q depth U ω) (w, 0))) := by
  have : (fun ω => blockVecDot ((w, 0) : BlockVec 2)
      (blockMatVecMul (cellMat M m Q depth U ω) (w, 0))) =
      fun ω => ∑ i, w i * ∑ j, (smoothFeedbackCellA M m U.val ω).upperLeft i j * w j := by
    funext ω
    rw [cellMat_eq_A]
    simp [blockVecDot, blockMatVecMul, vecDot, matVecMul]
  rw [this]
  exact Finset.measurable_sum _ (fun i _ => (Finset.measurable_sum _ (fun j _ =>
    ((cellA_upperLeft_measurable M m U.val i j).mul_const _))).const_mul _)

theorem cellMat_bottom_quad_measurable (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (depth : ℕ) (U : OldSignedCellIndex Q depth) (w : Vec 2) :
    Measurable (fun ω => blockVecDot ((0, w) : BlockVec 2)
      (blockMatVecMul (cellMat M m Q depth U ω) (0, w))) := by
  have : (fun ω => blockVecDot ((0, w) : BlockVec 2)
      (blockMatVecMul (cellMat M m Q depth U ω) (0, w))) =
      fun ω => ∑ i, w i * ∑ j, (smoothFeedbackCellA M m U.val ω).lowerRight i j * w j := by
    funext ω
    rw [cellMat_eq_A]
    simp [blockVecDot, blockMatVecMul, vecDot, matVecMul]
  rw [this]
  exact Finset.measurable_sum _ (fun i _ => (Finset.measurable_sum _ (fun j _ =>
    ((cellA_lowerRight_measurable M m U.val i j).mul_const _))).const_mul _)

section Charges

variable {ι : Type*} (S : Finset ι) (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
  (depth : ℕ) (u : ι → H10Function (openCubeSet Q))

theorem PK_measurable : Measurable (pK' S M m Q depth u) := by
  unfold pK'
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact measurable_cellAverage Q depth (fun U => cellMat_top_quad_measurable M m Q depth U _)

theorem PD_measurable : Measurable (pD S M m Q depth u) := by
  unfold pD
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact measurable_cellAverage Q depth
    (fun U => cellMat_bottom_quad_measurable M m Q depth U _)

theorem Apair_measurable : Measurable (apair S M m Q depth u) := by
  unfold apair
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact measurable_cellAverage Q depth (fun U =>
    ((cellMat_top_quad_measurable M m Q depth U _).add
      (cellMat_bottom_quad_measurable M m Q depth U _)).sub measurable_const)

theorem Theta_measurable : Measurable (theta'' S M m Q depth u) := by
  unfold theta''
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact measurable_cellAverage Q depth (fun U =>
    smooth_feedback_directional_gamma_measurable M m U.val _)

theorem Elift_measurable : Measurable (elift S M m Q depth u) := by
  unfold elift
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact measurable_cellAverage Q depth (fun U =>
    (cell_residual_functionals_measurable m Q U.val
      (openCubeSet_subset_of_mem_descendantsAtDepth U.property) M.nu
      (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).property
      (topLoad Q u i) (topLoad_memL2 Q u i) (fun _ => 0)
      (memLp_const 0)).1)

theorem RK_measurable : Measurable (rK' S M m Q depth u) := by
  unfold rK'
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact measurable_cellAverage Q depth (fun U =>
    (cell_residual_functionals_measurable m Q U.val
      (openCubeSet_subset_of_mem_descendantsAtDepth U.property) M.nu
      (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).property
      (centeredLoad Q u i U.val) (centeredLoad_memL2 Q u i U.val) (fun _ => 0)
      (memLp_const 0)).1)

theorem centeredBottomLoad_memL2 (i : ι) (U : TriadicCube 2) :
    MemBlockL2 (openCubeSet Q) (fun x => ((0 : Vec 2), fun j => (u i).toH1Function.grad x j -
      cellMean Q u i U j)) := by
  have hv : MemVectorL2 (openCubeSet Q) (fun x j => (u i).toH1Function.grad x j -
      cellMean Q u i U j) := by
    have := (u i).toH1Function.grad_memVectorL2.sub (memLp_const (cellMean Q u i U))
    convert this using 1
  exact scalar_bottom_load_memL2 hv

variable
    (hcenter : ∀ i, ∀ U : TriadicCube 2, U ∈ descendantsAtDepth Q depth →
      ScalarPositiveHaarAdmissible U (fun x j =>
        (u i).toH1Function.grad x j -
          cubeAverage U (fun y => (u i).toH1Function.grad y j)))

theorem RD_measurable : Measurable (rD S M m Q depth u hcenter) := by
  unfold rD
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact measurable_cellAverage Q depth (fun U =>
    (cell_residual_functionals_measurable m Q U.val
      (openCubeSet_subset_of_mem_descendantsAtDepth U.property) M.nu
      (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).property
      (fun x => ((0 : Vec 2), fun j => (u i).toH1Function.grad x j - cellMean Q u i U.val j))
      (centeredBottomLoad_memL2 Q u i U.val) (fun _ => 0) (memLp_const 0)).1)

end Charges

end

end ASDExplicitGamma.Scalar
