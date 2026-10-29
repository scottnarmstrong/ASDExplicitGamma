/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.SmoothFeedbackActualCellBounds
public import ASDExplicitGamma.Scalar.SmoothFeedbackGapMeasurable

/-! The crude pathwise bound `Gap ≤ 2 (E_lift + 𝓑 (Ω² + δ²))` for the actual
OLD maximizers, and the actual lift energy `E_lift`. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native ASDExplicitGamma.Main
open Algsuperdiff.Section3
open scoped BigOperators ENNReal
attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

section Defs

variable {ι : Type*} (S : Finset ι) (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
  (depth : ℕ) (u : ι → H10Function (openCubeSet Q))

/-- `E_lift = Σ_l ‖Z_lift,l‖²_{A,Q}` in its cell form: the average of the cell
energies of the residuals of the actual top loads. -/
def elift (ω : Cutoff.CutoffSample 2) : ℝ := ∑ i ∈ S,
  oldSignedCellAverage Q depth (fun U =>
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
        (oldCutoffSkewCoefficient m Q ω) (topLoad Q u i) (topLoad_memL2 Q u i)))

end Defs

section Bounds

variable {ι : Type*} (S : Finset ι) (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
  (depth : ℕ) (u : ι → H10Function (openCubeSet Q))

/-- The bottom-patch energy of the actual loads is paid by the inverse-history
maximum `𝓑` and the load size. -/
theorem actual_bottom_patch_le
    (H : ∀ i, HasWeakHessianOn (openCubeSet Q) (u i).toH1Function)
    (ω : Cutoff.CutoffSample 2) :
    (∑ i ∈ S, oldSignedCellAverage Q depth (fun U =>
      let hU := openCubeSet_subset_of_mem_descendantsAtDepth U.property
      let kU := oldSignedCellCoefficient Q U.val hU (oldCutoffSkewCoefficient m Q ω)
      let YB := scalarResidualField U.val M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
        (Annealed.sigmaBar M m).property kU
        (toHilbertBlockL2OfBlockField (upper_cell_reset_bottom_load_memL2 U.val
          (smooth_feedback_h2_projected_source_admissible Q U.val hU (u i) (H i)).2.1.memLp))
      oldSignedEnergyPairing U.val M.nu (Annealed.sigmaBar M m : ℝ) kU YB YB)) ≤
      bhist M m Q depth ω * (omega2 S Q u + deltaSq' S Q depth u) := by
  classical
  have hB0 : 0 ≤ bhist M m Q depth ω :=
    smooth_feedback_source_history_maximum_nonneg Q depth M.nu
      (Annealed.sigmaBar M m : ℝ) _
  have hcell (i : ι) (U : OldSignedCellIndex Q depth) :
      (let hU := openCubeSet_subset_of_mem_descendantsAtDepth U.property
       let kU := oldSignedCellCoefficient Q U.val hU (oldCutoffSkewCoefficient m Q ω)
       let YB := scalarResidualField U.val M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
         (Annealed.sigmaBar M m).property kU
         (toHilbertBlockL2OfBlockField (upper_cell_reset_bottom_load_memL2 U.val
           (smooth_feedback_h2_projected_source_admissible Q U.val hU (u i) (H i)).2.1.memLp))
       oldSignedEnergyPairing U.val M.nu (Annealed.sigmaBar M m : ℝ) kU YB YB) ≤
      bhist M m Q depth ω * (vecNormSq (fun j => cubeAverage U.val
          (fun x => (u i).toH1Function.grad x j)) +
        vectorPositiveHaarEnergy U.val (fun x j => (u i).toH1Function.grad x j -
          cubeAverage U.val (fun y => (u i).toH1Function.grad y j))) := by
    dsimp only
    have hU := openCubeSet_subset_of_mem_descendantsAtDepth U.property
    have hadm := smooth_feedback_h2_projected_source_admissible Q U.val hU (u i) (H i)
    have h1 := cell_bottom_energy_le M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
      (Annealed.sigmaBar M m).property Q U.val hU (oldCutoffSkewCoefficient m Q ω)
      (fun x j => (u i).toH1Function.grad x j) hadm.1
    have h2 := smooth_feedback_source_history_maximum_member_le Q depth M.nu
      (Annealed.sigmaBar M m : ℝ) (oldCutoffSkewCoefficient m Q ω) U.val U.property
    have h3 := vectorPositive_split U.val (fun x j => (u i).toH1Function.grad x j) hadm.1
    have h4 := vectorPositiveHaarEnergy_nonneg U.val (fun x j => (u i).toH1Function.grad x j)
    refine le_trans h1 ?_
    rw [h3] at h4 ⊢
    exact mul_le_mul h2 le_rfl h4 hB0
  have hsum (i : ι) :
      oldSignedCellAverage Q depth (fun U =>
        let hU := openCubeSet_subset_of_mem_descendantsAtDepth U.property
        let kU := oldSignedCellCoefficient Q U.val hU (oldCutoffSkewCoefficient m Q ω)
        let YB := scalarResidualField U.val M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
          (Annealed.sigmaBar M m).property kU
          (toHilbertBlockL2OfBlockField (upper_cell_reset_bottom_load_memL2 U.val
            (smooth_feedback_h2_projected_source_admissible Q U.val hU (u i)
              (H i)).2.1.memLp))
        oldSignedEnergyPairing U.val M.nu (Annealed.sigmaBar M m : ℝ) kU YB YB) ≤
      bhist M m Q depth ω * (volumeAverage (openCubeSet Q)
          (fun x => vecNormSq ((u i).toH1Function.grad x)) +
        oldSignedCellAverage Q depth (fun U => vectorPositiveHaarEnergy U.val
          (fun x j => (u i).toH1Function.grad x j -
            cubeAverage U.val (fun y => (u i).toH1Function.grad y j)))) := by
    refine (old_signed_cell_average_mono Q depth (hcell i)).trans ?_
    have hmean := cellMeanSq_le Q depth (fun x => (u i).toH1Function.grad x)
      (u i).toH1Function.grad_memVectorL2
    have hadd := old_signed_cell_average_add Q depth
      (fun U => vecNormSq (fun j => cubeAverage U.val (fun x => (u i).toH1Function.grad x j)))
      (fun U => vectorPositiveHaarEnergy U.val (fun x j => (u i).toH1Function.grad x j -
        cubeAverage U.val (fun y => (u i).toH1Function.grad y j)))
    have hmul := old_signed_cell_average_mul Q depth (bhist M m Q depth ω)
      (fun U => vecNormSq (fun j => cubeAverage U.val (fun x => (u i).toH1Function.grad x j)) +
        vectorPositiveHaarEnergy U.val (fun x j => (u i).toH1Function.grad x j -
          cubeAverage U.val (fun y => (u i).toH1Function.grad y j)))
    refine le_trans (le_of_eq hmul) ?_
    rw [hadd]
    exact mul_le_mul_of_nonneg_left (add_le_add_left hmean _) hB0
  refine (Finset.sum_le_sum fun i _ => hsum i).trans (le_of_eq ?_)
  unfold omega2 deltaSq'
  rw [← Finset.mul_sum, ← Finset.sum_add_distrib]

/-- The gap is at most twice the lift energy plus twice the bottom patch energy. -/
theorem actual_gap_le_two
    (H : ∀ i, HasWeakHessianOn (openCubeSet Q) (u i).toH1Function)
    (Z : Cutoff.CutoffSample 2 → ι → Vec 2 → BlockVec 2)
    (hZ : ∀ ω i, IsScalarOldMaximizer Q M.nu (Annealed.sigmaBar M m : ℝ)
      (oldCutoffSkewCoefficient m Q ω) (fun x => (u i).toH1Function.grad x) (Z ω i))
    (ω : Cutoff.CutoffSample 2) :
    gap' S M m Q depth u Z ω ≤ 2 * (elift S M m Q depth u ω +
      bhist M m Q depth ω * (omega2 S Q u + deltaSq' S Q depth u)) := by
  classical
  have hσ : 0 < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).property
  set σ : ℝ := (Annealed.sigmaBar M m : ℝ) with hσdef
  set k := oldCutoffSkewCoefficient m Q ω with hk
  let Ytop : ι → Vec 2 → BlockVec 2 := fun i => oldSignedLocalResidual Q depth M.nu σ M.nu_pos
    (Annealed.sigmaBar M m).property k (topLoad Q u i) (topLoad_memL2 Q u i)
  let Ybot : ι → Vec 2 → BlockVec 2 := fun i => oldSignedLocalResidual Q depth M.nu σ M.nu_pos
    (Annealed.sigmaBar M m).property k
    (scalarBottomLoad (fun x => (u i).toH1Function.grad x))
    (scalar_bottom_load_memL2 (u i).toH1Function.grad_memVectorL2)
  have hper (i : ι) : scalarFieldEnergy M.nu σ k (Z ω i - Ytop i) ≤
      2 * scalarFieldEnergy M.nu σ k (Ybot i) + 2 * scalarFieldEnergy M.nu σ k (Ytop i) := by
    have h1 := scalarFieldEnergy_sub_le Q M.nu σ M.nu_pos hσ k (hZ ω i).1.1
      (old_signed_local_residual_memLp Q depth M.nu σ M.nu_pos hσ k (topLoad Q u i)
        (topLoad_memL2 Q u i))
    have h2 := smooth_feedback_actual_bottom_local_dual_bound Q depth M.nu σ
      M.nu_pos hσ k (fun x => (u i).toH1Function.grad x) (u i).toH1Function.grad_memVectorL2
      (Z ω i) (hZ ω i)
    change scalarFieldEnergy M.nu σ k (Z ω i - Ytop i) ≤ _ at h1
    change scalarFieldEnergy M.nu σ k (Z ω i) ≤ scalarFieldEnergy M.nu σ k (Ybot i) at h2
    linarith
  have hTop : (∑ i ∈ S, scalarFieldEnergy M.nu σ k (Ytop i)) = elift S M m Q depth u ω := by
    unfold elift
    apply Finset.sum_congr rfl
    intro i _
    rw [scalarFieldEnergy_eq_pairing' Q M.nu σ M.nu_pos hσ k]
    exact old_signed_local_residual_cell_pairing Q depth M.nu σ M.nu_pos hσ k
      (topLoad Q u i) (topLoad Q u i) (topLoad_memL2 Q u i) (topLoad_memL2 Q u i)
  have hBot := actual_bottom_patch_le S M m Q depth u H ω
  have hBotEq : (∑ i ∈ S, scalarFieldEnergy M.nu σ k (Ybot i)) =
      ∑ i ∈ S, oldSignedCellAverage Q depth (fun U =>
      let hU := openCubeSet_subset_of_mem_descendantsAtDepth U.property
      let kU := oldSignedCellCoefficient Q U.val hU (oldCutoffSkewCoefficient m Q ω)
      let YB := scalarResidualField U.val M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
        (Annealed.sigmaBar M m).property kU
        (toHilbertBlockL2OfBlockField (upper_cell_reset_bottom_load_memL2 U.val
          (smooth_feedback_h2_projected_source_admissible Q U.val hU (u i) (H i)).2.1.memLp))
      oldSignedEnergyPairing U.val M.nu (Annealed.sigmaBar M m : ℝ) kU YB YB) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [scalarFieldEnergy_eq_pairing' Q M.nu σ M.nu_pos hσ k]
    exact old_signed_local_residual_cell_pairing Q depth M.nu σ M.nu_pos hσ k
      (scalarBottomLoad (fun x => (u i).toH1Function.grad x))
      (scalarBottomLoad (fun x => (u i).toH1Function.grad x))
      (scalar_bottom_load_memL2 (u i).toH1Function.grad_memVectorL2)
      (scalar_bottom_load_memL2 (u i).toH1Function.grad_memVectorL2)
  have hsum := Finset.sum_le_sum (s := S) (fun i _ => hper i)
  have hGap : gap' S M m Q depth u Z ω =
      ∑ i ∈ S, scalarFieldEnergy M.nu σ k (Z ω i - Ytop i) := rfl
  rw [hGap]
  refine hsum.trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hTop, hBotEq]
  linarith

end Bounds

end

end ASDExplicitGamma.Scalar
