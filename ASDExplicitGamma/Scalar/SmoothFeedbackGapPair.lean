/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.SmoothFeedbackGapFamily
public import ASDExplicitGamma.Scalar.SmoothFeedbackSourcePatchEnergy
public import ASDExplicitGamma.Scalar.SmoothFeedbackJointFeedback

/-! Pathwise `Gap <= G_pair` for the actual OLD cell responses, the actual
global maximizers and a finite family of H² shell loads. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native
open Algsuperdiff.Section3
open scoped BigOperators

noncomputable section

/-- The projection-gap bound `Gap <= G_pair` of the smooth-feedback estimate,
on the literal OLD objects. `Omega` is the actual normalized `L²` size of the
loads; the statement is the source's `G_pair`. -/
theorem smooth_feedback_h2_gap_le_gpair
    {ι : Type*} (S : Finset ι)
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (depth : ℕ)
    (ω : Cutoff.CutoffSample 2)
    (u : ι → H10Function (openCubeSet Q))
    (H : ∀ i, HasWeakHessianOn (openCubeSet Q) (u i).toH1Function)
    (hpos : ∀ i, ∀ U : TriadicCube 2,
      U ∈ descendantsAtDepth Q depth →
        ScalarPositiveHaarAdmissible U (fun x j => (u i).toH1Function.grad x j))
    (hcenter : ∀ i, ∀ U : TriadicCube 2,
      U ∈ descendantsAtDepth Q depth →
        ScalarPositiveHaarAdmissible U (fun x j =>
          (u i).toH1Function.grad x j -
            cubeAverage U (fun y => (u i).toH1Function.grad y j)))
    (Z : ι → Vec 2 → BlockVec 2)
    (hZ : ∀ i, IsScalarOldMaximizer Q M.nu
      (Annealed.sigmaBar M m : ℝ) (oldCutoffSkewCoefficient m Q ω)
      (fun x => (u i).toH1Function.grad x) (Z i)) :
    let σ : ℝ := Annealed.sigmaBar M m
    let k : ResponseCoefficient (openCubeSet Q) := oldCutoffSkewCoefficient m Q ω
    let f : ι → Vec 2 → Vec 2 := fun i x => (u i).toH1Function.grad x
    let F : ι → Vec 2 → BlockVec 2 := fun i x => (f i x, 0)
    let hF : ∀ i, MemBlockL2 (openCubeSet Q) (F i) := fun i =>
      memBlockL2_blockField (u i).toH1Function.grad_memVectorL2 MemLp.zero
    let Y : ι → Vec 2 → BlockVec 2 := fun i =>
      oldSignedLocalResidual Q depth M.nu σ M.nu_pos
        (Annealed.sigmaBar M m).property k (F i) (hF i)
    let Gap : ℝ := ∑ i ∈ S, scalarFieldEnergy M.nu σ k (Z i - Y i)
    let B : ℝ := smoothFeedbackSourceHistoryMaximum Q depth M.nu σ k
    let deltaSq : ℝ := ∑ i ∈ S, oldSignedCellAverage Q depth (fun U =>
      vectorPositiveHaarEnergy U.val
        (fun x j => f i x j - cubeAverage U.val (fun y => f i y j)))
    let Omega : ℝ := Real.sqrt (∑ i ∈ S,
      volumeAverage (openCubeSet Q) (fun x => vecNormSq (f i x)))
    let P_K : ℝ := ∑ i ∈ S, oldSignedCellAverage Q depth (fun U =>
      let mean : Vec 2 := fun j => cubeAverage U.val (fun x => f i x j)
      let P : BlockVec 2 := (mean, 0)
      blockVecDot P (blockMatVecMul
        (coarseBlockMatrix (openCubeSet U.val)
          (responseFramePlanarCoefficientField M.nu σ
            (oldSignedCellCoefficient Q U.val
              (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k))) P))
    let R_K : ℝ := ∑ i ∈ S, oldSignedCellAverage Q depth (fun U =>
      let hU := openCubeSet_subset_of_mem_descendantsAtDepth U.property
      let mean : Vec 2 := fun j => cubeAverage U.val (fun x => f i x j)
      let c : Vec 2 → Vec 2 := fun x j => f i x j - mean j
      let C : Vec 2 → BlockVec 2 := fun x => (c x, 0)
      let hC : MemBlockL2 (openCubeSet Q) C :=
        by
          have hsub : MemLp (fun x => F i x - (mean, 0)) 2
              (volumeMeasureOn (openCubeSet Q)) :=
            (hF i).sub (memLp_const (mean, 0))
          convert hsub using 1
          ext x j
          · simp [C, c, F, f]
          · change (0 : Vec 2) j = (0 - 0 : Vec 2) j
            simp
      oldSignedEnergyPairing U.val M.nu σ
        (oldSignedCellCoefficient Q U.val hU k)
        (oldSignedCellResidual Q U.val hU M.nu σ M.nu_pos
          (Annealed.sigmaBar M m).property k C hC)
        (oldSignedCellResidual Q U.val hU M.nu σ M.nu_pos
          (Annealed.sigmaBar M m).property k C hC))
    let P_D : ℝ := ∑ i ∈ S, oldSignedCellAverage Q depth (fun U =>
      let mean : Vec 2 := fun j => cubeAverage U.val (fun x => f i x j)
      let P : BlockVec 2 := (0, mean)
      blockVecDot P (blockMatVecMul
        (coarseBlockMatrix (openCubeSet U.val)
          (responseFramePlanarCoefficientField M.nu σ
            (oldSignedCellCoefficient Q U.val
              (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k))) P))
    let R_D : ℝ := ∑ i ∈ S, oldSignedCellAverage Q depth (fun U =>
      let hU := openCubeSet_subset_of_mem_descendantsAtDepth U.property
      let hC := upper_cell_reset_bottom_load_memL2 U.val
        (hcenter i U.val U.property).memLp
      let YC := scalarResidualField U.val M.nu σ M.nu_pos
        (Annealed.sigmaBar M m).property
        (oldSignedCellCoefficient Q U.val hU k)
        (toHilbertBlockL2OfBlockField hC)
      oldSignedEnergyPairing U.val M.nu σ
        (oldSignedCellCoefficient Q U.val hU k) YC YC)
    let A_pair : ℝ := ∑ i ∈ S, oldSignedCellAverage Q depth (fun U =>
      let mean : Vec 2 := fun j => cubeAverage U.val (fun x => f i x j)
      let Mat := coarseBlockMatrix (openCubeSet U.val)
        (responseFramePlanarCoefficientField M.nu σ
          (oldSignedCellCoefficient Q U.val
            (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k))
      blockVecDot ((mean, 0) : BlockVec 2) (blockMatVecMul Mat (mean, 0)) +
        blockVecDot ((0, mean) : BlockVec 2) (blockMatVecMul Mat (0, mean)) -
        2 * vecNormSq mean)
    let Ebar : ℝ := (Real.sqrt P_K + Real.sqrt R_K) ^ 2
    Gap ≤ A_pair + 2 * Real.sqrt (P_K * R_K) + R_K +
      2 * Real.sqrt (P_D * R_D) + R_D +
      2 * Real.sqrt deltaSq * (Real.sqrt (B * Ebar) + Omega) := by
  classical
  classical
  intro σ k f F hF Y Gap B deltaSq Omega P_K R_K P_D R_D A_pair Ebar
  have hσ : 0 < σ := (Annealed.sigmaBar M m).property
  have pre := smooth_feedback_h2_family_gap_precomparison S Q depth M.nu σ
    M.nu_pos hσ k u H Z hZ
  have top := smooth_feedback_h2_source_patch_energy_triangle S Q depth M.nu σ
    M.nu_pos hσ k u hpos hcenter
  have bottom := smooth_feedback_h2_family_bottom_patch_energy_triangle S Q depth
    M.nu σ M.nu_pos hσ k u hpos hcenter
  dsimp only at pre top bottom
  -- cell-average identification of the two global load energies
  let Cavg : ι → ℝ := fun i => oldSignedCellAverage Q depth (fun U =>
    vecNormSq (fun j => cubeAverage U.val (fun x => f i x j)))
  let Eavg : ι → ℝ := fun i => oldSignedCellAverage Q depth (fun U =>
    oldSignedEnergyPairing U.val M.nu σ
      (oldSignedCellCoefficient Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)
      (oldSignedCellResidual Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
        M.nu σ M.nu_pos hσ k (F i) (hF i))
      (oldSignedCellResidual Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
        M.nu σ M.nu_pos hσ k (F i) (hF i)))
  let ED : ℝ := ∑ i ∈ S, oldSignedCellAverage Q depth (fun U =>
    let hU := openCubeSet_subset_of_mem_descendantsAtDepth U.property
    let hB := upper_cell_reset_bottom_load_memL2 U.val
      (hpos i U.val U.property).memLp
    let YB := scalarResidualField U.val M.nu σ M.nu_pos hσ
      (oldSignedCellCoefficient Q U.val hU k)
      (toHilbertBlockL2OfBlockField hB)
    oldSignedEnergyPairing U.val M.nu σ
      (oldSignedCellCoefficient Q U.val hU k) YB YB)
  have hTop : (∑ i ∈ S, oldSignedEnergyPairing Q M.nu σ k
      (oldSignedLocalResidual Q depth M.nu σ M.nu_pos hσ k (F i) (hF i))
      (oldSignedLocalResidual Q depth M.nu σ M.nu_pos hσ k (F i) (hF i))) =
      ∑ i ∈ S, Eavg i := by
    apply Finset.sum_congr rfl
    intro i _
    exact old_signed_local_residual_cell_pairing Q depth M.nu σ M.nu_pos hσ k
      (F i) (F i) (hF i) (hF i)
  have hBottom : (∑ i ∈ S, oldSignedEnergyPairing Q M.nu σ k
      (oldSignedLocalResidual Q depth M.nu σ M.nu_pos hσ k
        (scalarBottomLoad (f i))
        (scalar_bottom_load_memL2 (memVectorL2_fst_of_memBlockL2 (hF i))))
      (oldSignedLocalResidual Q depth M.nu σ M.nu_pos hσ k
        (scalarBottomLoad (f i))
        (scalar_bottom_load_memL2 (memVectorL2_fst_of_memBlockL2 (hF i))))) = ED := by
    apply Finset.sum_congr rfl
    intro i _
    exact old_signed_local_residual_cell_pairing Q depth M.nu σ M.nu_pos hσ k
      (scalarBottomLoad (f i)) (scalarBottomLoad (f i))
      (scalar_bottom_load_memL2 (memVectorL2_fst_of_memBlockL2 (hF i)))
      (scalar_bottom_load_memL2 (memVectorL2_fst_of_memBlockL2 (hF i)))
  rw [hTop, hBottom] at pre
  have hB0 : 0 ≤ B := smooth_feedback_source_history_maximum_nonneg Q depth M.nu σ k
  have hcellP (P : BlockVec 2) (U : OldSignedCellIndex Q depth) :
      0 ≤ blockVecDot P (blockMatVecMul
        (coarseBlockMatrix (openCubeSet U.val)
          (responseFramePlanarCoefficientField M.nu σ
            (oldSignedCellCoefficient Q U.val
              (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k))) P) := by
    let hU := openCubeSet_subset_of_mem_descendantsAtDepth U.property
    let kU := oldSignedCellCoefficient Q U.val hU k
    rw [← old_signed_affine_energy U.val M.nu σ M.nu_pos hσ kU P]
    exact old_signed_energy_pairing_nonneg U.val M.nu σ M.nu_pos hσ kU _
  have hPK : 0 ≤ P_K := Finset.sum_nonneg fun i _ =>
    old_signed_cell_average_nonneg Q depth _ fun U => hcellP _ U
  have hPD : 0 ≤ P_D := Finset.sum_nonneg fun i _ =>
    old_signed_cell_average_nonneg Q depth _ fun U => hcellP _ U
  have hRK : 0 ≤ R_K := Finset.sum_nonneg fun i _ =>
    old_signed_cell_average_nonneg Q depth _ fun U =>
      old_signed_energy_pairing_nonneg U.val M.nu σ M.nu_pos hσ _ _
  have hRD : 0 ≤ R_D := Finset.sum_nonneg fun i _ =>
    old_signed_cell_average_nonneg Q depth _ fun U =>
      old_signed_energy_pairing_nonneg U.val M.nu σ M.nu_pos hσ _ _
  have hdelta : 0 ≤ Real.sqrt deltaSq := Real.sqrt_nonneg _
  have hA : A_pair = P_K + P_D - 2 * ∑ i ∈ S, Cavg i := by
    simp only [A_pair, P_K, P_D, Cavg]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← old_signed_cell_average_add, ← old_signed_cell_average_mul,
      ← old_signed_cell_average_sub]
  have hX : (∑ i ∈ S, Eavg i) ≤ Ebar := top
  have hXB : Real.sqrt (B * ∑ i ∈ S, Eavg i) ≤ Real.sqrt (B * Ebar) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hX hB0)
  have hOm : 0 ≤ Omega := Real.sqrt_nonneg _
  have hsK : Real.sqrt (P_K * R_K) = Real.sqrt P_K * Real.sqrt R_K :=
    Real.sqrt_mul hPK R_K
  have hsD : Real.sqrt (P_D * R_D) = Real.sqrt P_D * Real.sqrt R_D :=
    Real.sqrt_mul hPD R_D
  have hEbar : Ebar = P_K + R_K + 2 * (Real.sqrt P_K * Real.sqrt R_K) := by
    simp only [Ebar]
    rw [add_sq, Real.sq_sqrt hPK, Real.sq_sqrt hRK]
    ring
  have hEDb : ED ≤ P_D + R_D + 2 * (Real.sqrt P_D * Real.sqrt R_D) := by
    have := bottom
    rw [add_sq, Real.sq_sqrt hPD, Real.sq_sqrt hRD] at this
    linarith
  have hcross : 2 * Real.sqrt (B * ∑ i ∈ S, Eavg i) * Real.sqrt deltaSq ≤
      2 * Real.sqrt deltaSq * (Real.sqrt (B * Ebar) + Omega) := by
    nlinarith [mul_nonneg hdelta hOm, mul_le_mul_of_nonneg_right hXB hdelta]
  have hpre : Gap ≤ (∑ i ∈ S, Eavg i) - 2 * ∑ i ∈ S, Cavg i + ED +
      2 * Real.sqrt (B * ∑ i ∈ S, Eavg i) * Real.sqrt deltaSq := pre
  rw [hsK, hsD, hA]
  nlinarith [hpre, hX, hEDb, hEbar, hcross]

end

end ASDExplicitGamma.Scalar
