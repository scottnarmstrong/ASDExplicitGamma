/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.SmoothFeedbackBank

/-! Pathwise cellwise bounds of the actual smooth-feedback charges by the cell
histories `M_U` and the inverse-history maximum `B`. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native ASDExplicitGamma.Main
open Algsuperdiff.Section3
open scoped BigOperators ENNReal
attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

variable {ι : Type*} (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (depth : ℕ)

theorem cellMat_eq_A (U : OldSignedCellIndex Q depth) (ω : Cutoff.CutoffSample 2) :
    cellMat M m Q depth U ω = smoothFeedbackCellA M m U.val ω :=
  smooth_feedback_cell_coarse_eq_response M m Q U.val
    (openCubeSet_subset_of_mem_descendantsAtDepth U.property) ω

/-- A block quadratic form of the actual cell response is paid by `M_U`. -/
theorem cellMat_quad_le (U : OldSignedCellIndex Q depth) (ω : Cutoff.CutoffSample 2)
    (P : BlockVec 2) :
    blockVecDot P (blockMatVecMul (cellMat M m Q depth U ω) P) ≤
      cellResponseHistory M m U.val ω / (24 / 100) * blockVecDot P P := by
  have hU := openCubeSet_subset_of_mem_descendantsAtDepth U.property
  unfold cellMat
  rw [smooth_feedback_cell_coefficient_restrict m Q U.val hU ω,
    ← Variational.cube_coarseMatrix_eq_open U.val]
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet U.val)
    M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).property
    (oldCutoffSkewCoefficient m U.val ω)
  have h1 := blockQuad_le_opNorm U.val
    (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
      (oldCutoffSkewCoefficient m U.val ω)) P
  have h2 := opNorm_le_history U.val _ hEll
  have hd := inverseHistoryDiscount_le
  have hH := cellResponseHistory_nonneg M m U.val ω
  have hn := full_response_operator_norm_nonneg U.val
    (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
      (oldCutoffSkewCoefficient m U.val ω))
  have hPP : 0 ≤ blockVecDot P P := by
    simp only [blockVecDot, vecDot]
    exact add_nonneg (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
      (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ hPP)
  have h2' : (24 / 100) * fullResponseOperatorNorm U.val
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
        (oldCutoffSkewCoefficient m U.val ω)) ≤ cellResponseHistory M m U.val ω := by
    refine le_trans ?_ h2
    exact mul_le_mul_of_nonneg_right (by linarith) hn
  rw [le_div_iff₀ (by norm_num)]
  linarith

theorem scalarFieldEnergy_eq_pairing' (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F : Vec 2 → BlockVec 2) :
    scalarFieldEnergy nu sigma k F = oldSignedEnergyPairing Q nu sigma k F F := by
  unfold scalarFieldEnergy oldSignedEnergyPairing
  apply congrArg (volumeAverage (openCubeSet Q))
  funext x
  rw [responseFrameEnergyDensity_eq_scaledCoefficientBlock nu sigma
    (responseCoefficientExtension k x) hnu hsigma]
  rfl

/-- Energy parallelogram inequality for the actual OLD frame energy. -/
theorem scalarFieldEnergy_sub_le (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) {Z Y : Vec 2 → BlockVec 2}
    (hZ : MemBlockL2 (openCubeSet Q) Z) (hY : MemBlockL2 (openCubeSet Q) Y) :
    scalarFieldEnergy nu sigma k (Z - Y) ≤
      2 * scalarFieldEnergy nu sigma k Z + 2 * scalarFieldEnergy nu sigma k Y := by
  rw [scalarFieldEnergy_eq_pairing' Q nu sigma hnu hsigma k,
    scalarFieldEnergy_eq_pairing' Q nu sigma hnu hsigma k,
    scalarFieldEnergy_eq_pairing' Q nu sigma hnu hsigma k]
  have hd : MemBlockL2 (openCubeSet Q) (Z - Y) := hZ.sub hY
  have hs : MemBlockL2 (openCubeSet Q) (Z + Y) := hZ.add hY
  have h1 := old_signed_energy_pairing_sub_left Q nu sigma hnu hsigma k hZ hY hd
  have h2 := old_signed_energy_pairing_sub_right Q nu sigma hnu hsigma k hZ hZ hY
  have h3 := old_signed_energy_pairing_sub_right Q nu sigma hnu hsigma k hY hZ hY
  have h4 := old_signed_energy_pairing_add_left Q nu sigma hnu hsigma k hZ hY hs
  have h5 := old_signed_energy_pairing_add_right Q nu sigma hnu hsigma k hZ hZ hY
  have h6 := old_signed_energy_pairing_add_right Q nu sigma hnu hsigma k hY hZ hY
  have hpos := old_signed_energy_pairing_nonneg Q nu sigma hnu hsigma k (Z + Y)
  have hsym := old_signed_energy_pairing_symm Q nu sigma k Y Z
  rw [h4, h5, h6] at hpos
  rw [h1, h2, h3]
  nlinarith [hsym]

end

end ASDExplicitGamma.Scalar
