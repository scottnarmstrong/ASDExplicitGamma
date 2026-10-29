/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.SmoothFeedbackCellHistory
public import ASDExplicitGamma.Scalar.SmoothFeedbackActualQuantities
public import ASDExplicitGamma.Scalar.TopSourceResidualActual
public import ASDExplicitGamma.Scalar.UpperCellEnergyResetBottomResidual
public import ASDExplicitGamma.Native.OldSignedPureSecondSharp
public import ASDExplicitGamma.Native.OldSignedCenteredPositive
public import ASDExplicitGamma.Triadic.Support.ProjectedPoincare.Geometry

/-! Cellwise energy bounds of the actual OLD cell residuals by the cell
histories: top sources by the full-response history `M_U`, bottom sources by
the inverse history. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native ASDExplicitGamma.Main
open Algsuperdiff.Section3
open scoped BigOperators ENNReal

noncomputable section

/-- Positive Haar energies increase with the weight. -/
theorem primalEnergy_mono_base (U : TriadicCube 2) {q q' : ℝ} (hq' : 0 ≤ q') (hqq : q' ≤ q)
    (f : Vec 2 → ℝ)
    (hs : Summable (fun j : ℕ => q ^ (j + 1) * energy U (cubeIncrement U (j + 1) f))) :
    primalEnergy U q' f ≤ primalEnergy U q f := by
  unfold primalEnergy
  apply add_le_add_right
  have hs' : Summable (fun j : ℕ => q' ^ (j + 1) * energy U (cubeIncrement U (j + 1) f)) := by
    refine Summable.of_nonneg_of_le (fun j => mul_nonneg (pow_nonneg hq' _) (energy_nonneg U _))
      (fun j => mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq' hqq _) (energy_nonneg U _)) hs
  exact hs'.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ hq' hqq _) (energy_nonneg U _)) hs

theorem sourceHaarBase_le_sqrt3 : sourceHaarBase ≤ Real.sqrt 3 := by
  unfold sourceHaarBase
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)

theorem posSource_le_vectorPositive (U : TriadicCube 2) (f : Vec 2 → Vec 2)
    (hf : ScalarQuarterHaarAdmissible U f) :
    positiveSourceEnergy U f ≤ vectorPositiveHaarEnergy U f := by
  unfold positiveSourceEnergy vectorPositiveHaarEnergy
  apply Finset.sum_le_sum
  intro i _
  exact primalEnergy_mono_base U (le_of_lt (lt_trans zero_lt_one source_haar_base_gt_one))
    sourceHaarBase_le_sqrt3 _ (hf.increments i)

/-- The complete full-response history of an elliptic coefficient is finite. -/
theorem completeFullHistory_eq_ofReal (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    completeFullResponseHistory Q a = ENNReal.ofReal (oldSignedResponseHistory Q a) := by
  obtain ⟨hsum, heq⟩ := old_signed_response_history_series Q a hEll
  rw [heq]
  unfold completeFullResponseHistory
  have h1 : 0 ≤ 1 - inverseHistoryDiscount :=
    sub_nonneg.mpr inverse_history_discount_range.2.le
  rw [ENNReal.ofReal_mul h1, ENNReal.ofReal_tsum_of_nonneg
    (fun j => mul_nonneg (pow_nonneg inverse_history_discount_range.1.le _)
      (full_response_depth_max_nonneg Q a _)) hsum]

theorem cellResponseHistory_nonneg (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) : 0 ≤ cellResponseHistory M m U ω :=
  ENNReal.toReal_nonneg

theorem cellResponseHistory_ofReal (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) :
    completeFullResponseHistory U (oldCutoffNormalizedCoefficient M m ω) =
      ENNReal.ofReal (cellResponseHistory M m U ω) := by
  rw [← old_cutoff_complete_history_eq M m U ω]
  exact completeFullHistory_eq_ofReal U _
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet U)
      M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).property
      (oldCutoffSkewCoefficient m U ω))

/-- Cellwise energy of the residual of a top source, paid by `M_U`. -/
theorem cell_top_energy_le (M : ABKModel 2) (m : ℤ) (Q U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet Q) (ω : Cutoff.CutoffSample 2)
    (f : Vec 2 → Vec 2) (hf : ScalarPositiveHaarAdmissible U f)
    (hfq : ScalarQuarterHaarAdmissible U f)
    (C : Vec 2 → BlockVec 2) (hC : MemBlockL2 (openCubeSet Q) C)
    (hCf : ∀ x, C x = (f x, 0)) :
    oldSignedEnergyPairing U M.nu (Annealed.sigmaBar M m : ℝ)
        (oldSignedCellCoefficient Q U hU (oldCutoffSkewCoefficient m Q ω))
        (oldSignedCellResidual Q U hU M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
          (Annealed.sigmaBar M m).property (oldCutoffSkewCoefficient m Q ω) C hC)
        (oldSignedCellResidual Q U hU M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
          (Annealed.sigmaBar M m).property (oldCutoffSkewCoefficient m Q ω) C hC) ≤
      cellResponseHistory M m U ω * vectorPositiveHaarEnergy U f := by
  have hCeq : C = fun x => (f x, 0) := funext hCf
  subst hCeq
  have hk := smooth_feedback_cell_coefficient_restrict m Q U hU ω
  have hres : oldSignedCellResidual Q U hU M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
      (Annealed.sigmaBar M m).property (oldCutoffSkewCoefficient m Q ω)
      (fun x => (f x, 0)) hC =
      scalarResidualField U M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
        (Annealed.sigmaBar M m).property (oldCutoffSkewCoefficient m U ω)
        (toHilbertBlockL2OfBlockField (scalar_source_block_memL2 U hf.memLp)) := by
    unfold oldSignedCellResidual
    simp only []
    rw [hk]
  rw [hres, hk]
  have htop := old_cutoff_top_source_residual_actual M m U ω f hf
  rw [cellResponseHistory_ofReal M m U ω] at htop
  have hMU := cellResponseHistory_nonneg M m U ω
  have hpos : 0 ≤ positiveSourceEnergy U f := positive_source_energy_nonneg U f
  rw [← ENNReal.ofReal_mul hMU] at htop
  have hP : oldSignedEnergyPairing U M.nu (Annealed.sigmaBar M m : ℝ)
      (oldCutoffSkewCoefficient m U ω)
      (scalarResidualField U M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
        (Annealed.sigmaBar M m).property (oldCutoffSkewCoefficient m U ω)
        (toHilbertBlockL2OfBlockField (scalar_source_block_memL2 U hf.memLp)))
      (scalarResidualField U M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
        (Annealed.sigmaBar M m).property (oldCutoffSkewCoefficient m U ω)
        (toHilbertBlockL2OfBlockField (scalar_source_block_memL2 U hf.memLp))) =
      cubeAverage U (fun x => blockVecDot
        (scalarResidualField U M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
          (Annealed.sigmaBar M m).property (oldCutoffSkewCoefficient m U ω)
          (toHilbertBlockL2OfBlockField (scalar_source_block_memL2 U hf.memLp)) x)
        (scalarCoefficientFlux
          (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
            (oldCutoffSkewCoefficient m U ω))
          (scalarResidualField U M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
            (Annealed.sigmaBar M m).property (oldCutoffSkewCoefficient m U ω)
            (toHilbertBlockL2OfBlockField (scalar_source_block_memL2 U hf.memLp))) x)) := by
    rw [cube_average_eq_volume_average_open]
    rfl
  rw [hP]
  have hle := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hMU hpos)).mp htop
  exact hle.trans (mul_le_mul_of_nonneg_left (posSource_le_vectorPositive U f hfq) hMU)


/-- Cellwise energy of the residual of a bottom source, paid by the inverse
history of the cell. -/
theorem cell_bottom_energy_le (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (Q U : TriadicCube 2) (hU : openCubeSet U ⊆ openCubeSet Q)
    (k : ResponseCoefficient (openCubeSet Q))
    (g : Vec 2 → Vec 2) (hg : ScalarQuarterHaarAdmissible U g) :
    let kU := oldSignedCellCoefficient Q U hU k
    let R := scalarResidualField U nu sigma hnu hsigma kU
      (toHilbertBlockL2OfBlockField (upper_cell_reset_bottom_load_memL2 U hg.memLp))
    oldSignedEnergyPairing U nu sigma kU R R ≤
      lemmaVInverseHistory U (responseFramePlanarCoefficientField nu sigma kU)
        ((3 : ℝ) ^ (1 / 4 : ℝ)) * vectorPositiveHaarEnergy U g := by
  intro kU R
  have h := old_signed_pure_second_sharp_energy U nu sigma hnu hsigma kU g
    (upper_cell_reset_bottom_load_memL2 U hg.memLp) hg.increments
  have hn := vectorPositiveHaarEnergy_nonneg U g
  change oldSignedEnergyPairing U nu sigma kU R R ≤
    oldSignedInverseHistory U (responseFramePlanarCoefficientField nu sigma kU) *
      vectorPositiveHaarNorm U g ^ 2 at h
  have e : vectorPositiveHaarNorm U g ^ 2 = vectorPositiveHaarEnergy U g := by
    unfold vectorPositiveHaarNorm
    exact Real.sq_sqrt hn
  rw [e] at h
  exact h

/-- Splitting the positive quarter energy into the mean and the oscillation. -/
theorem vectorPositive_split (U : TriadicCube 2) (f : Vec 2 → Vec 2)
    (hf : ScalarQuarterHaarAdmissible U f) :
    vectorPositiveHaarEnergy U f =
      vecNormSq (fun j => cubeAverage U (fun x => f x j)) +
        vectorPositiveHaarEnergy U (fun x j => f x j - cubeAverage U (fun y => f y j)) := by
  have hcoord (j : Fin 2) : MemLp (fun x => f x j) 2 (normalizedCubeMeasure U) :=
    (memLp_pi_iff.mp hf.memLp) j
  unfold vectorPositiveHaarEnergy
  have h1 : (∑ j : Fin 2, primalEnergy U (Real.sqrt 3)
      (fun x => f x j - cubeAverage U (fun y => f y j))) =
      ∑ j : Fin 2, (primalEnergy U (Real.sqrt 3) (fun x => f x j) -
        cubeAverage U (fun x => f x j) ^ 2) := by
    apply Finset.sum_congr rfl
    intro j _
    exact old_signed_primal_sub_mean U (Real.sqrt 3) (fun x => f x j) (hcoord j)
  rw [h1, Finset.sum_sub_distrib]
  simp only [vecNormSq, vecDot, Fin.sum_univ_two]
  simp only [Fin.sum_univ_two] at *
  ring


theorem blockQuad_le_opNorm (U : TriadicCube 2) (a : CoeffField 2) (P : BlockVec 2) :
    blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet U) a) P) ≤
      fullResponseOperatorNorm U a * blockVecDot P P := by
  set A := HilbertBlockVec.applyBlockMat (coarseBlockMatrix (cubeSet U) a) with hA
  have h1 := real_inner_le_norm (HilbertBlockVec.ofBlockVec P) (A (HilbertBlockVec.ofBlockVec P))
  have h2 : ‖A (HilbertBlockVec.ofBlockVec P)‖ ≤ ‖A‖ * ‖HilbertBlockVec.ofBlockVec P‖ :=
    A.le_opNorm _
  have h3 : inner ℝ (HilbertBlockVec.ofBlockVec P) (A (HilbertBlockVec.ofBlockVec P)) =
      blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet U) a) P) := by
    rw [hA]; exact HilbertBlockVec.inner_ofBlockVec_applyBlockMat _ _ _
  have h4 := HilbertBlockVec.norm_sq_ofBlockVec P
  have hn := norm_nonneg (HilbertBlockVec.ofBlockVec P)
  rw [← h3]
  unfold fullResponseOperatorNorm
  calc _ ≤ ‖HilbertBlockVec.ofBlockVec P‖ * ‖A (HilbertBlockVec.ofBlockVec P)‖ := h1
    _ ≤ ‖HilbertBlockVec.ofBlockVec P‖ * (‖A‖ * ‖HilbertBlockVec.ofBlockVec P‖) :=
        mul_le_mul_of_nonneg_left h2 hn
    _ = ‖A‖ * ‖HilbertBlockVec.ofBlockVec P‖ ^ 2 := by ring
    _ = _ := by rw [h4]

theorem opNorm_le_history (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    (1 - inverseHistoryDiscount) * fullResponseOperatorNorm Q a ≤
      oldSignedResponseHistory Q a := by
  obtain ⟨hsum, heq⟩ := old_signed_response_history_series Q a hEll
  rw [heq]
  have h1 : 0 ≤ 1 - inverseHistoryDiscount :=
    sub_nonneg.mpr inverse_history_discount_range.2.le
  apply mul_le_mul_of_nonneg_left _ h1
  have h0 := hsum.le_tsum 0 (fun j _ => mul_nonneg
    (pow_nonneg inverse_history_discount_range.1.le _) (full_response_depth_max_nonneg Q a _))
  have hd : fullResponseOperatorNorm Q a ≤ fullResponseDepthMax Q a 0 :=
    full_response_norm_le_depth_max Q Q a 0 (by simp)
  rw [pow_zero, one_mul] at h0
  exact hd.trans h0


theorem inverseHistoryDiscount_le : inverseHistoryDiscount ≤ 76 / 100 := by
  have h0 := inverse_history_discount_range.1.le
  have h4 : inverseHistoryDiscount ^ 4 = 1 / 3 := by
    unfold inverseHistoryDiscount
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  by_contra h
  push_neg at h
  have : (76 / 100 : ℝ) ^ 4 < inverseHistoryDiscount ^ 4 :=
    pow_lt_pow_left₀ h (by norm_num) (by norm_num)
  rw [h4] at this
  norm_num at this


/-- Averaging the squared cell means is dominated by the squared `L²` norm. -/
theorem cellMeanSq_le (Q : TriadicCube 2) (depth : ℕ) (f : Vec 2 → Vec 2)
    (hf : MemVectorL2 (openCubeSet Q) f) :
    oldSignedCellAverage Q depth (fun U =>
      vecNormSq (fun j => cubeAverage U.val (fun x => f x j))) ≤
      volumeAverage (openCubeSet Q) (fun x => vecNormSq (f x)) := by
  classical
  have hcoord (j : Fin 2) : MemLp (fun x => f x j) 2 (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On (hf.eval j)
  have hsqint (j : Fin 2) : IntegrableOn (fun x => f x j ^ 2) (cubeSet Q) volume :=
    integrableOn_of_integrable_normalizedCubeMeasure Q ((hcoord j).integrable_sq)
  have hpart (j : Fin 2) : cubeAverage Q (fun x => f x j ^ 2) =
      oldSignedCellAverage Q depth (fun U => cubeAverage U.val (fun x => f x j ^ 2)) := by
    rw [cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q depth _ (hsqint j),
      ← old_signed_cell_average_eq_descendantsAverage]
  have hcell (j : Fin 2) (U : OldSignedCellIndex Q depth) :
      (cubeAverage U.val (fun x => f x j)) ^ 2 ≤ cubeAverage U.val (fun x => f x j ^ 2) := by
    have hsub := openCubeSet_subset_of_mem_descendantsAtDepth U.property
    have hU : MemLp (fun x => f x j) 2 (normalizedCubeMeasure U.val) :=
      memLp_normalized_of_memL2On
        (((hf.eval j).mono_measure (Measure.restrict_mono_set volume hsub)))
    exact ASDExplicitGamma.Triadic.Support.ProjectedPoincare.cubeAverage_sq_le U.val hU
  have hsum : oldSignedCellAverage Q depth (fun U =>
      vecNormSq (fun j => cubeAverage U.val (fun x => f x j))) ≤
      ∑ j : Fin 2, cubeAverage Q (fun x => f x j ^ 2) := by
    simp_rw [hpart]
    rw [← old_signed_cell_average_sum]
    apply old_signed_cell_average_mono
    intro U
    have h0 := hcell 0 U
    have h1 := hcell 1 U
    simp only [vecNormSq, vecDot, Fin.sum_univ_two]
    nlinarith [h0, h1]
  refine hsum.trans (le_of_eq ?_)
  rw [← cube_average_eq_volume_average_open]
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
  have hi (j : Fin 2) : Integrable (fun x => f x j ^ 2) (normalizedCubeMeasure Q) :=
    (hcoord j).integrable_sq
  have : (fun x => vecNormSq (f x)) = fun x => f x 0 ^ 2 + f x 1 ^ 2 := by
    funext x
    simp [vecNormSq, vecDot, Fin.sum_univ_two, sq]
  rw [this, integral_add (hi 0) (hi 1), Fin.sum_univ_two]


end

end ASDExplicitGamma.Scalar
