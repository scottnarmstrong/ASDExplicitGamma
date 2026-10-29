module

public import ASDExplicitGamma.Main.FlatFieldH1Bounds
public import ASDExplicitGamma.Triadic.HilbertHaarCellGeometry
public import ASDExplicitGamma.Triadic.HilbertPoincareNorms

/-! Cell variance and broken oscillation consequences of the flat-field H¹ trace. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open scoped BigOperators

noncomputable section

private theorem main_hilbertGradientEnergy_descendantsAverage
    (Q : TriadicCube 2) (j : ℕ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (u : HilbertH1Function (openCubeSet Q) E) :
    hilbertGradientEnergy Q u.grad =
      descendantsAverage Q j (fun U => hilbertGradientEnergy U u.grad) := by
  unfold hilbertGradientEnergy
  calc
    (∑ i, hilbertEnergy Q (fun x => u.grad x i)) =
        ∑ i, descendantsAverage Q j (fun U => hilbertEnergy U (fun x => u.grad x i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hilbertEnergy_eq_descendantsAverage Q j
        (u.gradMemL2_normalized Q i)
    _ = descendantsAverage Q j (fun U => ∑ i, hilbertEnergy U (fun x => u.grad x i)) := by
      exact (descendantsAverage_sum Q j Finset.univ
        (fun U i => hilbertEnergy U (fun x => u.grad x i))).symm

private theorem main_hilbert_cell_variance_le_gradient
    (Q : TriadicCube 2) (j : ℕ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (u : HilbertH1Function (openCubeSet Q) E) :
    descendantsAverage Q j (fun U =>
      hilbertEnergy U (fun x => u.toFun x - hilbertCubeAverage U u.toFun)) ≤
        (cubeScaleFactor Q / (Real.pi * (3 : ℝ)^j))^2 *
          hilbertGradientEnergy Q u.grad := by
  have hpoincare (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q j) :
      hilbertEnergy U (fun x => u.toFun x - hilbertCubeAverage U u.toFun) ≤
        (cubeScaleFactor U / Real.pi)^2 * hilbertGradientEnergy U u.grad := by
    have hsub : openCubeSet U ⊆ openCubeSet Q :=
      openCubeSet_subset_of_mem_descendantsAtDepth hU
    let hu : HilbertH1Function (openCubeSet U) E := {
      toFun := u.toFun
      grad := u.grad
      memL2 := u.memL2.mono_measure (Measure.restrict_mono hsub le_rfl)
      gradMemL2 := fun i => (u.gradMemL2 i).mono_measure
        (Measure.restrict_mono hsub le_rfl)
      hasWeakGradient := fun e => hasWeakGradientOn_mono hsub
        (measurableSet_openCubeSet Q) (u.hasWeakGradient e) }
    have hp := hilbert_cube_poincare U hu
    change hilbertEnergy U (fun x => u.toFun x - hilbertCubeAverage U u.toFun) ≤
      (cubeScaleFactor U / Real.pi)^2 * hilbertGradientEnergy U u.grad at hp
    exact hp
  have hscale : ∀ U ∈ descendantsAtDepth Q j,
      (cubeScaleFactor U / Real.pi)^2 =
        (cubeScaleFactor Q / (Real.pi * (3 : ℝ)^j))^2 := by
    intro U hU
    rw [cubeScaleFactor_descendant_eq_div_pow hU]
    field_simp
  have havg := main_hilbertGradientEnergy_descendantsAverage Q j u
  calc
    _ ≤ descendantsAverage Q j (fun U =>
        (cubeScaleFactor Q / (Real.pi * (3 : ℝ)^j))^2 *
          hilbertGradientEnergy U u.grad) := by
      unfold descendantsAverage
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro U hU
      rw [← hscale U hU]
      exact hpoincare U hU
    _ = (cubeScaleFactor Q / (Real.pi * (3 : ℝ)^j))^2 *
        descendantsAverage Q j (fun U => hilbertGradientEnergy U u.grad) := by
      rw [descendantsAverage_mul_left]
    _ = _ := by rw [← havg]

/-- The normalized sum of cell variances of a Hilbert-valued H¹ field is
controlled by its parent gradient energy with the sharp cell Poincaré factor. -/
theorem main_hilbert_cell_variance_le_gradient_tsum
    (Q : TriadicCube 2) (j : ℕ)
    {ι E : Type*} [Countable ι] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (F : ι → HilbertH1Function (openCubeSet Q) E)
    (hgrad : Summable (fun n => hilbertGradientEnergy Q (F n).grad)) :
    Summable (fun n => descendantsAverage Q j (fun U =>
      hilbertEnergy U (fun x => (F n).toFun x - hilbertCubeAverage U (F n).toFun))) ∧
    (∑' n, descendantsAverage Q j (fun U =>
      hilbertEnergy U (fun x => (F n).toFun x - hilbertCubeAverage U (F n).toFun))) ≤
        (cubeScaleFactor Q / (Real.pi * (3 : ℝ)^j))^2 *
          ∑' n, hilbertGradientEnergy Q (F n).grad := by
  let D := fun n => descendantsAverage Q j (fun U =>
    hilbertEnergy U (fun x => (F n).toFun x - hilbertCubeAverage U (F n).toFun))
  let G := fun n => hilbertGradientEnergy Q (F n).grad
  let C := (cubeScaleFactor Q / (Real.pi * (3 : ℝ)^j))^2
  have hle (n : ι) : D n ≤ C * G n := by
    simpa only [D, G, C] using main_hilbert_cell_variance_le_gradient Q j (F n)
  have hDnonneg (n : ι) : 0 ≤ D n := by
    unfold D descendantsAverage
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro U hU
    exact hilbertEnergy_nonneg U _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound : Summable (fun n => C * G n) := hgrad.mul_left C
  have hD : Summable D := hbound.of_nonneg_of_le hDnonneg hle
  refine ⟨?_, ?_⟩
  · simpa only [D] using hD
  · calc
      (∑' n, D n) ≤ ∑' n, C * G n := hD.tsum_le_tsum hle hbound
      _ = C * ∑' n, G n := tsum_mul_left
      _ = _ := rfl

/-- The source cell variance of the minus flat field, summed over q3 shell
modes and averaged over a triadic tiling. -/
def mainFlatMinusCellVariance (Q : TriadicCube 2) (j : ℕ) (b : ℝ) : ℝ :=
  ∑' n : Gaussian.whiteBasisIndex, descendantsAverage Q j (fun U =>
    hilbertEnergy U (fun x =>
      (mainFlatMinusH1 Q b (mainFlatQ3Length Q) n).toFun x -
        hilbertCubeAverage U (mainFlatMinusH1 Q b (mainFlatQ3Length Q) n).toFun))

/-- The source cell variance of the plus flat field, summed over q3 shell
modes and averaged over a triadic tiling. -/
def mainFlatPlusCellVariance (Q : TriadicCube 2) (j : ℕ) (b : ℝ) : ℝ :=
  ∑' n : Gaussian.whiteBasisIndex, descendantsAverage Q j (fun U =>
    hilbertEnergy U (fun x =>
      (mainFlatPlusH1 Q b (mainFlatQ3Length Q) n).toFun x -
        hilbertCubeAverage U (mainFlatPlusH1 Q b (mainFlatQ3Length Q) n).toFun))

/-- Cell Poincaré transfers the exact minus gradient trace to the source
variance loss, with no mode-summability assumption. -/
theorem mainFlatMinusCellVariance_q3_le (Q : TriadicCube 2) (j : ℕ) (b : ℝ) :
    Summable (fun n : Gaussian.whiteBasisIndex => descendantsAverage Q j (fun U =>
      hilbertEnergy U (fun x =>
        (mainFlatMinusH1 Q b (mainFlatQ3Length Q) n).toFun x -
          hilbertCubeAverage U (mainFlatMinusH1 Q b (mainFlatQ3Length Q) n).toFun))) ∧
    mainFlatMinusCellVariance Q j b ≤
      (cubeScaleFactor Q / (Real.pi * (3 : ℝ)^j))^2 *
        mainFlatSigmaSq b (mainFlatQ3Length Q) := by
  let F := fun n : Gaussian.whiteBasisIndex =>
    mainFlatMinusH1 Q b (mainFlatQ3Length Q) n
  have htrace := mainFlatMinusGradientEnergy_tsum Q b (mainFlatQ3Length Q)
  have hcell := main_hilbert_cell_variance_le_gradient_tsum Q j F htrace.1
  refine ⟨?_, ?_⟩
  · simpa only [F] using hcell.1
  · rw [htrace.2] at hcell
    simpa only [mainFlatMinusCellVariance, F] using hcell.2

/-- Cell Poincaré transfers the certified plus gradient bound to the source
variance loss, with no mode-summability assumption. -/
theorem mainFlatPlusCellVariance_q3_le (Q : TriadicCube 2) (j : ℕ) (b : ℝ) :
    Summable (fun n : Gaussian.whiteBasisIndex => descendantsAverage Q j (fun U =>
      hilbertEnergy U (fun x =>
        (mainFlatPlusH1 Q b (mainFlatQ3Length Q) n).toFun x -
          hilbertCubeAverage U (mainFlatPlusH1 Q b (mainFlatQ3Length Q) n).toFun))) ∧
    mainFlatPlusCellVariance Q j b ≤
      (cubeScaleFactor Q / (Real.pi * (3 : ℝ)^j))^2 *
        ((1 + Real.sqrt 2)^2 * mainFlatSigmaSq b (mainFlatQ3Length Q)) := by
  let F := fun n : Gaussian.whiteBasisIndex =>
    mainFlatPlusH1 Q b (mainFlatQ3Length Q) n
  have htrace := mainFlatPlusGradientEnergy_tsum Q b (mainFlatQ3Length Q)
  have hcell := main_hilbert_cell_variance_le_gradient_tsum Q j F htrace.1
  refine ⟨?_, ?_⟩
  · simpa only [F] using hcell.1
  · calc
      mainFlatPlusCellVariance Q j b ≤
          (cubeScaleFactor Q / (Real.pi * (3 : ℝ)^j))^2 *
            ∑' n : Gaussian.whiteBasisIndex,
              hilbertGradientEnergy Q (mainFlatPlusH1 Q b (mainFlatQ3Length Q) n).grad := by
        simpa only [mainFlatPlusCellVariance, F] using hcell.2
      _ ≤ (cubeScaleFactor Q / (Real.pi * (3 : ℝ)^j))^2 *
          ((1 + Real.sqrt 2)^2 * mainFlatSigmaSq b (mainFlatQ3Length Q)) :=
        mul_le_mul_of_nonneg_left htrace.2 (sq_nonneg _)

/-- The two source cell variance losses are paid by the two sharp H¹ traces. -/
theorem mainFlatCellVariance_q3_le (Q : TriadicCube 2) (j : ℕ) (b : ℝ) :
    mainFlatPlusCellVariance Q j b + mainFlatMinusCellVariance Q j b ≤
      (4 + 2 * Real.sqrt 2) *
        (cubeScaleFactor Q / (Real.pi * (3 : ℝ)^j))^2 *
          mainFlatSigmaSq b (mainFlatQ3Length Q) := by
  have hp := (mainFlatPlusCellVariance_q3_le Q j b).2
  have hm := (mainFlatMinusCellVariance_q3_le Q j b).2
  have hsig : 0 ≤ mainFlatSigmaSq b (mainFlatQ3Length Q) := by
    unfold mainFlatSigmaSq
    positivity
  have hcoef : (1 + Real.sqrt 2)^2 + 1 = 4 + 2 * Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hscale : 0 ≤ (cubeScaleFactor Q / (Real.pi * (3 : ℝ)^j))^2 := sq_nonneg _
  calc
    _ ≤ (cubeScaleFactor Q / (Real.pi * (3 : ℝ)^j))^2 *
          ((1 + Real.sqrt 2)^2 * mainFlatSigmaSq b (mainFlatQ3Length Q)) +
        (cubeScaleFactor Q / (Real.pi * (3 : ℝ)^j))^2 *
          mainFlatSigmaSq b (mainFlatQ3Length Q) := add_le_add hp hm
    _ = (4 + 2 * Real.sqrt 2) *
        (cubeScaleFactor Q / (Real.pi * (3 : ℝ)^j))^2 *
          mainFlatSigmaSq b (mainFlatQ3Length Q) := by
      calc
        _ = (cubeScaleFactor Q / (Real.pi * (3 : ℝ)^j))^2 *
            (((1 + Real.sqrt 2)^2 + 1) * mainFlatSigmaSq b (mainFlatQ3Length Q)) := by ring
        _ = _ := by rw [hcoef]; ring

/-- The cell variance charge is at most the source's coarse-scale constant;
the sharper cell-size factor is retained in `mainFlatCellVariance_q3_le`. -/
theorem mainFlatCellVariance_q3_coarse_le (Q : TriadicCube 2) (j : ℕ) (b : ℝ) :
    mainFlatPlusCellVariance Q j b + mainFlatMinusCellVariance Q j b ≤
      (4 + 2 * Real.sqrt 2) * (cubeScaleFactor Q / Real.pi)^2 *
        mainFlatSigmaSq b (mainFlatQ3Length Q) := by
  have h := mainFlatCellVariance_q3_le Q j b
  have hsig : 0 ≤ mainFlatSigmaSq b (mainFlatQ3Length Q) := by
    unfold mainFlatSigmaSq
    positivity
  have hs : 0 ≤ cubeScaleFactor Q / Real.pi :=
    div_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le Real.pi_pos.le
  have h3 : 1 ≤ (3 : ℝ)^j := one_le_pow₀ (by norm_num : 1 ≤ (3 : ℝ))
  have hR : 0 < cubeScaleFactor Q :=
    ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q
  have hsmall : cubeScaleFactor Q / (Real.pi * (3 : ℝ)^j) ≤ cubeScaleFactor Q / Real.pi := by
    rw [div_le_div_iff₀ (mul_pos Real.pi_pos (by positivity)) Real.pi_pos]
    have hgap : 0 ≤ cubeScaleFactor Q * Real.pi * ((3 : ℝ)^j - 1) :=
      mul_nonneg (mul_nonneg hR.le Real.pi_pos.le) (by linarith [h3])
    nlinarith [hgap]
  have hleft : 0 ≤ cubeScaleFactor Q / (Real.pi * (3 : ℝ)^j) :=
    div_nonneg hR.le (mul_pos Real.pi_pos (by positivity)).le
  have hnonneg : 0 ≤ (4 + 2 * Real.sqrt 2) * mainFlatSigmaSq b (mainFlatQ3Length Q) :=
    mul_nonneg (by positivity) hsig
  have hpow : (cubeScaleFactor Q / (Real.pi * (3 : ℝ)^j))^2 ≤
      (cubeScaleFactor Q / Real.pi)^2 :=
    (sq_le_sq₀ hleft hs).2 hsmall
  have hmul := mul_le_mul_of_nonneg_left hpow hnonneg
  exact h.trans (by simpa [mul_assoc, mul_left_comm, mul_comm] using hmul)

/-- The strict source numeric bound for the summed cell variance loss. -/
theorem mainFlatCellVariance_q3_shell_lt (Q : TriadicCube 2) (j : ℕ) (b : ℝ)
    (hb : b ≠ 0) :
    mainFlatPlusCellVariance Q j b + mainFlatMinusCellVariance Q j b <
      (4 + 2 * Real.sqrt 2) * (31.2 : ℝ) * mainA2 (b^2) / 9 := by
  have h := mainFlatCellVariance_q3_coarse_le Q j b
  have hscale := mainFlatSigmaSq_q3_shell_scale Q b
  have hsigma : 0 ≤ mainFlatSigmaSq b (mainFlatQ3Length Q) := by
    unfold mainFlatSigmaSq
    positivity
  have hc0 : 0 < cubeScaleFactor Q :=
    ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q
  have hA2 : 0 < (31.2 : ℝ) * mainA2 (b^2) := by
    unfold mainA2
    exact mul_pos (by norm_num) (mul_pos (sq_pos_of_ne_zero hb) (by positivity))
  have hsigmaPos : 0 < mainFlatSigmaSq b (mainFlatQ3Length Q) := by
    have hR2 : 0 < cubeScaleFactor Q ^ 2 := sq_pos_of_pos hc0
    nlinarith [hscale, hA2]
  have hpi : (9 : ℝ) < Real.pi^2 := by
    nlinarith [Real.pi_gt_three]
  have hstrict : (cubeScaleFactor Q / Real.pi)^2 *
      mainFlatSigmaSq b (mainFlatQ3Length Q) < (31.2 : ℝ) * mainA2 (b^2) / 9 := by
    calc
      _ = (cubeScaleFactor Q ^ 2 * mainFlatSigmaSq b (mainFlatQ3Length Q)) /
          Real.pi^2 := by rw [div_pow]; ring
      _ = ((31.2 : ℝ) * mainA2 (b^2)) / Real.pi^2 := by rw [hscale]
      _ < ((31.2 : ℝ) * mainA2 (b^2)) / 9 := by
        have hinv : (Real.pi^2)⁻¹ < (9 : ℝ)⁻¹ :=
          (inv_lt_inv₀ (by positivity : 0 < Real.pi^2)
            (by norm_num : (0 : ℝ) < 9)).2 hpi
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_lt_mul_of_pos_left hinv hA2
  have hfactor : 0 < 4 + 2 * Real.sqrt 2 := by positivity
  calc
    _ ≤ (4 + 2 * Real.sqrt 2) *
        (cubeScaleFactor Q / Real.pi)^2 * mainFlatSigmaSq b (mainFlatQ3Length Q) := h
    _ = (4 + 2 * Real.sqrt 2) *
        ((cubeScaleFactor Q / Real.pi)^2 * mainFlatSigmaSq b (mainFlatQ3Length Q)) := by ring
    _ < (4 + 2 * Real.sqrt 2) * ((31.2 : ℝ) * mainA2 (b^2) / 9) :=
      mul_lt_mul_of_pos_left hstrict hfactor
    _ = _ := by ring

end

end ASDExplicitGamma.Main
