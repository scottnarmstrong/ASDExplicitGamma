module

public import ASDExplicitGamma.Main.FlatFieldSourceCaps
public import ASDExplicitGamma.Triadic.HilbertHaarCellGeometry
public import ASDExplicitGamma.Triadic.HilbertPoincareNorms
public import ASDExplicitGamma.Main.EOscillationCellFamily
public import ASDExplicitGamma.Native.OldSignedActualCellPotentials
public import ASDExplicitGamma.Native.OldSignedFlatBlockFields
public import ASDExplicitGamma.Scalar.FlatSourceHaarLimit
public import ASDExplicitGamma.Scalar.FlatSourceQ3PositiveHaar
public import ASDExplicitGamma.Main.HilbertFiniteCoordinates
public import ASDExplicitGamma.Native.OldSignedPlusFirstBudget
public import ASDExplicitGamma.Native.OldSignedMinusFirstBudget
public import ASDExplicitGamma.Variational.LemmaVTiles
public import ASDExplicitGamma.Native.OldSignedFlatBounds
public import ASDExplicitGamma.Variational.LemmaVHaar
public import ASDExplicitGamma.Native.OldSignedFlatCellRegularity
public import ASDExplicitGamma.Native.OldSignedCompatibleMeans
public import ASDExplicitGamma.Native.OldSignedPatchMeans
public import ASDExplicitGamma.Native.OldSignedFlatProfiles

/-! Parent caps for the actual centered OLD flat-source row. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Native
open scoped BigOperators

noncomputable section

private theorem main_hilbertGradientEnergy_descendantsAverage'
    (Q : TriadicCube 2) (depth : ℕ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (u : HilbertH1Function (openCubeSet Q) E) :
    hilbertGradientEnergy Q u.grad =
      descendantsAverage Q depth (fun U => hilbertGradientEnergy U u.grad) := by
  unfold hilbertGradientEnergy
  calc
    (∑ i, hilbertEnergy Q (fun x => u.grad x i)) =
        ∑ i, descendantsAverage Q depth (fun U => hilbertEnergy U (fun x => u.grad x i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hilbertEnergy_eq_descendantsAverage Q depth
        (u.gradMemL2_normalized Q i)
    _ = descendantsAverage Q depth
        (fun U => ∑ i, hilbertEnergy U (fun x => u.grad x i)) := by
      exact (descendantsAverage_sum Q depth Finset.univ
        (fun U i => hilbertEnergy U (fun x => u.grad x i))).symm

private theorem main_hilbert_cell_circ_square_le_gradient
    (Q : TriadicCube 2) (depth : ℕ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (u : HilbertH1Function (openCubeSet Q) E) :
    descendantsAverage Q depth (fun U =>
      hilbertPositiveCircHaarNorm U ((3 : ℝ) ^ (2 * (1 / 4 : ℝ))) u.toFun ^ 2) ≤
        (cubeScaleFactor Q / (3 : ℝ) ^ depth * planarC0) ^ 2 *
          hilbertGradientEnergy Q u.grad := by
  have hc0 : 0 ≤ planarC0 := Real.sqrt_nonneg _
  have hlocal (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
      hilbertPositiveCircHaarNorm U ((3 : ℝ) ^ (2 * (1 / 4 : ℝ))) u.toFun ^ 2 ≤
        (cubeScaleFactor U * planarC0) ^ 2 * hilbertGradientEnergy U u.grad := by
    let hsub : openCubeSet U ⊆ openCubeSet Q :=
      openCubeSet_subset_of_mem_descendantsAtDepth hU
    let uU := u.restrict hsub (measurableSet_openCubeSet Q)
    have hp := hilbert_positive_circ_poincare_norm U (1 / 4 : ℝ)
      (by constructor <;> norm_num) uU
    rw [haarPoincareC2_quarter, Real.sqrt_sq_eq_abs,
      abs_of_nonneg hc0] at hp
    have hright : 0 ≤ cubeScaleFactor U * planarC0 *
        Real.sqrt (hilbertGradientEnergy U u.grad) :=
      mul_nonneg (mul_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' U).le hc0)
        (Real.sqrt_nonneg _)
    have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) hright).2 hp
    have hgrad : 0 ≤ hilbertGradientEnergy U u.grad := by
      unfold hilbertGradientEnergy
      exact Finset.sum_nonneg fun i _ => hilbertEnergy_nonneg U _
    calc
      _ ≤ (cubeScaleFactor U * planarC0 *
          Real.sqrt (hilbertGradientEnergy U u.grad)) ^ 2 := hsq
      _ = (cubeScaleFactor U * planarC0) ^ 2 *
          hilbertGradientEnergy U u.grad := by
        rw [mul_pow, Real.sq_sqrt hgrad]
  have hscaleSq (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
      (cubeScaleFactor U * planarC0) ^ 2 =
        (cubeScaleFactor Q / (3 : ℝ) ^ depth * planarC0) ^ 2 := by
    rw [cubeScaleFactor_descendant_eq_div_pow hU]
  have havgGrad := main_hilbertGradientEnergy_descendantsAverage' Q depth u
  calc
    _ ≤ descendantsAverage Q depth (fun U =>
        (cubeScaleFactor Q / (3 : ℝ) ^ depth * planarC0) ^ 2 *
          hilbertGradientEnergy U u.grad) := by
      unfold descendantsAverage
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro U hU
      rw [← hscaleSq U hU]
      exact hlocal U hU
    _ = (cubeScaleFactor Q / (3 : ℝ) ^ depth * planarC0) ^ 2 *
        descendantsAverage Q depth (fun U => hilbertGradientEnergy U u.grad) := by
      rw [descendantsAverage_mul_left]
    _ = _ := by rw [← havgGrad]

/-- The normalized average of local quarter-order circ squares is bounded
by the parent gradient energy, with the actual descendant cell scale. -/
theorem main_hilbert_cell_circ_tsum_le_gradient
    {ι E : Type*} [Countable ι] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube 2) (depth : ℕ)
    (F : ι → HilbertH1Function (openCubeSet Q) E)
    (hgrad : Summable (fun n => hilbertGradientEnergy Q (F n).grad)) :
    Summable (fun n => descendantsAverage Q depth (fun U =>
      hilbertPositiveCircHaarNorm U ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
        (F n).toFun ^ 2)) ∧
    (∑' n, descendantsAverage Q depth (fun U =>
      hilbertPositiveCircHaarNorm U ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
        (F n).toFun ^ 2)) ≤
      (cubeScaleFactor Q / (3 : ℝ) ^ depth * planarC0) ^ 2 *
        ∑' n, hilbertGradientEnergy Q (F n).grad := by
  let C := (cubeScaleFactor Q / (3 : ℝ) ^ depth * planarC0) ^ 2
  let D := fun n => descendantsAverage Q depth (fun U =>
    hilbertPositiveCircHaarNorm U ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
      (F n).toFun ^ 2)
  let G := fun n => hilbertGradientEnergy Q (F n).grad
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hDnonneg (n : ι) : 0 ≤ D n := by
    unfold D descendantsAverage
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro U hU
    exact sq_nonneg _
  have hle (n : ι) : D n ≤ C * G n := by
    simpa only [D, C, G] using
      main_hilbert_cell_circ_square_le_gradient Q depth (F n)
  have hbound : Summable (fun n => C * G n) := hgrad.mul_left C
  have hD : Summable D := hbound.of_nonneg_of_le hDnonneg hle
  refine ⟨?_, ?_⟩
  · simpa only [D] using hD
  · calc
      (∑' n, D n) ≤ ∑' n, C * G n := hD.tsum_le_tsum hle hbound
      _ = C * ∑' n, G n := tsum_mul_left
      _ = _ := rfl

end
end ASDExplicitGamma.Main
