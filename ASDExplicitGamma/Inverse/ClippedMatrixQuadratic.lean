module

public import ASDExplicitGamma.Inverse.ResetMean
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Positive clipping and genuine finite-dimensional matrix expectations. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise

/-- Evaluation of a full matrix quadratic form is a continuous linear functional
of the matrix; the load is fixed throughout the expectation. -/
noncomputable def fullMatrixQuadratic (v : BlockCoord 2 → ℝ) : FullBlockMat 2 →L[ℝ] ℝ := by
  let L : FullBlockMat 2 →ₗ[ℝ] ℝ :=
    { toFun := fun A => dotProduct v (A.mulVec v)
      map_add' := by intro A B; simp only [Matrix.add_mulVec, dotProduct_add]
      map_smul' := by intro c A; simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, RingHom.id_apply] }
  exact ⟨L, L.continuous_of_finiteDimensional⟩

/-- An arbitrary measurable positive clipping cannot increase the full matrix
mean, in any direction. The clipping may be correlated with the matrix. -/
theorem clipped_matrix_integral_quadratic_le {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (A : Ω → FullBlockMat 2) (hA : Integrable A mu)
    (hpos : ∀ᵐ ω ∂mu, ∀ v : BlockCoord 2 → ℝ, 0 ≤ fullMatrixQuadratic v (A ω))
    (E : Set Ω) (hE : MeasurableSet E) (v : BlockCoord 2 → ℝ) :
    fullMatrixQuadratic v (∫ ω, E.indicator A ω ∂mu) ≤
      fullMatrixQuadratic v (∫ ω, A ω ∂mu) := by
  calc
    _ = ∫ ω, fullMatrixQuadratic v (E.indicator A ω) ∂mu :=
      ((fullMatrixQuadratic v).integral_comp_comm (hA.indicator hE)).symm
    _ ≤ ∫ ω, fullMatrixQuadratic v (A ω) ∂mu := by
      apply integral_mono_ae ((fullMatrixQuadratic v).integrable_comp (hA.indicator hE))
        ((fullMatrixQuadratic v).integrable_comp hA)
      filter_upwards [hpos] with ω hω
      by_cases hωE : ω ∈ E
      · simp only [Set.indicator_of_mem hωE, le_refl]
      · simp only [Set.indicator_of_notMem hωE]
        exact (le_of_eq (fullMatrixQuadratic v).map_zero).trans (hω v)
    _ = _ := (fullMatrixQuadratic v).integral_comp_comm hA

end ASDExplicitGamma.Inverse
