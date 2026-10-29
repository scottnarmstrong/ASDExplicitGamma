module

public import ASDExplicitGamma.Inverse.AssemblyShearedMean
public import ASDExplicitGamma.Inverse.HybridCells

/-! Positivity removes the actual identity mask from sheared trace layers. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Congruence preserves positivity of the actual clipped full trace. -/
theorem assembly_sheared_clipped_trace_nonneg (M : Algsuperdiff.Section3.ABKModel 2)
    (n : ℤ) (P : TriadicCube 2) (τ : ℝ) (ω : Cutoff.CutoffSample 2) (R : FullBlockMat 2) :
    0 ≤ Matrix.trace (R.transpose*clippedCellMatrix M n P τ ω*R)/4 := by
  have hh := assembly_trace_le_of_quadratic 0 (R.transpose*clippedCellMatrix M n P τ ω*R) 1 (by
    intro v
    rw [fullMatrixQuadratic_congruence,map_zero,one_mul]
    exact clipped_cell_matrix_quadratic_nonneg M n P τ ω (R.mulVec v))
  simpa only [Matrix.trace_zero,zero_div,one_mul] using hh

/-- Every stopped untouched-cell trace is enlarged to the full deterministic
sheared matrix layer before any mean or probability bound is applied. -/
theorem assembly_identity_trace_sum_le_layers (M : Algsuperdiff.Section3.ABKModel 2)
    (Q : TriadicCube 2) (H : ℕ) (S : Set (TriadicCube 2)) (N : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) :
    (∑' i : HybridIdentityCell Q H S, ENNReal.ofReal
      (w i.val.1*(volume (cubeSet i.val.2.val)).toReal/(volume (cubeSet Q)).toReal*
        (Matrix.trace ((assemblyPhysicalShearMatrix M (i.val.2.val.scale+40) i.val.2.val.scale N
            (((i.val.2.val.index 0:ℝ)-1/2)*(3:ℝ)^i.val.2.val.scale)
            (((i.val.2.val.index 1:ℝ)-1/2)*(3:ℝ)^i.val.2.val.scale) weights ω).transpose*
          clippedCellMatrix M (i.val.2.val.scale+40) i.val.2.val resetAllOrderTau ω*
            assemblyPhysicalShearMatrix M (i.val.2.val.scale+40) i.val.2.val.scale N
            (((i.val.2.val.index 0:ℝ)-1/2)*(3:ℝ)^i.val.2.val.scale)
            (((i.val.2.val.index 1:ℝ)-1/2)*(3:ℝ)^i.val.2.val.scale) weights ω)/4))) ≤
      ∑' n : ℕ, ENNReal.ofReal (w n*assemblyShearedLayerTrace M Q H n N weights ω) := by
  classical
  let R := fun P : TriadicCube 2 => assemblyPhysicalShearMatrix M (P.scale+40) P.scale N
    (((P.index 0:ℝ)-1/2)*(3:ℝ)^P.scale) (((P.index 1:ℝ)-1/2)*(3:ℝ)^P.scale) weights ω
  let t := fun P : TriadicCube 2 => Matrix.trace ((R P).transpose*
    clippedCellMatrix M (P.scale+40) P resetAllOrderTau ω*R P)/4
  let f : WhitneyIndexedCell Q H → ℝ≥0∞ := fun i => ENNReal.ofReal
    (w i.1*(volume (cubeSet i.2.val)).toReal/(volume (cubeSet Q)).toReal*t i.2.val)
  have hcomp := ENNReal.tsum_comp_le_tsum_of_injective
    (Subtype.val_injective : Function.Injective (fun i : HybridIdentityCell Q H S => i.val)) f
  apply hcomp.trans_eq
  change (∑' i : Σ n : ℕ, ↥(whitneyRootLayer Q H n), f i)=_
  rw [ENNReal.tsum_sigma']
  apply tsum_congr
  intro n
  rw [tsum_fintype]
  have hsum := Finset.sum_coe_sort (whitneyRootLayer Q H n) (fun P : TriadicCube 2 =>
    ENNReal.ofReal (w n*(volume (cubeSet P)).toReal/(volume (cubeSet Q)).toReal*t P))
  change (∑ P : ↥(whitneyRootLayer Q H n), ENNReal.ofReal
    (w n*(volume (cubeSet P.val)).toReal/(volume (cubeSet Q)).toReal*t P.val))=_
  rw [hsum]
  have hnonneg (P : TriadicCube 2) (_hP : P ∈ whitneyRootLayer Q H n) :
      0 ≤ w n*(volume (cubeSet P)).toReal/(volume (cubeSet Q)).toReal*t P :=
    mul_nonneg (div_nonneg (mul_nonneg (hw n) ENNReal.toReal_nonneg) ENNReal.toReal_nonneg)
      (assembly_sheared_clipped_trace_nonneg M (P.scale+40) P resetAllOrderTau ω (R P))
  rw [← ENNReal.ofReal_sum_of_nonneg hnonneg]
  congr 1
  dsimp only [assemblyShearedLayerTrace,t,R]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  ring

end
end ASDExplicitGamma.Inverse
