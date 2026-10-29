module

public import ASDExplicitGamma.Inverse.HybridCells
public import ASDExplicitGamma.Inverse.ClippedMatrixPositiveSums

/-! Whole untouched cells are enlarged to deterministic layers before means. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
noncomputable section

/-- The full countable identity-cell contribution is bounded by complete
deterministic layer sums. Only positivity is used to remove the random mask. -/
theorem hybrid_identity_clipped_sum_le_layers (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (S : Set (TriadicCube 2)) (τ : ℝ) (ω : Cutoff.CutoffSample 2)
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (q : Vec 2) :
    (∑' i : HybridIdentityCell Q H S, ENNReal.ofReal
      (w i.val.1*(volume (cubeSet i.val.2.val)).toReal/(volume (cubeSet Q)).toReal*
        fullMatrixQuadratic (toFullBlockVec (0,q))
          (clippedCellMatrix M (i.val.2.val.scale+40) i.val.2.val τ ω))) ≤
      ∑' n : ℕ, ENNReal.ofReal (∑ P ∈ whitneyRootLayer Q H n,
        w n*(volume (cubeSet P)).toReal/(volume (cubeSet Q)).toReal*
          fullMatrixQuadratic (toFullBlockVec (0,q)) (clippedCellMatrix M (P.scale+40) P τ ω)) := by
  classical
  let f := fun i : WhitneyIndexedCell Q H => ENNReal.ofReal
    (w i.1*(volume (cubeSet i.2.val)).toReal/(volume (cubeSet Q)).toReal*
      fullMatrixQuadratic (toFullBlockVec (0,q)) (clippedCellMatrix M (i.2.val.scale+40) i.2.val τ ω))
  have hh := ENNReal.tsum_comp_le_tsum_of_injective
    (Subtype.val_injective : Function.Injective (fun i : HybridIdentityCell Q H S => i.val)) f
  apply hh.trans_eq
  change (∑' i : Σ n : ℕ, ↥(whitneyRootLayer Q H n), f i)=_
  rw [ENNReal.tsum_sigma']
  apply tsum_congr
  intro n
  rw [tsum_fintype]
  change (∑ P : ↥(whitneyRootLayer Q H n), ENNReal.ofReal
    (w n*(volume (cubeSet P.val)).toReal/(volume (cubeSet Q)).toReal*
      fullMatrixQuadratic (toFullBlockVec (0,q)) (clippedCellMatrix M (P.val.scale+40) P.val τ ω)))=_
  have he := Finset.sum_coe_sort (whitneyRootLayer Q H n) (fun P : TriadicCube 2 =>
    ENNReal.ofReal (w n*(volume (cubeSet P)).toReal/(volume (cubeSet Q)).toReal*
      fullMatrixQuadratic (toFullBlockVec (0,q)) (clippedCellMatrix M (P.scale+40) P τ ω)))
  apply he.trans
  symm
  apply ENNReal.ofReal_sum_of_nonneg
  intro P _
  exact mul_nonneg (div_nonneg (mul_nonneg (hw n) ENNReal.toReal_nonneg) ENNReal.toReal_nonneg)
    (clipped_cell_matrix_quadratic_nonneg M (P.scale+40) P τ ω _)

end
end ASDExplicitGamma.Inverse
