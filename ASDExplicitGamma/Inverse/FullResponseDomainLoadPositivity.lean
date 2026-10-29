module

public import ASDExplicitGamma.Inverse.FullResponseActiveTriangle
public import ASDExplicitGamma.Inverse.HybridFullTraceCongruence
public import ASDExplicitGamma.Inverse.HybridFrameComparison

/-! Actual load positivity with independent coefficient and observation labels. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Multiscale
open ASDExplicitGamma.Triadic ASDExplicitGamma.Response ASDExplicitGamma.Variational

noncomputable section

/-- Actual transformed loads are nonnegative on every observation subdomain
in every scalar frame. The completed coefficient label is independent of
the root scale and of the chosen frame. -/
theorem attenuated_domain_full_trace_cell_load_nonneg
    (M : ABKModel 2) (Q : TriadicCube 2) (T : Book.Ch02.Domain 2)
    (hT : (T : Set (Vec 2)) ⊆ openCubeSet Q)
    (m J : ℤ) (hmJ : m ≤ J) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) (σ : ℝ) (C : Mat 2) (j : Fin 2 × Bool) :
    0 ≤ hybridFullTraceCellLoadEnergy σ
      (coarseBlockMatrix (T : Set (Vec 2)) (attenuatedCoefficient M m J weights ω)) C j := by
  let aQ := sensitivityBookCoeffOn Q M.nu M.nu_pos
    (oldResponseCoefficient Q m ω +
      laterResponseCoefficient Q m J (sourceBandWeights m weights) ω)
  let aT := restrictCoeffOn aQ hT
  let A := coarseBlockMatrix (T : Set (Vec 2)) (attenuatedCoefficient M m J weights ω)
  have hBook : Book.Ch02.coarseBlockMatrix T aT = A :=
    attenuated_domain_matrix_eq M Q m m J le_rfl hmJ weights ω T hT
  have hquad (X : BlockVec 2) : 0 ≤ blockVecDot X (blockMatVecMul A X) := by
    by_cases hX : X = 0
    · rw [hX]
      simp [blockVecDot, blockMatVecMul, vecDot, matVecMul]
    · rw [← hBook]
      exact (Book.Ch02.blockCoarseMatrixTheory T aT).block_matrix_posDef X hX |>.le
  exact hquad _

end
end ASDExplicitGamma.Inverse
