module

public import ASDExplicitGamma.Triadic.DiagNodalPeriod

/-! The concrete source nodal functional is the doubled-period cell average. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization
open scoped BigOperators Fin.CommRing

noncomputable section

/-- Each folded periodic neighbor is the actual cell sampled by DIAG. -/
theorem diagSourceMean_period_neighbor (Q : TriadicCube 2) (j : ℕ)
    (v : H1Function (openCubeSet Q)) (z : Fin 2 → Fin (3^j+1)) (b : Fin 2 → Fin 2) :
    let instPeriodNonzero : NeZero (2*3^j) := ⟨by positivity⟩
    cubeProjection Q j v.toFun (diagNeighborCenter (cubeCorner Q) (diagMeshRadius Q j) (3^j) z b) =
      diagSourceMeans Q j v (fun i => diagReflectIndex (3^j) (diagNodalPeriodIndex (z i) (b i))) := by
  intro instPeriodNonzero
  obtain ⟨R, hR, hx, _, havg⟩ := diagNeighborCenter_cellMean Q j z b
  rw [havg]
  let k : Fin 2 → Fin (3^j) := fun i => diagReflectIndex (3^j) (diagNodalPeriodIndex (z i) (b i))
  have heq : R = diagMeshCell Q j k := by
    apply diagCube_eq_of_scale_corner
    · rw [scale_eq_sub_of_mem_descendantsAtDepth hR,
        scale_eq_sub_of_mem_descendantsAtDepth (diagMeshCell_mem Q j k)]
    · intro i
      rw [diagNeighborCenter_cell_corner Q j z b hR hx, diagMeshCell_corner]
      dsimp only [k]
      rw [diagNodalPeriodIndex_fold (pow_pos (by norm_num) j)]
  rw [heq]
  rfl

/-- The four signed source cell means are exactly the periodic nodal average. -/
theorem diagOddNodalMean_eq_period (Q : TriadicCube 2) (j : ℕ)
    (v : H1Function (openCubeSet Q)) (z : Fin 2 → Fin (3^j+1)) :
    let N := 3^j
    let instPeriodNonzero : NeZero (2*N) := ⟨by positivity⟩
    diagOddNodalMean (cubeCorner Q) (diagMeshRadius Q j) N (cubeProjection Q j v.toFun) z =
      (∑ b0 : Fin 2, ∑ b1 : Fin 2,
        diagOddGrid N (diagSourceMeans Q j v)
          (fun i => diagNodalPeriodIndex (z i) (![b0,b1] i))) / 4 := by
  intro N instPeriodNonzero
  unfold diagOddNodalMean
  congr 1
  apply Finset.sum_congr rfl
  intro b0 _
  apply Finset.sum_congr rfl
  intro b1 _
  rw [diagSourceMean_period_neighbor]
  unfold diagOddGrid
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    diagNodalPeriodIndex_sign (N := N) (pow_pos (by norm_num : 0 < (3:ℕ)) j)]
  rfl

end

end ASDExplicitGamma.Triadic
