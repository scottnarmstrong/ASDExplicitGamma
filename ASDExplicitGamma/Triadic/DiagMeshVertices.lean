module

public import ASDExplicitGamma.Triadic.DiagCells

/-! Exact nodal values on the full closed mesh, including all parent faces. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization
open scoped BigOperators

noncomputable section

/-- Physical vertex in the full source grid. -/
def diagMeshVertex (Q : TriadicCube 2) (j : ℕ) (z : Fin 2 → Fin (3^j+1)) : Vec 2 :=
  fun i => cubeCorner Q i + (z i).val * diagMeshRadius Q j

/-- The exact source nodal rule holds also at boundary vertices. -/
theorem diagInterpolant_at_full_vertex (Q : TriadicCube 2) (j : ℕ)
    (v : H1Function (openCubeSet Q)) (z : Fin 2 → Fin (3^j+1)) :
    (diagInterpolant Q j v).toFun (diagMeshVertex Q j z) =
      (∑ i, diagMeanGradientLinear Q v i * diagMeshVertex Q j z i) +
      diagOddNodalMean (cubeCorner Q) (diagMeshRadius Q j) (3^j)
        (cubeProjection Q j (diagResidualLinear Q v).toFun) z := by
  have hN : 0 < (3:ℕ)^j := pow_pos (by norm_num) j
  by_cases hb : ∃ i, (z i).val = 0 ∨ (z i).val = 3^j
  · obtain ⟨i, hi⟩ := hb
    have hface : diagMeshVertex Q j z i = cubeCorner Q i ∨
        diagMeshVertex Q j z i = cubeCorner Q i + cubeScaleFactor Q := by
      rcases hi with hi | hi
      · left
        simp [diagMeshVertex, hi]
      · right
        simp only [diagMeshVertex, hi, Nat.cast_pow, Nat.cast_ofNat, diagMeshRadius]
        field_simp
    rw [diagInterpolant_face Q j v _ i hface]
    have hz : diagOddNodalMean (cubeCorner Q) (diagMeshRadius Q j) (3^j)
        (cubeProjection Q j (diagResidualLinear Q v).toFun) z = 0 := by
      fin_cases i
      · exact diagOddNodalMean_face0 _ _ hN _ _ hi
      · exact diagOddNodalMean_face1 _ _ hN _ _ hi
    rw [hz, add_zero]
  · have hz (i : Fin 2) : 0 < (z i).val ∧ (z i).val < 3^j := by
      have h := z i |>.isLt
      have hn : ¬ ((z i).val = 0 ∨ (z i).val = 3^j) := fun hi => hb ⟨i, hi⟩
      omega
    let w : Fin 2 → Fin (3^j-1) := fun i => ⟨(z i).val-1, by have := hz i; omega⟩
    have hindex : diagInteriorVertexIndex j w = z := by
      funext i
      apply Fin.ext
      change (z i).val-1+1 = (z i).val
      have := hz i
      omega
    have hvertex : diagInteriorVertex Q j w = diagMeshVertex Q j z := by
      funext i
      have hval : (w i).val + 1 = (z i).val := congrArg Fin.val (congrFun hindex i)
      unfold diagInteriorVertex diagMeshVertex
      rw [← Nat.cast_one (R := ℝ), ← Nat.cast_add, hval]
    simpa only [hvertex, hindex] using diagInterpolant_at_vertex Q j v w

end

end ASDExplicitGamma.Triadic
