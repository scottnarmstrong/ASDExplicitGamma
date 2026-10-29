module

public import ASDExplicitGamma.Inverse.StoppedCellMeshVertices

/-! Interior vertices of root-mesh cells are actual DIAG nodes even when
the cell itself is adjacent to the root boundary. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney ASDExplicitGamma.Triadic
noncomputable section

theorem cell_corner_node_of_mem_open (Q : TriadicCube 2) {V : TriadicCube 2} {j : ℕ}
    (hV : V ∈ descendantsAtDepth Q j)
    (ε : Fin 2 → Fin 2) (hinterior : cellCornerVertex V ε ∈ openCubeSet Q) :
    ∃ z : InteriorNode j, diagInteriorVertex Q j z = cellCornerVertex V ε := by
  let m : Fin 2 → ℤ := cellCornerPosition Q V j ε
  have hm : ∀ d, 0 < m d ∧ m d < (3^j:ℤ) := by
    intro d
    have hx := hinterior d
    rw [show ((Q.index d:ℝ)+1/2)*cubeScaleFactor Q =
      cubeCorner Q d+cubeScaleFactor Q by unfold cubeCorner; ring] at hx
    change cubeCorner Q d < cellCornerVertex V ε d ∧
      cellCornerVertex V ε d < cubeCorner Q d+cubeScaleFactor Q at hx
    rw [cell_corner_vertex_coordinate Q hV ε d] at hx
    have hmesh := diagMeshRadius_pos Q j
    have hroot : cubeScaleFactor Q = (3:ℝ)^j*diagMeshRadius Q j := by
      unfold diagMeshRadius
      field_simp
    have hm0 : (0:ℝ) < m d := by change 0 < (cellCornerPosition Q V j ε d:ℝ); nlinarith only [hx.1,hmesh]
    have hm1 : (m d:ℝ) < (3:ℝ)^j := by
      change (cellCornerPosition Q V j ε d:ℝ) < _
      rw [hroot] at hx
      nlinarith only [hx.2,hmesh]
    exact ⟨by exact_mod_cast hm0,by exact_mod_cast hm1⟩
  let z : InteriorNode j := fun d => ⟨(m d).toNat-1,by
    have hd := hm d
    have he := Int.toNat_of_nonneg (show 0 ≤ m d by omega)
    have hpow : ((3^j:ℕ):ℤ) = 3^j := by norm_cast
    omega⟩
  refine ⟨z,?_⟩
  funext d
  rw [cell_corner_vertex_coordinate Q hV ε d]
  have hd := hm d
  have he := Int.toNat_of_nonneg (show 0 ≤ m d by omega)
  have hz : ((z d).val:ℝ)+1 = (m d:ℝ) := by
    have he' : ((z d).val:ℤ)+1 = m d := by dsimp only [z]; omega
    exact_mod_cast he'
  exact congrArg (fun t : ℝ => cubeCorner Q d+t*diagMeshRadius Q j) hz

end
end ASDExplicitGamma.Inverse
