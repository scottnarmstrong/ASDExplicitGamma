module

public import ASDExplicitGamma.Inverse.WhitneyRootLayerInterior
public import ASDExplicitGamma.Inverse.CompatibleMidpoint

/-! Actual corners of strictly interior triadic cells are nodes of the
compatible DIAG mesh, with all integer and half-cell offsets retained. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney ASDExplicitGamma.Triadic
noncomputable section

/-- One of the four actual closed-cell vertices. -/
def cellCornerVertex (V : TriadicCube 2) (ε : Fin 2 → Fin 2) : Vec 2 :=
  fun d => cubeCorner V d+(ε d).val*cubeScaleFactor V

theorem cell_corner_vertex_closed (V : TriadicCube 2) (ε : Fin 2 → Fin 2) :
    cellCornerVertex V ε ∈ Metric.closedBall (cubeCenter V) (cubeRadius V) := by
  apply mem_closedBall_cubeCenter_iff.mpr
  intro d
  have he0 : (0:ℝ) ≤ (ε d).val := Nat.cast_nonneg _
  have he1 : ((ε d).val:ℝ) ≤ 1 := by exact_mod_cast (show (ε d).val ≤ 1 by have := (ε d).isLt; omega)
  have hs := ASDExplicitGamma.Triadic.cubeScaleFactor_pos' V
  change ((V.index d:ℝ)-1/2)*cubeScaleFactor V ≤
    ((V.index d:ℝ)-1/2)*cubeScaleFactor V+(ε d).val*cubeScaleFactor V ∧
    ((V.index d:ℝ)-1/2)*cubeScaleFactor V+(ε d).val*cubeScaleFactor V ≤
      ((V.index d:ℝ)+1/2)*cubeScaleFactor V
  constructor <;> nlinarith only [he0,he1,hs]

/-- Exact unshifted integer vertex coordinate on the root mesh. -/
def cellCornerPosition (Q V : TriadicCube 2) (j : ℕ) (ε : Fin 2 → Fin 2) (d : Fin 2) : ℤ :=
  V.index d-(3^j:ℤ)*Q.index d+extremeIdx j+(ε d).val

theorem cell_corner_vertex_coordinate (Q : TriadicCube 2) {V : TriadicCube 2} {j : ℕ}
    (hV : V ∈ descendantsAtDepth Q j) (ε : Fin 2 → Fin 2) (d : Fin 2) :
    cellCornerVertex V ε d = cubeCorner Q d+(cellCornerPosition Q V j ε d:ℝ)*diagMeshRadius Q j := by
  have hs := scale_eq_sub_of_mem_descendantsAtDepth hV
  have hside : cubeScaleFactor V = diagMeshRadius Q j := by
    unfold diagMeshRadius cubeScaleFactor
    rw [hs,zpow_sub₀ (by norm_num : (3:ℝ) ≠ 0),zpow_natCast]
  have hroot : cubeScaleFactor Q = (3:ℝ)^j*diagMeshRadius Q j := by
    unfold diagMeshRadius
    field_simp
  have hE := two_mul_extremeIdx_add_one j
  have hER : (extremeIdx j:ℝ) = ((3:ℝ)^j-1)/2 := by
    have he : 2*(extremeIdx j:ℝ)+1 = (3:ℝ)^j := by exact_mod_cast hE
    linarith only [he]
  simp only [cellCornerVertex,cubeCorner,cellCornerPosition,Int.cast_add,Int.cast_sub,
    Int.cast_mul,Int.cast_pow,Int.cast_ofNat,Int.cast_natCast]
  rw [hside,hroot,hER]
  ring

/-- Every actual corner of a strictly interior cell is represented by one
interior DIAG node at the cell's own root generation. -/
theorem cell_corner_interior_node (Q : TriadicCube 2) {V : TriadicCube 2} {j : ℕ}
    (hV : V ∈ descendantsAtDepth Q j)
    (hinterior : Metric.closedBall (cubeCenter V) (cubeRadius V) ⊆ openCubeSet Q)
    (ε : Fin 2 → Fin 2) :
    ∃ z : InteriorNode j, diagInteriorVertex Q j z = cellCornerVertex V ε := by
  let m : Fin 2 → ℤ := cellCornerPosition Q V j ε
  have hm : ∀ d, 0 < m d ∧ m d < (3^j:ℤ) := by
    intro d
    have hx := hinterior (cell_corner_vertex_closed V ε) d
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
