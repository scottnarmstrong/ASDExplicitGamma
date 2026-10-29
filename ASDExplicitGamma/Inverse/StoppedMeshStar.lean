module

public import ASDExplicitGamma.Inverse.StoppedCellMeshVertices
public import ASDExplicitGamma.Inverse.StoppedMeshHatBounds

/-! A nonzero tensor-hat derivative on an interior coarse cell has its node
on that cell's closed realization, provided the common mesh refines the cell. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney ASDExplicitGamma.Triadic
noncomputable section

theorem diag_mesh_radius_refinement (Q : TriadicCube 2) {j J : ℕ} (hj : j ≤ J) :
    diagMeshRadius Q j = (3:ℝ)^(J-j)*diagMeshRadius Q J := by
  have he : (3:ℝ)^J = (3:ℝ)^j*(3:ℝ)^(J-j) := by
    rw [← pow_add]
    congr 1
    omega
  unfold diagMeshRadius
  rw [he]
  field_simp

private theorem integer_mesh_cell (a r x : ℝ) (A B k : ℤ) (hr : 0 < r)
    (hx : a+(A:ℝ)*r < x ∧ x < a+(B:ℝ)*r)
    (hnear : |x-(a+(k:ℝ)*r)| ≤ r) : A ≤ k ∧ k ≤ B := by
  have hn := abs_le.mp hnear
  constructor
  · by_contra hh
    have hgap : (k:ℝ)+1 ≤ A := by exact_mod_cast (show k+1 ≤ A by omega)
    have hm := mul_le_mul_of_nonneg_right hgap hr.le
    nlinarith only [hm,hx.1,hn.2]
  · by_contra hh
    have hgap : (B:ℝ)+1 ≤ k := by exact_mod_cast (show B+1 ≤ k by omega)
    have hm := mul_le_mul_of_nonneg_right hgap hr.le
    nlinarith only [hm,hx.2,hn.1]

/-- The common-mesh closed star of a node can meet an interior coarser cell
only if the node itself lies in that cell's closed realization. -/
theorem common_mesh_star_node_in_cell (Q : TriadicCube 2) {P : TriadicCube 2} {j J : ℕ}
    (hP : P ∈ descendantsAtDepth Q j) (hj : j ≤ J) (z : InteriorNode J)
    {x : Vec 2} (hx : x ∈ openCubeSet P)
    (hnear : ∀ k, |x k-diagInteriorVertex Q J z k| ≤ diagMeshRadius Q J) :
    diagInteriorVertex Q J z ∈ Metric.closedBall (cubeCenter P) (cubeRadius P) := by
  have hscale : cubeScaleFactor P = diagMeshRadius Q j := by
    unfold diagMeshRadius cubeScaleFactor
    rw [scale_eq_sub_of_mem_descendantsAtDepth hP,zpow_sub₀ (by norm_num : (3:ℝ) ≠ 0),zpow_natCast]
  apply mem_closedBall_cubeCenter_iff.mpr
  intro k
  let A : ℤ := cellCornerPosition Q P j (fun _ => 0) k*(3^(J-j):ℤ)
  let B : ℤ := A+(3^(J-j):ℤ)
  let node : ℤ := (z k).val+1
  have hcorner : cubeCorner P k = cubeCorner Q k+(A:ℝ)*diagMeshRadius Q J := by
    have hh := cell_corner_vertex_coordinate Q hP (fun _ => 0) k
    simp only [cellCornerVertex,Fin.val_zero,Nat.cast_zero,zero_mul,add_zero] at hh
    rw [diag_mesh_radius_refinement Q hj] at hh
    simpa only [A,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,mul_assoc] using hh
  have hupper : ((P.index k:ℝ)+1/2)*cubeScaleFactor P =
      cubeCorner Q k+(B:ℝ)*diagMeshRadius Q J := by
    rw [show ((P.index k:ℝ)+1/2)*cubeScaleFactor P = cubeCorner P k+cubeScaleFactor P by unfold cubeCorner; ring,
      hcorner,hscale,diag_mesh_radius_refinement Q hj]
    simp only [B,Int.cast_add,Int.cast_pow,Int.cast_ofNat]
    ring
  have hxk := hx k
  change cubeCorner P k < x k ∧ x k < ((P.index k:ℝ)+1/2)*cubeScaleFactor P at hxk
  rw [hcorner,hupper] at hxk
  have hnode : diagInteriorVertex Q J z k = cubeCorner Q k+(node:ℝ)*diagMeshRadius Q J := by
    simp only [diagInteriorVertex,node,Int.cast_add,Int.cast_natCast,Int.cast_one]
  have hn : A ≤ node ∧ node ≤ B := integer_mesh_cell (cubeCorner Q k) (diagMeshRadius Q J) (x k)
    A B node (diagMeshRadius_pos Q J) hxk (by simpa only [hnode] using hnear k)
  have hm0 := mul_le_mul_of_nonneg_right (show (A:ℝ) ≤ node by exact_mod_cast hn.1) (diagMeshRadius_pos Q J).le
  have hm1 := mul_le_mul_of_nonneg_right (show (node:ℝ) ≤ B by exact_mod_cast hn.2) (diagMeshRadius_pos Q J).le
  change cubeCorner P k ≤ diagInteriorVertex Q J z k ∧
    diagInteriorVertex Q J z k ≤ ((P.index k:ℝ)+1/2)*cubeScaleFactor P
  rw [hcorner,hupper]
  rw [hnode]
  constructor <;> linarith only [hm0,hm1]

end
end ASDExplicitGamma.Inverse
