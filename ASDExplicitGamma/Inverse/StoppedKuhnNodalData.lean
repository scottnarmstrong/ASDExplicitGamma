module

public import ASDExplicitGamma.Inverse.StoppedRootMeshVertex
public import ASDExplicitGamma.Inverse.StoppedMeshValueBounds
public import Algsuperdiff.Section3.Provider.Whitney.KuhnCells

/-! The finite Kuhn mesh reads exactly the already fixed stopped nodal data.
Nonzero vertex data have a genuine interior mesh-node representative. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization ASDExplicitGamma.Triadic
open Algsuperdiff.Section3.Provider.Whitney
noncomputable section

theorem diag_synthesis_at_node (Q : TriadicCube 2) (j : ℕ)
    (b : InteriorNode j → ℝ) (z : InteriorNode j) :
    (diagSynthesisH1Linear Q j b).toFun (diagInteriorVertex Q j z)=b z := by
  classical
  rw [diagSynthesisH1Linear_toFun]
  simp only [diagPhysicalHat_at_vertex]
  rw [Finset.sum_eq_single z]
  · simp only [ite_true,mul_one]
  · intro w hw hwz
    rw [ite_eq_right hwz,mul_zero]
  · intro hz
    exact (hz (Finset.mem_univ z)).elim

/-- A nonzero tensor nodal datum is strictly inside its root. -/
theorem diag_synthesis_nonzero_mem_open (Q : TriadicCube 2) (j : ℕ)
    (b : InteriorNode j → ℝ) {x : Vec 2}
    (hx : (diagSynthesisH1Linear Q j b).toFun x ≠ 0) : x ∈ openCubeSet Q := by
  classical
  rw [diagSynthesisH1Linear_toFun] at hx
  obtain ⟨z,hz⟩ : ∃ z, b z*diagPhysicalHat (diagInteriorVertex Q j z) (diagMeshRadius Q j) x ≠ 0 := by
    by_contra! hn
    exact hx (Finset.sum_eq_zero (fun z _ => hn z))
  have hh := (mul_ne_zero_iff.mp hz).2
  change (∏ k, diagHat ((x k-diagInteriorVertex Q j z k)/diagMeshRadius Q j)) ≠ 0 at hh
  intro k
  have hp := diag_hat_positive_support ((Finset.prod_ne_zero_iff.mp hh) k (Finset.mem_univ k))
  have hr := diagMeshRadius_pos Q j
  have hs := diagInteriorVertex_support Q j z k
  have hnear := abs_lt.mpr hp
  rw [abs_div,abs_of_pos hr] at hnear
  have hn := (div_lt_one hr).mp hnear
  have ha := abs_lt.mp hn
  change ((Q.index k:ℝ)-1/2)*cubeScaleFactor Q < x k ∧ x k < ((Q.index k:ℝ)+1/2)*cubeScaleFactor Q
  change cubeCorner Q k ≤ _ ∧ _ ≤ cubeCorner Q k+cubeScaleFactor Q at hs
  have he : ((Q.index k:ℝ)+1/2)*cubeScaleFactor Q=cubeCorner Q k+cubeScaleFactor Q := by unfold cubeCorner; ring
  rw [he]
  change cubeCorner Q k < x k ∧ x k < cubeCorner Q k+cubeScaleFactor Q
  constructor <;> linarith only [ha,hs]

/-- Every literal Kuhn vertex is one actual support-cube corner. -/
theorem kuhn_vertex_is_cell_corner (T : KuhnCell 2) (k : Fin 3) :
    ∃ ε : Fin 2 → Fin 2, T.vertex k=cellCornerVertex T.supportCube ε := by
  let ε : Fin 2 → Fin 2 := fun i => if 2 ≤ (T.order.symm i).val+k.val then 1 else 0
  refine ⟨ε,?_⟩
  funext i
  simp only [KuhnCell.vertex,cellCornerVertex,cubeCorner,ε]
  split_ifs <;> norm_num <;> ring_nf
  simp only [true_or]

/-- Nonzero Kuhn vertex data coincide with exactly the source interior
nodal correction; no arbitrary off-mesh extension enters the construction. -/
theorem kuhn_nonzero_vertex_datum (Q : TriadicCube 2) (j : ℕ)
    (b : InteriorNode j → ℝ) {T : KuhnCell 2}
    (hT : T ∈ triadicSimplexPartition Q (Q.scale-(j:ℤ))) (k : Fin 3)
    (hv : (diagSynthesisH1Linear Q j b).toFun (T.vertex k) ≠ 0) :
    ∃ z : InteriorNode j, diagInteriorVertex Q j z=T.vertex k ∧
      b z=(diagSynthesisH1Linear Q j b).toFun (T.vertex k) := by
  have hTd : T.supportCube ∈ descendantsAtDepth Q j := by
    rw [mem_triadicSimplexPartition_iff,descendantsAtScale_eq_descendantsAtDepth Q (by omega)] at hT
    simpa only [show (Q.scale-(Q.scale-(j:ℤ))).toNat=j by omega] using hT
  obtain ⟨ε,he⟩ := kuhn_vertex_is_cell_corner T k
  have hi := diag_synthesis_nonzero_mem_open Q j b hv
  rw [he] at hi
  obtain ⟨z,hz⟩ := cell_corner_node_of_mem_open Q hTd ε hi
  have hez : diagInteriorVertex Q j z=T.vertex k := hz.trans he.symm
  exact ⟨z,hez,by rw [← hez,diag_synthesis_at_node]⟩

end
end ASDExplicitGamma.Inverse
