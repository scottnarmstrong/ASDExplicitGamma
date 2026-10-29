module

public import ASDExplicitGamma.Triadic.DiagCells
public import ASDExplicitGamma.Triadic.DiagNeighbors
public import Mathlib.Data.Fintype.EquivFin

/-! Exact Cartesian indexing of source cells for the finite lattice estimates. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization
open scoped BigOperators

noncomputable section

/-- Embed a source cell's lower vertex into the full mesh vertex grid. -/
def diagCellVertexIndex (j : ℕ) (k : Fin 2 → Fin (3 ^ j)) : Fin 2 → Fin (3 ^ j + 1) :=
  fun i => ⟨(k i).val, Nat.lt_succ_of_lt (k i).isLt⟩

theorem diagCellVertex_neighbor_index (j : ℕ) (k : Fin 2 → Fin (3 ^ j)) (i : Fin 2) :
    diagNeighborIndex (3 ^ j) (diagCellVertexIndex j k i) 0 = (k i).val := by
  have hk : (k i).val ≠ 3 ^ j := (k i).isLt.ne
  by_cases hz : (k i).val = 0
  · simp [diagNeighborIndex, diagCellVertexIndex, hz]
  · simp [diagNeighborIndex, diagCellVertexIndex, hz, hk]

/-- The unique actual triadic cell with the prescribed grid center. -/
def diagMeshCell (Q : TriadicCube 2) (j : ℕ) (k : Fin 2 → Fin (3 ^ j)) : TriadicCube 2 :=
  Classical.choose (diagNeighborCenter_unique_cell Q j (diagCellVertexIndex j k) (fun _ => 0))

theorem diagMeshCell_mem (Q : TriadicCube 2) (j : ℕ) (k : Fin 2 → Fin (3 ^ j)) :
    diagMeshCell Q j k ∈ descendantsAtDepth Q j :=
  (Classical.choose_spec (diagNeighborCenter_unique_cell Q j (diagCellVertexIndex j k) (fun _ => 0))).1.1

theorem diagMeshCell_sample_mem (Q : TriadicCube 2) (j : ℕ) (k : Fin 2 → Fin (3 ^ j)) :
    diagNeighborCenter (cubeCorner Q) (diagMeshRadius Q j) (3 ^ j)
      (diagCellVertexIndex j k) (fun _ => 0) ∈ cubeSet (diagMeshCell Q j k) :=
  (Classical.choose_spec (diagNeighborCenter_unique_cell Q j (diagCellVertexIndex j k) (fun _ => 0))).1.2

/-- Exact lower corner, so this is source mesh indexing, not an auxiliary partition. -/
theorem diagMeshCell_corner (Q : TriadicCube 2) (j : ℕ) (k : Fin 2 → Fin (3 ^ j)) (i : Fin 2) :
    cubeCorner (diagMeshCell Q j k) i = cubeCorner Q i + (k i).val * diagMeshRadius Q j := by
  rw [diagNeighborCenter_cell_corner Q j (diagCellVertexIndex j k) (fun _ => 0)
    (diagMeshCell_mem Q j k) (diagMeshCell_sample_mem Q j k) i,
    diagCellVertex_neighbor_index]

@[simp] theorem diagMeshCell_side (Q : TriadicCube 2) (j : ℕ) (k : Fin 2 → Fin (3 ^ j)) :
    cubeScaleFactor (diagMeshCell Q j k) = diagMeshRadius Q j :=
  cubeScaleFactor_descendant_eq_div_pow (diagMeshCell_mem Q j k)

theorem diagMeshCell_injective (Q : TriadicCube 2) (j : ℕ) : Function.Injective (diagMeshCell Q j) := by
  intro k l h
  funext i
  apply Fin.ext
  have hc := congrArg (fun R : TriadicCube 2 => cubeCorner R i) h
  rw [diagMeshCell_corner, diagMeshCell_corner] at hc
  have hp : ((k i).val : ℝ) * diagMeshRadius Q j = (l i).val * diagMeshRadius Q j := by
    linarith only [hc]
  have hval := mul_right_cancel₀ (diagMeshRadius_pos Q j).ne' hp
  exact_mod_cast hval

/-- The exact enumeration of all source cells by the Cartesian grid. -/
def diagMeshCellEquiv (Q : TriadicCube 2) (j : ℕ) :
    (Fin 2 → Fin (3 ^ j)) ≃ {R : TriadicCube 2 // R ∈ descendantsAtDepth Q j} := by
  let f : (Fin 2 → Fin (3 ^ j)) → {R : TriadicCube 2 // R ∈ descendantsAtDepth Q j} :=
    fun k => ⟨diagMeshCell Q j k, diagMeshCell_mem Q j k⟩
  have hinj : Function.Injective f := fun k l h => diagMeshCell_injective Q j (congrArg Subtype.val h)
  have hcard : Fintype.card (Fin 2 → Fin (3 ^ j)) =
      Fintype.card {R : TriadicCube 2 // R ∈ descendantsAtDepth Q j} := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Fintype.card_coe,
      descendantsAtDepth_card]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm j 2]
  exact Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩)

/-- Tile averages and the finite lattice average are exactly the same. -/
theorem diagDescendantsAverage_eq_grid_average (Q : TriadicCube 2) (j : ℕ)
    (F : TriadicCube 2 → ℝ) : descendantsAverage Q j F =
      ((3 ^ j : ℕ) : ℝ)⁻¹ ^ 2 * ∑ k : Fin 2 → Fin (3 ^ j), F (diagMeshCell Q j k) := by
  have hsum : (∑ R ∈ descendantsAtDepth Q j, F R) =
      ∑ k : Fin 2 → Fin (3 ^ j), F (diagMeshCell Q j k) := by
    rw [← Finset.sum_attach (descendantsAtDepth Q j) F]
    exact (Equiv.sum_comp (diagMeshCellEquiv Q j) (fun R => F R.val)).symm
  dsimp only [descendantsAverage]
  rw [hsum, descendantsAtDepth_card]
  have hc : ((3 ^ 2) ^ j : ℕ) = (3 ^ j) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 j]
  rw [hc]
  push_cast
  rw [inv_pow]

/-- Equal scale and lower corners determine the actual triadic cube. -/
theorem diagCube_eq_of_scale_corner {R S : TriadicCube 2} (hscale : R.scale = S.scale)
    (hcorner : ∀ i, cubeCorner R i = cubeCorner S i) : R = S := by
  cases R with
  | mk r a =>
    cases S with
    | mk s b =>
      change r = s at hscale
      subst s
      have hab : a = b := by
        funext i
        have h := hcorner i
        change ((a i : ℝ) - 1 / 2) * (3 : ℝ) ^ r = ((b i : ℝ) - 1 / 2) * (3 : ℝ) ^ r at h
        have hh := mul_right_cancel₀ (zpow_pos (by norm_num : (0 : ℝ) < 3) r).ne' h
        have hc : (a i : ℝ) = (b i : ℝ) := by linarith only [hh]
        exact_mod_cast hc
      subst b
      rfl

/-- Incrementing a Cartesian cell index gives precisely the physical neighbor. -/
theorem diagMeshCell_neighbor (Q : TriadicCube 2) (j : ℕ) (i : Fin 2)
    (k l : Fin 2 → Fin (3 ^ j))
    (hstep : ∀ b, (l b).val = (k b).val + if b = i then 1 else 0) :
    diagMeshCell Q j l = diagCellNeighbor (diagMeshCell Q j k) i := by
  apply diagCube_eq_of_scale_corner
  · change (diagMeshCell Q j l).scale = (diagMeshCell Q j k).scale
    rw [scale_eq_sub_of_mem_descendantsAtDepth (diagMeshCell_mem Q j l),
      scale_eq_sub_of_mem_descendantsAtDepth (diagMeshCell_mem Q j k)]
  · intro b
    rw [diagMeshCell_corner, diagCellNeighbor_corner, diagMeshCell_corner, diagMeshCell_side]
    have hh : ((l b).val : ℝ) = (k b).val + if b = i then 1 else 0 := by
      by_cases hb : b = i
      · rw [ite_eq_left hb]
        exact_mod_cast (show (l b).val = (k b).val + 1 from by simpa only [ite_eq_left hb] using hstep b)
      · rw [ite_eq_right hb]
        exact_mod_cast (show (l b).val = (k b).val + 0 from by simpa only [ite_eq_right hb] using hstep b)
    rw [hh]
    by_cases hb : b = i <;> simp only [hb, ite_true, ite_false] <;> ring

/-- The first Cartesian cell touches the lower parent face. -/
theorem diagMeshCell_lower_face (Q : TriadicCube 2) (j : ℕ) (i : Fin 2)
    (k : Fin 2 → Fin (3 ^ j)) (hk : (k i).val = 0) :
    cubeCorner (diagMeshCell Q j k) i = cubeCorner Q i := by
  rw [diagMeshCell_corner, hk]
  norm_num

/-- The last Cartesian cell touches the upper parent face. -/
theorem diagMeshCell_upper_face (Q : TriadicCube 2) (j : ℕ) (i : Fin 2)
    (k : Fin 2 → Fin (3 ^ j)) (hk : (k i).val + 1 = 3 ^ j) :
    cubeCorner (diagMeshCell Q j k) i + cubeScaleFactor (diagMeshCell Q j k) =
      cubeCorner Q i + cubeScaleFactor Q := by
  rw [diagMeshCell_corner, diagMeshCell_side]
  have hkr : ((k i).val : ℝ) + 1 = (3 : ℝ) ^ j := by exact_mod_cast hk
  have hside : (3 : ℝ) ^ j * diagMeshRadius Q j = cubeScaleFactor Q := by
    unfold diagMeshRadius
    field_simp
  calc
    _ = cubeCorner Q i + (((k i).val : ℝ) + 1) * diagMeshRadius Q j := by ring
    _ = _ := by rw [hkr, hside]

/-- One source-cell row, with transverse index b. -/
def diagMeshLine {N : ℕ} (i : Fin 2) (b t : Fin N) : Fin 2 → Fin N :=
  fun k => if k = i then t else b

@[simp] theorem diagMeshLine_apply_self {N : ℕ} (i : Fin 2) (b t : Fin N) :
    diagMeshLine i b t i = t := by simp [diagMeshLine]

theorem diagMeshLine_step {N : ℕ} (i : Fin 2) (b k l : Fin N)
    (hkl : l.val = k.val + 1) :
    ∀ a, (diagMeshLine i b l a).val = (diagMeshLine i b k a).val + if a = i then 1 else 0 := by
  intro a
  by_cases ha : a = i <;> simp [diagMeshLine, ha, hkl]

/-- Row coordinates enumerate every Cartesian source cell once. -/
def diagGridLineEquiv {N : ℕ} (i s : Fin 2) (his : i ≠ s) :
    (Fin N × Fin N) ≃ (Fin 2 → Fin N) where
  toFun p := diagMeshLine i p.1 p.2
  invFun k := (k s, k i)
  left_inv p := by
    rcases p with ⟨b, t⟩
    simp [diagMeshLine, his.symm]
  right_inv k := by
    funext a
    have ha : a = i ∨ a = s := by fin_cases i <;> fin_cases s <;> fin_cases a <;> simp_all
    rcases ha with rfl | rfl
    · simp [diagMeshLine]
    · simp [diagMeshLine, his.symm]

theorem diagGridLine_sum {N : ℕ} (i s : Fin 2) (his : i ≠ s)
    (F : (Fin 2 → Fin N) → ℝ) :
    (∑ b : Fin N, ∑ t : Fin N, F (diagMeshLine i b t)) = ∑ k : Fin 2 → Fin N, F k := by
  have h := Equiv.sum_comp (diagGridLineEquiv i s his) F
  rw [Fintype.sum_prod_type] at h
  exact h

/-- The other coordinate in the planar source grid. -/
def diagOtherCoordinate (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

theorem diagOtherCoordinate_ne (i : Fin 2) : i ≠ diagOtherCoordinate i := by
  fin_cases i <;> norm_num [diagOtherCoordinate]

end

end ASDExplicitGamma.Triadic
