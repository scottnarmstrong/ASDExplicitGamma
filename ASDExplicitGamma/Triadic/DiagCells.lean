module

public import ASDExplicitGamma.Triadic.DiagBilinear

/-! The geometric neighbor samples in DIAG are actual triadic cell means. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory

noncomputable section

theorem diagNeighborIndex_bounds {N : ℕ} (hN : 0 < N)
    (z : Fin (N + 1)) (b : Fin 2) :
    0 ≤ diagNeighborIndex N z b ∧ diagNeighborIndex N z b + 1 ≤ N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  by_cases hz0 : z.val = 0
  · simp only [diagNeighborIndex, hz0, ite_true]
    exact ⟨le_rfl, by linarith only [hNr]⟩
  · by_cases hzN : z.val = N
    · simp only [diagNeighborIndex, hzN, Nat.ne_of_gt hN, ite_false, ite_true]
      exact ⟨by linarith only [hNr], by linarith⟩
    · simp only [diagNeighborIndex, hz0, hzN, ite_false]
      have hzlo : (1 : ℝ) ≤ z.val := by exact_mod_cast (show 1 ≤ z.val by omega)
      have hzhi : (z.val : ℝ) + 1 ≤ N := by exact_mod_cast (show z.val + 1 ≤ N by have := z.isLt; omega)
      have hblo : (0 : ℝ) ≤ b.val := Nat.cast_nonneg _
      have hbhi : (b.val : ℝ) ≤ 1 := by exact_mod_cast (show b.val ≤ 1 by have := b.isLt; omega)
      exact ⟨by linarith only [hzlo, hbhi], by linarith only [hzhi, hblo]⟩

/-- Every reflected neighbor sample is strictly inside the parent cube. -/
theorem diagNeighborCenter_mem_openCube (Q : TriadicCube 2) (j : ℕ)
    (z : Fin 2 → Fin (3 ^ j + 1)) (b : Fin 2 → Fin 2) :
    diagNeighborCenter (cubeCorner Q) (diagMeshRadius Q j) (3 ^ j) z b ∈ openCubeSet Q := by
  rw [openCubeSet_eq_box]
  intro i _
  have hi := diagNeighborIndex_bounds (pow_pos (by norm_num : 0 < (3 : ℕ)) j) (z i) (b i)
  have hr := diagMeshRadius_pos Q j
  have hside : ((3 ^ j : ℕ) : ℝ) * diagMeshRadius Q j = cubeScaleFactor Q := by
    unfold diagMeshRadius
    norm_cast
    field_simp
  change cubeCorner Q i < cubeCorner Q i + (diagNeighborIndex (3 ^ j) (z i) (b i) + 1 / 2) *
      diagMeshRadius Q j ∧
    cubeCorner Q i + (diagNeighborIndex (3 ^ j) (z i) (b i) + 1 / 2) * diagMeshRadius Q j <
      cubeCorner Q i + cubeScaleFactor Q
  constructor <;> nlinarith only [hi.1, hi.2, hr, hside]

/-- A neighbor sample determines its unique actual depth-j descendant cell,
and evaluating the conditional mean there is exactly that cell's mean.
This also identifies the physical cell side, with no artificial mesh cells. -/
theorem diagNeighborCenter_unique_cell (Q : TriadicCube 2) (j : ℕ)
    (z : Fin 2 → Fin (3 ^ j + 1)) (b : Fin 2 → Fin 2) :
    let x := diagNeighborCenter (cubeCorner Q) (diagMeshRadius Q j) (3 ^ j) z b
    ∃! R : TriadicCube 2, R ∈ descendantsAtDepth Q j ∧ x ∈ cubeSet R := by
  intro x
  obtain ⟨R, hR, hx⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet j
    (openCubeSet_subset_cubeSet Q (diagNeighborCenter_mem_openCube Q j z b))
  refine ⟨R, ⟨hR, hx⟩, ?_⟩
  intro S hS
  by_contra hSR
  have hdis := pairwiseDisjoint_descendantsAtDepth Q j hS.1 hR hSR
  exact Set.disjoint_left.mp hdis hS.2 hx

theorem diagNeighborCenter_cellMean (Q : TriadicCube 2) (j : ℕ)
    (z : Fin 2 → Fin (3 ^ j + 1)) (b : Fin 2 → Fin 2) :
    let x := diagNeighborCenter (cubeCorner Q) (diagMeshRadius Q j) (3 ^ j) z b
    ∃ R ∈ descendantsAtDepth Q j, x ∈ cubeSet R ∧
      cubeScaleFactor R = diagMeshRadius Q j ∧
      ∀ f : Vec 2 → ℝ, cubeProjection Q j f x = cubeAverage R f := by
  intro x
  obtain ⟨R, ⟨hR, hx⟩, _⟩ := diagNeighborCenter_unique_cell Q j z b
  refine ⟨R, hR, hx, cubeScaleFactor_descendant_eq_div_pow hR, ?_⟩
  intro f
  exact cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth f hR hx

/-- The sampled point is the actual center of its selected triadic cell.
Oddness of 3^j aligns the uniform mesh with integer-indexed triadic cubes. -/
theorem diagNeighborCenter_is_cellCenter (Q : TriadicCube 2) (j : ℕ)
    (z : Fin 2 → Fin (3 ^ j + 1)) (b : Fin 2 → Fin 2)
    {R : TriadicCube 2} (hR : R ∈ descendantsAtDepth Q j)
    (hx : diagNeighborCenter (cubeCorner Q) (diagMeshRadius Q j) (3 ^ j) z b ∈ cubeSet R)
    (i : Fin 2) :
    diagNeighborCenter (cubeCorner Q) (diagMeshRadius Q j) (3 ^ j) z b i =
      (R.index i : ℝ) * diagMeshRadius Q j := by
  let N : ℕ := 3 ^ j
  let H : ℕ := (N - 1) / 2
  have hodd : N % 2 = 1 := by dsimp [N]; norm_num [Nat.pow_mod]
  have hN : N = 2 * H + 1 := by
    have hmod := Nat.mod_add_div N 2
    change N = 2 * ((N - 1) / 2) + 1
    omega
  have hNr : (N : ℝ) = 2 * (H : ℝ) + 1 := by exact_mod_cast hN
  have hr := diagMeshRadius_pos Q j
  have hside : cubeScaleFactor Q = (N : ℝ) * diagMeshRadius Q j := by
    dsimp [N, diagMeshRadius]
    push_cast
    field_simp
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (k : ℝ) = diagNeighborIndex N (z i) (b i) := by
    unfold diagNeighborIndex
    split_ifs
    · exact ⟨0, by norm_num⟩
    · exact ⟨(N : ℤ) - 1, by push_cast; rfl⟩
    · exact ⟨((z i).val : ℤ) - (b i).val, by push_cast; rfl⟩
  let n : ℤ := Q.index i * N + k - H
  have hn : (n : ℝ) = ((Q.index i : ℝ) - 1 / 2) * N +
      diagNeighborIndex N (z i) (b i) + 1 / 2 := by
    dsimp [n]
    push_cast
    rw [← hk, hNr]
    ring
  have hxn : diagNeighborCenter (cubeCorner Q) (diagMeshRadius Q j) N z b i =
      (n : ℝ) * diagMeshRadius Q j := by
    rw [hn]
    unfold diagNeighborCenter cubeCorner
    rw [hside]
    ring
  have hi := hx i
  rw [cubeScaleFactor_descendant_eq_div_pow hR] at hi
  change ((R.index i : ℝ) - 1 / 2) * diagMeshRadius Q j ≤
      diagNeighborCenter (cubeCorner Q) (diagMeshRadius Q j) N z b i ∧
    diagNeighborCenter (cubeCorner Q) (diagMeshRadius Q j) N z b i <
      ((R.index i : ℝ) + 1 / 2) * diagMeshRadius Q j at hi
  rw [hxn] at hi
  have hlo := (mul_le_mul_iff_left₀ hr).mp hi.1
  have hhi := (mul_lt_mul_iff_left₀ hr).mp hi.2
  have hni : n = R.index i := by
    have hle : n ≤ R.index i := by
      by_contra h
      have hh : R.index i + 1 ≤ n := by omega
      have hh' : (R.index i : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hh
      linarith only [hh', hhi]
    have hge : R.index i ≤ n := by
      by_contra h
      have hh : n + 1 ≤ R.index i := by omega
      have hh' : (n : ℝ) + 1 ≤ (R.index i : ℝ) := by exact_mod_cast hh
      linarith only [hh', hlo]
    exact le_antisymm hle hge
  simpa only [hni] using hxn

/-- The cell corners coincide with the source mesh corners. -/
theorem diagNeighborCenter_cell_corner (Q : TriadicCube 2) (j : ℕ)
    (z : Fin 2 → Fin (3 ^ j + 1)) (b : Fin 2 → Fin 2)
    {R : TriadicCube 2} (hR : R ∈ descendantsAtDepth Q j)
    (hx : diagNeighborCenter (cubeCorner Q) (diagMeshRadius Q j) (3 ^ j) z b ∈ cubeSet R)
    (i : Fin 2) : cubeCorner R i = cubeCorner Q i +
      diagNeighborIndex (3 ^ j) (z i) (b i) * diagMeshRadius Q j := by
  have hc := diagNeighborCenter_is_cellCenter Q j z b hR hx i
  unfold diagNeighborCenter at hc
  unfold cubeCorner
  rw [cubeScaleFactor_descendant_eq_div_pow hR]
  change ((R.index i : ℝ) - 1 / 2) * diagMeshRadius Q j = _
  change ((R.index i : ℝ) - 1 / 2) * diagMeshRadius Q j =
    cubeCorner Q i + diagNeighborIndex (3 ^ j) (z i) (b i) * diagMeshRadius Q j
  linarith only [hc]

end

end ASDExplicitGamma.Triadic
