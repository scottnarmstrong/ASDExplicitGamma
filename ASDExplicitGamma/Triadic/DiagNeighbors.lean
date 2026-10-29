module

public import ASDExplicitGamma.Triadic.DiagCoordinate
public import ASDExplicitGamma.Triadic.DiagTentKernel

/-! Adjacent actual cells and the exact two-cell tent kernels. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory Set

noncomputable section

/-- The congruent cell immediately after `R` in coordinate `i`. -/
def diagCellNeighbor (R : TriadicCube 2) (i : Fin 2) : TriadicCube 2 :=
  ⟨R.scale, fun k => R.index k + if k = i then 1 else 0⟩

@[simp] theorem diagCellNeighbor_side (R : TriadicCube 2) (i : Fin 2) :
    cubeScaleFactor (diagCellNeighbor R i) = cubeScaleFactor R := rfl

theorem diagCellNeighbor_corner (R : TriadicCube 2) (i k : Fin 2) :
    cubeCorner (diagCellNeighbor R i) k = cubeCorner R k +
      if k = i then cubeScaleFactor R else 0 := by
  by_cases hk : k = i
  · simp [cubeCorner, diagCellNeighbor, cubeScaleFactor, hk]
    ring
  · simp [cubeCorner, diagCellNeighbor, cubeScaleFactor, hk]

/-- In dimension two these two distinct coordinate intervals specify the whole cell. -/
theorem diagOpenCube_mem_two (R : TriadicCube 2) (i s : Fin 2) (his : i ≠ s) (x : Vec 2) :
    x ∈ openCubeSet R ↔
      x i ∈ Ioo (cubeCorner R i) (cubeCorner R i + cubeScaleFactor R) ∧
      x s ∈ Ioo (cubeCorner R s) (cubeCorner R s + cubeScaleFactor R) := by
  rw [openCubeSet_eq_box]
  constructor
  · intro h
    exact ⟨h i (mem_univ i), h s (mem_univ s)⟩
  · intro h k _
    have hk : k = i ∨ k = s := by
      fin_cases i <;> fin_cases s <;> fin_cases k <;> simp_all
    rcases hk with rfl | rfl
    · exact h.1
    · exact h.2

/-- The tent across a common face splits into the source affine kernels on
exactly the two neighboring cells. The weak slope has the opposite signs. -/
theorem diagTwoCell_tentKernels (R : TriadicCube 2) (i s : Fin 2) (his : i ≠ s) :
    let r := cubeScaleFactor R
    let c := cubeCorner R i + r
    let strip := fun x : Vec 2 => x s ∈ Ioo (cubeCorner R s) (cubeCorner R s + r)
    ∀ᵐ x : Vec 2 ∂volume,
      ((if strip x then (1 : ℝ) else 0) * diagHat ((x i - c) / r) =
        (openCubeSet R).indicator (fun x => (x i - c + r) / r) x +
        (openCubeSet (diagCellNeighbor R i)).indicator (fun x => (c + r - x i) / r) x) ∧
      ((if strip x then (1 : ℝ) else 0) * diagHatSlope r (x i - c) =
        (openCubeSet R).indicator (fun _ => 1 / r) x +
        (openCubeSet (diagCellNeighbor R i)).indicator (fun _ => -1 / r) x) := by
  classical
  intro r c strip
  have h0 : ∀ᵐ x : Vec 2 ∂volume, x i ≠ c := Measure.ae_eval_ne (fun _ : Fin 2 => (volume : Measure ℝ)) i c
  have h1 : ∀ᵐ x : Vec 2 ∂volume, x i ≠ c + r := Measure.ae_eval_ne (fun _ : Fin 2 => (volume : Measure ℝ)) i (c + r)
  filter_upwards [h0, h1] with x hx0 hx1
  let t := x i - c
  have ht0 : t ≠ 0 := by dsimp [t]; intro h; apply hx0; linarith only [h]
  have ht1 : t ≠ r := by dsimp [t]; intro h; apply hx1; linarith only [h]
  have hkernel := diagTentKernel_split (cubeScaleFactor_pos' R) ht0 ht1
  have hR : x ∈ openCubeSet R ↔ strip x ∧ (-r < t ∧ t < 0) := by
    rw [diagOpenCube_mem_two R i s his]
    dsimp only [strip, t, c, r]
    constructor
    · intro h
      exact ⟨h.2, by linarith only [h.1.1], by linarith only [h.1.2]⟩
    · intro h
      exact ⟨⟨by linarith only [h.2.1], by linarith only [h.2.2]⟩, h.1⟩
  have hS : x ∈ openCubeSet (diagCellNeighbor R i) ↔ strip x ∧ (0 < t ∧ t < r) := by
    rw [diagOpenCube_mem_two (diagCellNeighbor R i) i s his]
    simp only [diagCellNeighbor_side, diagCellNeighbor_corner, ite_true, ite_eq_right his.symm, add_zero]
    dsimp only [strip, t, c, r]
    constructor
    · intro h
      exact ⟨h.2, by linarith only [h.1.1], by linarith only [h.1.2]⟩
    · intro h
      exact ⟨⟨by linarith only [h.2.1], by linarith only [h.2.2]⟩, h.1⟩
  constructor
  · rw [hkernel.1, mul_add]
    have heq : cubeScaleFactor R - t = c + r - x i := by dsimp [t, r]; ring
    simp only [Set.indicator_apply, hR, hS, heq]
    by_cases hs : strip x
    · simp only [hs, ite_true, true_and, one_mul]
      rfl
    · simp only [hs, ite_false, false_and, zero_mul, zero_add]
  · rw [hkernel.2, mul_add]
    simp only [Set.indicator_apply, hR, hS]
    by_cases hs : strip x
    · simp only [hs, ite_true, true_and, one_mul]
      rfl
    · simp only [hs, ite_false, false_and, zero_mul, zero_add]

end

end ASDExplicitGamma.Triadic
