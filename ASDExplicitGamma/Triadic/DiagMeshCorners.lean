module

public import ASDExplicitGamma.Triadic.DiagCellReconstruct
public import ASDExplicitGamma.Triadic.DiagSourceNodes
public import ASDExplicitGamma.Triadic.DiagPeriodAverages

/-! Physical mesh corners and their exact doubled-period indices. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization
open scoped BigOperators Fin.CommRing

noncomputable section

/-- Full mesh index of a source cell corner. -/
def diagMeshCornerIndex (j : ℕ) (k : Fin 2 → Fin (3^j)) (b : Fin 2 → Fin 2) :
    Fin 2 → Fin (3^j+1) := fun i => ⟨(k i).val+(b i).val, by
      have := (k i).isLt; have := (b i).isLt; omega⟩

theorem diagMeshCell_corner_vertex (Q : TriadicCube 2) (j : ℕ)
    (k : Fin 2 → Fin (3^j)) (b : Fin 2 → Fin 2) :
    diagCellCorner (diagMeshCell Q j k) b = diagMeshVertex Q j (diagMeshCornerIndex j k b) := by
  funext i
  simp only [diagCellCorner, diagMeshCell_corner, diagMeshCell_side, diagMeshVertex,
    diagMeshCornerIndex, Nat.cast_add]
  ring

/-- Bit vectors as coordinate displacements on the finite period. -/
def diagPeriodBits (N : ℕ) [NeZero (2*N)] (b : Fin 2 → Fin 2) : Fin 2 → Fin (2*N) :=
  fun i => ((b i).val : Fin (2*N))

theorem diagPeriodBits_axes (N : ℕ) [NeZero (2*N)] (b : Fin 2 → Fin 2) :
    diagPeriodBits N b = (if b 0 = 0 then 0 else diagPeriodLag N (diagAxisLag 0)) +
      (if b 1 = 0 then 0 else diagPeriodLag N (diagAxisLag 1)) := by
  have hbit (t : Fin 2) : ((t.val : ℕ) : Fin (2*N)) = if t = 0 then 0 else 1 := by
    fin_cases t <;> simp
  funext i
  fin_cases i <;> by_cases h0 : b 0 = 0 <;> by_cases h1 : b 1 = 0 <;>
    simp [diagPeriodBits, diagPeriodLag, diagAxisLag, hbit, h0, h1]

/-- A source nodal neighbor has its literal cell-corner minus bit index. -/
theorem diagMeshCorner_period_neighbor (j : ℕ) (k : Fin 2 → Fin (3^j))
    (b d : Fin 2 → Fin 2) :
    let N := 3^j
    let instPeriodNonzero : NeZero (2*N) := ⟨by positivity⟩
    (fun i => diagNodalPeriodIndex (diagMeshCornerIndex j k b i) (d i)) =
      diagPeriodEmbed k + diagPeriodBits N b - diagPeriodBits N d := by
  intro N instPeriodNonzero
  funext i
  change (((k i).val+(b i).val : ℕ) : Fin (2*N)) - ((d i).val : Fin (2*N)) =
    (diagReflectionEquiv N (Sum.inl (k i))) + ((b i).val : Fin (2*N)) - ((d i).val : Fin (2*N))
  rw [Nat.cast_add]
  congr 2
  exact (Fin.natCast_eq_mk (by have := (k i).isLt; omega)).trans rfl

/-- The source four-cell corner average in literal periodic array notation. -/
theorem diagSourceNodes_at_cell_corner (Q : TriadicCube 2) (j : ℕ)
    (v : H1Function (openCubeSet Q)) (k : Fin 2 → Fin (3^j)) (b : Fin 2 → Fin 2) :
    let N := 3^j
    let instPeriodNonzero : NeZero (2*N) := ⟨by positivity⟩
    let f := diagOddGrid N (diagSourceMeans Q j v)
    let z := diagPeriodEmbed k + diagPeriodBits N b
    diagOddNodalMean (cubeCorner Q) (diagMeshRadius Q j) N (cubeProjection Q j v.toFun)
        (diagMeshCornerIndex j k b) =
      (f z+f (z-diagPeriodLag N (diagAxisLag 0))+f (z-diagPeriodLag N (diagAxisLag 1))+
        f (z-diagPeriodLag N (diagAxisLag 0)-diagPeriodLag N (diagAxisLag 1)))/4 := by
  intro N instPeriodNonzero f z
  dsimp only [f, z]
  rw [diagOddNodalMean_eq_period]
  simp_rw [diagMeshCorner_period_neighbor, diagPeriodBits_axes]
  simp only [Fin.sum_univ_two]
  norm_num
  simp only [sub_add_eq_sub_sub, add_assoc]
  ring

end

end ASDExplicitGamma.Triadic
