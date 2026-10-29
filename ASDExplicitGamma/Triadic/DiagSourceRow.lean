module

public import ASDExplicitGamma.Triadic.DiagBoundaryMean
public import ASDExplicitGamma.Triadic.DiagMesh
public import ASDExplicitGamma.Triadic.DiagReflectionRow
public import ASDExplicitGamma.Variational.LemmaVTiles

/-! Source H¹₀ cell means satisfy the sharp reflected lattice difference estimate. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

/-- The array of actual source cell means. -/
def diagSourceMeans (Q : TriadicCube 2) (j : ℕ) (u : H1Function (openCubeSet Q))
    (k : Fin 2 → Fin (3 ^ j)) : ℝ := cubeAverage (diagMeshCell Q j k) u.toFun

/-- Source one-dimensional reflected difference bound on each transverse row.
The reflection factor two is explicit before normalizing the doubled period. -/
theorem diagSourceRow_difference_energy (Q : TriadicCube 2) (j : ℕ)
    (u : H10Function (openCubeSet Q)) (i s : Fin 2) (his : i ≠ s)
    (b : Fin (3 ^ j)) :
    let m := fun t => diagSourceMeans Q j u.toH1Function (diagMeshLine i b t)
    (∑ k : Fin (2 * 3 ^ j),
      ((diagReflectOdd (3 ^ j) m (diagPeriodShift (3 ^ j) k) -
        diagReflectOdd (3 ^ j) m k) / diagMeshRadius Q j) ^ 2) ≤
      2 * ∑ t : Fin (3 ^ j), dualEnergy (diagMeshCell Q j (diagMeshLine i b t))
        (Real.sqrt 3) (fun x => u.toH1Function.grad x i) := by
  intro m
  let R (t : Fin (3 ^ j)) := diagMeshCell Q j (diagMeshLine i b t)
  let a (t : Fin (3 ^ j)) := cubeAverage (R t) (fun x => u.toH1Function.grad x i)
  let d (t : Fin (3 ^ j)) := pairing (R t) (fun x => u.toH1Function.grad x i)
    (diagCenteredCoordinate (R t) i)
  let ρ := Real.sqrt diagWeakFaceVariance
  let e (t : Fin (3 ^ j)) := d t / ρ
  let B (t : Fin (3 ^ j)) := dualEnergy (R t) (Real.sqrt 3) (fun x => u.toH1Function.grad x i)
  have hN : 0 < (3 : ℕ) ^ j := pow_pos (by norm_num) j
  have hρ : 0 < ρ := Real.sqrt_pos.mpr diagWeakFaceVariance_pos
  have hρsq : ρ ^ 2 = diagWeakFaceVariance := Real.sq_sqrt diagWeakFaceVariance_nonneg
  have hρbound : ρ ^ 2 ≤ 1 / 4 := by rw [hρsq]; exact diagWeakFaceVariance_lt_quarter.le
  have he (t : Fin (3 ^ j)) : ρ * e t = d t := by
    dsimp [e]
    field_simp [hρ.ne']
  have hinner (k l : Fin (3 ^ j)) (hkl : l.val = k.val + 1) :
      (m l - m k) / diagMeshRadius Q j = (a k + a l) / 2 + ρ * (e k - e l) := by
    have hnext : R l = diagCellNeighbor (R k) i :=
      diagMeshCell_neighbor Q j i _ _ (diagMeshLine_step i b k l hkl)
    have hS : diagCellNeighbor (R k) i ∈ descendantsAtDepth Q j := by
      rw [← hnext]
      exact diagMeshCell_mem Q j _
    have h := diagCellNeighbor_mean_difference Q j (R k) i s his (diagMeshCell_mem Q j _) hS u
    rw [← hnext, diagMeshCell_side] at h
    change (m l - m k) / diagMeshRadius Q j = (a k + a l) / 2 + d k - d l at h
    rw [mul_sub, he, he]
    linarith only [h]
  have hlower : m ⟨0, hN⟩ / diagMeshRadius Q j = a ⟨0, hN⟩ / 2 - ρ * e ⟨0, hN⟩ := by
    have h := diagLowerFace_mean_identity Q j (R ⟨0, hN⟩) i s his (diagMeshCell_mem Q j _)
      (diagMeshCell_lower_face Q j i _ (by simp)) u
    rw [diagMeshCell_side] at h
    rw [he]
    exact h
  have hupper : m ⟨3 ^ j - 1, by omega⟩ / diagMeshRadius Q j =
      -a ⟨3 ^ j - 1, by omega⟩ / 2 - ρ * e ⟨3 ^ j - 1, by omega⟩ := by
    have h := diagUpperFace_mean_identity Q j (R ⟨3 ^ j - 1, by omega⟩) i s his (diagMeshCell_mem Q j _)
      (diagMeshCell_upper_face Q j i _ (by simp; omega)) u
    rw [diagMeshCell_side] at h
    rw [he]
    exact h
  have hcell (t : Fin (3 ^ j)) : a t ^ 2 + e t ^ 2 ≤ B t := by
    have hg := memLp_on_descendant_of_memLp (diagMeshCell_mem Q j (diagMeshLine i b t))
      (u.toH1Function.grad_memL2_normalizedCubeMeasure i)
    have h := diagWeakFace_jointBessel (R t) i hg
    change a t ^ 2 + d t ^ 2 / diagWeakFaceVariance ≤ B t at h
    have heq : e t ^ 2 = d t ^ 2 / diagWeakFaceVariance := by
      dsimp [e]
      rw [div_pow, hρsq]
    rw [heq]
    exact h
  exact diagReflectedMeans_difference_energy_le hN (diagMeshRadius Q j) ρ hρbound m a e B
    hinner hlower hupper hcell

/-- Summing the sharp reflected rows gives exactly the source broken weak
energy, with normalized doubled-period counting and no overlap factor. -/
theorem diagSourceRow_total_energy (Q : TriadicCube 2) (j : ℕ)
    (u : H10Function (openCubeSet Q)) :
    let N : ℕ := 3 ^ j
    let m := fun i b t => diagSourceMeans Q j u.toH1Function (diagMeshLine i b t)
    (((N : ℝ)⁻¹) ^ 2 / 2) *
      (∑ i : Fin 2, ∑ b : Fin N, ∑ k : Fin (2 * N),
        ((diagReflectOdd N (m i b) (diagPeriodShift N k) -
          diagReflectOdd N (m i b) k) / diagMeshRadius Q j) ^ 2) ≤
        ASDExplicitGamma.Variational.lemmaVTiledWeakEnergy Q j u.toH1Function.grad := by
  intro N m
  let K := fun i (k : Fin 2 → Fin N) =>
    dualEnergy (diagMeshCell Q j k) (Real.sqrt 3) (fun x => u.toH1Function.grad x i)
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun b _ =>
      diagSourceRow_difference_energy Q j u i (diagOtherCoordinate i) (diagOtherCoordinate_ne i) b
  have hright : (∑ i : Fin 2, ∑ b : Fin N, 2 * ∑ t : Fin N, K i (diagMeshLine i b t)) =
      2 * ∑ i : Fin 2, ∑ k : Fin 2 → Fin N, K i k := by
    simp_rw [← Finset.mul_sum, diagGridLine_sum _ _ (diagOtherCoordinate_ne _)]
  have henergy : ASDExplicitGamma.Variational.lemmaVTiledWeakEnergy Q j u.toH1Function.grad =
      ((N : ℝ)⁻¹) ^ 2 * (∑ i : Fin 2, ∑ k : Fin 2 → Fin N, K i k) := by
    unfold ASDExplicitGamma.Variational.lemmaVTiledWeakEnergy vectorWeakHaarEnergy
    rw [descendantsAverage_sum]
    simp_rw [diagDescendantsAverage_eq_grid_average]
    rw [← Finset.mul_sum]
  rw [henergy]
  have hc : 0 ≤ ((N : ℝ)⁻¹) ^ 2 / 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hsum hc
  change (((N : ℝ)⁻¹) ^ 2 / 2) * _ ≤ (((N : ℝ)⁻¹) ^ 2 / 2) *
    (∑ i : Fin 2, ∑ b : Fin N, 2 * ∑ t : Fin N, K i (diagMeshLine i b t)) at hscaled
  rw [hright] at hscaled
  convert hscaled using 1
  ring

end

end ASDExplicitGamma.Triadic
