module

public import ASDExplicitGamma.Triadic.DiagBroken
public import ASDExplicitGamma.Triadic.DiagCellBounds

/-! Exact mean-zero source cell bounds assembled with disjoint tile normalization. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

theorem diagProjection_mesh_cell_ae (Q : TriadicCube 2) (j : ℕ)
    (v : H1Function (openCubeSet Q)) (k : Fin 2 → Fin (3^j)) :
    cubeProjection Q j v.toFun =ᵐ[volume.restrict (cubeSet (diagMeshCell Q j k))]
      (fun _ => cubeAverage (diagMeshCell Q j k) v.toFun) := by
  apply (ae_restrict_mem (measurableSet_cubeSet _)).mono
  intro x hx
  exact cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth _ (diagMeshCell_mem Q j k) hx

/-- Sharp mean-zero positive estimate on all source cells, with no cell H10 premise. -/
theorem diagTiledFluctuation_positive_energy_le (Q : TriadicCube 2) (j : ℕ)
    (v : H1Function (openCubeSet Q)) :
    diagTiledScalarPositiveEnergy Q j (fun x => v.toFun x-cubeProjection Q j v.toFun x) ≤
      diagMeshRadius Q j^2*(2/Real.pi)^2 *
        ASDExplicitGamma.Variational.lemmaVTiledWeakEnergy Q j v.grad := by
  have hpoint (k : Fin 2 → Fin (3^j)) :
      primalEnergy (diagMeshCell Q j k) (Real.sqrt 3) (fun x => v.toFun x-cubeProjection Q j v.toFun x) ≤
        diagMeshRadius Q j^2*(2/Real.pi)^2*vectorWeakHaarEnergy (diagMeshCell Q j k) v.grad := by
    let R := diagMeshCell Q j k
    let w := v.restrictToOpenSubcube (diagMeshCell_mem Q j k)
    have hae : (fun x => v.toFun x-cubeProjection Q j v.toFun x) =ᵐ[volume.restrict (cubeSet R)]
        (diagCellFluctuation R w).toFun := by
      filter_upwards [diagProjection_mesh_cell_ae Q j v k] with x hx
      simp only [diagCellFluctuation, H1Function.sub_toFun, h1ConstantOnCube_toFun]
      change v.toFun x-cubeProjection Q j v.toFun x = v.toFun x-cubeAverage R v.toFun
      rw [hx]
    rw [diagPrimalEnergy_congr_ae R _ hae]
    have h := diag_meanZero_positiveHaar_sq R (diagCellFluctuation R w) (diagCellFluctuation_mean R w)
    have hg : (diagCellFluctuation R w).grad = v.grad := by
      simp only [diagCellFluctuation, H1Function.sub_grad, h1ConstantOnCube_grad,
        Pi.zero_apply, sub_zero]
      rfl
    rw [hg, positiveHaarNorm, vectorWeakHaarNorm,
      Real.sq_sqrt (primalEnergy_nonneg R (Real.sqrt 3) (Real.sqrt_nonneg _) _),
      Real.sq_sqrt (vectorWeakHaarEnergy_nonneg R v.grad)] at h
    simpa only [R, diagMeshCell_side] using h
  unfold diagTiledScalarPositiveEnergy ASDExplicitGamma.Variational.lemmaVTiledWeakEnergy
  rw [diagDescendantsAverage_eq_grid_average, diagDescendantsAverage_eq_grid_average]
  apply le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hpoint k) (sq_nonneg _))
  rw [← Finset.mul_sum]
  apply le_of_eq
  ring

/-- Sharp mean-zero global L2 estimate with the Neumann cell constant c0. -/
theorem diagTiledFluctuation_L2_energy_le (Q : TriadicCube 2) (j : ℕ)
    (v : H1Function (openCubeSet Q)) :
    energy Q (fun x => v.toFun x-cubeProjection Q j v.toFun x) ≤
      diagMeshRadius Q j^2*planarC0^2 *
        ASDExplicitGamma.Variational.lemmaVTiledWeakEnergy Q j v.grad := by
  have hf : MemLp (fun x => v.toFun x-cubeProjection Q j v.toFun x) 2 (normalizedCubeMeasure Q) :=
    v.memL2_normalizedCubeMeasure.sub (projection_memLp Q j v.toFun 2)
  rw [energy_eq_descendantsAverage Q j hf]
  have hpoint (k : Fin 2 → Fin (3^j)) :
      energy (diagMeshCell Q j k) (fun x => v.toFun x-cubeProjection Q j v.toFun x) ≤
        diagMeshRadius Q j^2*planarC0^2*vectorWeakHaarEnergy (diagMeshCell Q j k) v.grad := by
    let R := diagMeshCell Q j k
    let w := v.restrictToOpenSubcube (diagMeshCell_mem Q j k)
    have hae : (fun x => v.toFun x-cubeProjection Q j v.toFun x) =ᵐ[volume.restrict (cubeSet R)]
        (fun x => w.toFun x-cubeAverage R w.toFun) := by
      filter_upwards [diagProjection_mesh_cell_ae Q j v k] with x hx
      change v.toFun x-cubeProjection Q j v.toFun x = v.toFun x-cubeAverage R v.toFun
      rw [hx]
    rw [diagEnergy_congr_ae R hae]
    have h := h1_fluctuation_L2_bridge_sq R w
    have hg : (fun x i => w.grad x i) = v.grad := rfl
    rw [hg, vectorWeakHaarNorm, Real.sq_sqrt (vectorWeakHaarEnergy_nonneg R v.grad)] at h
    simpa only [R, diagMeshCell_side] using h
  unfold ASDExplicitGamma.Variational.lemmaVTiledWeakEnergy
  rw [diagDescendantsAverage_eq_grid_average, diagDescendantsAverage_eq_grid_average]
  apply le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hpoint k) (sq_nonneg _))
  rw [← Finset.mul_sum]
  apply le_of_eq
  ring

end

end ASDExplicitGamma.Triadic
