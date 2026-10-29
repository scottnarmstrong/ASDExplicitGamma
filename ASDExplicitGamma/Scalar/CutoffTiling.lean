module

public import ASDExplicitGamma.Scalar.CutoffPatching
public import Homogenization.Geometry.CubeColoring
public import Homogenization.Geometry.CubeMeasure

/-! Exact finite triadic cell energy accounting for the parent trial. -/

@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory

/-- Open cell faces are null, so the integral over a parent is exactly the
finite sum of its same-scale open-cell integrals. -/
theorem setIntegral_descendant_cells (Q : TriadicCube 2) (q : ℤ) (hq : q ≤ Q.scale)
    (f : Vec 2 → ℝ)
    (hf : ∀ R ∈ descendantsAtScale Q q, IntegrableOn f (openCubeSet R)) :
    (∫ x in openCubeSet Q, f x) =
      ∑ R ∈ descendantsAtScale Q q, ∫ x in openCubeSet R, f x := by
  rw [← setIntegral_cubeSet_eq_setIntegral_openCubeSet]
  have hsplit := integral_biUnion_finset (descendantsAtScale Q q)
    (fun R _ => measurableSet_cubeSet R) (pairwiseDisjoint_descendantsAtScale Q hq)
    (fun R hR => by
      change Integrable f (volume.restrict (cubeSet R))
      rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet R]
      exact hf R hR)
  have hcover : (⋃ R ∈ descendantsAtScale Q q, cubeSet R) = cubeSet Q := by
    simpa only [Finset.mem_coe] using (cubeSet_eq_iUnion_descendantsAtScale Q hq).symm
  rw [hcover] at hsplit
  rw [hsplit]
  apply Finset.sum_congr rfl
  intro R hR
  exact setIntegral_cubeSet_eq_setIntegral_openCubeSet

/-- Normalization preserves exactly the cell-volume weights. -/
theorem volumeAverage_descendant_cells (Q : TriadicCube 2) (q : ℤ)
    (hq : q ≤ Q.scale) (f : Vec 2 → ℝ)
    (hf : ∀ R ∈ descendantsAtScale Q q, IntegrableOn f (openCubeSet R)) :
    volumeAverage (openCubeSet Q) f =
      ∑ R ∈ descendantsAtScale Q q,
        (cubeVolume R/cubeVolume Q)*volumeAverage (openCubeSet R) f := by
  unfold volumeAverage
  rw [setIntegral_descendant_cells Q q hq f hf, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro R hR
  rw [volume_openCubeSet_toReal, volume_openCubeSet_toReal]
  field_simp [(cubeVolume_pos R).ne', (cubeVolume_pos Q).ne']

/-- The deterministic weights in the tiling sum to one. -/
theorem descendant_cell_weights_sum (Q : TriadicCube 2) (q : ℤ) (hq : q ≤ Q.scale) :
    (∑ R ∈ descendantsAtScale Q q, cubeVolume R/cubeVolume Q) = 1 := by
  have hfin (R : TriadicCube 2) : IsFiniteMeasure (volume.restrict (openCubeSet R)) :=
    ⟨by simpa using volume_openCubeSet_lt_top R⟩
  have hf : ∀ R ∈ descendantsAtScale Q q,
      IntegrableOn (fun _ : Vec 2 => (1:ℝ)) (openCubeSet R) := by
    intro R hR
    let finiteWeightCell := hfin R
    exact integrable_const 1
  have he := volumeAverage_descendant_cells Q q hq (fun _ => 1) hf
  have hc (R : TriadicCube 2) : volumeAverage (openCubeSet R) (fun _ => (1:ℝ))=1 :=
    volumeAverage_const (by rw [volume_openCubeSet_toReal]; exact (cubeVolume_pos R).ne')
  simp_rw [hc, mul_one] at he
  exact he.symm

/-- A complete tiling has the prescribed local trial on almost every point
of each cell, so its parent energy is the exact weighted cell-energy sum. -/
theorem tiled_patch_energy (Q : TriadicCube 2) (q : ℤ) (hq : q ≤ Q.scale)
    (Y : Vec 2 → BlockVec 2) (Z : TriadicCube 2 → Vec 2 → BlockVec 2)
    (E : Vec 2 → BlockVec 2 → ℝ)
    (hint : ∀ R ∈ descendantsAtScale Q q,
      IntegrableOn (fun x => E x (Z R x)) (openCubeSet R)) :
    volumeAverage (openCubeSet Q) (fun x => E x
      (compatibleCellPatch Y (descendantsAtScale Q q) openCubeSet Z x)) =
      ∑ R ∈ descendantsAtScale Q q,
        (cubeVolume R/cubeVolume Q)*volumeAverage (openCubeSet R) (fun x => E x (Z R x)) := by
  have hd : ∀ R ∈ descendantsAtScale Q q, ∀ S ∈ descendantsAtScale Q q,
      R ≠ S → Disjoint (openCubeSet R) (openCubeSet S) := by
    intro R hR S hS hRS
    exact ((pairwiseDisjoint_descendantsAtScale Q hq) hR hS hRS).mono
      (openCubeSet_subset_cubeSet R) (openCubeSet_subset_cubeSet S)
  have heq (R : TriadicCube 2) (hR : R ∈ descendantsAtScale Q q) :
      (fun x => E x (compatibleCellPatch Y (descendantsAtScale Q q) openCubeSet Z x)) =ᵐ[
        volume.restrict (openCubeSet R)] fun x => E x (Z R x) := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
    rw [compatible_cell_patch_eq_on_cell Y (descendantsAtScale Q q) openCubeSet Z
      hd hR hx]
  rw [volumeAverage_descendant_cells Q q hq _
    (fun R hR => (hint R hR).congr_fun_ae (heq R hR).symm)]
  apply Finset.sum_congr rfl
  intro R hR
  congr 1
  unfold volumeAverage
  rw [integral_congr_ae (heq R hR)]

end ASDExplicitGamma.Scalar
