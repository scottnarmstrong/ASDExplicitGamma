module

public import ASDExplicitGamma.Triadic.HilbertHaarBasic

/-! Conditional-mean geometry and functoriality of actual Hilbert-valued Haar projections. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- Restricting an Lp field to an actual descendant preserves local Lp membership. -/
theorem hilbert_memLp_descendant {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {Q R : TriadicCube d} {j : ℕ} {p : ℝ≥0∞} {F : Vec d → E}
    (hR : R ∈ descendantsAtDepth Q j) (hF : MemLp F p (normalizedCubeMeasure Q)) :
    MemLp F p (normalizedCubeMeasure R) := by
  have hrestrict := hF.restrict (cubeSet R)
  have hle : normalizedCubeMeasure R ≤ ENNReal.ofReal (cubeVolume Q/cubeVolume R) •
      (normalizedCubeMeasure Q).restrict (cubeSet R) := by
    simp only [normalizedCubeMeasure_descendant_eq_smul_restrict hR, le_refl]
  exact hrestrict.of_measure_le_smul ENNReal.ofReal_ne_top hle

/-- Projection takes exactly the actual Bochner mean on every source tile. -/
theorem hilbertCubeProjection_eq_average {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube d) (j : ℕ) (F : Vec d → E) {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth Q j) {x : Vec d} (hx : x ∈ cubeSet R) :
    hilbertCubeProjection Q j F x = hilbertCubeAverage R F := by
  classical
  unfold hilbertCubeProjection
  rw [Finset.sum_eq_single R]
  · rw [ite_eq_left hx]
  · intro S hS hSR
    have hdis := pairwiseDisjoint_descendantsAtDepth Q j hS hR hSR
    have hnot : x ∉ cubeSet S := fun hxS => Set.disjoint_left.mp hdis hxS hx
    rw [ite_eq_right hnot]
  · intro hnot
    exact (hnot hR).elim

theorem hilbertCubeProjection_memLp {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube d) (j : ℕ) (F : Vec d → E) (p : ℝ≥0∞) :
    MemLp (hilbertCubeProjection Q j F) p (normalizedCubeMeasure Q) := by
  classical
  unfold hilbertCubeProjection
  apply memLp_finsetSum
  intro R _
  exact (memLp_const (hilbertCubeAverage R F)).indicator (measurableSet_cubeSet R)

/-- Projection commutes with bounded linear maps, on actual Bochner cell means. -/
theorem hilbertCubeProjection_map {d : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (Q : TriadicCube d) (j : ℕ) (L : E →L[ℝ] F) {u : Vec d → E}
    (hu : MemLp u 2 (normalizedCubeMeasure Q)) :
    hilbertCubeProjection Q j (fun x => L (u x)) = fun x => L (hilbertCubeProjection Q j u x) := by
  classical
  funext x
  unfold hilbertCubeProjection
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro R hR
  split_ifs with hx
  · exact hilbertCubeAverage_map R L (hilbert_memLp_descendant hR hu)
  · exact (map_zero L).symm

/-- Every bounded scalar Hilbert coordinate sees the source scalar projection. -/
theorem hilbertCubeProjection_inner {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (Q : TriadicCube d) (j : ℕ)
    (e : E) {u : Vec d → E} (hu : MemLp u 2 (normalizedCubeMeasure Q)) :
    cubeProjection Q j (fun x => inner ℝ e (u x)) =
      fun x => inner ℝ e (hilbertCubeProjection Q j u x) := by
  rw [← hilbertCubeProjection_real]
  exact hilbertCubeProjection_map Q j (innerSL ℝ e) hu

/-- Cube normalization preserves the L2 membership of a Hilbert-valued field. -/
theorem hilbert_memLp_normalized_of_open {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) {F : Vec d → E} (hF : MemLp F 2 (volume.restrict (openCubeSet Q))) :
    MemLp F 2 (normalizedCubeMeasure Q) := by
  rw [← volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] at hF
  exact hF.smul_measure ENNReal.ofReal_ne_top

theorem HilbertH1Function.memL2_normalized {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (Q : TriadicCube d)
    (u : HilbertH1Function (openCubeSet Q) E) : MemLp u.toFun 2 (normalizedCubeMeasure Q) :=
  hilbert_memLp_normalized_of_open Q u.memL2

theorem HilbertH1Function.gradMemL2_normalized {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (Q : TriadicCube d)
    (u : HilbertH1Function (openCubeSet Q) E) (i : Fin d) :
    MemLp (fun x => u.grad x i) 2 (normalizedCubeMeasure Q) :=
  hilbert_memLp_normalized_of_open Q (u.gradMemL2 i)

end

end ASDExplicitGamma.Triadic
