module

public import ASDExplicitGamma.Triadic.HilbertH1Maps

/-! Functoriality and equivalence-class invariance of Hilbert Haar increments. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
open Homogenization MeasureTheory
noncomputable section

 theorem hilbertCubeIncrement_memLp {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (Q : TriadicCube d) (j : ℕ) (F : Vec d → E) :
    MemLp (hilbertCubeIncrement Q j F) 2 (normalizedCubeMeasure Q) := by
  cases j with
  | zero => exact hilbertCubeProjection_memLp Q 0 F 2
  | succ j => exact (hilbertCubeProjection_memLp Q (j+1) F 2).sub (hilbertCubeProjection_memLp Q j F 2)

 theorem hilbertCubeIncrement_map {d : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (Q : TriadicCube d) (j : ℕ) (L : E →L[ℝ] F) {u : Vec d → E}
    (hu : MemLp u 2 (normalizedCubeMeasure Q)) :
    hilbertCubeIncrement Q j (fun x => L (u x)) = fun x => L (hilbertCubeIncrement Q j u x) := by
  cases j <;> simp only [hilbertCubeIncrement, hilbertCubeProjection_map Q _ L hu, map_sub]

 theorem hilbertCubeIncrement_inner {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (Q : TriadicCube d) (j : ℕ) (e : E)
    {u : Vec d → E} (hu : MemLp u 2 (normalizedCubeMeasure Q)) :
    cubeIncrement Q j (fun x => inner ℝ e (u x)) =
      fun x => inner ℝ e (hilbertCubeIncrement Q j u x) := by
  rw [← hilbertCubeIncrement_real]
  exact hilbertCubeIncrement_map Q j (innerSL ℝ e) hu

 theorem hilbertCubeProjection_congr_ae {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (Q : TriadicCube d) (j : ℕ) {u v : Vec d → E}
    (huv : u =ᵐ[normalizedCubeMeasure Q] v) : hilbertCubeProjection Q j u = hilbertCubeProjection Q j v := by
  classical
  funext x
  unfold hilbertCubeProjection
  apply Finset.sum_congr rfl
  intro R hR
  have hdom : normalizedCubeMeasure R ≤ ENNReal.ofReal (cubeVolume Q/cubeVolume R) •
      (normalizedCubeMeasure Q).restrict (cubeSet R) := by
    rw [normalizedCubeMeasure_descendant_eq_smul_restrict hR]
  have h : u =ᵐ[normalizedCubeMeasure R] v :=
    by
      rw [normalizedCubeMeasure_descendant_eq_smul_restrict hR]
      exact Measure.ae_smul_measure huv.restrict _
  rw [hilbertCubeAverage_congr_ae R h]

 theorem hilbertCubeIncrement_congr_ae {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (Q : TriadicCube d) (j : ℕ) {u v : Vec d → E}
    (huv : u =ᵐ[normalizedCubeMeasure Q] v) : hilbertCubeIncrement Q j u = hilbertCubeIncrement Q j v := by
  cases j <;> simp only [hilbertCubeIncrement, hilbertCubeProjection_congr_ae Q _ huv]

end
end ASDExplicitGamma.Triadic
