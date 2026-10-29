module

public import ASDExplicitGamma.Triadic.HilbertSeparableReduction
public import ASDExplicitGamma.Triadic.HilbertH1Maps

/-! Sharp Hilbert-valued cube Poincare from genuine scalar weak derivatives. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

/-- The normalized Frobenius L2 energy of a Hilbert-valued gradient. -/
def hilbertGradientEnergy {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) (G : Vec d → Fin d → E) : ℝ :=
  ∑ i, hilbertEnergy Q (fun x => G x i)

/-- Scalar inner coordinates of the actual Bochner mean are scalar cell means. -/
theorem hilbertCubeAverage_inner {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (Q : TriadicCube d) (e : E)
    {F : Vec d → E} (hF : MemLp F 2 (normalizedCubeMeasure Q)) :
    cubeAverage Q (fun x => inner ℝ e (F x)) = inner ℝ e (hilbertCubeAverage Q F) := by
  rw [← hilbertCubeAverage_real]
  exact hilbertCubeAverage_map Q (innerSL ℝ e) hF

/-- Sharp Poincare on a Hilbert space with a countable Hilbert basis.
The separability restriction is removed separately at the theorem. -/
theorem hilbert_cube_poincare_of_basis {d : ℕ} {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [Countable ι] (Q : TriadicCube d)
    (b : HilbertBasis ι ℝ E) (u : HilbertH1Function (openCubeSet Q) E) :
    hilbertEnergy Q (fun x => u.toFun x-hilbertCubeAverage Q u.toFun) ≤
      (cubeScaleFactor Q/Real.pi)^2 * hilbertGradientEnergy Q u.grad := by
  have hu := u.memL2_normalized Q
  have hfluct : MemLp (fun x => u.toFun x-hilbertCubeAverage Q u.toFun) 2 (normalizedCubeMeasure Q) :=
    hu.sub (memLp_const _)
  rw [hilbertEnergy_eq_tsum_coordinates Q b hfluct]
  apply Real.tsum_le_of_sum_le (fun i => energy_nonneg Q (fun x =>
    inner ℝ (b i) (u.toFun x-hilbertCubeAverage Q u.toFun)))
  intro s
  have hcoord (i : ι) : (fun x => inner ℝ (b i) (u.toFun x-hilbertCubeAverage Q u.toFun)) =
      fun x => (u.scalar (b i)).toFun x-cubeAverage Q (u.scalar (b i)).toFun := by
    funext x
    rw [inner_sub_right, ← hilbertCubeAverage_inner Q (b i) hu]
    rfl
  have hscalar (i : ι) : energy Q (fun x => inner ℝ (b i) (u.toFun x-hilbertCubeAverage Q u.toFun)) ≤
      (cubeScaleFactor Q/Real.pi)^2 * ∑ a, energy Q (fun x => inner ℝ (b i) (u.grad x a)) := by
    rw [hcoord]
    exact cube_poincare Q (memLp_normalized_of_memL2On (u.scalar (b i)).memL2)
      (fun a => memLp_normalized_of_memL2On ((u.scalar (b i)).gradMemL2 a))
      (u.scalar (b i)).hasWeakGradient
  calc
    _ ≤ ∑ i ∈ s, (cubeScaleFactor Q/Real.pi)^2 * ∑ a, energy Q (fun x => inner ℝ (b i) (u.grad x a)) :=
      Finset.sum_le_sum fun i _ => hscalar i
    _ = (cubeScaleFactor Q/Real.pi)^2 * ∑ a, ∑ i ∈ s, energy Q (fun x => inner ℝ (b i) (u.grad x a)) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ =>
      hilbertEnergy_coordinates_finset_le Q b b.orthonormal (u.gradMemL2_normalized Q a) s) (sq_nonneg _)

/-- Sharp cube Poincare for every real Hilbert-valued H1 field, without a
separability or finite-dimensionality premise on the ambient Hilbert space. -/
theorem hilbert_cube_poincare {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (Q : TriadicCube d)
    (u : HilbertH1Function (openCubeSet Q) E) :
    hilbertEnergy Q (fun x => u.toFun x-hilbertCubeAverage Q u.toFun) ≤
      (cubeScaleFactor Q/Real.pi)^2 * hilbertGradientEnergy Q u.grad := by
  obtain ⟨V, hclosed, hsep, hmem⟩ := exists_separable_closed_subspace_ae (u.memL2_normalized Q).aestronglyMeasurable
  let instClosedV : IsClosed (V : Set E) := hclosed
  let instCompleteV : CompleteSpace V := IsClosed.completeSpace_coe
  let instSeparableV : TopologicalSpace.SeparableSpace V := hsep.separableSpace
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℝ V
  let instCountableW : Countable w := hilbert_orthonormal_countable b b.orthonormal
  let v := u.map V.orthogonalProjectionOnto
  have hval : (fun x => (v.toFun x : E)) =ᵐ[normalizedCubeMeasure Q] u.toFun := by
    filter_upwards [hmem] with x hx
    exact congrArg Subtype.val (V.orthogonalProjectionOnto_mem_subspace_eq_self ⟨u.toFun x,hx⟩)
  have hmean : ((hilbertCubeAverage Q v.toFun : V) : E) = hilbertCubeAverage Q u.toFun := by
    have h := hilbertCubeAverage_map Q V.subtypeL (v.memL2_normalized Q)
    change hilbertCubeAverage Q (fun x => (v.toFun x : E)) =
      ((hilbertCubeAverage Q v.toFun : V) : E) at h
    rw [hilbertCubeAverage_congr_ae Q hval] at h
    exact h.symm
  have henergy : hilbertEnergy Q (fun x => v.toFun x-hilbertCubeAverage Q v.toFun) =
      hilbertEnergy Q (fun x => u.toFun x-hilbertCubeAverage Q u.toFun) := by
    change hilbertEnergy Q (fun x => ((v.toFun x-hilbertCubeAverage Q v.toFun : V) : E)) = _
    apply hilbertEnergy_congr_ae
    filter_upwards [hval] with x hx
    change (v.toFun x : E)-((hilbertCubeAverage Q v.toFun : V) : E) = _
    rw [hx, hmean]
  have hgrad : hilbertGradientEnergy Q v.grad ≤ hilbertGradientEnergy Q u.grad := by
    apply Finset.sum_le_sum
    intro i _
    exact hilbertEnergy_map_le Q V.orthogonalProjectionOnto V.orthogonalProjectionOnto_norm_le
      (u.gradMemL2_normalized Q i)
  rw [← henergy]
  exact (hilbert_cube_poincare_of_basis Q b v).trans (mul_le_mul_of_nonneg_left hgrad (sq_nonneg _))

end

end ASDExplicitGamma.Triadic
