module

public import ASDExplicitGamma.Triadic.HilbertCubePoincare
public import ASDExplicitGamma.Triadic.HilbertHaarAlgebra

/-! Sharp Hilbert-valued Poincare on every complete triadic cell partition. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

/-- Sharp Poincare on a Hilbert space with a countable Hilbert basis.
The separability restriction is removed separately at the theorem. -/
theorem hilbert_cell_poincare_of_basis {d : ℕ} {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [Countable ι] (Q : TriadicCube d) (j : ℕ)
    (b : HilbertBasis ι ℝ E) (u : HilbertH1Function (openCubeSet Q) E) :
    hilbertEnergy Q (fun x => u.toFun x-hilbertCubeProjection Q j u.toFun x) ≤
      (cubeScaleFactor Q^2/(9^j*Real.pi^2)) * hilbertGradientEnergy Q u.grad := by
  have hu := u.memL2_normalized Q
  have hfluct : MemLp (fun x => u.toFun x-hilbertCubeProjection Q j u.toFun x) 2 (normalizedCubeMeasure Q) :=
    hu.sub (hilbertCubeProjection_memLp Q j u.toFun 2)
  rw [hilbertEnergy_eq_tsum_coordinates Q b hfluct]
  apply Real.tsum_le_of_sum_le (fun i => energy_nonneg Q (fun x =>
    inner ℝ (b i) (u.toFun x-hilbertCubeProjection Q j u.toFun x)))
  intro s
  have hcoord (i : ι) : (fun x => inner ℝ (b i) (u.toFun x-hilbertCubeProjection Q j u.toFun x)) =
      fun x => (u.scalar (b i)).toFun x-cubeProjection Q j (u.scalar (b i)).toFun x := by
    funext x
    rw [inner_sub_right, ← congrFun (hilbertCubeProjection_inner Q j (b i) hu) x]
    rfl
  have hscalar (i : ι) : energy Q (fun x => inner ℝ (b i) (u.toFun x-hilbertCubeProjection Q j u.toFun x)) ≤
      (cubeScaleFactor Q^2/(9^j*Real.pi^2)) * ∑ a, energy Q (fun x => inner ℝ (b i) (u.grad x a)) := by
    rw [hcoord]
    exact cell_poincare_of_weakGradient Q j (u.scalar (b i)).memL2
      (u.scalar (b i)).gradMemL2 (u.scalar (b i)).hasWeakGradient
  calc
    _ ≤ ∑ i ∈ s, (cubeScaleFactor Q^2/(9^j*Real.pi^2)) * ∑ a, energy Q (fun x => inner ℝ (b i) (u.grad x a)) :=
      Finset.sum_le_sum fun i _ => hscalar i
    _ = (cubeScaleFactor Q^2/(9^j*Real.pi^2)) * ∑ a, ∑ i ∈ s, energy Q (fun x => inner ℝ (b i) (u.grad x a)) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ =>
      hilbertEnergy_coordinates_finset_le Q b b.orthonormal (u.gradMemL2_normalized Q a) s) (div_nonneg (sq_nonneg _) (mul_nonneg (by positivity) (sq_nonneg _)))

/-- Sharp cube Poincare for every real Hilbert-valued H1 field, without a
separability or finite-dimensionality premise on the ambient Hilbert space. -/
theorem hilbert_cell_poincare {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (Q : TriadicCube d) (j : ℕ)
    (u : HilbertH1Function (openCubeSet Q) E) :
    hilbertEnergy Q (fun x => u.toFun x-hilbertCubeProjection Q j u.toFun x) ≤
      (cubeScaleFactor Q^2/(9^j*Real.pi^2)) * hilbertGradientEnergy Q u.grad := by
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
  have hprojection : (fun x => ((hilbertCubeProjection Q j v.toFun x : V) : E)) = hilbertCubeProjection Q j u.toFun := by
    have h := hilbertCubeProjection_map Q j V.subtypeL (v.memL2_normalized Q)
    change hilbertCubeProjection Q j (fun x => (v.toFun x : E)) = _ at h
    rw [hilbertCubeProjection_congr_ae Q j hval] at h
    exact h.symm
  have henergy : hilbertEnergy Q (fun x => v.toFun x-hilbertCubeProjection Q j v.toFun x) =
      hilbertEnergy Q (fun x => u.toFun x-hilbertCubeProjection Q j u.toFun x) := by
    change hilbertEnergy Q (fun x => ((v.toFun x-hilbertCubeProjection Q j v.toFun x : V) : E)) = _
    apply hilbertEnergy_congr_ae
    filter_upwards [hval] with x hx
    change (v.toFun x : E)-((hilbertCubeProjection Q j v.toFun x : V) : E) = _
    rw [hx, congrFun hprojection x]
  have hgrad : hilbertGradientEnergy Q v.grad ≤ hilbertGradientEnergy Q u.grad := by
    apply Finset.sum_le_sum
    intro i _
    exact hilbertEnergy_map_le Q V.orthogonalProjectionOnto V.orthogonalProjectionOnto_norm_le
      (u.gradMemL2_normalized Q i)
  rw [← henergy]
  exact (hilbert_cell_poincare_of_basis Q j b v).trans (mul_le_mul_of_nonneg_left hgrad (div_nonneg (sq_nonneg _) (mul_nonneg (by positivity) (sq_nonneg _))))

end

end ASDExplicitGamma.Triadic
