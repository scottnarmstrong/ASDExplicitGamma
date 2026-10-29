module

public import ASDExplicitGamma.Triadic.HilbertOperatorSobolev

/-! Orthogonal mean/residual energy decomposition on arbitrary real Hilbert spaces. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
open Homogenization MeasureTheory
open scoped BigOperators
noncomputable section

 theorem hilbert_projection_residual_energy_of_basis {d : ℕ} {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [Countable ι] (Q : TriadicCube d) (j : ℕ)
    (b : HilbertBasis ι ℝ E) {F : Vec d → E} (hF : MemLp F 2 (normalizedCubeMeasure Q)) :
    hilbertEnergy Q (hilbertCubeProjection Q j F)+hilbertEnergy Q (fun x => F x-hilbertCubeProjection Q j F x) = hilbertEnergy Q F := by
  have hp := hilbertCubeProjection_memLp Q j F 2
  have hr : MemLp (fun x => F x-hilbertCubeProjection Q j F x) 2 (normalizedCubeMeasure Q) := hF.sub hp
  rw [hilbertEnergy_eq_tsum_coordinates Q b hp, hilbertEnergy_eq_tsum_coordinates Q b hr,
    hilbertEnergy_eq_tsum_coordinates Q b hF,
    ← (hilbertEnergy_coordinates_summable Q b b.orthonormal hp).tsum_add
      (hilbertEnergy_coordinates_summable Q b b.orthonormal hr)]
  apply tsum_congr
  intro i
  have heq : (fun x => inner ℝ (b i) (F x-hilbertCubeProjection Q j F x)) =
      fun x => inner ℝ (b i) (F x)-cubeProjection Q j (fun y => inner ℝ (b i) (F y)) x := by
    funext x
    rw [inner_sub_right, ← congrFun (hilbertCubeProjection_inner Q j (b i) hF) x]
  rw [heq, ← hilbertCubeProjection_inner Q j (b i) hF,
    energy_residual Q j (f := fun x => inner ℝ (b i) (F x)) ((innerSL ℝ (b i)).comp_memLp' hF)]
  ring

 theorem hilbert_projection_residual_energy {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (Q : TriadicCube d) (j : ℕ)
    {F : Vec d → E} (hF : MemLp F 2 (normalizedCubeMeasure Q)) :
    hilbertEnergy Q (hilbertCubeProjection Q j F)+hilbertEnergy Q (fun x => F x-hilbertCubeProjection Q j F x) = hilbertEnergy Q F := by
  obtain ⟨V, hc, hs, hm⟩ := exists_separable_closed_subspace_ae hF.aestronglyMeasurable
  let instClosedV : IsClosed (V : Set E) := hc
  let instCompleteV : CompleteSpace V := IsClosed.completeSpace_coe
  let instSeparableV : TopologicalSpace.SeparableSpace V := hs.separableSpace
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℝ V
  let instCountableW : Countable w := hilbert_orthonormal_countable b b.orthonormal
  let v : Vec d → V := fun x => V.orthogonalProjectionOnto (F x)
  have hv : MemLp v 2 (normalizedCubeMeasure Q) := V.orthogonalProjectionOnto.comp_memLp' hF
  have he : (fun x => (v x : E)) =ᵐ[normalizedCubeMeasure Q] F := by
    filter_upwards [hm] with x hx
    exact congrArg Subtype.val (V.orthogonalProjectionOnto_mem_subspace_eq_self ⟨F x,hx⟩)
  have hp : (fun x => ((hilbertCubeProjection Q j v x : V) : E)) = hilbertCubeProjection Q j F := by
    have h := hilbertCubeProjection_map Q j V.subtypeL hv
    change hilbertCubeProjection Q j (fun x => (v x : E)) = _ at h
    rw [hilbertCubeProjection_congr_ae Q j he] at h
    exact h.symm
  have hproj : hilbertEnergy Q (hilbertCubeProjection Q j v) = hilbertEnergy Q (hilbertCubeProjection Q j F) := by
    change hilbertEnergy Q (fun x => ((hilbertCubeProjection Q j v x : V) : E)) = _
    rw [hp]
  have hres : hilbertEnergy Q (fun x => v x-hilbertCubeProjection Q j v x) = hilbertEnergy Q (fun x => F x-hilbertCubeProjection Q j F x) := by
    change hilbertEnergy Q (fun x => ((v x-hilbertCubeProjection Q j v x : V) : E)) = _
    apply hilbertEnergy_congr_ae
    filter_upwards [he] with x hx
    change (v x : E)-((hilbertCubeProjection Q j v x : V) : E) = _
    rw [hx, congrFun hp x]
  have hen : hilbertEnergy Q v = hilbertEnergy Q F := hilbertEnergy_congr_ae Q he
  simpa only [hproj, hres, hen] using hilbert_projection_residual_energy_of_basis Q j b hv

 theorem hilbertEnergy_projection_le {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (Q : TriadicCube d) (j : ℕ)
    {F : Vec d → E} (hF : MemLp F 2 (normalizedCubeMeasure Q)) :
    hilbertEnergy Q (hilbertCubeProjection Q j F) ≤ hilbertEnergy Q F := by
  have h := hilbert_projection_residual_energy Q j hF
  linarith only [h, hilbertEnergy_nonneg Q (fun x => F x-hilbertCubeProjection Q j F x)]

end
end ASDExplicitGamma.Triadic
