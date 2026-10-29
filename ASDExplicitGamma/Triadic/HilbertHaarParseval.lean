module

public import ASDExplicitGamma.Triadic.HilbertHaarAlgebra
public import ASDExplicitGamma.Triadic.HilbertSeparableReduction
public import ASDExplicitGamma.Triadic.HaarParseval

/-! Complete Hilbert-valued Haar Parseval and strict residual tails. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
open Homogenization MeasureTheory
open scoped BigOperators
noncomputable section

/-- Complete strict-tail identity in countable Hilbert coordinates. -/
theorem hilbert_residual_tail_of_basis {d : ℕ} {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [Countable ι] (Q : TriadicCube d)
    (b : HilbertBasis ι ℝ E) {F : Vec d → E} (hF : MemLp F 2 (normalizedCubeMeasure Q)) :
    Summable (fun n => hilbertEnergy Q (hilbertCubeIncrement Q n F)) ∧
    (∑' n, hilbertEnergy Q (hilbertCubeIncrement Q n F)) = hilbertEnergy Q F ∧
    ∀ j, hilbertEnergy Q (fun x => F x-hilbertCubeProjection Q j F x) =
      ∑' n, hilbertEnergy Q (hilbertCubeIncrement Q (n+j+1) F) := by
  let a : ι → ℕ → ℝ := fun i n => energy Q (cubeIncrement Q n (fun x => inner ℝ (b i) (F x)))
  have hi (i : ι) : MemLp (fun x => inner ℝ (b i) (F x)) 2 (normalizedCubeMeasure Q) :=
    (innerSL ℝ (b i)).comp_memLp' hF
  have hprod : Summable (Function.uncurry a) := by
    apply (summable_prod_of_nonneg (f := Function.uncurry a) (fun p => energy_nonneg Q _)).2
    constructor
    · intro i
      change Summable (fun n => energy Q (cubeIncrement Q n (fun x => inner ℝ (b i) (F x))))
      exact summable_cubeIncrement_energy Q (f := fun x => inner ℝ (b i) (F x)) (hi i)
    · change Summable (fun i => ∑' n, energy Q (cubeIncrement Q n (fun x => inner ℝ (b i) (F x))))
      simp_rw [tsum_cubeIncrement_energy Q (hi _)]
      exact hilbertEnergy_coordinates_summable Q b b.orthonormal hF
  have hinc (n : ℕ) : hilbertEnergy Q (hilbertCubeIncrement Q n F) = ∑' i, a i n := by
    rw [hilbertEnergy_eq_tsum_coordinates Q b (hilbertCubeIncrement_memLp Q n F)]
    apply tsum_congr
    intro i
    rw [← hilbertCubeIncrement_inner Q n (b i) hF]
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [hinc]
    exact hprod.prod_symm.prod
  · simp_rw [hinc]
    rw [hprod.tsum_comm]
    simp_rw [a, tsum_cubeIncrement_energy Q (hi _)]
    exact (hilbertEnergy_eq_tsum_coordinates Q b hF).symm
  · intro j
    have ht : Summable (Function.uncurry (fun i n => a i (n+j+1))) := by
      apply (summable_prod_of_nonneg (f := Function.uncurry (fun i n => a i (n+j+1))) (fun p => energy_nonneg Q _)).2
      constructor
      · intro i
        simpa only [Function.uncurry, a, Nat.add_assoc] using (summable_nat_add_iff (j+1)).2 (summable_cubeIncrement_energy Q (f := fun x => inner ℝ (b i) (F x)) (hi i))
      · apply hprod.prod.of_nonneg_of_le (fun i => tsum_nonneg fun n => energy_nonneg Q _)
        intro i
        have h := (summable_cubeIncrement_energy Q (f := fun x => inner ℝ (b i) (F x)) (hi i)).sum_add_tsum_nat_add (j+1)
        have hn : 0 ≤ ∑ n ∈ Finset.range (j+1), a i n := Finset.sum_nonneg fun n _ => energy_nonneg Q _
        change (∑ n ∈ Finset.range (j+1), a i n)+(∑' n, a i (n+(j+1))) = ∑' n, a i n at h
        change (∑' n, a i (n+j+1)) ≤ ∑' n, a i n
        simp only [← Nat.add_assoc] at h
        linarith only [h, hn]
    rw [hilbertEnergy_eq_tsum_coordinates Q b (F := fun x => F x-hilbertCubeProjection Q j F x) (hF.sub (hilbertCubeProjection_memLp Q j F 2))]
    have he (i : ι) : energy Q (fun x => inner ℝ (b i) (F x-hilbertCubeProjection Q j F x)) = ∑' n, a i (n+j+1) := by
      have heq : (fun x => inner ℝ (b i) (F x-hilbertCubeProjection Q j F x)) =
          fun x => inner ℝ (b i) (F x)-cubeProjection Q j (fun y => inner ℝ (b i) (F y)) x := by
        funext x
        rw [inner_sub_right, ← congrFun (hilbertCubeProjection_inner Q j (b i) hF) x]
      rw [heq]
      exact energy_residual_eq_tsum_increments Q j (hi i)
    simp_rw [he, hinc]
    exact ht.tsum_comm.symm

/-- Complete Parseval and exact residual tails for arbitrary real Hilbert spaces.
Strong measurability supplies the separable closed subspace used in the proof. -/
theorem hilbert_haar_parseval {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (Q : TriadicCube d)
    {F : Vec d → E} (hF : MemLp F 2 (normalizedCubeMeasure Q)) :
    Summable (fun n => hilbertEnergy Q (hilbertCubeIncrement Q n F)) ∧
    (∑' n, hilbertEnergy Q (hilbertCubeIncrement Q n F)) = hilbertEnergy Q F ∧
    ∀ j, hilbertEnergy Q (fun x => F x-hilbertCubeProjection Q j F x) =
      ∑' n, hilbertEnergy Q (hilbertCubeIncrement Q (n+j+1) F) := by
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
  have hp (j : ℕ) : (fun x => ((hilbertCubeProjection Q j v x : V) : E)) = hilbertCubeProjection Q j F := by
    have h := hilbertCubeProjection_map Q j V.subtypeL hv
    change hilbertCubeProjection Q j (fun x => (v x : E)) = _ at h
    rw [hilbertCubeProjection_congr_ae Q j he] at h
    exact h.symm
  have hi (j : ℕ) : hilbertEnergy Q (hilbertCubeIncrement Q j v) = hilbertEnergy Q (hilbertCubeIncrement Q j F) := by
    have h := hilbertCubeIncrement_map Q j V.subtypeL hv
    change hilbertCubeIncrement Q j (fun x => (v x : E)) = _ at h
    rw [hilbertCubeIncrement_congr_ae Q j he] at h
    change hilbertEnergy Q (fun x => ((hilbertCubeIncrement Q j v x : V) : E)) = _
    exact congrArg (hilbertEnergy Q) h.symm
  have hres (j : ℕ) : hilbertEnergy Q (fun x => v x-hilbertCubeProjection Q j v x) =
      hilbertEnergy Q (fun x => F x-hilbertCubeProjection Q j F x) := by
    change hilbertEnergy Q (fun x => ((v x-hilbertCubeProjection Q j v x : V) : E)) = _
    apply hilbertEnergy_congr_ae
    filter_upwards [he] with x hx
    change (v x : E)-((hilbertCubeProjection Q j v x : V) : E) = _
    rw [hx, congrFun (hp j) x]
  have h := hilbert_residual_tail_of_basis Q b hv
  have hen : hilbertEnergy Q v = hilbertEnergy Q F := hilbertEnergy_congr_ae Q he
  simpa only [hi, hres, hen] using h

end
end ASDExplicitGamma.Triadic
