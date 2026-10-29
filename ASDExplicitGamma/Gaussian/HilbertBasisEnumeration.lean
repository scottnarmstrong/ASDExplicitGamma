module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! # Countable Hilbert bases and zero-padded Gaussian direction sequences -/

@[expose] public section

open Set Function
open scoped Topology

namespace ASDExplicitGamma.Gaussian

/-- An orthonormal family in a separable real Hilbert space is countable. -/
theorem orthonormal_countable {W ι : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [SecondCountableTopology W] (e : ι → W) (he : Orthonormal ℝ e) : Countable ι := by
  let : TopologicalSpace ι := ⊥
  let : DiscreteTopology ι := ⟨rfl⟩
  have hsep : Pairwise (fun i j => (1 : ℝ) ≤ dist (e i) (e j)) := by
    intro i j hij
    have hh := norm_sub_sq_real (e i) (e j)
    rw [he.norm_eq_one, he.norm_eq_one, he.inner_eq_zero hij] at hh
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (e i - e j)]
  have hclosed := Metric.isClosedEmbedding_of_pairwise_le_dist (by norm_num : (0 : ℝ) < 1) hsep
  let : SecondCountableTopology ι := hclosed.isEmbedding.secondCountableTopology
  exact countable_of_Lindelof_of_discrete

/-- A countable direction family, zero-padded on ℕ without assuming infinite dimension. -/
noncomputable def gaussEnumerated {ι V : Type*} [Countable ι] [Zero V] (v : ι → V) : ℕ → V :=
  @Function.extend ι ℕ V (@Encodable.encode ι (Encodable.ofCountable ι)) v 0

theorem enumerated_encode {ι V : Type*} [Countable ι] [Zero V] (v : ι → V) (i : ι) :
    gaussEnumerated v (@Encodable.encode ι (Encodable.ofCountable ι) i) = v i := by
  let := Encodable.ofCountable ι
  exact Function.Injective.extend_apply Encodable.encode_injective v 0 i

/-- Zero-padding preserves square summability exactly. -/
theorem enumerated_summable_sq {ι V : Type*} [Countable ι] [NormedAddCommGroup V]
    (v : ι → V) (hv : Summable (fun i => ‖v i‖ ^ 2)) :
    Summable (fun n => ‖gaussEnumerated v n‖ ^ 2) := by
  classical
  let := Encodable.ofCountable ι
  have he : (fun n => ‖gaussEnumerated v n‖ ^ 2) =
      Function.extend Encodable.encode (fun i => ‖v i‖ ^ 2) 0 := by
    funext n
    by_cases hn : n ∈ Set.range (Encodable.encode : ι → ℕ)
    · obtain ⟨i, rfl⟩ := hn
      rw [enumerated_encode, Function.Injective.extend_apply Encodable.encode_injective]
    · rw [gaussEnumerated, Function.extend_apply' _ _ _ hn, Function.extend_apply' _ _ _ hn]
      simp
  rw [he]
  exact (summable_extend_zero Encodable.encode_injective).mpr hv

/-- Any scalar expression vanishing at zero has the same sum after enumeration. -/
theorem enumerated_tsum_apply {ι V : Type*} [Countable ι] [Zero V]
    (v : ι → V) (f : V → ℝ) (hf : f 0 = 0) :
    (∑' n, f (gaussEnumerated v n)) = ∑' i, f (v i) := by
  classical
  let := Encodable.ofCountable ι
  have he : (fun n => f (gaussEnumerated v n)) =
      Function.extend Encodable.encode (fun i => f (v i)) 0 := by
    funext n
    by_cases hn : n ∈ Set.range (Encodable.encode : ι → ℕ)
    · obtain ⟨i, rfl⟩ := hn
      rw [enumerated_encode, Function.Injective.extend_apply Encodable.encode_injective]
    · rw [gaussEnumerated, Function.extend_apply' _ _ _ hn, Function.extend_apply' _ _ _ hn]
      exact hf
  rw [he, tsum_extend_zero Encodable.encode_injective]

/-- Bounded linear maps commute with the zero-padded enumeration. -/
theorem enumerated_map {ι V E : Type*} [Countable ι]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : V →L[ℝ] E) (v : ι → V) (n : ℕ) : T (gaussEnumerated v n) = gaussEnumerated (T ∘ v) n := by
  classical
  let := Encodable.ofCountable ι
  by_cases hn : n ∈ Set.range (Encodable.encode : ι → ℕ)
  · obtain ⟨i, rfl⟩ := hn
    rw [enumerated_encode, enumerated_encode]
    rfl
  · rw [gaussEnumerated, gaussEnumerated, Function.extend_apply' _ _ _ hn, Function.extend_apply' _ _ _ hn,
      Pi.zero_apply, Pi.zero_apply, map_zero]

end ASDExplicitGamma.Gaussian
