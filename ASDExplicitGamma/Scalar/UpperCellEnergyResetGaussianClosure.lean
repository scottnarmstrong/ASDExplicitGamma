module

public import ASDExplicitGamma.Gaussian.DerivativeLawFamilies
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Topology.Sequences

/-! Centered Gaussianity on the actual closed L2 span, needed to retain
Gaussian moments after the stationary full-flux projection. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory Filter ASDExplicitGamma.Gaussian
open scoped Topology
noncomputable section

/-- Finite L2 linear combinations of a jointly centered Gaussian family
retain their actual centered Gaussian marginal laws. -/
theorem upper_cell_reset_gaussian_span
    {Ω : Type*} {I : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : I → Lp ℝ 2 μ)
    (hX : IsCenteredGaussianFamily μ (fun i ω => X i ω))
    (F : Lp ℝ 2 μ) (hF : F ∈ Submodule.span ℝ (Set.range X)) :
    ∃ v : NNReal, μ.map F=gaussianReal 0 v := by
  classical
  rw [←Finsupp.range_linearCombination ℝ] at hF
  obtain ⟨c,rfl⟩ := hF
  obtain ⟨v,hv⟩ := hX.2 (fun i : ↥c.support => i.val) (fun i : ↥c.support => c i.val)
  refine ⟨v,?_⟩
  rw [←hv]
  apply Measure.map_congr
  filter_upwards [Lp.coeFn_linearCombination c X] with ω hω
  rw [hω]
  simp only [Finsupp.linearCombination_apply,Finsupp.sum,Finset.sum_apply,
    Pi.smul_apply,smul_eq_mul]
  exact (Finset.sum_coe_sort c.support (fun i => c i*X i ω)).symm

/-- Every member of the complete L2 first-chaos span has an actual centered
Gaussian law. The proof extracts an AE-convergent subsequence from the actual
L2 approximation, rather than imposing a Gaussian hypothesis on its limit. -/
theorem upper_cell_reset_gaussian_closed_span
    {Ω : Type*} {I : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : I → Lp ℝ 2 μ)
    (hX : IsCenteredGaussianFamily μ (fun i ω => X i ω))
    (F : Lp ℝ 2 μ)
    (hF : F ∈ (Submodule.span ℝ (Set.range X)).topologicalClosure) :
    ∃ v : NNReal, μ.map F=gaussianReal 0 v := by
  change F ∈ closure (Submodule.span ℝ (Set.range X) : Set (Lp ℝ 2 μ)) at hF
  obtain ⟨f,hf,ht⟩ := mem_closure_iff_seq_limit.mp hF
  obtain ⟨ns,_hns,hns⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
  have hlaw (n : ℕ) := upper_cell_reset_gaussian_span μ X hX (f (ns n)) (hf (ns n))
  choose v hv using hlaw
  obtain ⟨V,_hV,hV,_hv⟩ := exists_gaussianReal_map_of_ae_limit μ
    (fun n ω => f (ns n) ω) F v
    (fun n => (Lp.memLp (f (ns n))).aestronglyMeasurable.aemeasurable)
    (Lp.memLp F).aestronglyMeasurable.aemeasurable hv hns
  exact ⟨Real.toNNReal V,hV⟩

end
end ASDExplicitGamma.Scalar
