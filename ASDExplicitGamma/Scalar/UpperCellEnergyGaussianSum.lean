module

public import ASDExplicitGamma.Gaussian.DerivativeLawFamilies
public import Mathlib.Probability.Independence.Basic

/-! Joint Gaussian laws for finite bands are summed before any supremum. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory ASDExplicitGamma.Gaussian
open scoped BigOperators
noncomputable section

/-- A finite sum of independent centered Gaussian real variables has the
sum of their variances, including the empty band. -/
theorem upper_cell_independent_gaussian_sum {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) (v : ι → NNReal)
    (hind : iIndepFun X μ) (hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 (v i)) μ)
    (s : Finset ι) :
    HasLaw (fun ω => ∑ i ∈ s,X i ω) (gaussianReal 0 (∑ i ∈ s,v i)) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨aemeasurable_const,by simp⟩
  | @insert i s hi ih =>
    have hsum : (fun ω => ∑ j ∈ s,X j ω) = ∑ j ∈ s,X j := by
      funext ω; simp only [Finset.sum_apply]
    have hind' : IndepFun (X i) (fun ω => ∑ j ∈ s,X j ω) μ := by
      rw [hsum]
      exact (hind.indepFun_finsetSum_of_notMem₀ (fun j => (hlaw j).aemeasurable) hi).symm
    have hmap := gaussianReal_add_gaussianReal_of_indepFun hind' (hlaw i) ih
    refine ⟨?_,?_⟩
    · exact Finset.aemeasurable_fun_sum _ (fun j _ => (hlaw j).aemeasurable)
    · change μ.map (fun ω => X i ω + ∑ j ∈ s,X j ω) = _ at hmap
      simpa only [Finset.sum_insert hi,zero_add] using hmap

/-- Independent Gaussian families may be combined into one weighted band
family, keeping all cross-point and mixed derivative observations joint. -/
theorem upper_cell_independent_gaussian_family_sum
    {Ω ι E I : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → E)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (obs : I → E → ℝ) (hobs : ∀ o, Measurable (obs o))
    (hgauss : ∀ i, IsCenteredGaussianFamily (μ.map (X i)) obs)
    (s : Finset ι) (w : ι → ℝ) :
    IsCenteredGaussianFamily μ (fun o ω => ∑ i ∈ s,w i*obs o (X i ω)) := by
  classical
  refine ⟨fun o => (Finset.measurable_sum _ (fun i _ =>
    ((hobs o).comp (hX i)).const_mul (w i))).aemeasurable,?_⟩
  intro J _ o t
  let Y := fun i x => ∑ j : J,(t j*w i)*obs (o j) x
  have hY (i : ι) : Measurable (Y i) :=
    Finset.measurable_sum _ (fun j _ => (hobs (o j)).const_mul _)
  have hlaw (i : ι) : ∃ v : NNReal,HasLaw (fun ω => Y i (X i ω)) (gaussianReal 0 v) μ := by
    obtain ⟨v,hv⟩ := (hgauss i).2 o (fun j => t j*w i)
    refine ⟨v,((hY i).comp (hX i)).aemeasurable,?_⟩
    change μ.map (Y i ∘ X i) = _
    rw [← Measure.map_map (hY i) (hX i)]
    exact hv
  choose v hv using hlaw
  have hh := upper_cell_independent_gaussian_sum μ (fun i ω => Y i (X i ω)) v
    (hind.comp Y hY) hv s
  refine ⟨∑ i ∈ s,v i,?_⟩
  have heq : (fun ω => ∑ j : J,t j*(∑ i ∈ s,w i*obs (o j) (X i ω))) =
      (fun ω => ∑ i ∈ s,Y i (X i ω)) := by
    funext ω
    simp only [Y,Finset.mul_sum,←mul_assoc]
    rw [Finset.sum_comm]
  rw [heq]
  exact hh.map_eq

end
end ASDExplicitGamma.Scalar
