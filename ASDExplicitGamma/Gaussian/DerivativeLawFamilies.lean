module

public import ASDExplicitGamma.Gaussian.DerivativeLawMoments

/-! Actual finite centered Gaussian families and their linear images and limits. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators
noncomputable section

/-- Every finite scalar linear combination has a centered Gaussian law, and all
observations are genuinely measurable. This is the ordinary finite-law definition. -/
def IsCenteredGaussianFamily {Ω I : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : I → Ω → ℝ) : Prop :=
  (∀ i, AEMeasurable (X i) μ) ∧
  ∀ {J : Type} [Fintype J] (x : J → I) (t : J → ℝ),
    ∃ v : NNReal, μ.map (fun ω => ∑ i, t i*X (x i) ω)=gaussianReal 0 v

 theorem IsCenteredGaussianFamily.comp {Ω I J : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : I → Ω → ℝ} (hX : IsCenteredGaussianFamily μ X) (f : J → I) :
    IsCenteredGaussianFamily μ (fun j => X (f j)) := by
  refine ⟨fun j => hX.1 (f j), ?_⟩
  intro K _ x t
  exact hX.2 (fun k => f (x k)) t

 theorem IsCenteredGaussianFamily.map_single {Ω I : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : I → Ω → ℝ} (hX : IsCenteredGaussianFamily μ X) (i : I) :
    ∃ v : NNReal, μ.map (X i)=gaussianReal 0 v := by
  obtain ⟨v,hv⟩ := hX.2 (fun _ : Fin 1 => i) (fun _ => 1)
  exact ⟨v, by simpa using hv⟩

/-- Every finite linear image of a genuine Gaussian family remains Gaussian. -/
theorem IsCenteredGaussianFamily.finite_linear_image {Ω I K : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : I → Ω → ℝ} (hX : IsCenteredGaussianFamily μ X) {A : Type} [Fintype A]
    (x : K → A → I) (c : K → A → ℝ) :
    IsCenteredGaussianFamily μ (fun k ω => ∑ a, c k a*X (x k a) ω) := by
  classical
  constructor
  · intro k
    exact Finset.aemeasurable_fun_sum Finset.univ fun a _ => aemeasurable_const.mul (hX.1 (x k a))
  · intro J _ z t
    obtain ⟨v,hv⟩ := hX.2 (fun p : J × A => x (z p.1) p.2) (fun p => t p.1*c (z p.1) p.2)
    refine ⟨v, ?_⟩
    have heq : (fun ω => ∑ i : J, t i*(∑ a, c (z i) a*X (x (z i) a) ω)) =
        fun ω => ∑ p : J × A, (t p.1*c (z p.1) p.2)*X (x (z p.1) p.2) ω := by
      funext ω
      simp only [Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
    rw [heq]
    exact hv

/-- Actual almost-sure limits preserve the complete finite joint centered Gaussian law. -/
theorem isCenteredGaussianFamily_ae_limit {Ω I : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → I → Ω → ℝ) (Z : I → Ω → ℝ)
    (hX : ∀ n, IsCenteredGaussianFamily μ (X n)) (hZ : ∀ i, AEMeasurable (Z i) μ)
    (hlim : ∀ i, ∀ᵐ ω ∂μ, Tendsto (fun n => X n i ω) atTop (𝓝 (Z i ω))) :
    IsCenteredGaussianFamily μ Z := by
  classical
  refine ⟨hZ, ?_⟩
  intro J _ x t
  let Y := fun n ω => ∑ i : J, t i*X n (x i) ω
  let W := fun ω => ∑ i : J, t i*Z (x i) ω
  have hY (n : ℕ) : AEMeasurable (Y n) μ :=
    Finset.aemeasurable_fun_sum Finset.univ fun i _ => aemeasurable_const.mul ((hX n).1 (x i))
  have hW : AEMeasurable W μ := Finset.aemeasurable_fun_sum Finset.univ fun i _ => aemeasurable_const.mul (hZ (x i))
  have hlaw (n : ℕ) : ∃ v : NNReal, μ.map (Y n)=gaussianReal 0 v := (hX n).2 x t
  choose v hv using hlaw
  have hYW : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (𝓝 (W ω)) := by
    have h := ae_all_iff.2 (fun i : J => hlim (x i))
    filter_upwards [h] with ω hω
    exact tendsto_finsetSum Finset.univ fun i _ => (hω i).const_mul (t i)
  obtain ⟨V,_,hV,_⟩ := exists_gaussianReal_map_of_ae_limit μ Y W v hY hW hv hYW
  exact ⟨Real.toNNReal V,hV⟩

end
end ASDExplicitGamma.Gaussian
