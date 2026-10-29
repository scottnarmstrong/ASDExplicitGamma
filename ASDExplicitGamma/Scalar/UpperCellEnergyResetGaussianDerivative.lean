module

public import ASDExplicitGamma.Scalar.UpperCellEnergyResetGaussianL2
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Strong L2 differentiation of actual smooth Gaussian forcing families,
without an unproved domination estimate on their difference quotients. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory Filter ASDExplicitGamma.Gaussian
open scoped Topology
noncomputable section

private def resetGaussianRemainder {Ω : Type*}
    (phi : ℝ → Ω → ℝ) (d : Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ‖t‖⁻¹*(phi t ω-phi 0 ω-t*d ω)

/-- The normalized Taylor remainder of a genuine joint Gaussian value/jet
family has an actual centered Gaussian law, also at t=0. -/
theorem upper_cell_reset_gaussian_remainder
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (phi : ℝ → Ω → ℝ) (d : Ω → ℝ)
    (hX : IsCenteredGaussianFamily μ (Sum.elim phi (fun _ : Unit => d))) (t : ℝ) :
    ∃ v : NNReal, μ.map (fun ω => ‖t‖⁻¹*(phi t ω-phi 0 ω-t*d ω))=gaussianReal 0 v := by
  obtain ⟨v,hv⟩ := hX.2
    (fun i : Fin 3 => if i=0 then Sum.inl t else if i=1 then Sum.inl 0 else Sum.inr ())
    (fun i : Fin 3 => if i=0 then ‖t‖⁻¹ else if i=1 then -‖t‖⁻¹ else -‖t‖⁻¹*t)
  refine ⟨v,?_⟩
  have heq : (fun ω => ‖t‖⁻¹*(phi t ω-phi 0 ω-t*d ω))=
      (fun ω => ∑ i : Fin 3,
        (if i=0 then ‖t‖⁻¹ else if i=1 then -‖t‖⁻¹ else -‖t‖⁻¹*t)*
          (Sum.elim phi (fun _ : Unit => d))
            (if i=0 then Sum.inl t else if i=1 then Sum.inl 0 else Sum.inr ()) ω) := by
    funext ω
    simp only [Fin.sum_univ_three]
    norm_num
    ring
  rw [heq]
  exact hv

/-- Smooth representatives of a jointly Gaussian value/first-jet family
are strongly differentiable in the actual L2 probability space. Both the
Gaussian law and the pointwise derivative concern the physical forcing;
no regularity or moment bound on a projected field is assumed. -/
theorem upper_cell_reset_gaussian_hasDerivAt_L2
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : ℝ → Lp ℝ 2 μ) (D : Lp ℝ 2 μ)
    (phi : ℝ → Ω → ℝ) (d : Ω → ℝ)
    (hF : ∀ t,F t =ᵐ[μ] phi t) (hD : D =ᵐ[μ] d)
    (hX : IsCenteredGaussianFamily μ (Sum.elim phi (fun _ : Unit => d)))
    (hd : ∀ᵐ ω ∂μ,HasDerivAt (fun t => phi t ω) (d ω) 0) :
    HasDerivAt F D 0 := by
  let R : ℝ → Lp ℝ 2 μ := fun t => ‖t‖⁻¹ • (F t-F 0-t • D)
  have hrep (t : ℝ) : R t =ᵐ[μ] resetGaussianRemainder phi d t := by
    filter_upwards [Lp.coeFn_smul ‖t‖⁻¹ (F t-F 0-t • D),
      Lp.coeFn_sub (F t-F 0) (t • D),Lp.coeFn_sub (F t) (F 0),
      Lp.coeFn_smul t D,hF t,hF 0,hD] with ω hs hsub hsub0 hsm ht h0 hd0
    simp only [Pi.smul_apply,Pi.sub_apply] at hs hsub hsub0 hsm
    dsimp only [R]
    rw [hs,hsub,hsub0,hsm,ht,h0,hd0]
    rfl
  have hgauss (t : ℝ) : ∃ v : NNReal,μ.map (R t)=gaussianReal 0 v := by
    obtain ⟨v,hv⟩ := upper_cell_reset_gaussian_remainder μ phi d hX t
    exact ⟨v,(Measure.map_congr (hrep t)).trans hv⟩
  have hR : Tendsto R (𝓝 (0:ℝ)) (𝓝 0) := by
    apply tendsto_iff_seq_tendsto.mpr
    intro u hu
    apply upper_cell_reset_gaussian_L2_zero μ (fun n => R (u n)) (fun n => hgauss (u n))
    have hrepseq := ae_all_iff.mpr (fun n : ℕ => hrep (u n))
    filter_upwards [hd,hrepseq] with ω hω hr
    have ht := (hasDerivAt_iff_tendsto.mp hω).comp hu
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have heq : (fun n => ‖R (u n) ω‖)=
        (fun n => ‖u n‖⁻¹*‖phi (u n) ω-phi 0 ω-u n • d ω‖) := by
      funext n
      rw [hr n]
      simp only [resetGaussianRemainder,norm_mul,Real.norm_eq_abs,
        abs_inv,abs_abs,smul_eq_mul]
    rw [heq]
    simpa only [Function.comp_def,sub_zero] using ht
  apply hasDerivAt_iff_tendsto.mpr
  have hn := tendsto_zero_iff_norm_tendsto_zero.mp hR
  simpa only [R,norm_smul,Real.norm_eq_abs,
    abs_inv,abs_abs,sub_zero] using hn

end
end ASDExplicitGamma.Scalar
