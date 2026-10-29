module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Strong differentiation of actual L2 families from pointwise derivatives
and a square-integrable bound on normalized remainders. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory Filter
open scoped Topology
noncomputable section

/-- A pointwise derivative with an actual L2 remainder majorant is the
strong L2 derivative. The bound may vary over the measure space, so this
applies to frequency-weighted projected characters as well as potentials. -/
theorem old_signed_hasFDerivAt_L2
    {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace Ω]
    (μ : Measure Ω) (F : E → Lp ℂ 2 μ) (phi : E → Ω → ℂ) (x : E)
    (D : E →L[ℝ] Lp ℂ 2 μ) (d : Ω → E →L[ℝ] ℂ) (B : Lp ℝ 2 μ)
    (hF : ∀ y, (F y : Ω → ℂ) =ᵐ[μ] phi y)
    (hD : ∀ v, (D v : Ω → ℂ) =ᵐ[μ] fun w => d w v)
    (hd : ∀ᵐ w ∂μ, HasFDerivAt (fun y => phi y w) (d w) x)
    (hbound : ∀ y, ∀ᵐ w ∂μ,
      ‖phi y w-phi x w-d w (y-x)‖ ≤ ‖B w‖*‖y-x‖) :
    HasFDerivAt F D x := by
  let r : E → Ω → ℂ := fun y w => ‖y-x‖⁻¹ • (phi y w-phi x w-d w (y-x))
  let R : E → Lp ℂ 2 μ := fun y => ‖y-x‖⁻¹ • (F y-F x-D (y-x))
  have hrep (y : E) : (R y : Ω → ℂ) =ᵐ[μ] r y := by
    filter_upwards [Lp.coeFn_smul ‖y-x‖⁻¹ (F y-F x-D (y-x)),
      Lp.coeFn_sub (F y-F x) (D (y-x)),Lp.coeFn_sub (F y) (F x),
      hF y,hF x,hD (y-x)] with w hs hsub hsub' hy hx hv
    simp only [Pi.smul_apply] at hs
    simp only [Pi.sub_apply] at hsub hsub'
    exact hs.trans (congrArg (fun z : ℂ => ‖y-x‖⁻¹ • z)
      (hsub.trans (by rw [hsub',hy,hx,hv])))
  have hm (y : E) : AEStronglyMeasurable (r y) μ :=
    (Lp.memLp (R y)).aestronglyMeasurable.congr (hrep y)
  have hb (y : E) : ∀ᵐ w ∂μ, ‖r y w‖ ≤ ‖B w‖ := by
    filter_upwards [hbound y] with w hw
    by_cases hy : y=x
    · simp only [r,hy,sub_self,norm_zero,inv_zero,zero_smul,norm_zero]
      exact norm_nonneg _
    have hn : 0<‖y-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hy)
    dsimp only [r]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn)]
    calc
      _ ≤ ‖y-x‖⁻¹*(‖B w‖*‖y-x‖) := mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr hn.le)
      _ = _ := by field_simp
  have hi : Integrable (fun w => ‖B w‖^2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp B).aestronglyMeasurable).mp (Lp.memLp B)
  have hdom (y : E) : ∀ᵐ w ∂μ, ‖‖r y w‖^2‖ ≤ ‖B w‖^2 := by
    filter_upwards [hb y] with w hw
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hw 2
  have hlim : ∀ᵐ w ∂μ, Tendsto (fun y => ‖r y w‖^2) (𝓝 x) (𝓝 (0:ℝ)) := by
    filter_upwards [hd] with w hw
    have hh := (hasFDerivAt_iff_tendsto.mp hw).pow 2
    simpa only [r,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      zero_pow (by decide : 2≠0)] using hh
  have hint := tendsto_integral_filter_of_dominated_convergence
    (fun w => ‖B w‖^2) (Filter.Eventually.of_forall fun y => (hm y).norm.pow 2)
    (Filter.Eventually.of_forall hdom) hi hlim
  simp only [Pi.pow_apply,integral_zero] at hint
  have hnorm (y : E) : ‖R y‖^2=∫ w, ‖r y w‖^2 ∂μ := by
    rw [←real_inner_self_eq_norm_sq,L2.inner_def]
    simp_rw [real_inner_self_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [hrep y] with w hw
    rw [hw]
  have hs : Tendsto (fun y => ‖R y‖^2) (𝓝 x) (𝓝 (0:ℝ)) := by
    simpa only [hnorm] using hint
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  have ht' : Tendsto (fun y => ‖R y‖) (𝓝 x) (𝓝 (0:ℝ)) := by
    simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using ht
  apply hasFDerivAt_iff_tendsto.mpr
  simpa only [R,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] using ht'

end
end ASDExplicitGamma.Native
