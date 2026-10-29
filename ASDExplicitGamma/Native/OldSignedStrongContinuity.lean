module

public import ASDExplicitGamma.Native.OldSignedStrongDifferentiation

/-! Strong L2 continuity under a square-integrable pointwise majorant. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory Filter
open scoped Topology
noncomputable section

/-- Pointwise continuity and a common genuine L2 bound give strong L2
continuity. No integral or norm is converted through an infinite value. -/
theorem old_signed_continuous_L2
    {E Ω : Type*} [TopologicalSpace E] [FirstCountableTopology E] [MeasurableSpace Ω]
    (μ : Measure Ω) (F : E → Lp ℂ 2 μ) (phi : E → Ω → ℂ) (B : Lp ℝ 2 μ)
    (hF : ∀ y, (F y : Ω → ℂ) =ᵐ[μ] phi y)
    (hc : ∀ᵐ w ∂μ, Continuous (fun y => phi y w))
    (hb : ∀ y, ∀ᵐ w ∂μ, ‖phi y w‖ ≤ ‖B w‖) : Continuous F := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let r : E → Ω → ℂ := fun y w => phi y w-phi x w
  have hrep (y : E) : ((F y-F x: Lp ℂ 2 μ) : Ω → ℂ) =ᵐ[μ] r y := by
    filter_upwards [Lp.coeFn_sub (F y) (F x),hF y,hF x] with w hs hy hx
    simp only [Pi.sub_apply] at hs
    exact hs.trans (by rw [hy,hx])
  have hm (y : E) : AEStronglyMeasurable (r y) μ :=
    (Lp.memLp (F y-F x)).aestronglyMeasurable.congr (hrep y)
  have hdom (y : E) : ∀ᵐ w ∂μ, ‖‖r y w‖^2‖ ≤ 4*‖B w‖^2 := by
    filter_upwards [hb y,hb x] with w hy hx
    have hh : ‖r y w‖≤2*‖B w‖ :=
      (norm_sub_le _ _).trans ((add_le_add hy hx).trans_eq (by ring))
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ (2*‖B w‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hh 2
      _ = _ := by ring
  have hi : Integrable (fun w => 4*‖B w‖^2) μ :=
    ((memLp_two_iff_integrable_sq_norm (Lp.memLp B).aestronglyMeasurable).mp (Lp.memLp B)).const_mul 4
  have hl : ∀ᵐ w ∂μ, Tendsto (fun y => ‖r y w‖^2) (𝓝 x) (𝓝 (0:ℝ)) := by
    filter_upwards [hc] with w hw
    have hh := ((hw.continuousAt (x := x)).sub_const (phi x w)).norm.pow 2
    simpa only [sub_self,norm_zero,zero_pow (by decide : 2≠0)] using hh
  have hint := tendsto_integral_filter_of_dominated_convergence
    (fun w => 4*‖B w‖^2) (Filter.Eventually.of_forall fun y => (hm y).norm.pow 2)
    (Filter.Eventually.of_forall hdom) hi hl
  simp only [Pi.pow_apply,integral_zero] at hint
  have hn (y : E) : ‖F y-F x‖^2=∫ w, ‖r y w‖^2 ∂μ := by
    rw [←real_inner_self_eq_norm_sq,L2.inner_def]
    simp_rw [real_inner_self_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [hrep y] with w hw
    rw [hw]
  have hs : Tendsto (fun y => ‖F y-F x‖^2) (𝓝 x) (𝓝 (0:ℝ)) := by
    simpa only [hn] using hint
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using ht

end
end ASDExplicitGamma.Native
