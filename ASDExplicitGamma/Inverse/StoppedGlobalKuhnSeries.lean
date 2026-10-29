module

public import ASDExplicitGamma.Inverse.StoppedGlobalKuhnCorrection
public import ASDExplicitGamma.Inverse.StoppedSeriesRepresentative

/-! Absolute parent-space summability and the actual pointwise representative
of the stopped global coordinate correction. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
noncomputable section

variable (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (hH : 333 ≤ H)
  (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
  (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
    (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
  (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
  (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)

theorem stopped_kuhn_group_function_norm_summable (i : Fin 2) :
    Summable (fun a => ‖compatibleFunctionLpTerm
      (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i a)‖) := by
  apply Summable.of_nonneg_of_le (fun a => norm_nonneg _) _
    ((group_clock_volume_summable Q H).mul_left ((3:ℝ)^Q.scale))
  intro a
  apply (stopped_kuhn_group_function_L2_bound M Q H hH τ η ω hgood S hS hbad a _ _ i).trans
  have hs : (3:ℝ)^(Q.scale-((a+whitneyProfile H a:ℕ):ℤ)) ≤ (3:ℝ)^Q.scale :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ rootGroupClock H a by unfold rootGroupClock; positivity)
  have hh := mul_le_mul_of_nonneg_right hm (Real.sqrt_nonneg (rootGroupVolumeBudget Q a))
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hh

theorem stopped_kuhn_group_gradient_norm_summable (i k : Fin 2) :
    Summable (fun a => ‖compatibleGradientLpTerm
      (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i a) k‖) := by
  apply Summable.of_nonneg_of_le (fun a => norm_nonneg _) _
    ((group_clock_volume_summable Q H).mul_left 18)
  intro a
  simpa only [stoppedKuhnGroupCorrection,mul_assoc] using
    stopped_kuhn_group_gradient_L2_bound M Q H hH τ η ω hgood S hS hbad a
      (stopped_component_group_finite M Q H hH τ η ω hgood S hS hbad a)
      (fun C => stopped_component_group_nodes_nonempty M Q H hH τ η ω hgood S hS hbad a C.property) i k

/-- Values and every weak derivative are the actual group series on one
common spatial null set. -/
theorem stopped_global_kuhn_correction_ae_hasSum (i : Fin 2) :
    ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
      HasSum (fun a => (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i a).toFun x)
        ((stoppedGlobalKuhnCorrection M Q H hH τ η ω hgood S hS hbad i).toFun x) ∧
      ∀ k, HasSum (fun a => (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i a).grad x k)
        ((stoppedGlobalKuhnCorrection M Q H hH τ η ω hgood S hS hbad i).grad x k) := by
  have hf := compatible_series_function_ae_hasSum
    (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i)
    (stopped_kuhn_group_function_norm_summable M Q H hH τ η ω hgood S hS hbad i)
    (stopped_kuhn_group_gradient_summable M Q H hH τ η ω hgood S hS hbad i)
  have hg (k : Fin 2) := compatible_series_gradient_ae_hasSum
    (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i)
    (stopped_kuhn_group_function_summable M Q H hH τ η ω hgood S hS hbad i)
    (stopped_kuhn_group_gradient_norm_summable M Q H hH τ η ω hgood S hS hbad i) k
  exact hf.and (ae_all_iff.mpr hg)

end
end ASDExplicitGamma.Inverse
