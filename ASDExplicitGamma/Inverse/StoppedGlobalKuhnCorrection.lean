module

public import ASDExplicitGamma.Inverse.StoppedKuhnGroupL2Bounds

/-! The actual loading-independent stopped midpoint correction on the whole
root. All group finiteness and all H1 summability premises are discharged
from the source successful-separation event. -/
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

/-- Every actual group, on its own compatible source mesh. -/
def stoppedKuhnGroupCorrection (i : Fin 2) (a : ℕ) : H1Function (openCubeSet Q) :=
  rootKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad a
    (stopped_component_group_finite M Q H hH τ η ω hgood S hS hbad a)
    (fun C => stopped_component_group_nodes_nonempty M Q H hH τ η ω hgood S hS hbad a C.property) i

theorem stopped_kuhn_group_function_summable (i : Fin 2) :
    Summable (fun a => compatibleFunctionLpTerm
      (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i a)) := by
  apply ((group_clock_volume_summable Q H).mul_left ((3:ℝ)^Q.scale)).of_norm_bounded
  intro a
  apply (stopped_kuhn_group_function_L2_bound M Q H hH τ η ω hgood S hS hbad a _ _ i).trans
  have hs : (3:ℝ)^(Q.scale-((a+whitneyProfile H a:ℕ):ℤ)) ≤ (3:ℝ)^Q.scale :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ rootGroupClock H a by unfold rootGroupClock; positivity)
  have hh := mul_le_mul_of_nonneg_right hm (Real.sqrt_nonneg (rootGroupVolumeBudget Q a))
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hh

theorem stopped_kuhn_group_gradient_summable (i k : Fin 2) :
    Summable (fun a => compatibleGradientLpTerm
      (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i a) k) := by
  apply ((group_clock_volume_summable Q H).mul_left 18).of_norm_bounded
  intro a
  simpa only [stoppedKuhnGroupCorrection,mul_assoc] using
    stopped_kuhn_group_gradient_L2_bound M Q H hH τ η ω hgood S hS hbad a
      (stopped_component_group_finite M Q H hH τ η ω hgood S hS hbad a)
      (fun C => stopped_component_group_nodes_nonempty M Q H hH τ η ω hgood S hS hbad a C.property) i k

/-- Whole-root coordinate correction, with a genuine weak gradient. The
same two coordinates serve every affine potential and flux loading. -/
def stoppedGlobalKuhnCorrection (i : Fin 2) : H1Function (openCubeSet Q) :=
  compatibleSeriesLimit
    (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i)
    (stopped_kuhn_group_function_summable M Q H hH τ η ω hgood S hS hbad i)
    (stopped_kuhn_group_gradient_summable M Q H hH τ η ω hgood S hS hbad i)

theorem stopped_global_kuhn_correction_memH10 (i : Fin 2) :
    MemH10 (openCubeSet Q)
      (stoppedGlobalKuhnCorrection M Q H hH τ η ω hgood S hS hbad i).toFun := by
  apply compatible_countable_h10_gluing (isOpenBoundedConvexDomain_openCubeSet Q)
  intro a
  exact root_kuhn_group_correction_memH10 M Q H hH τ η ω hgood S hS hbad a _ _ i

end
end ASDExplicitGamma.Inverse
