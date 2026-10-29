module

public import ASDExplicitGamma.Inverse.StoppedKuhnGroupFallback
public import ASDExplicitGamma.Inverse.StoppedSupportedL2Bounds
public import ASDExplicitGamma.Inverse.StoppedGroupDecay
public import ASDExplicitGamma.Inverse.CompatibleGluing

/-! Actual L2 budgets of the stopped common-mesh groups. The norms are
those of the parent H1 representatives, before taking their countable sum. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
noncomputable section

theorem stopped_kuhn_group_function_L2_bound (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (hH : 333 ≤ H) (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
    (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
    (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)
    (a : ℕ) (hfin : (rootComponentGroup Q H S a).Finite)
    (hne : ∀ C : rootComponentGroup Q H S a,
      (componentMeshNodes Q (compatibleWhitneyMeshDepth H (a+1)) C.val).Nonempty)
    (i : Fin 2) :
    ‖compatibleFunctionLpTerm (rootKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad a hfin hne i)‖ ≤
      (rootGroupClock H a*(3:ℝ)^(Q.scale-((a+whitneyProfile H a:ℕ):ℤ)))*
        Real.sqrt (rootGroupVolumeBudget Q a) := by
  apply supported_L2_norm_bound _ _ _ (rootGroupSupport Q H a)
    (root_group_support_measurable Q H a) _ _ (by unfold rootGroupClock; positivity)
    (root_group_volume_budget_nonneg Q a) (root_group_support_restrict_measure_le Q H a)
  · exact (stopped_kuhn_group_ae_support M Q H hH τ η ω hgood S hS hbad a hfin hne i).mono
      (fun x hx hv => hx (Or.inl hv))
  · exact Filter.Eventually.of_forall
      (stopped_kuhn_group_value_fallback M Q H hH τ η ω hgood S hS hbad a hfin hne i)

theorem stopped_kuhn_group_gradient_L2_bound (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (hH : 333 ≤ H) (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
    (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
    (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)
    (a : ℕ) (hfin : (rootComponentGroup Q H S a).Finite)
    (hne : ∀ C : rootComponentGroup Q H S a,
      (componentMeshNodes Q (compatibleWhitneyMeshDepth H (a+1)) C.val).Nonempty)
    (i k : Fin 2) :
    ‖compatibleGradientLpTerm (rootKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad a hfin hne i) k‖ ≤
      (18*rootGroupClock H a)*Real.sqrt (rootGroupVolumeBudget Q a) := by
  apply supported_L2_norm_bound _ _ _ (rootGroupSupport Q H a)
    (root_group_support_measurable Q H a) _ _ (by unfold rootGroupClock; positivity)
    (root_group_volume_budget_nonneg Q a) (root_group_support_restrict_measure_le Q H a)
  · exact (stopped_kuhn_group_ae_support M Q H hH τ η ω hgood S hS hbad a hfin hne i).mono
      (fun x hx hv => hx (Or.inr ⟨k,hv⟩))
  · exact (stopped_kuhn_group_gradient_fallback M Q H hH τ η ω hgood S hS hbad a hfin hne i k)

end
end ASDExplicitGamma.Inverse
