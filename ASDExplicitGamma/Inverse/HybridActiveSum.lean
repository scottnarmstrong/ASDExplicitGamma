module

public import ASDExplicitGamma.Inverse.HybridActiveIntegral
public import ASDExplicitGamma.Inverse.GroupedCellIntegrals

/-! Complete countable active-cell energy payment by deterministic layers. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
open scoped ENNReal
noncomputable section

variable (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (hH : 333 ≤ H)
  (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
  (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
    (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
  (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
  (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)

/-- The complete active-cell squared-flux sum is paid by the full actual
deterministic layer densities. The weights are arbitrary nonnegative layer
clocks, so the exact true-frame clocks can be inserted afterwards. -/
theorem hybrid_active_square_sum_le_layers
    (hfinite : ∀ j ≤ Q.scale-(H:ℤ), ∀ z,
      diameterField (q3PlanarMarks M j τ η) ω z ≠ ∞)
    (C : HybridCell Q H S → Mat 2)
    (hC : ∀ i, ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), x ∈ (hybridDomain i:Set (Vec 2)) →
      stoppedKuhnGradient M Q H hH τ η ω hgood S hS hbad x=C i)
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (q : Vec 2) :
    (∑' i : HybridActiveCell Q H S, ENNReal.ofReal
      (w i.1.val.1*(volume (hybridDomain (.inr i):Set (Vec 2))).toReal/(volume (cubeSet Q)).toReal*
        dotProduct (matVecMul (planarFluxMatrix (C (.inr i))) q)
          (matVecMul (planarFluxMatrix (C (.inr i))) q))) ≤
      ∑' n : ℕ, ENNReal.ofReal (w n*(planarGradientCharge 40+1)*
        ((∑ e : Fin 3, ∫ x in rootLayerCarrier Q H n,
          (layerResolutionDiameter M Q H τ η n e ω x)^2)/(volume (cubeSet Q)).toReal)*dotProduct q q) := by
  classical
  let Z := fun n (e : Fin 3) x => (layerResolutionDiameter M Q H τ η n e ω x)^2
  let f := fun n x => (w n/(volume (cubeSet Q)).toReal*(planarGradientCharge 40+1))*
    (∑ e : Fin 3, Z n e x)*dotProduct q q
  have hv : 0 ≤ dotProduct q q := Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
  have hS0 : 0 ≤ planarGradientCharge 40+1 := by unfold planarGradientCharge; positivity
  have hZ (n : ℕ) (e : Fin 3) : IntegrableOn (Z n e) (rootLayerCarrier Q H n) := by
    by_cases hn : n=0
    · subst n
      simp only [root_layer_carrier_zero,integrableOn_empty]
    · have hn1 : 1 ≤ n := by omega
      simpa only [Nat.add_zero,Nat.sub_add_cancel hn1] using
        layer_resolution_square_integrableOn M Q H hH (0,n-1) τ η e ω
  have hf (n : ℕ) : IntegrableOn (f n) (rootLayerCarrier Q H n) :=
    ((integrable_finsetSum Finset.univ (fun e _ => hZ n e)).const_mul _).mul_const _
  have hf0 (n : ℕ) (x : Vec 2) : 0 ≤ f n x := by
    dsimp only [f]
    exact mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg (hw n) ENNReal.toReal_nonneg) hS0)
      (Finset.sum_nonneg (fun e _ => sq_nonneg _))) hv
  have hsub (i : HybridActiveCell Q H S) :
      (hybridDomain (.inr i):Set (Vec 2)) ⊆ rootLayerCarrier Q H i.1.val.1 := by
    intro x hx
    exact Set.mem_iUnion₂.mpr ⟨i.1.val.2.val,i.1.val.2.property,
      openCubeSet_subset_cubeSet _ (hybrid_domain_subset_parent (.inr i) hx)⟩
  have hgroup := grouped_disjoint_cell_integrals_le volume
    (fun i : HybridActiveCell Q H S => (hybridDomain (.inr i):Set (Vec 2)))
    (rootLayerCarrier Q H) (fun i => i.1.val.1) (fun i => (hybridDomain (.inr i)).measurableSet)
    (root_layer_carrier_measurable Q H)
    (fun i j hne => hybrid_domains_disjoint Q H S (fun he => hne (Sum.inr_injective he)))
    hsub f hf0 hf
  apply (ENNReal.tsum_le_tsum (fun i => ?_)).trans hgroup |>.trans_eq ?_
  · apply tsum_congr
    intro n
    rw [show (∫ x in rootLayerCarrier Q H n, f n x)=
      (w n/(volume (cubeSet Q)).toReal*(planarGradientCharge 40+1))*
        (∑ e : Fin 3, ∫ x in rootLayerCarrier Q H n, Z n e x)*dotProduct q q by
        rw [integral_mul_const,integral_const_mul,integral_finsetSum Finset.univ (fun e _ => hZ n e)]]
    congr 1
    ring
  · apply ENNReal.ofReal_le_ofReal
    have hh := hybrid_active_flux_square_integral M Q H hH τ η ω hgood S hS hbad hfinite C hC i q
    have hh' := mul_le_mul_of_nonneg_left hh (div_nonneg (hw i.1.val.1)
      (ENNReal.toReal_nonneg (a := volume (cubeSet Q))))
    have hi : ∫ x in (hybridDomain (.inr i):Set (Vec 2)), f i.1.val.1 x =
        (w i.1.val.1/(volume (cubeSet Q)).toReal*(planarGradientCharge 40+1))*
          (∑ e : Fin 3, ∫ x in (hybridDomain (.inr i):Set (Vec 2)), Z i.1.val.1 e x)*dotProduct q q := by
      rw [integral_mul_const,integral_const_mul,integral_finsetSum Finset.univ
        (fun e _ => (hZ i.1.val.1 e).mono_set (hsub i))]
    rw [hi]
    convert hh' using 1 <;> ring

end
end ASDExplicitGamma.Inverse
