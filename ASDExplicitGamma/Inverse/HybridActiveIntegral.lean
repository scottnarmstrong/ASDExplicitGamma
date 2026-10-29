module

public import ASDExplicitGamma.Inverse.HybridGradientConstants
public import ASDExplicitGamma.Inverse.LayerDensityComparison
public import ASDExplicitGamma.Inverse.FluxNorm
public import ASDExplicitGamma.Inverse.StoppedKuhnActiveCharge

/-! Physical integral payment for each actual active hybrid simplex. -/
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

/-- The actual active-cell charge pays its constant flux square by the
integrals of the same three physical diameter fields. Spatial integrability
is derived from the finite physical block population on every sample. -/
theorem hybrid_active_flux_square_integral
    (hfinite : ∀ j ≤ Q.scale-(H:ℤ), ∀ z,
      diameterField (q3PlanarMarks M j τ η) ω z ≠ ∞)
    (C : HybridCell Q H S → Mat 2)
    (hC : ∀ i, ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), x ∈ (hybridDomain i:Set (Vec 2)) →
      stoppedKuhnGradient M Q H hH τ η ω hgood S hS hbad x=C i)
    (i : HybridActiveCell Q H S) (q : Vec 2) :
    (volume (hybridDomain (.inr i):Set (Vec 2))).toReal*
      dotProduct (matVecMul (planarFluxMatrix (C (.inr i))) q)
        (matVecMul (planarFluxMatrix (C (.inr i))) q) ≤
      (planarGradientCharge 40+1)*
        (∑ e : Fin 3, ∫ x in (hybridDomain (.inr i):Set (Vec 2)),
          (layerResolutionDiameter M Q H τ η i.1.val.1 e ω x)^2)*dotProduct q q := by
  classical
  let V := hybridDomain (.inr i)
  let n := i.1.val.1
  let P := i.1.val.2.val
  let Z := fun e : Fin 3 => fun x => (layerResolutionDiameter M Q H τ η n e ω x)^2
  let b := matVecMul (planarFluxMatrix (C (.inr i))) q
  have hn : 1 ≤ n := root_whitney_layer_pos Q H n i.1.val.2.property
  have hVL : (V:Set (Vec 2)) ⊆ rootLayerCarrier Q H n := by
    intro x hx
    exact Set.mem_iUnion₂.mpr ⟨P,i.1.val.2.property,
      openCubeSet_subset_cubeSet P (hybrid_domain_subset_parent (.inr i) hx)⟩
  have hZ (e : Fin 3) : IntegrableOn (Z e) (V:Set (Vec 2)) := by
    have hh := layer_resolution_square_integrableOn M Q H hH (0,n-1) τ η e ω
    have hh' : IntegrableOn (Z e) (rootLayerCarrier Q H n) := by
      simpa only [Nat.add_zero,Nat.sub_add_cancel hn] using hh
    exact hh'.mono_set hVL
  have hsum : IntegrableOn (fun x => ∑ e : Fin 3, Z e x) (V:Set (Vec 2)) :=
    integrable_finsetSum Finset.univ (fun e _ => hZ e)
  have hactive : ∃ D ∈ S, CubeTouch P D := by
    simpa only [not_forall,not_imp,not_not,exists_prop,P] using i.1.property
  have hcharge := stopped_kuhn_gradient_ae_active_charge M Q H hH τ η ω hgood S hS hbad hfinite
  have hineq : ∀ᵐ x ∂volumeMeasureOn (V:Set (Vec 2)), dotProduct b b ≤
      (planarGradientCharge 40+1)*(∑ e : Fin 3, Z e x)*dotProduct q q := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (hybrid_domain_subset_root (.inr i)) hcharge,
      ae_restrict_of_ae_restrict_of_subset (hybrid_domain_subset_root (.inr i)) (hC (.inr i)),
      ae_restrict_mem V.measurableSet] with x hxcharge hxC hxV
    have hc := hxcharge n P i.1.val.2.property hactive (hybrid_domain_subset_parent (.inr i) hxV)
    rw [hxC hxV] at hc
    exact (planar_flux_loading_square_le (C (.inr i)) q).trans
      (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)))
  have hleft : IntegrableOn (fun _ : Vec 2 => dotProduct b b) (V:Set (Vec 2)) :=
    integrableOn_const V.isDomain.2.1.volume_lt_top.ne
  have hright := (hsum.const_mul (planarGradientCharge 40+1)).mul_const (dotProduct q q)
  have hh := integral_mono_ae hleft hright hineq
  rw [integral_const,Measure.real_def,smul_eq_mul,integral_mul_const,integral_const_mul,
    integral_finsetSum Finset.univ (fun e _ => hZ e)] at hh
  simpa only [Measure.restrict_apply_univ] using hh

end
end ASDExplicitGamma.Inverse
