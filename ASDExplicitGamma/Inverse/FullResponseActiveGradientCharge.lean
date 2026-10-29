module

public import ASDExplicitGamma.Inverse.FullResponseActiveTriangle
public import ASDExplicitGamma.Inverse.HybridFullTraceCongruence
public import ASDExplicitGamma.Inverse.HybridFrameComparison
public import ASDExplicitGamma.Inverse.StoppedKuhnActiveCharge
public import ASDExplicitGamma.Inverse.LayerDensityComparison

/-! The squared common gradient factor on every active simplex is paid by the
same three physical resolution fields that occur in the profile. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
open scoped ENNReal Matrix.Norms.Elementwise

noncomputable section

variable (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (hH : 333 ≤ H)
  (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
  (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
    (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
  (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
  (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)

/- A constant simplex gradient inherits the active three-resolution charge
on its entire physical cell, up to a null set. -/
theorem hybrid_active_full_gradient_square_ae
    (hfinite : ∀ j ≤ Q.scale-(H:ℤ), ∀ z,
      diameterField (q3PlanarMarks M j τ η) ω z ≠ ∞)
    (C : HybridCell Q H S → Mat 2)
    (hC : ∀ i, ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
      x ∈ (hybridDomain i : Set (Vec 2)) →
        stoppedKuhnGradient M Q H hH τ η ω hgood S hS hbad x = C i)
    (i : HybridActiveCell Q H S) :
    ∀ᵐ x ∂volumeMeasureOn (hybridDomain (.inr i) : Set (Vec 2)),
      ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (C (.inr i))‖^2 ≤
        (planarGradientCharge 40+1) *
          ∑ e : Fin 3, (layerResolutionDiameter M Q H τ η i.1.val.1 e ω x)^2 := by
  let V := hybridDomain (.inr i)
  let n := i.1.val.1
  let P := i.1.val.2.val
  have hactive : ∃ D ∈ S, CubeTouch P D := by
    simpa only [not_forall, not_imp, not_not, exists_prop, P] using i.1.property
  have hcharge := stopped_kuhn_gradient_ae_active_charge
    M Q H hH τ η ω hgood S hS hbad hfinite
  have hsubset := hybrid_domain_subset_root (.inr i)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsubset hcharge,
    ae_restrict_of_ae_restrict_of_subset hsubset (hC (.inr i)),
    ae_restrict_mem V.measurableSet] with x hxcharge hxC hxV
  have hxP : x ∈ openCubeSet P :=
    hybrid_domain_subset_parent (.inr i) hxV
  have hlocal := hxcharge n P i.1.val.2.property hactive hxP
  rw [hxC hxV] at hlocal
  exact hlocal

/- The active simplex's constant squared gradient is bounded by the
integrated three-resolution charge. This is the measure-level form consumed
by the active full-response layer sum. -/
theorem hybrid_active_full_gradient_square_integral
    (hfinite : ∀ j ≤ Q.scale-(H:ℤ), ∀ z,
      diameterField (q3PlanarMarks M j τ η) ω z ≠ ∞)
    (C : HybridCell Q H S → Mat 2)
    (hC : ∀ i, ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
      x ∈ (hybridDomain i : Set (Vec 2)) →
        stoppedKuhnGradient M Q H hH τ η ω hgood S hS hbad x = C i)
    (i : HybridActiveCell Q H S) :
    (volume (hybridDomain (.inr i) : Set (Vec 2))).toReal *
        ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (C (.inr i))‖^2 ≤
      (planarGradientCharge 40+1) *
        ∑ e : Fin 3, ∫ x in (hybridDomain (.inr i) : Set (Vec 2)),
          (layerResolutionDiameter M Q H τ η i.1.val.1 e ω x)^2 := by
  classical
  let V := hybridDomain (.inr i)
  let n := i.1.val.1
  let P := i.1.val.2.val
  let Z := fun e : Fin 3 => fun x =>
    (layerResolutionDiameter M Q H τ η n e ω x)^2
  have hn : 1 ≤ n := root_whitney_layer_pos Q H n i.1.val.2.property
  have hVL : (V : Set (Vec 2)) ⊆ rootLayerCarrier Q H n := by
    intro x hx
    exact Set.mem_iUnion₂.mpr ⟨P, i.1.val.2.property,
      openCubeSet_subset_cubeSet P (hybrid_domain_subset_parent (.inr i) hx)⟩
  have hZ (e : Fin 3) : IntegrableOn (Z e) (V : Set (Vec 2)) := by
    have hh := layer_resolution_square_integrableOn M Q H hH (0,n-1) τ η e ω
    have hh' : IntegrableOn (Z e) (rootLayerCarrier Q H n) := by
      simpa only [Nat.add_zero, Nat.sub_add_cancel hn] using hh
    exact hh'.mono_set hVL
  have hsum : IntegrableOn (fun x => ∑ e : Fin 3, Z e x) (V : Set (Vec 2)) :=
    integrable_finsetSum Finset.univ (fun e _ => hZ e)
  have hineq := hybrid_active_full_gradient_square_ae
    M Q H hH τ η ω hgood S hS hbad hfinite C hC i
  have hleft : IntegrableOn (fun _ : Vec 2 =>
      ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (C (.inr i))‖^2)
      (V : Set (Vec 2)) :=
    integrableOn_const V.isDomain.2.1.volume_lt_top.ne
  have hright : IntegrableOn (fun x =>
      (planarGradientCharge 40+1) * ∑ e : Fin 3, Z e x)
      (V : Set (Vec 2)) := hsum.const_mul _
  have hmono := integral_mono_ae hleft hright hineq
  have hleftEq : (∫ x in (V : Set (Vec 2)),
      ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (C (.inr i))‖^2) =
      (volume V.carrier).toReal *
        ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (C (.inr i))‖^2 := by
    rw [integral_const, Measure.real_def, smul_eq_mul]
    congr 1
    simp only [Measure.restrict_apply_univ]
  have hrightEq : (∫ x in (V : Set (Vec 2)),
      (planarGradientCharge 40+1) * ∑ e : Fin 3, Z e x) =
      (planarGradientCharge 40+1) *
        ∑ e : Fin 3, ∫ x in (V : Set (Vec 2)), Z e x := by
    rw [integral_const_mul, integral_finsetSum Finset.univ (fun e _ => hZ e)]
  have hresult :
      (volume V.carrier).toReal *
          ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (C (.inr i))‖^2 ≤
        (planarGradientCharge 40+1) *
          ∑ e : Fin 3, ∫ x in (V : Set (Vec 2)), Z e x := by
    calc
      _ = ∫ x in (V : Set (Vec 2)),
          ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (C (.inr i))‖^2 := hleftEq.symm
      _ ≤ ∫ x in (V : Set (Vec 2)),
          (planarGradientCharge 40+1) * ∑ e : Fin 3, Z e x := hmono
      _ = (planarGradientCharge 40+1) *
          ∑ e : Fin 3, ∫ x in (V : Set (Vec 2)), Z e x := hrightEq
  simpa only [Measure.restrict_apply_univ, Z] using hresult

end
end ASDExplicitGamma.Inverse
