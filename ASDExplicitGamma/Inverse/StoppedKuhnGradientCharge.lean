module

public import ASDExplicitGamma.Inverse.StoppedKuhnResolutionBounds
public import ASDExplicitGamma.Inverse.StoppedKuhnTwoGroupRepresentative
public import ASDExplicitGamma.Inverse.StoppedGlobalKuhnMidpointMap
public import ASDExplicitGamma.Inverse.StoppedThreeResolutionAlgebra

/-! The source operator-square charge of the actual common midpoint map,
using the three pointwise physical Z fields at their literal resolutions. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Affine Algsuperdiff.Section3.Provider.Whitney
open scoped ENNReal
noncomputable section

variable (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (hH : 333 ≤ H)
  (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
  (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
    (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
  (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
  (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)

/-- Source convention F_ik=partial_i Phi_k for the common Kuhn map. -/
def stoppedKuhnGradient (x : Vec 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i k => (stoppedKuhnMidpointCoordinate M Q H hH τ η ω hgood S hS hbad k).grad x i

/-- Source (4.4) for the actual whole-root map; the only probabilistic input
to this pathwise helper is finiteness of the protected old Z fields. -/
theorem stopped_kuhn_gradient_ae_three_resolution_charge
    (hfinite : ∀ j ≤ Q.scale-(H:ℤ), ∀ z,
      diameterField (q3PlanarMarks M j τ η) ω z ≠ ∞) :
    ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), ∀ (n : ℕ) (P : TriadicCube 2),
      P ∈ whitneyRootLayer Q H n → x ∈ openCubeSet P →
      ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (stoppedKuhnGradient M Q H hH τ η ω hgood S hS hbad x)‖^2 ≤
        1+planarGradientCharge 40*(∑ e : Fin 3, (layerResolutionDiameter M Q H τ η n e ω x)^2) := by
  have hreps : ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), ∀ i : Fin 2,
      ∀ (n : ℕ) (P : TriadicCube 2), P ∈ whitneyRootLayer Q H n → x ∈ openCubeSet P →
        (stoppedGlobalKuhnCorrection M Q H hH τ η ω hgood S hS hbad i).toFun x=
          (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i n).toFun x+
          (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i (n-1)).toFun x ∧
        ∀ k, (stoppedGlobalKuhnCorrection M Q H hH τ η ω hgood S hS hbad i).grad x k=
          (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i n).grad x k+
          (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad i (n-1)).grad x k :=
    ae_all_iff.mpr (fun i => stopped_global_kuhn_correction_ae_two_groups M Q H hH τ η ω hgood S hS hbad i)
  have hcovers : ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), ∀ a : ℕ,
      ∃ U ∈ rootKuhnMesh Q (compatibleWhitneyMeshDepth H (a+1)), x ∈ U.openCarrier :=
    ae_all_iff.mpr (fun a => root_kuhn_ae_open_cover Q _)
  filter_upwards [hreps,hcovers] with x hrep hcover
  intro n P hP hxP
  have hn := root_whitney_layer_pos Q H n hP
  let e := layerPreviousResolution H n
  let Z : Fin 3 → ℝ := fun r => layerResolutionDiameter M Q H τ η n r ω x
  let A : Matrix (Fin 2) (Fin 2) ℝ := fun i k => (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad k n).grad x i
  let B : Matrix (Fin 2) (Fin 2) ℝ := fun i k => (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad k (n-1)).grad x i
  obtain ⟨U0,hU0,hxU0⟩ := hcover n
  obtain ⟨Up,hUp,hxUp⟩ := hcover (n-1)
  have hA (i k : Fin 2) : |A i k| ≤ 18*(3:ℝ)^40*Z 0 :=
    stopped_kuhn_group_resolution_bound M Q H hH τ η ω hgood S hS hbad hfinite n n le_rfl (by omega) 0
      (by simp only [layerResolutionLabel,Fin.val_zero,Nat.cast_zero,add_zero]) P hP x hxP U0 hU0 hxU0 k i
  have hB (i k : Fin 2) : |B i k| ≤ 18*(3:ℝ)^40*Z e :=
    stopped_kuhn_group_resolution_bound M Q H hH τ η ω hgood S hS hbad hfinite (n-1) n (by omega) (by omega) e
      (layer_previous_resolution_label Q H n).symm P hP x hxP Up hUp hxUp k i
  have he : e ≠ 0 := by
    intro he
    have hp := layer_previous_resolution_pos H n hn
    have hv := congrArg Fin.val he
    change (layerPreviousResolution H n).val=0 at hv
    omega
  have hZ0 (r : Fin 3) : 0 ≤ Z r := layer_resolution_diameter_nonneg M Q H τ η n r ω x
  have hZsq (r : Fin 3) : Z r ≤ (Z r)^2 :=
    real_diameter_le_square _ _ _ (hfinite _ (layer_resolution_protected Q H n r) _)
  have hF : stoppedKuhnGradient M Q H hH τ η ω hgood S hS hbad x=1+A+B := by
    ext i k
    change (diagAffineLinear Q (basisVec k)).grad x i+
      (stoppedGlobalKuhnCorrection M Q H hH τ η ω hgood S hS hbad k).grad x i= (1 : Matrix (Fin 2) (Fin 2) ℝ) i k+A i k+B i k
    rw [(hrep k n P hP hxP).2 i]
    change basisVec k i+(A i k+B i k)=_
    have hid : basisVec k i=(1 : Matrix (Fin 2) (Fin 2) ℝ) i k := by
      simp only [basisVec,Pi.single_apply,Matrix.one_apply]
    rw [hid]
    ring
  rw [hF]
  exact planar_three_resolution_operator_square 40 A B Z e he hZ0 hZsq hA hB

end
end ASDExplicitGamma.Inverse
