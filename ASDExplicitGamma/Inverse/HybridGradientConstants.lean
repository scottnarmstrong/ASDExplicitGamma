module

public import ASDExplicitGamma.Inverse.HybridDissection
public import ASDExplicitGamma.Inverse.StoppedKuhnFinalFields
public import ASDExplicitGamma.Inverse.StoppedKuhnGlobalBadCells
public import ASDExplicitGamma.Inverse.StoppedKuhnGlobalIdentityCells

/-! One common family of literal hybrid slopes for every loading. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
noncomputable section

variable (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (hH : 333 ≤ H)
  (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
  (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
    (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
  (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
  (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)

/-- Actual common slopes on the hybrid partition, equal to the identity on
whole untouched cubes and exactly zero on all bad cells. The family is
chosen before every loading and represents the same global weak gradient. -/
theorem hybrid_common_gradient_constants :
    ∃ C : HybridCell Q H S → Mat 2,
      (∀ i : HybridIdentityCell Q H S, C (.inl i)=1) ∧
      (∀ i, (hybridParent i).2.val ∈ S → C i=0) ∧
      (∀ i, ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), x ∈ (hybridDomain i:Set (Vec 2)) →
        stoppedKuhnGradient M Q H hH τ η ω hgood S hS hbad x=C i) := by
  classical
  let F := fun i : HybridActiveCell Q H S =>
    if hi : i.1.val.2.val ∈ S then (0:Mat 2) else
      (stopped_kuhn_gradient_constant_on_final_simplex M Q H hH τ η ω hgood S hS hbad
        i.1.val.1 i.1.val.2.val i.1.val.2.property i.2.val i.2.property).choose
  let C : HybridCell Q H S → Mat 2 := Sum.elim (fun _ => 1) F
  refine ⟨C,fun _ => rfl,?_,?_⟩
  · intro i hi
    cases i with
    | inl i => exact (i.property i.val.2.val hi (cubeTouch_refl _)).elim
    | inr i => exact dite_eq_left hi
  · intro i
    cases i with
    | inl i =>
      have hae := ae_all_iff.mpr (fun b : Fin 2 =>
        stopped_global_kuhn_midpoint_ae_identity_cells M Q H hH τ η ω hgood S hS hbad b)
      filter_upwards [hae] with x hx
      intro hxcell
      ext a b
      change (stoppedKuhnMidpointCoordinate M Q H hH τ η ω hgood S hS hbad b).grad x a=(1:Mat 2) a b
      rw [(hx b i.val.1 i.val.2.val i.val.2.property i.property hxcell).2 a]
      simp [basisVec,Pi.single_apply,Matrix.one_apply]
    | inr i =>
      by_cases hi : i.1.val.2.val ∈ S
      · have hae := ae_all_iff.mpr (fun b : Fin 2 =>
          stopped_global_kuhn_midpoint_ae_bad_cells M Q H hH τ η ω hgood S hS hbad b)
        filter_upwards [hae] with x hx
        intro hxcell
        have hxparent := hybrid_domain_subset_parent (.inr i) hxcell
        change stoppedKuhnGradient M Q H hH τ η ω hgood S hS hbad x=F i
        dsimp only [F]
        rw [dite_eq_left hi]
        ext a b
        exact (hx b i.1.val.2.val hi hxparent).2 a
      · have hh := (stopped_kuhn_gradient_constant_on_final_simplex M Q H hH τ η ω hgood S hS hbad
          i.1.val.1 i.1.val.2.val i.1.val.2.property i.2.val i.2.property).choose_spec
        change ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), x ∈ i.2.val.openCarrier →
          stoppedKuhnGradient M Q H hH τ η ω hgood S hS hbad x=F i
        simpa only [F,dite_eq_right hi] using hh

end
end ASDExplicitGamma.Inverse
