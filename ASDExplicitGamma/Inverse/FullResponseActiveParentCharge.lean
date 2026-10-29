module

public import ASDExplicitGamma.Inverse.FullResponseActiveGradientCharge
public import ASDExplicitGamma.Inverse.GroupedCellIntegrals

/-! Parent-dependent wave coefficients survive the active density payment. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider Algsuperdiff.Section3.Provider.Whitney
open scoped ENNReal

noncomputable section

/-- The common gradient on all active simplices is paid by the three actual
resolution densities while retaining an arbitrary nonnegative coefficient
on each Whitney parent. Thus the parent's wave mean need not be replaced
by a layer supremum. -/
theorem hybrid_active_gradient_square_sum_le_parent_densities
    (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (hH : 333 ≤ H)
    (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
    (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
    (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)
    (hfinite : ∀ j ≤ Q.scale-(H:ℤ), ∀ z,
      diameterField (q3PlanarMarks M j τ η) ω z ≠ ∞)
    (C : HybridCell Q H S → Mat 2)
    (hC : ∀ i, ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
      x ∈ (hybridDomain i : Set (Vec 2)) →
        stoppedKuhnGradient M Q H hH τ η ω hgood S hS hbad x = C i)
    (b : WhitneyIndexedCell Q H → ℝ) (hb : ∀ P, 0 ≤ b P) :
    (∑' i : HybridActiveCell Q H S, ENNReal.ofReal
      (b (hybridParent (.inr i)) *
        (volume (hybridDomain (.inr i) : Set (Vec 2))).toReal /
          (volume (cubeSet Q)).toReal *
            ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (C (.inr i))‖^2)) ≤
      ∑' P : WhitneyIndexedCell Q H, ENNReal.ofReal
        (b P * (planarGradientCharge 40+1) *
          (∑ e : Fin 3, ∫ x in cubeSet P.2.val,
            (layerResolutionDiameter M Q H τ η P.1 e ω x)^2) /
              (volume (cubeSet Q)).toReal) := by
  classical
  let Z := fun n (e : Fin 3) x =>
    (layerResolutionDiameter M Q H τ η n e ω x)^2
  let f := fun P : WhitneyIndexedCell Q H => fun x =>
    (b P/(volume (cubeSet Q)).toReal*(planarGradientCharge 40+1)) *
      ∑ e : Fin 3, Z P.1 e x
  have hZ (P : WhitneyIndexedCell Q H) (e : Fin 3) :
      IntegrableOn (Z P.1 e) (cubeSet P.2.val) := by
    have hn : 1 ≤ P.1 := root_whitney_layer_pos Q H P.1 P.2.property
    have hh := layer_resolution_square_integrableOn M Q H hH
      (0, P.1-1) τ η e ω
    have hh' : IntegrableOn (Z P.1 e) (rootLayerCarrier Q H P.1) := by
      simpa only [Nat.add_zero, Nat.sub_add_cancel hn, Z] using hh
    exact hh'.mono_set (fun x hx => Set.mem_iUnion₂.mpr ⟨P.2.val, P.2.property, hx⟩)
  have hfi (P : WhitneyIndexedCell Q H) : IntegrableOn (f P) (cubeSet P.2.val) :=
    (integrable_finsetSum Finset.univ (fun e _ => hZ P e)).const_mul _
  have hf0 (P : WhitneyIndexedCell Q H) (x : Vec 2) : 0 ≤ f P x := by
    have hcharge : 0 ≤ planarGradientCharge 40+1 := by
      unfold planarGradientCharge
      positivity
    dsimp only [f, Z]
    exact mul_nonneg
      (mul_nonneg (div_nonneg (hb P) ENNReal.toReal_nonneg) hcharge)
      (Finset.sum_nonneg fun e _ => sq_nonneg _)
  have hsub (i : HybridActiveCell Q H S) :
      (hybridDomain (.inr i) : Set (Vec 2)) ⊆
        cubeSet (hybridParent (.inr i)).2.val :=
    (hybrid_domain_subset_parent (.inr i)).trans (openCubeSet_subset_cubeSet _)
  have hgroup := grouped_disjoint_cell_integrals_le volume
    (fun i : HybridActiveCell Q H S => (hybridDomain (.inr i) : Set (Vec 2)))
    (fun P : WhitneyIndexedCell Q H => cubeSet P.2.val)
    (fun i => hybridParent (.inr i))
    (fun i => (hybridDomain (.inr i)).measurableSet)
    (fun P => measurableSet_cubeSet P.2.val)
    (fun i j hne => hybrid_domains_disjoint Q H S
      (fun he => hne (Sum.inr_injective he))) hsub f hf0 hfi
  apply (ENNReal.tsum_le_tsum (fun i => ?_)).trans hgroup |>.trans_eq ?_
  · apply tsum_congr
    intro P
    rw [integral_const_mul, integral_finsetSum Finset.univ (fun e _ => hZ P e)]
    congr 1
    dsimp only [f, Z]
    ring
  · apply ENNReal.ofReal_le_ofReal
    have hh := hybrid_active_full_gradient_square_integral M Q H hH τ η ω
      hgood S hS hbad hfinite C hC i
    have hh' := mul_le_mul_of_nonneg_left hh
      (div_nonneg (hb (hybridParent (.inr i)))
        (ENNReal.toReal_nonneg (a := volume (cubeSet Q))))
    have hi : (∫ x in (hybridDomain (.inr i) : Set (Vec 2)),
        f (hybridParent (.inr i)) x) =
      (b (hybridParent (.inr i))/(volume (cubeSet Q)).toReal *
        (planarGradientCharge 40+1)) *
          ∑ e : Fin 3, ∫ x in (hybridDomain (.inr i) : Set (Vec 2)),
            Z (hybridParent (.inr i)).1 e x := by
      rw [integral_const_mul, integral_finsetSum Finset.univ
        (fun e _ => (hZ (hybridParent (.inr i)) e).mono_set (hsub i))]
    rw [hi]
    dsimp only [Z, hybridParent] at hh' ⊢
    convert hh' using 1 <;> ring

end
end ASDExplicitGamma.Inverse
