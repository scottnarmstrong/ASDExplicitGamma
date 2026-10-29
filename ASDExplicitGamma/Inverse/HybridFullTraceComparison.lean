module

public import ASDExplicitGamma.Inverse.HybridFullVariationalComparison
public import ASDExplicitGamma.Inverse.HybridGradientConstants

/-! The actual stopped Kuhn map gives the complete four-load trace comparison
in one fixed frame, before the identity and active-cell response estimates. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- A full-response trace load after transfer of the scalar frame to its
potential and flux coordinates. -/
def hybridFullTraceLoadEnergy (σ : ℝ) (A : BlockMat 2)
    (j : Fin 2 × Bool) : ℝ :=
  let P := fullResponseTraceLoad j
  let Pσ := ((Real.sqrt σ)⁻¹ • P.1, Real.sqrt σ • P.2)
  blockVecDot Pσ (blockMatVecMul A Pσ)

/-- The same trace load on a hybrid cell after applying its common potential
gradient and planar solenoidal-flux maps. -/
def hybridFullTraceCellLoadEnergy (σ : ℝ) (A : BlockMat 2)
    (C : Mat 2) (j : Fin 2 × Bool) : ℝ :=
  let P := fullResponseTraceLoad j
  let Pσ := ((Real.sqrt σ)⁻¹ • P.1, Real.sqrt σ • P.2)
  let PσC := (matVecMul C Pσ.1, matVecMul (planarFluxMatrix C) Pσ.2)
  blockVecDot PσC (blockMatVecMul A PσC)

/-- The actual common stopped midpoint map gives a four-load comparison for
the full framed response trace. The conclusion retains every identity cube
and active simplex with its physical volume and its actual transformed pair
loading. It does not yet estimate those local responses. -/
theorem actual_hybrid_full_trace_load_sum_comparison
    (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (r : RootRow)
    (hH : rootH0 r ≤ H) (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
    (m J : ℤ) (hmJ : m ≤ J) (weights : ℤ → ℝ)
    (σ : ℝ) (hσ : 0 < σ) :
    let S := rootBadWhitneyCells M Q H τ η ω
    ∃ C : HybridCell Q H S → Mat 2,
      (∀ i : HybridIdentityCell Q H S, C (.inl i) = 1) ∧
      (∀ i, (hybridParent i).2.val ∈ S → C i = 0) ∧
      (∀ i, ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
        x ∈ (hybridDomain i : Set (Vec 2)) →
          stoppedKuhnGradient M Q H
            (by
              have hhroot : 333 ≤ rootH0 r := by
                cases r <;> norm_num [rootH0]
              exact hhroot.trans hH)
            τ η ω hgood S (fun _ h => h.1) (fun _ h => h.2) x = C i) ∧
      (∑ j : Fin 2 × Bool, ENNReal.ofReal
        (hybridFullTraceLoadEnergy σ
          (coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M m J weights ω)) j)) ≤
        ∑ j : Fin 2 × Bool, ∑' i : HybridCell Q H S, ENNReal.ofReal
          (((volume (hybridDomain i : Set (Vec 2))).toReal /
              (volume (openCubeSet Q)).toReal) *
            hybridFullTraceCellLoadEnergy σ
              (coarseBlockMatrix (hybridDomain i : Set (Vec 2))
                (attenuatedCoefficient M m J weights ω)) (C i) j) := by
  classical
  dsimp only
  let S := rootBadWhitneyCells M Q H τ η ω
  have h333 : 333 ≤ H := by
    cases r <;> norm_num [rootH0] at hH ⊢ <;> omega
  have hS : S ⊆ whitneyRootPartition Q H := fun _ h => h.1
  have hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V := fun _ h => h.2
  obtain ⟨C, hCi, hCb, hCa⟩ :=
    hybrid_common_gradient_constants M Q H h333 τ η ω hgood S hS hbad
  refine ⟨C, hCi, hCb, hCa, ?_⟩
  simpa only [hybridFullTraceLoadEnergy, hybridFullTraceCellLoadEnergy] using
    (actual_hybrid_full_four_load_comparison M Q H h333 τ η ω hgood S hS hbad
      m J hmJ weights C hCa σ hσ)

end
end ASDExplicitGamma.Inverse
