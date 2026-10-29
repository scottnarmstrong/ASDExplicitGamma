module

public import ASDExplicitGamma.Native.ParentBoundaryCommonAffineGenerator
public import ASDExplicitGamma.Native.ParentBoundaryCommonSquareBracket
public import ASDExplicitGamma.Gaussian.SquareBounds

/-! Complete common-center trace drift on every descendant observation square. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Main Model Response Triadic Variational Scalar Inverse
open scoped BigOperators
noncomputable section

/-- The actual full covariance drift of the common-center trace, in the
true frame and with the complete actual source-cell inverse histories. -/
theorem parent_boundary_common_trace_generator
    (P0 Q : TriadicCube 2) (hQP : cubeSet Q ⊆ cubeSet P0)
    (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (L : {l : ℝ // 0 < l}) (m : ℕ)
    (k : ResponseCoefficient (openCubeSet Q)) :
    let T := squareTrace Q ν σ k
    let B := pureFluxSourceTileHistory Q m (responseFramePlanarCoefficientField ν σ k)
    (1/2:ℝ)*modelCovarianceTrace (squareTrace Q ν σ)
      (parentBoundaryCommonResponseDirections P0 Q b L) k ≤
      |σ⁻¹|^2*pureFluxCovarianceMu (parentBoundaryCommonRowCoefficient P0 Q b L m)
        (parentBoundaryCommonFeedbackCoefficient P0 Q b L m)*B^2*(T+4) := by
  intro T B
  let H := parentBoundaryCommonResponseDirections P0 Q b L
  let E := squareLoadEnergy Q ν σ hν hσ
  let C := |σ⁻¹|^2*pureFluxCovarianceMu (parentBoundaryCommonRowCoefficient P0 Q b L m)
    (parentBoundaryCommonFeedbackCoefficient P0 Q b L m)*B^2
  have hH := parent_boundary_common_response_directions_summable P0 Q b L
  have hE (p : Fin 2 × Bool) : ContDiff ℝ 2 (E p) :=
    responseFrameEnergyObservable_contDiff _ _ ν σ hν hσ _
  have hs (p : Fin 2 × Bool) : Summable (fun n => secondDirectionalDerivative (E p) k (H n)) :=
    pureFlux_secondDirectionalDerivative_summable _ (hE p) H hH k
  have heq : modelCovarianceTrace (squareTrace Q ν σ) H k =
      ∑ p : Fin 2 × Bool,modelCovarianceTrace (E p) H k := by
    calc
      _ = ∑' n,∑ p : Fin 2 × Bool,secondDirectionalDerivative (E p) k (H n) := by
        apply tsum_congr
        intro n
        exact squareTrace_secondDirectional_eq_load_sum Q ν σ hν hσ k (H n)
      _ = ∑ p : Fin 2 × Bool,∑' n,secondDirectionalDerivative (E p) k (H n) :=
        Summable.tsum_finsetSum (fun p _ => hs p)
      _ = _ := rfl
  have hload (p : Fin 2 × Bool) : (1/2:ℝ)*modelCovarianceTrace (E p) H k ≤ C*E p k :=
    parent_boundary_common_affine_generator P0 Q hQP ν σ b hν hσ L m
      (orthonormalFrameLoad p.1 (lemmaVLoadSign p.2)) k B
      (pureFlux_source_tile_history_nonneg Q m _)
      (pureFlux_source_tile_history_member_le Q m _)
  have hall := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 2 × Bool))) (fun p _ => hload p)
  rw [← Finset.mul_sum,← Finset.mul_sum,← heq] at hall
  have hsum : (∑ p : Fin 2 × Bool,E p k)=T+4 := by
    dsimp only [T]
    rw [squareTrace_eq_load_sum Q ν σ hν hσ]
    dsimp only [E]
    ring
  rw [hsum] at hall
  exact hall

end
end ASDExplicitGamma.Native
