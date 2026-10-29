module

public import ASDExplicitGamma.Inverse.SourceQ3PowerIdentity
public import ASDExplicitGamma.Gaussian.H3Centering

/-! Measurability and polynomial control of the canonical physical shell
covariance contraction, used for actual finite-band integrability. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
noncomputable section

theorem source_q3_directions_sq_summable (n : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l}) :
    Summable (fun j => ‖pureFluxMainCubeQ3Directions n b L j‖^2) := by
  exact @summable_sq_bounded_image ℕ (MainCubeH3 n b L)
    C(closure (cubeSet (originCube 2 n)),ℝ) inferInstance
    (mainCubeH3InnerProductSpace n b L).toNormedSpace inferInstance inferInstance
    (mainCubeQ3Directions n b L) (mainCubeQ3Directions_summable n b L) (mainCubeH3Value n b L)

/-- Canonical shell traces preserve the required test measurability and
polynomial growth, with no probabilistic moment estimate as a premise. -/
theorem source_q3_covariance_trace_regular (n : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l})
    (Φ : C(closure (cubeSet (originCube 2 n)),ℝ) → ℝ)
    (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) :
    Measurable (modelCovarianceTrace Φ (pureFluxMainCubeQ3Directions n b L)) ∧
    HasPolynomialGrowth (modelCovarianceTrace Φ (pureFluxMainCubeQ3Directions n b L)) :=
  ⟨measurable_modelCovarianceTrace Φ hΦ.1 _,
    polynomial_modelCovarianceTrace _ (source_q3_directions_sq_summable n b L) Φ hΦ⟩

end
end ASDExplicitGamma.Inverse
