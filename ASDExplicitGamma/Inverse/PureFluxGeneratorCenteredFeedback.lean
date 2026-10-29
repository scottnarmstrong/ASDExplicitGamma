module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorCenteredRow
public import ASDExplicitGamma.Inverse.PureFluxGeneratorCoefficient

/-! The exact bank feedback row for distinct direction-dependent potentials. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped BigOperators
noncomputable section

theorem pureFluxQ3_centered_distinct_h10_normalized_row_bound {ι : Type*}
    (e : HilbertBasis ι ℝ WhiteNoise) (s : Finset ι) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (m q i : ℕ)
    (hρ : cubeScaleFactor Q/L.1 = pureFluxCovarianceRho q i)
    (hδ : diagMeshRadius Q m/L.1 = pureFluxCovarianceDelta q i)
    (z : ι → H10Function (openCubeSet Q)) :
    let S := pureFluxQ3CenteredDistinctRow e s b L Q m z
    (∀ U ∈ descendantsAtDepth Q m, ∀ j : Fin 2,
      Summable (fun k => (Real.sqrt 3)^(k+1)*energy U
        (cubeIncrement U (k+1) (fun x => S x j)))) ∧
    Real.sqrt (lemmaVTiledPositiveEnergy Q m S) ≤
      |b| * pureFluxCovarianceB q i *
        Real.sqrt (∑ l ∈ s, lemmaVTiledWeakEnergy Q m (z l).toH1Function.grad) := by
  have h := pureFluxQ3Centered_distinct_h10_row_bound e s b L Q m z
  have hc := pureFlux_centered_feedback_coefficient_eq q i b (cubeScaleFactor Q)
    (diagMeshRadius Q m) L.1 L.2 hρ hδ
  dsimp only at h
  rw [hc] at h
  exact h

end
end ASDExplicitGamma.Inverse
