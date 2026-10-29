module

public import ASDExplicitGamma.Inverse.RootClockedObservables
public import ASDExplicitGamma.Inverse.RootPositiveSeriesComparison
public import ASDExplicitGamma.Inverse.RootOperatorNorm

/-! The actual deterministic positive root comparison at a successful height. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The exact positive source root bound at any successful height. The
complete positive E_l is used without a response subtraction, and the
comparison is uniform in all flux loadings before taking the operator norm. -/
theorem positive_root_bound_of_successful_height (M : ABKModel 2) (hg : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (H : ℕ) (r : RootRow) (hH : rootH0 r ≤ H) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) (rootTau r)
        (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r))) k (rootBlockStart Q k))
    (hfinite : ∀ j ≤ Q.scale-(H:ℤ), ∀ z, diameterField
      (q3PlanarMarks M j (rootTau r) (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r))) ω z ≠ ∞)
    (m J : ℤ) (hQ : Q.scale ≤ m) (hm : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (hmean : ClippedInverseMeanInput M m r) :
    ENNReal.ofReal (rootInverseResponse M Q m J weights ω) ≤
      ENNReal.ofReal ((3:ℝ)^(2*M.gamma*|(m-Q.scale+1:ℤ)|))*
        (ENNReal.ofReal (rootLi M.gamma r)*ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((H:ℝ)-38)))+
          positiveRootError M Q r ω) := by
  apply root_norm_le_of_all_unit_energies M Q m J hm weights ω
  intro q hq
  have hroot := actual_root_energy_le_clocked_observables M Q H r hH ω hgood hfinite m J hQ hm weights hw q hq
  have hterms := ENNReal.tsum_le_tsum (fun k : ℕ =>
    root_layer_positive_energy M Q m hQ r hmean (H-rootH0 r,k) ω q hq
      ((3:ℝ)^(2*M.gamma*(localizationResetAbscissa (rootH0 r-38) (H-rootH0 r) k:ℝ))) (by positivity))
  have hs := (mul_le_mul_right hterms (ENNReal.ofReal (rootEdelta r))).trans
    (root_positive_layer_series_le M hg Q r H hH ω)
  exact hroot.trans (mul_le_mul_right hs _)

end
end ASDExplicitGamma.Inverse
