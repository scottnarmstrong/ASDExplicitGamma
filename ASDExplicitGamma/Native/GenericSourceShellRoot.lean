module

public import ASDExplicitGamma.Inverse.RawShellBankInputs
public import ASDExplicitGamma.Inverse.RawShellBankMoment
public import ASDExplicitGamma.Inverse.RawShellQ3Law
public import ASDExplicitGamma.Inverse.SourceQ3Drift
public import ASDExplicitGamma.Inverse.SourceQ3FullBracket
public import ASDExplicitGamma.Inverse.BankHeatIntegrability
public import ASDExplicitGamma.Inverse.BankOnePassHeat
public import ASDExplicitGamma.Gaussian.ModelHeatTrace
public import ASDExplicitGamma.Gaussian.ModelHeatPower
public import ASDExplicitGamma.Inverse.RawMomentRoot
public import ASDExplicitGamma.Native.VanishingBracket
public import ASDExplicitGamma.Triadic.DiagInterpolant
public import ASDExplicitGamma.Inverse.FullResponseCoefficientTransport
public import ASDExplicitGamma.Inverse.BankObservers
public import ASDExplicitGamma.Model.Cutoff
public import ASDExplicitGamma.Inverse.PureFluxGeneratorBankLaw
public import ASDExplicitGamma.Inverse.BankOnePassMeanActual
public import ASDExplicitGamma.Gaussian.ShellBracket
public import ASDExplicitGamma.Native.GenericSourceBankAdapter
public import ASDExplicitGamma.Gaussian.ModelHeatResponse
public import ASDExplicitGamma.Inverse.SourceCovarianceCaps

/-! Actual source-shell p20 root increments at every partial insertion time. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Response ASDExplicitGamma.Variational
open ASDExplicitGamma.Triadic ASDExplicitGamma.Inverse
noncomputable section

/-- The sharp single-direction coefficient at shell `i+1`. -/
def nativeSourceShellK (i : ℕ) : ℝ :=
  lemmaVH2kn (pureFluxCovarianceRho 0 i) (pureFluxCovarianceDelta 0 i)

/-- The sharp remainder and single-direction bracket coefficient at shell `i+1`. -/
def nativeSourceShellQ (i : ℕ) : ℝ :=
  (pureFluxCovarianceB 0 i)^2 + nativeSourceShellK i

/-- The genuine pure-source feedback coefficient at shell `i+1`. -/
def nativeSourceShellMu (i : ℕ) : ℝ :=
  pureFluxCovarianceMu (pureFluxCovarianceA 0 i) (pureFluxCovarianceB 0 i)

theorem native_source_shell_coefficients_nonneg (i : ℕ) :
    0 ≤ nativeSourceShellK i ∧ 0 ≤ nativeSourceShellQ i ∧ 0 ≤ nativeSourceShellMu i := by
  have hρ := (pureFlux_covariance_rho_pos 0 i).le
  have hδ := (pureFlux_covariance_delta_bounds 0 i).1
  have hκ : 0 ≤ nativeSourceShellK i := by
    unfold nativeSourceShellK lemmaVH2kn lemmaVH2R1 lemmaVH2C1 lemmaVH2C2
    positivity
  exact ⟨hκ,add_nonneg (sq_nonneg _) hκ,(pureFlux_covariance_mu_lower _ _).1⟩

end
end ASDExplicitGamma.Native
