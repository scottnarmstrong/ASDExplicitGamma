module

public import ASDExplicitGamma.Inverse.RawShellQ3PowerGenerator
public import ASDExplicitGamma.Inverse.SourceQ3Drift
public import ASDExplicitGamma.Inverse.SourceQ3FullBracket

/-! A real-power source row assembled from the exact q3 drift and carré-du-champ bounds. -/

@[expose] public section

open Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
open ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational

namespace ASDExplicitGamma.Native

/-- The drift and complete bracket rows give the same
real-power generator estimate in the source's own coefficient frame. This
retains the sharp source covariance coefficients needed before shell
summation. -/
theorem nativeHeat_sourceTracePowerGenerator_le_profile
    (n : ℤ) (s : ℕ) (hs : 1 ≤ s) (ν σ b p : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ) (hp : 2 ≤ p)
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let Q := originCube 2 n
    let Φ := modelTraceObservable n ν σ
    let H := pureFluxMainCubeQ3Directions n b
      (q3ModelLength (n + (s : ℤ)))
    let k := pureFluxOpenResponseRestriction n x
    let Bmix := lemmaVTileHistory Q (pureFluxBankSourceDepth s)
      (responseFramePlanarCoefficientField ν σ k)
    let Brem := pureFluxSourceTileHistory Q (pureFluxBankSourceDepth s)
      (responseFramePlanarCoefficientField ν σ k)
    let B := max Bmix Brem
    let ρ := cubeScaleFactor Q / (q3ModelLength (n + (s : ℤ))).1
    let δ := diagMeshRadius Q (pureFluxBankSourceDepth s) /
      (q3ModelLength (n + (s : ℤ))).1
    let κ := lemmaVH2kn ρ δ
    let κB := lemmaVH2Bn ρ δ
    let μ := pureFluxCovarianceMu (pureFluxCovarianceA 0 (s - 1))
      (pureFluxCovarianceB 0 (s - 1))
    let v := b ^ 2 / σ ^ 2
    let Acoef := coarseBlockMatrix (cubeSet Q)
      (responsePlanarCoefficientField ν
        (ContinuousMap.linearIsometryBoundedOfCompact
          (closure (cubeSet Q)) ℝ ℝ x))
    let D := Matrix.trace (frameMatrix σ Acoef).lowerRight
    let T := Φ x
    modelPowerHeatGenerator Φ H p x ≤
      p * T ^ (p - 1) *
          (v * D + (2 * v * κ * B + v * μ * B ^ 2) * (T + 4)) +
        (p * (p - 1) / 2) * T ^ (p - 2) *
          (4 * v * T * ((1 + κ) * D +
            (κB ^ 2 + κ) * B ^ 2 * (T + 4))):= by
  classical
  intro Q Φ H k Bmix Brem B ρ δ κ κB μ v Acoef D T
  have htrace : 0 ≤ T := by
    dsimp [T, Φ]
    exact modelTraceObservable_nonneg n ν σ hν hσ x
  have hcov := source_model_q3_positive_generator_row
    n s hs ν σ b hν hσ x
  have hcov' :
      (1 / 2 : ℝ) * modelCovarianceTrace Φ H x ≤
        v * D + (2 * v * κ * B + v * μ * B ^ 2) * (T + 4) := by
    simpa [Q, Φ, H, k, Bmix, Brem, B, ρ, δ, κ, μ, v, Acoef, D, T] using hcov
  have hbracket := source_model_q3_full_bracket_row
    n s ν σ b hν hσ x
  have hbracket' :
      modelGradientSquareTrace Φ H x ≤
        4 * v * T * ((1 + κ) * D +
          (κB ^ 2 + κ) * B ^ 2 * (T + 4)) := by
    simpa [Q, Φ, H, k, Bmix, Brem, B, ρ, δ, κ, κB, v, Acoef, D, T] using hbracket
  have hp0 : 0 ≤ p := by linarith
  have hpminus : 0 ≤ p - 1 := by linarith
  have hcoef : 0 ≤ p * (p - 1) / 2 := by positivity
  have hpow1 : 0 ≤ T ^ (p - 1) := Real.rpow_nonneg htrace _
  have hpow2 : 0 ≤ T ^ (p - 2) := Real.rpow_nonneg htrace _
  change p * T ^ (p - 1) * ((1 / 2 : ℝ) * modelCovarianceTrace Φ H x) +
      (p * (p - 1) / 2) * T ^ (p - 2) * modelGradientSquareTrace Φ H x ≤ _
  exact add_le_add
    (mul_le_mul_of_nonneg_left hcov' (mul_nonneg hp0 hpow1))
    (mul_le_mul_of_nonneg_left hbracket' (mul_nonneg hcoef hpow2))

end ASDExplicitGamma.Native

end
