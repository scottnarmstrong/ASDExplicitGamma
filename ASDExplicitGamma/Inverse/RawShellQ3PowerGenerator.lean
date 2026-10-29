module

public import ASDExplicitGamma.Inverse.RawShellQ3Drift
public import ASDExplicitGamma.Inverse.RawShellQ3FullBracket
public import ASDExplicitGamma.Gaussian.GaussMomentHolder
public import ASDExplicitGamma.Gaussian.ModelHeatPower

/-! The actual q3 trace's p=20 moment-generator row in finite-p form. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
noncomputable section

theorem raw_trace_model_q3_p20_power_generator_row_tight
    (n : ℤ) (s : ℕ) (hs : 1 ≤ s) (ν σ b : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ)
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let Q := originCube 2 n
    let Φ := modelTraceObservable n ν σ
    let H := pureFluxMainCubeQ3Directions n b (q3ModelLength (n + (s : ℤ)))
    let k := pureFluxOpenResponseRestriction n x
    let Bmix := lemmaVTileHistory Q (pureFluxBankSourceDepth s)
      (responseFramePlanarCoefficientField ν σ k)
    let Brem := pureFluxSourceTileHistory Q (pureFluxBankSourceDepth s)
      (responseFramePlanarCoefficientField ν σ k)
    let B := max Bmix Brem
    let ρ := cubeScaleFactor Q / (q3ModelLength (n + (s : ℤ))).1
    let δ := diagMeshRadius Q (pureFluxBankSourceDepth s) /
      (q3ModelLength (n + (s : ℤ))).1
    let κf := lemmaVH2kn ρ δ
    let κB := lemmaVH2Bn ρ δ
    let μ := pureFluxCovarianceMu (pureFluxCovarianceA 0 (s - 1))
      (pureFluxCovarianceB 0 (s - 1))
    let v := b ^ 2 / σ ^ 2
    let Acoef := coarseBlockMatrix (cubeSet Q)
      (responsePlanarCoefficientField ν
        (ContinuousMap.linearIsometryBoundedOfCompact
          (closure (cubeSet Q)) ℝ ℝ x))
    let D := Matrix.trace (frameMatrix σ Acoef).lowerRight
    modelPowerHeatGenerator Φ H 20 x ≤
      20 * (Φ x) ^ (19 : ℝ) *
        (v * (39 + 38 * κf) * D +
          2 * v * κf * B * (Φ x + 4) +
          v * (μ + 38 * (κB ^ 2 + κf)) * B ^ 2 * (Φ x + 4)) := by
  classical
  intro Q Φ H k Bmix Brem B ρ δ κf κB μ v Acoef D
  let F := Φ x + 4
  let T := Φ x
  have hdrift := raw_trace_model_q3_positive_generator_row_tight n s hs ν σ b hν hσ x
  have hdrift' : (1 / 2 : ℝ) * modelCovarianceTrace Φ H x ≤
      v * D + (2 * v * κf * B + v * μ * B ^ 2) * F := by
    simpa [Q, Φ, H, k, Bmix, Brem, B, ρ, δ, κf, μ, v, Acoef, D, F] using hdrift
  have hbracket := raw_trace_model_q3_full_bracket_row_tight n s ν σ b hν hσ x
  have hbracket' : modelGradientSquareTrace Φ H x ≤
      4 * v * T * ((1 + κf) * D + (κB ^ 2 + κf) * B ^ 2 * F) := by
    simpa [Q, Φ, H, Bmix, Brem, B, ρ, δ, κf, κB, v, Acoef, D, T, F] using hbracket
  have hT : 0 ≤ T := by
    dsimp [T, Φ]
    exact modelTraceObservable_nonneg n ν σ hν hσ x
  have hpow : T ^ (18 : ℝ) * T = T ^ (19 : ℝ) := by
    calc
      _ = T ^ (18 : ℝ) * T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = T ^ ((18 : ℝ) + 1) :=
        (Real.rpow_add' hT (by norm_num : (18 : ℝ) + 1 ≠ 0)).symm
      _ = _ := by congr 1; norm_num
  have hgen : modelPowerHeatGenerator Φ H 20 x =
      20 * T ^ (19 : ℝ) * ((1 / 2 : ℝ) * modelCovarianceTrace Φ H x) +
        190 * T ^ (18 : ℝ) * modelGradientSquareTrace Φ H x := by
    simp [modelPowerHeatGenerator, T, Φ]
    norm_num
  calc
    modelPowerHeatGenerator Φ H 20 x =
        20 * T ^ (19 : ℝ) * ((1 / 2 : ℝ) * modelCovarianceTrace Φ H x) +
          190 * T ^ (18 : ℝ) * modelGradientSquareTrace Φ H x := hgen
    _ ≤ 20 * T ^ (19 : ℝ) *
          (v * D + (2 * v * κf * B + v * μ * B ^ 2) * F) +
        190 * T ^ (18 : ℝ) *
          (4 * v * T * ((1 + κf) * D + (κB ^ 2 + κf) * B ^ 2 * F)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hdrift' (by positivity)
      · exact mul_le_mul_of_nonneg_left hbracket' (by positivity)
    _ = 20 * T ^ (19 : ℝ) *
          (v * (39 + 38 * κf) * D + 2 * v * κf * B * F +
            v * (μ + 38 * (κB ^ 2 + κf)) * B ^ 2 * F) := by
      calc
        _ = 20 * T ^ (19 : ℝ) *
              (v * D + (2 * v * κf * B + v * μ * B ^ 2) * F) +
            760 * v * (T ^ (18 : ℝ) * T) *
              ((1 + κf) * D + (κB ^ 2 + κf) * B ^ 2 * F) := by ring
        _ = _ := by rw [hpow]; ring
    _ = _ := by rfl

end
end ASDExplicitGamma.Inverse
