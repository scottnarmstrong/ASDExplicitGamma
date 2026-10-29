module

public import ASDExplicitGamma.Inverse.SourceMixedShearRows
public import ASDExplicitGamma.Inverse.SourcePureFluxRow

/-! The sharp source drift, using the single-direction and pure-source
coefficients. Adapted from RawShellQ3Drift before outward weakening. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
noncomputable section

/-- The two complete local histories used by the mixed and remainder source
rows are retained separately and combined by their maximum. -/
theorem source_model_q3_positive_generator_row
    (n : ℤ) (s : ℕ) (hs : 1 ≤ s) (ν σ b : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ)
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let Q := originCube 2 n
    let L := q3ModelLength (n + (s : ℤ))
    let m := pureFluxBankSourceDepth s
    let Φ := modelTraceObservable n ν σ
    let H := pureFluxMainCubeQ3Directions n b L
    let k := pureFluxOpenResponseRestriction n x
    let a := responseFramePlanarCoefficientField ν σ k
    let Bmix := lemmaVTileHistory Q m a
    let Brem := pureFluxSourceTileHistory Q m a
    let B := max Bmix Brem
    let ρ := cubeScaleFactor Q / L.1
    let δ := diagMeshRadius Q m / L.1
    let κ := lemmaVH2kn ρ δ
    let A := pureFluxCovarianceA 0 (s - 1)
    let A' := pureFluxCovarianceB 0 (s - 1)
    let μ := pureFluxCovarianceMu A A'
    let v := b ^ 2 / σ ^ 2
    let Acoef := coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField ν
      (ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet Q)) ℝ ℝ x))
    let D := Matrix.trace (frameMatrix σ Acoef).lowerRight
    (1 / 2 : ℝ) * modelCovarianceTrace Φ H x ≤
      v * D + (2 * v * κ * B + v * μ * B ^ 2) * (Φ x + 4) := by
  classical
  intro Q L m Φ H k a Bmix Brem B ρ δ κ A A' μ v Acoef D
  let center := pureFluxParentCenter n
  let C : C(closure (cubeSet Q), ℝ) →L[ℝ] (Fin 1 → ℝ) :=
    ContinuousLinearMap.pi fun _ => ContinuousMap.evalCLM ℝ center
  let I : (Fin 1 → ℝ) →L[ℝ] C(closure (cubeSet Q), ℝ) :=
    (ContinuousLinearMap.proj (0 : Fin 1)).smulRight (1 : C(closure (cubeSet Q), ℝ))
  let R := centeringMap center
  let Hess := fderiv ℝ (fderiv ℝ Φ) x
  have hsplit : (1 / 2 : ℝ) * modelCovarianceTrace Φ H x =
      centerGenerator H C I Hess +
        mixedGenerator H C I R Hess +
          (1 / 2 : ℝ) * ∑' j, Hess (R (H j)) (R (H j)) := by
    simpa [Q, L, m, Φ, H, center, C, I, R] using
      (raw_trace_model_q3_generator_split n ν σ b hν hσ L x)
  have hcenter : centerGenerator H C I Hess =
      v * D := by
    calc
      _ = b ^ 2 * (Matrix.trace (frameMatrix σ
          Acoef).lowerRight / σ ^ 2) := by
        simpa [Q, L, m, Φ, H, center, C, I, Hess, Acoef] using
          (raw_trace_model_q3_center_shear_row n ν σ b hν hσ L x)
      _ = _ := by dsimp [D, v]; ring
  have hmixed : |mixedGenerator H C I R Hess| ≤
      2 * v * κ * Bmix * (Φ x + 4) := by
    simpa [Q, L, m, Φ, H, center, C, I, R, k, a, Bmix, ρ, δ, κ,
      v, Hess] using
      (source_raw_trace_model_q3_mixed_generator_abs_le n ν σ b hν hσ m L x)
  have hrem : (1 / 2 : ℝ) * modelCovarianceTrace Φ (fun j => R (H j)) x ≤
      v * μ * Brem ^ 2 * (Φ x + 4) := by
    simpa [Q, L, m, Φ, H, center, C, I, R, k, a, Brem, A, A', μ, v] using
      (source_model_q3_remainder_covariance_row n s hs ν σ b hν hσ x)
  have hremSum : (1 / 2 : ℝ) * ∑' j, Hess (R (H j)) (R (H j)) =
      (1 / 2 : ℝ) * modelCovarianceTrace Φ (fun j => R (H j)) x := by
    rw [modelCovarianceTrace]
    congr 1
    apply tsum_congr
    intro j
    exact (second_fderiv_eq
      (modelTraceObservable_hasPolynomiallyBoundedC2Derivatives n ν σ hν hσ).1
      x (R (H j)) (R (H j))).symm
  have hBmix0 : 0 ≤ Bmix := by
    simpa [Q, m, a] using lemmaVTileHistory_nonneg Q m a
  have hBrem0 : 0 ≤ Brem := by
    simpa [Q, m, a] using pureFlux_source_tile_history_nonneg Q m a
  have hBmixB : Bmix ≤ B := le_max_left _ _
  have hBremB : Brem ≤ B := le_max_right _ _
  have hB0 : 0 ≤ B := le_max_of_le_left hBmix0
  have hT4 : 0 ≤ Φ x + 4 := by
    have hΦ0 : 0 ≤ Φ x := by simpa [Φ] using modelTraceObservable_nonneg n ν σ hν hσ x
    positivity
  have hv : 0 ≤ v := by positivity
  have hρ : 0 ≤ ρ := by
    dsimp [ρ, Q, L]
    exact div_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos'
      (originCube 2 n)).le
      L.2.le
  have hδ : 0 ≤ δ := by
    dsimp [δ, Q, m, L]
    exact div_nonneg
      (diagMeshRadius_pos (originCube 2 n) (pureFluxBankSourceDepth s)).le
      L.2.le
  have hκ : 0 ≤ κ := by
    dsimp [κ]
    unfold lemmaVH2kn lemmaVH2R1 lemmaVH2C1 lemmaVH2C2
    positivity
  have hμ : 0 ≤ μ := (pureFlux_covariance_mu_lower A A').1
  have hmixGrow : 2 * v * κ * Bmix * (Φ x + 4) ≤
      2 * v * κ * B * (Φ x + 4) := by
    have hc : 0 ≤ 2 * v * κ * (Φ x + 4) := by positivity
    calc
      _ = (2 * v * κ * (Φ x + 4)) * Bmix := by ring
      _ ≤ (2 * v * κ * (Φ x + 4)) * B := mul_le_mul_of_nonneg_left hBmixB hc
      _ = _ := by ring
  have hsq : Brem ^ 2 ≤ B ^ 2 := by nlinarith [sq_nonneg (B - Brem)]
  have hremGrow : v * μ * Brem ^ 2 * (Φ x + 4) ≤
      v * μ * B ^ 2 * (Φ x + 4) := by
    have hc : 0 ≤ v * μ * (Φ x + 4) := by positivity
    calc
      _ = (v * μ * (Φ x + 4)) * Brem ^ 2 := by ring
      _ ≤ (v * μ * (Φ x + 4)) * B ^ 2 := mul_le_mul_of_nonneg_left hsq hc
      _ = _ := by ring
  have hcomponents :
      centerGenerator H C I Hess + mixedGenerator H C I R Hess +
        (1 / 2 : ℝ) * ∑' j, Hess (R (H j)) (R (H j)) ≤
      v * D + 2 * v * κ * Bmix * (Φ x + 4) +
        v * μ * Brem ^ 2 * (Φ x + 4) := by
    rw [hcenter, hremSum]
    have hmixUpper : mixedGenerator H C I R Hess ≤
        2 * v * κ * Bmix * (Φ x + 4) :=
      (le_abs_self _).trans hmixed
    have hremUpper := hrem
    nlinarith [hmixUpper, hremUpper]
  calc
    (1 / 2 : ℝ) * modelCovarianceTrace Φ H x =
        centerGenerator H C I Hess + mixedGenerator H C I R Hess +
          (1 / 2 : ℝ) * ∑' j, Hess (R (H j)) (R (H j)) := hsplit
    _ ≤ v * D + (2 * v * κ * B + v * μ * B ^ 2) * (Φ x + 4) := by
      nlinarith [hcomponents, hmixGrow, hremGrow, hcenter]

end
end ASDExplicitGamma.Inverse
