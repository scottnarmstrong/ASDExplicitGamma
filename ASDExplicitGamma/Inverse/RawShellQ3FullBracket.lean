module

public import ASDExplicitGamma.Inverse.RawShellQ3Bracket
public import ASDExplicitGamma.Native.VanishingBracket

/-! The actual fresh-q3 OLD trace carré-du-champ row. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational
noncomputable section

/-- The full first-gradient-square bracket for the actual fresh-q3 OLD trace.
The center, covariance-defect cross term, and centered remainder are all kept
until the exact finite-p Young bracket is applied. -/
theorem raw_trace_model_q3_full_bracket_row
    (n : ℤ) (s : ℕ) (ν σ b : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ)
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let Q := originCube 2 n
    let K := closure (cubeSet Q)
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
    let κf := rawTraceRemainderKappaF ρ δ
    let κB := rawTraceRemainderB ρ δ
    let v := b ^ 2 / σ ^ 2
    let kclosed : ResponseCoefficient (cubeSet Q) :=
      ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ x
    let A := coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField ν kclosed)
    let D := Matrix.trace (frameMatrix σ A).lowerRight
    modelGradientSquareTrace Φ H x ≤
      4 * v * Φ x * ((1 + κf) * D + (κB ^ 2 + κf) * B ^ 2 * (Φ x + 4)) := by
  classical
  intro Q K Φ H k Bmix Brem B ρ δ κf κB v kclosed A D
  let center := pureFluxParentCenter n
  let R := fun j => centeringMap center (H j)
  let defect : C(K, ℝ) :=
    ⟨fun y => q3CovarianceDefect (q3ModelLength (n + (s : ℤ))).1
        center.1 y.1,
      (q3CovarianceDefect_contDiff
        (q3ModelLength (n + (s : ℤ))).1 center.1).continuous.comp
        continuous_subtype_val⟩
  let T := Φ x
  let F := T + 4
  let z := Variational.shearTraceLinear A
  let df := σ * fderiv ℝ Φ x defect
  let ΓR := ∑' j, (fderiv ℝ Φ x (R j)) ^ 2
  have hdecomp := raw_trace_model_q3_gradient_square_decomposition
    n ν σ b (q3ModelLength (n + (s : ℤ))) x
  have hgrad : modelGradientSquareTrace Φ H x =
      b ^ 2 * (fderiv ℝ Φ x 1) ^ 2 +
        2 * b ^ 2 * (fderiv ℝ Φ x 1) * (fderiv ℝ Φ x defect) + ΓR := by
    simpa [Q, K, Φ, H, center, R, defect, ΓR] using hdecomp.2
  have hlinear := raw_trace_model_constant_shear_first_derivative n ν σ hν hσ x
  have hzframe : σ * fderiv ℝ Φ x (1 : C(K, ℝ)) = 2 * z := by
    simpa [Q, K, kclosed, A, z, Φ] using hlinear
  have hD1 : fderiv ℝ Φ x (1 : C(K, ℝ)) = (2 * z) / σ := by
    calc
      _ = σ⁻¹ * (σ * fderiv ℝ Φ x 1) := by field_simp [hσ.ne']
      _ = σ⁻¹ * (2 * z) := by rw [hzframe]
      _ = _ := by ring
  have htrace := raw_trace_model_q3_covariance_defect_bracket_row
    n (pureFluxBankSourceDepth s) ν σ (q3ModelLength (n + (s : ℤ)))
      hν hσ x
  have hdfabs : |df| ≤ 2 * κf * Bmix * Real.sqrt (T * F) := by
    simpa [Q, K, Φ, center, k, Bmix, ρ, δ, κf, defect, T, F, df] using htrace
  have hrem := raw_trace_model_q3_remainder_bracket_row n s ν σ b hν hσ x
  have hremSum : Summable (fun j => (fderiv ℝ Φ x (R j)) ^ 2) := by
    simpa [Q, K, Φ, H, center, R, k, Brem, ρ, δ, v] using hrem.1
  have hremBound : ΓR ≤ 4 * v * κB ^ 2 * Bmix ^ 2 * T * F := by
    simpa [Q, K, Φ, H, center, R, k, Bmix, ρ, δ, v, κB, ΓR, T, F] using hrem.2
  have hT : 0 ≤ T := by
    dsimp [T, Φ]
    exact modelTraceObservable_nonneg n ν σ hν hσ x
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hBmix : 0 ≤ Bmix := by
    simpa [Q, k] using lemmaVTileHistory_nonneg Q (pureFluxBankSourceDepth s)
      (responseFramePlanarCoefficientField ν σ k)
  have hBrem : 0 ≤ Brem := by
    simpa [Q, k] using pureFlux_source_tile_history_nonneg Q
      (pureFluxBankSourceDepth s) (responseFramePlanarCoefficientField ν σ k)
  have hB : 0 ≤ B := le_max_of_le_left hBmix
  have hBmixB : Bmix ≤ B := le_max_left _ _
  have hBremB : Brem ≤ B := le_max_right _ _
  have hBmixSq : Bmix ^ 2 ≤ B ^ 2 := by nlinarith [sq_nonneg (B - Bmix)]
  have hρ : 0 ≤ ρ := by
    dsimp [ρ, Q]
    exact div_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos'
      (originCube 2 n)).le
      (q3ModelLength (n + (s : ℤ))).2.le
  have hδ : 0 ≤ δ := by
    dsimp [δ, Q]
    exact div_nonneg (diagMeshRadius_pos (originCube 2 n)
      (pureFluxBankSourceDepth s)).le (q3ModelLength (n + (s : ℤ))).2.le
  have hκf : 0 ≤ κf := by
    dsimp [κf]
    unfold rawTraceRemainderKappaF
    positivity
  have hκB : 0 ≤ κB := by
    dsimp [κB]
    unfold rawTraceRemainderB
    positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hσ2 : 0 < σ ^ 2 := sq_pos_of_pos hσ
  have hrows := nativeTraceShearDefectRows Q ν σ hν hσ kclosed
  have hTrows : traceDefect (cubeSet Q) (responsePlanarCoefficientField ν kclosed) σ = T := by
    rfl
  have hDnorm : 0 < D / σ ^ 2 := by
    simpa [Q, A, D, kclosed, T, Φ, hTrows] using hrows.2.1
  have hD : 0 < D := by
    have hprod : 0 < (D / σ ^ 2) * σ ^ 2 := mul_pos hDnorm hσ2
    have heq : (D / σ ^ 2) * σ ^ 2 = D := div_mul_cancel₀ D hσ2.ne'
    rw [heq] at hprod
    exact hprod
  have hz : z ^ 2 ≤ D * T := by
    have hz' := Variational.shearTraceLinear_sq_le Q ν σ hν hσ kclosed
    simpa [Q, A, D, T, Φ, hTrows] using hz'
  have hdf : df ^ 2 ≤ 4 * κf ^ 2 * B ^ 2 * T * F := by
    have hdfNonneg : 0 ≤ 2 * κf * Bmix * Real.sqrt (T * F) := by positivity
    have hsquare := pow_le_pow_left₀ (abs_nonneg df) hdfabs 2
    have hsqrt : 0 ≤ T * F := mul_nonneg hT hF
    calc
      df ^ 2 = |df| ^ 2 := (sq_abs df).symm
      _ ≤ (2 * κf * Bmix * Real.sqrt (T * F)) ^ 2 := hsquare
      _ = 4 * κf ^ 2 * Bmix ^ 2 * T * F := by
        rw [mul_pow, Real.sq_sqrt hsqrt]
        ring
      _ ≤ 4 * κf ^ 2 * B ^ 2 * T * F := by
        have hc : 0 ≤ 4 * κf ^ 2 * T * F := by positivity
        calc
          _ = (4 * κf ^ 2 * T * F) * Bmix ^ 2 := by ring
          _ ≤ (4 * κf ^ 2 * T * F) * B ^ 2 := mul_le_mul_of_nonneg_left hBmixSq hc
          _ = _ := by ring
  have hrem' : ΓR ≤ 4 * v * κB ^ 2 * B ^ 2 * T * F := by
    calc
      _ ≤ 4 * v * κB ^ 2 * Bmix ^ 2 * T * F := hremBound
      _ = (4 * v * κB ^ 2 * T * F) * Bmix ^ 2 := by ring
      _ ≤ (4 * v * κB ^ 2 * T * F) * B ^ 2 := by
        have hc : 0 ≤ 4 * v * κB ^ 2 * T * F := by positivity
        exact mul_le_mul_of_nonneg_left hBmixSq hc
      _ = _ := by ring
  have hbracket := nativeConstantRemainderShellBracket_le
    v κf κB B T F D z df ΓR hv hκf hB hT hF hD.le rfl hz hdf hrem'
  have hidentity :
      modelGradientSquareTrace Φ H x =
        v * (2 * z) ^ 2 + 2 * v * (2 * z) * df + ΓR := by
    rw [hgrad, hD1]
    dsimp [v, df]
    field_simp [hσ.ne']
  rw [hidentity]
  simpa [T, F] using hbracket


theorem raw_trace_model_q3_full_bracket_row_tight
    (n : ℤ) (s : ℕ) (ν σ b : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ)
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let Q := originCube 2 n
    let K := closure (cubeSet Q)
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
    let v := b ^ 2 / σ ^ 2
    let kclosed : ResponseCoefficient (cubeSet Q) :=
      ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ x
    let A := coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField ν kclosed)
    let D := Matrix.trace (frameMatrix σ A).lowerRight
    modelGradientSquareTrace Φ H x ≤
      4 * v * Φ x * ((1 + κf) * D + (κB ^ 2 + κf) * B ^ 2 * (Φ x + 4)) := by
  classical
  intro Q K Φ H k Bmix Brem B ρ δ κf κB v kclosed A D
  let center := pureFluxParentCenter n
  let R := fun j => centeringMap center (H j)
  let defect : C(K, ℝ) :=
    ⟨fun y => q3CovarianceDefect (q3ModelLength (n + (s : ℤ))).1
        center.1 y.1,
      (q3CovarianceDefect_contDiff
        (q3ModelLength (n + (s : ℤ))).1 center.1).continuous.comp
        continuous_subtype_val⟩
  let T := Φ x
  let F := T + 4
  let z := Variational.shearTraceLinear A
  let df := σ * fderiv ℝ Φ x defect
  let ΓR := ∑' j, (fderiv ℝ Φ x (R j)) ^ 2
  have hdecomp := raw_trace_model_q3_gradient_square_decomposition
    n ν σ b (q3ModelLength (n + (s : ℤ))) x
  have hgrad : modelGradientSquareTrace Φ H x =
      b ^ 2 * (fderiv ℝ Φ x 1) ^ 2 +
        2 * b ^ 2 * (fderiv ℝ Φ x 1) * (fderiv ℝ Φ x defect) + ΓR := by
    simpa [Q, K, Φ, H, center, R, defect, ΓR] using hdecomp.2
  have hlinear := raw_trace_model_constant_shear_first_derivative n ν σ hν hσ x
  have hzframe : σ * fderiv ℝ Φ x (1 : C(K, ℝ)) = 2 * z := by
    simpa [Q, K, kclosed, A, z, Φ] using hlinear
  have hD1 : fderiv ℝ Φ x (1 : C(K, ℝ)) = (2 * z) / σ := by
    calc
      _ = σ⁻¹ * (σ * fderiv ℝ Φ x 1) := by field_simp [hσ.ne']
      _ = σ⁻¹ * (2 * z) := by rw [hzframe]
      _ = _ := by ring
  have htrace := raw_trace_model_q3_covariance_defect_bracket_row_tight
    n (pureFluxBankSourceDepth s) ν σ (q3ModelLength (n + (s : ℤ)))
      hν hσ x
  have hdfabs : |df| ≤ 2 * κf * Bmix * Real.sqrt (T * F) := by
    simpa [Q, K, Φ, center, k, Bmix, ρ, δ, κf, defect, T, F, df] using htrace
  have hrem := raw_trace_model_q3_remainder_bracket_row_tight n s ν σ b hν hσ x
  have hremSum : Summable (fun j => (fderiv ℝ Φ x (R j)) ^ 2) := by
    simpa [Q, K, Φ, H, center, R, k, Brem, ρ, δ, v] using hrem.1
  have hremBound : ΓR ≤ 4 * v * κB ^ 2 * Bmix ^ 2 * T * F := by
    simpa [Q, K, Φ, H, center, R, k, Bmix, ρ, δ, v, κB, ΓR, T, F] using hrem.2
  have hT : 0 ≤ T := by
    dsimp [T, Φ]
    exact modelTraceObservable_nonneg n ν σ hν hσ x
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hBmix : 0 ≤ Bmix := by
    simpa [Q, k] using lemmaVTileHistory_nonneg Q (pureFluxBankSourceDepth s)
      (responseFramePlanarCoefficientField ν σ k)
  have hBrem : 0 ≤ Brem := by
    simpa [Q, k] using pureFlux_source_tile_history_nonneg Q
      (pureFluxBankSourceDepth s) (responseFramePlanarCoefficientField ν σ k)
  have hB : 0 ≤ B := le_max_of_le_left hBmix
  have hBmixB : Bmix ≤ B := le_max_left _ _
  have hBremB : Brem ≤ B := le_max_right _ _
  have hBmixSq : Bmix ^ 2 ≤ B ^ 2 := by nlinarith [sq_nonneg (B - Bmix)]
  have hρ : 0 ≤ ρ := by
    dsimp [ρ, Q]
    exact div_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos'
      (originCube 2 n)).le
      (q3ModelLength (n + (s : ℤ))).2.le
  have hδ : 0 ≤ δ := by
    dsimp [δ, Q]
    exact div_nonneg (diagMeshRadius_pos (originCube 2 n)
      (pureFluxBankSourceDepth s)).le (q3ModelLength (n + (s : ℤ))).2.le
  have hκf : 0 ≤ κf := by
    dsimp [κf]
    unfold lemmaVH2kn lemmaVH2C1 lemmaVH2C2 lemmaVH2R1
    positivity
  have hκB : 0 ≤ κB := by
    dsimp [κB]
    unfold lemmaVH2Bn lemmaVH2R1 lemmaVH2C1 lemmaVH2C2 lemmaVH2A2
    positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hσ2 : 0 < σ ^ 2 := sq_pos_of_pos hσ
  have hrows := nativeTraceShearDefectRows Q ν σ hν hσ kclosed
  have hTrows : traceDefect (cubeSet Q) (responsePlanarCoefficientField ν kclosed) σ = T := by
    rfl
  have hDnorm : 0 < D / σ ^ 2 := by
    simpa [Q, A, D, kclosed, T, Φ, hTrows] using hrows.2.1
  have hD : 0 < D := by
    have hprod : 0 < (D / σ ^ 2) * σ ^ 2 := mul_pos hDnorm hσ2
    have heq : (D / σ ^ 2) * σ ^ 2 = D := div_mul_cancel₀ D hσ2.ne'
    rw [heq] at hprod
    exact hprod
  have hz : z ^ 2 ≤ D * T := by
    have hz' := Variational.shearTraceLinear_sq_le Q ν σ hν hσ kclosed
    simpa [Q, A, D, T, Φ, hTrows] using hz'
  have hdf : df ^ 2 ≤ 4 * κf ^ 2 * B ^ 2 * T * F := by
    have hdfNonneg : 0 ≤ 2 * κf * Bmix * Real.sqrt (T * F) := by positivity
    have hsquare := pow_le_pow_left₀ (abs_nonneg df) hdfabs 2
    have hsqrt : 0 ≤ T * F := mul_nonneg hT hF
    calc
      df ^ 2 = |df| ^ 2 := (sq_abs df).symm
      _ ≤ (2 * κf * Bmix * Real.sqrt (T * F)) ^ 2 := hsquare
      _ = 4 * κf ^ 2 * Bmix ^ 2 * T * F := by
        rw [mul_pow, Real.sq_sqrt hsqrt]
        ring
      _ ≤ 4 * κf ^ 2 * B ^ 2 * T * F := by
        have hc : 0 ≤ 4 * κf ^ 2 * T * F := by positivity
        calc
          _ = (4 * κf ^ 2 * T * F) * Bmix ^ 2 := by ring
          _ ≤ (4 * κf ^ 2 * T * F) * B ^ 2 := mul_le_mul_of_nonneg_left hBmixSq hc
          _ = _ := by ring
  have hrem' : ΓR ≤ 4 * v * κB ^ 2 * B ^ 2 * T * F := by
    calc
      _ ≤ 4 * v * κB ^ 2 * Bmix ^ 2 * T * F := hremBound
      _ = (4 * v * κB ^ 2 * T * F) * Bmix ^ 2 := by ring
      _ ≤ (4 * v * κB ^ 2 * T * F) * B ^ 2 := by
        have hc : 0 ≤ 4 * v * κB ^ 2 * T * F := by positivity
        exact mul_le_mul_of_nonneg_left hBmixSq hc
      _ = _ := by ring
  have hbracket := nativeConstantRemainderShellBracket_le
    v κf κB B T F D z df ΓR hv hκf hB hT hF hD.le rfl hz hdf hrem'
  have hidentity :
      modelGradientSquareTrace Φ H x =
        v * (2 * z) ^ 2 + 2 * v * (2 * z) * df + ΓR := by
    rw [hgrad, hD1]
    dsimp [v, df]
    field_simp [hσ.ne']
  rw [hidentity]
  simpa [T, F] using hbracket

end
end ASDExplicitGamma.Inverse
