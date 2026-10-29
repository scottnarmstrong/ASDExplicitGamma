module

public import ASDExplicitGamma.Main.ErrorCoefficients
public import ASDExplicitGamma.Main.ELinearCauchy
public import ASDExplicitGamma.Native.OldSignedFlatProfileCaps
public import ASDExplicitGamma.Native.OldSignedRemainderCovarianceVector
public import ASDExplicitGamma.Native.OldSignedFlatCovarianceFeedback
public import ASDExplicitGamma.Native.BoundaryChargeFlatConstants

/-! The sharp root-mean-square cap of the covariance beta (either sign flag) by D-main's
`mainBe`: harmonic-remainder energy `B_flat/2 <= v q/2` plus the planar Poincare
cell oscillation, for observers with cell side at most `3^-6` times the flat
length. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization ASDExplicitGamma.Native ASDExplicitGamma.Triadic

noncomputable section

/-- RMS beta cap: the cell average of `beta_U²` is at most `mainBe (b²) q ²`. -/
theorem main_covariance_beta_rms_le_mainBe_flag (plus : Bool) (Q : TriadicCube 2) (d : ℕ) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (q : ℝ)
    (hq : oldSignedFlatBoundaryEnergy Q b L ≤ b ^ 2 * q) (hq0 : 0 ≤ q)
    (hr : cubeScaleFactor Q / (3 : ℝ) ^ d ≤ (3 : ℝ) ^ (-6 : ℤ) * L.1) :
    Real.sqrt (descendantsAverage Q d (fun U =>
      oldSignedCovarianceBeta Q U b L plus ^ 2)) ≤ mainBe (b ^ 2) q := by
  have hb := old_signed_covariance_beta_bound Q d b L plus
  have hsq : descendantsAverage Q d (fun U => oldSignedCovarianceBeta Q U b L plus ^ 2) =
      descendantsAverage Q d (fun U => ∑ i : Fin 2,
        vectorPositiveHaarNorm U (oldSignedRemainderCovarianceField Q b L plus i) ^ 2) := by
    unfold descendantsAverage
    dsimp only
    congr 1
    apply Finset.sum_congr rfl
    intro U _
    unfold oldSignedCovarianceBeta
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  rw [hsq]
  refine hb.trans ?_
  have hL := L.2
  have hB0 : Real.sqrt (oldSignedFlatBoundaryEnergy Q b L / 2) ≤ |b| * Real.sqrt (q / 2) := by
    rw [← Real.sqrt_sq (abs_nonneg b), ← Real.sqrt_mul (sq_nonneg _), sq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hσ : Real.sqrt (mainFlatSigmaSq b L) = Real.sqrt (156 / 5) * |b| / L.1 := by
    unfold mainFlatSigmaSq
    rw [show 2 * (b ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ)) = (156 / 5) * (|b| / L.1) ^ 2 by
      rw [div_pow, sq_abs]; ring, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
    ring
  have hR0 : 0 ≤ cubeScaleFactor Q / (3 : ℝ) ^ d := by unfold cubeScaleFactor; positivity
  have hc1 : planarC1 ≤ 304 / 1000 := native_boundary_planarC1_le
  have hc10 : 0 ≤ planarC1 := Real.sqrt_nonneg _
  have hRs : cubeScaleFactor Q / (3 : ℝ) ^ d * Real.sqrt (mainFlatSigmaSq b L) ≤
      (3 : ℝ) ^ (-6 : ℤ) * (Real.sqrt (156 / 5) * |b|) := by
    rw [hσ]
    calc cubeScaleFactor Q / (3 : ℝ) ^ d * (Real.sqrt (156 / 5) * |b| / L.1)
        ≤ ((3 : ℝ) ^ (-6 : ℤ) * L.1) * (Real.sqrt (156 / 5) * |b| / L.1) :=
          mul_le_mul_of_nonneg_right hr (by positivity)
      _ = _ := by field_simp
  have hq2 : 0 ≤ Real.sqrt (q / 2) := Real.sqrt_nonneg _
  have hmid : cubeScaleFactor Q / (3 : ℝ) ^ d * planarC1 *
      (Real.sqrt (mainFlatSigmaSq b L) * Real.sqrt (oldSignedFlatBoundaryEnergy Q b L / 2) +
        2 * |b| * Real.sqrt (mainFlatSigmaSq b L)) ≤
      (304 / 1000) * ((3 : ℝ) ^ (-6 : ℤ) * (Real.sqrt (156 / 5) * |b|)) *
        (|b| * Real.sqrt (q / 2) + 2 * |b|) := by
    have e1 : cubeScaleFactor Q / (3 : ℝ) ^ d * planarC1 *
        (Real.sqrt (mainFlatSigmaSq b L) * Real.sqrt (oldSignedFlatBoundaryEnergy Q b L / 2) +
          2 * |b| * Real.sqrt (mainFlatSigmaSq b L)) =
        planarC1 * (cubeScaleFactor Q / (3 : ℝ) ^ d * Real.sqrt (mainFlatSigmaSq b L)) *
          (Real.sqrt (oldSignedFlatBoundaryEnergy Q b L / 2) + 2 * |b|) := by ring
    rw [e1]
    have h2 : Real.sqrt (oldSignedFlatBoundaryEnergy Q b L / 2) + 2 * |b| ≤
        |b| * Real.sqrt (q / 2) + 2 * |b| := by linarith
    have h3 : 0 ≤ cubeScaleFactor Q / (3 : ℝ) ^ d * Real.sqrt (mainFlatSigmaSq b L) :=
      mul_nonneg hR0 (Real.sqrt_nonneg _)
    refine mul_le_mul (mul_le_mul hc1 hRs h3 (by norm_num)) h2
      (by positivity) (by positivity)
  unfold mainBe
  have hv : (|b| * Real.sqrt (q / 2) + 0) = |b| * Real.sqrt (q / 2) := by ring
  have e2 : b ^ 2 * (Real.sqrt (q / 2) + 304 / 1000 * Real.sqrt (156 / 5) * (3 : ℝ) ^ (-6 : ℤ) *
      (Real.sqrt (q / 2) + 2)) = |b| * (|b| * Real.sqrt (q / 2)) +
      (304 / 1000) * ((3 : ℝ) ^ (-6 : ℤ) * (Real.sqrt (156 / 5) * |b|)) *
        (|b| * Real.sqrt (q / 2) + 2 * |b|) := by
    rw [← sq_abs b]; ring
  rw [e2]
  have h1 : |b| * Real.sqrt (oldSignedFlatBoundaryEnergy Q b L / 2) ≤ |b| * (|b| * Real.sqrt (q / 2)) :=
    mul_le_mul_of_nonneg_left hB0 (abs_nonneg b)
  linarith

/-- Cauchy-Schwarz over the cells: the beta-weighted average of any nonnegative
cell sizes `V` is at most `mainBe` times their root mean square. -/
theorem main_covariance_beta_weighted_le_flag (plus : Bool) (Q : TriadicCube 2) (d : ℕ) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (q : ℝ)
    (hq : oldSignedFlatBoundaryEnergy Q b L ≤ b ^ 2 * q) (hq0 : 0 ≤ q)
    (hr : cubeScaleFactor Q / (3 : ℝ) ^ d ≤ (3 : ℝ) ^ (-6 : ℤ) * L.1)
    (V : TriadicCube 2 → ℝ) :
    descendantsAverage Q d (fun U => oldSignedCovarianceBeta Q U b L plus * V U) ≤
      mainBe (b ^ 2) q * Real.sqrt (descendantsAverage Q d (fun U => V U ^ 2)) := by
  have hcap := main_covariance_beta_rms_le_mainBe_flag plus Q d b L q hq hq0 hr
  have hC := finAvg_mul_le (descendantsAtDepth Q d)
    (fun U => oldSignedCovarianceBeta Q U b L plus) V
  change finAvg (descendantsAtDepth Q d) _ ≤ Real.sqrt (finAvg _ _) * Real.sqrt (finAvg _ _)
    at hC
  change finAvg (descendantsAtDepth Q d) (fun U => oldSignedCovarianceBeta Q U b L plus * V U) ≤ _
  refine hC.trans ?_
  exact mul_le_mul_of_nonneg_right hcap (Real.sqrt_nonneg _)

end

end ASDExplicitGamma.Main
