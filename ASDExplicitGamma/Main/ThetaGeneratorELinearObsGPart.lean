module

public import ASDExplicitGamma.Main.ThetaGeneratorELinearObsSplit
public import ASDExplicitGamma.Main.ThetaGeneratorELinearCellExpectation
public import ASDExplicitGamma.Main.ThetaGeneratorELinearObsMeanAmplitude
public import ASDExplicitGamma.Main.ELinearCauchy
public import ASDExplicitGamma.Main.ELinearFlatCaps
public import ASDExplicitGamma.Main.EOscillationFlatOscillationCaps
public import ASDExplicitGamma.Native.OldSignedCenteredPositive
public import ASDExplicitGamma.Main.EOscillationCellScale
public import ASDExplicitGamma.Main.AffineFlatBoundary
public import ASDExplicitGamma.Main.HotTopCovariancePathwise
public import ASDExplicitGamma.Main.ELinearCauchyExpectation
public import ASDExplicitGamma.Main.ThetaGeneratorObserverAvgTheta
public import ASDExplicitGamma.Main.ObserverParentGapPaired
public import ASDExplicitGamma.Scalar.SmoothFeedbackCellEnergy

/-! The parent-gap weighted part (the `G`-weighted half-gain feedback) of the
`L` group at the observer root: its expectation is at most
`(mainFourLoadAG - 2 mainBe) * sqrt (2 xi)`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Inverse
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

/-- Component bound: square of a multiplier-history square root factor. -/
theorem g_part_carrier_sq_Th {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B Mu : Ω → ℝ)
    (hB : MemLp B 2 μ) (hMu : MemLp Mu 2 μ) (hB0 : ∀ ω, 0 ≤ B ω)
    (hMu0 : 0 ≤ᵐ[μ] Mu) (P : ℝ) (hP : 0 ≤ P) (hprod : (∫ ω, B ω * Mu ω ∂μ) ≤ P)
    (w : ℝ) :
    Integrable (fun ω => ((Real.sqrt (B ω * Mu ω) + 1) * w) ^ 2) μ ∧
      (∫ ω, ((Real.sqrt (B ω * Mu ω) + 1) * w) ^ 2 ∂μ) ≤ (Real.sqrt P + 1) ^ 2 * w ^ 2 := by
  have hBMint : Integrable (fun ω => B ω * Mu ω) μ := hB.integrable_mul hMu
  have hBM0 : 0 ≤ᵐ[μ] (fun ω => B ω * Mu ω) := by
    filter_upwards [hMu0] with ω hω
    exact mul_nonneg (hB0 ω) hω
  obtain ⟨sBMi, sBMb⟩ := main_sqrt_expectation_ae_Th μ _ hBMint hBM0
  have hfun : Integrable (fun ω => (B ω * Mu ω + 2 * Real.sqrt (B ω * Mu ω) + 1) * w ^ 2) μ :=
    (((hBMint.add (sBMi.const_mul 2)).add (integrable_const (1 : ℝ))).mul_const _)
  have hae : (fun ω => ((Real.sqrt (B ω * Mu ω) + 1) * w) ^ 2) =ᵐ[μ]
      (fun ω => (B ω * Mu ω + 2 * Real.sqrt (B ω * Mu ω) + 1) * w ^ 2) := by
    filter_upwards [hBM0] with ω hω
    have h1 := Real.sq_sqrt hω
    calc ((Real.sqrt (B ω * Mu ω) + 1) * w) ^ 2 =
        ((Real.sqrt (B ω * Mu ω)) ^ 2 + 2 * Real.sqrt (B ω * Mu ω) + 1) * w ^ 2 := by ring
      _ = _ := by rw [h1]
  refine ⟨hfun.congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_mul_const]
  have hint : (∫ ω, (B ω * Mu ω + 2 * Real.sqrt (B ω * Mu ω) + 1) ∂μ) =
      (∫ ω, B ω * Mu ω ∂μ) + 2 * (∫ ω, Real.sqrt (B ω * Mu ω) ∂μ) + 1 := by
    have e1 := integral_add hBMint (sBMi.const_mul 2)
    have e2 := integral_add (hBMint.add (sBMi.const_mul 2)) (integrable_const (1 : ℝ))
    simp only [Pi.add_apply] at e1 e2
    rw [e2, e1, integral_const_mul]
    simp
  rw [hint]
  have hs : (∫ ω, Real.sqrt (B ω * Mu ω) ∂μ) ≤ Real.sqrt P := sBMb.trans (Real.sqrt_le_sqrt hprod)
  have hPs : Real.sqrt P ^ 2 = P := Real.sq_sqrt hP
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  nlinarith [hs, hPs]

/-- Component bound: history carrier times a deterministic factor. -/
theorem g_part_history_sq_Th {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : Ω → ℝ) (hB : MemLp B 2 μ)
    (β : ℝ) (hβ : lpNorm B 2 μ ≤ β) (c w : ℝ) :
    Integrable (fun ω => (c * B ω * w) ^ 2) μ ∧
      (∫ ω, (c * B ω * w) ^ 2 ∂μ) ≤ (c * β) ^ 2 * w ^ 2 := by
  have hI := ((hB.integrable_sq).const_mul ((c * w) ^ 2))
  have heq : (fun ω => (c * B ω * w) ^ 2) = fun ω => (c * w) ^ 2 * B ω ^ 2 := by
    funext ω; ring
  rw [heq]
  refine ⟨hI, ?_⟩
  rw [integral_const_mul]
  have hsq : (∫ ω, B ω ^ 2 ∂μ) ≤ β ^ 2 := by
    rw [← ASDExplicitGamma.Gaussian.rio_lpNorm_two_sq hB]
    exact pow_le_pow_left₀ lpNorm_nonneg hβ 2
  calc (c * w) ^ 2 * ∫ ω, B ω ^ 2 ∂μ ≤ (c * w) ^ 2 * β ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = (c * β) ^ 2 * w ^ 2 := by ring

/-- Real-variable form of the pathwise cell bound. -/
theorem g_part_real_ineq_Th (κ kd G Pp Pm Hh Rr Bc Mc Ωp Ωm α : ℝ)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ kd) (hG : 0 ≤ G) (hPp : 0 ≤ Pp) (hPm : 0 ≤ Pm)
    (hH : 0 ≤ Hh) (hR : 0 ≤ Rr) (hHB : Hh ≤ Bc) (hRM : Rr = Mc)
    (hΩp : 0 ≤ Ωp) (hΩm : 0 ≤ Ωm) (hα : 0 ≤ α) :
    2 * κ * G * (Real.sqrt Pp + α * Hh * Ωp) +
      2 * κ * G * (Real.sqrt Pm + (Real.sqrt (Hh * Rr) + 1) * Ωm) ≤
    2 * kd * (G * Real.sqrt Pp + G * (α * Bc * Ωp) + G * Real.sqrt Pm +
      G * ((Real.sqrt (Bc * Mc) + 1) * Ωm)) := by
  subst hRM
  have hBc : 0 ≤ Bc := hH.trans hHB
  have hsq : Real.sqrt (Hh * Rr) ≤ Real.sqrt (Bc * Rr) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hHB hR)
  have h1 : α * Hh * Ωp ≤ α * Bc * Ωp :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hHB hα) hΩp
  have h2 : (Real.sqrt (Hh * Rr) + 1) * Ωm ≤ (Real.sqrt (Bc * Rr) + 1) * Ωm :=
    mul_le_mul_of_nonneg_right (by linarith) hΩm
  have a1 : 0 ≤ Real.sqrt Pp + α * Hh * Ωp :=
    add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (mul_nonneg hα hH) hΩp)
  have a2 : 0 ≤ Real.sqrt Pm + (Real.sqrt (Hh * Rr) + 1) * Ωm :=
    add_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (add_nonneg (Real.sqrt_nonneg _) zero_le_one) hΩm)
  have hkd : 0 ≤ kd := hκ0.trans hκ
  have e1 : 2 * κ * G * (Real.sqrt Pp + α * Hh * Ωp) ≤
      2 * kd * G * (Real.sqrt Pp + α * Bc * Ωp) :=
    mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκ (by norm_num)) hG)
      (by linarith) a1 (by positivity)
  have e2 : 2 * κ * G * (Real.sqrt Pm + (Real.sqrt (Hh * Rr) + 1) * Ωm) ≤
      2 * kd * G * (Real.sqrt Pm + (Real.sqrt (Bc * Rr) + 1) * Ωm) :=
    mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκ (by norm_num)) hG)
      (by linarith) a2 (by positivity)
  nlinarith [e1, e2]

/-- The final algebra of the `G`-weighted feedback bound. -/
theorem g_part_final_alg_Th (ξ kd w v q op om β α' Cm : ℝ) (hξ : 0 ≤ ξ) (hkd : 0 ≤ kd)
    (hw : 0 ≤ w) (hv : 0 ≤ v) (hα' : 0 ≤ α') (hα'le : α' ≤ 63 / 50) (hβ : 0 ≤ β)
    (hop : 0 ≤ op) (hom : 0 ≤ om) (hC : 0 ≤ Cm) :
    2 * kd * (Real.sqrt (2 * ξ) * Real.sqrt (ξ / 2 * w) +
      Real.sqrt (2 * ξ) * Real.sqrt ((α' * β * op) ^ 2) +
      Real.sqrt (2 * ξ) * Real.sqrt (ξ / 2 * v) +
      Real.sqrt (2 * ξ) * Real.sqrt ((Cm * om) ^ 2)) ≤
    2 * kd * (Real.sqrt ξ * (Real.sqrt w + Real.sqrt v) / Real.sqrt 2 +
      (63 / 50) * β * op + Cm * om) * Real.sqrt (2 * ξ) := by
  have hs0 : 0 ≤ Real.sqrt (2 * ξ) := Real.sqrt_nonneg _
  have e0 : Real.sqrt (2 * ξ) * Real.sqrt (ξ / 2) = ξ := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show 2 * ξ * (ξ / 2) = ξ ^ 2 by ring]
    exact Real.sqrt_sq hξ
  have e0' : Real.sqrt ξ * Real.sqrt (2 * ξ) / Real.sqrt 2 = ξ := by
    have h2 : Real.sqrt (2 * ξ) = Real.sqrt 2 * Real.sqrt ξ := Real.sqrt_mul (by norm_num) _
    rw [h2]
    have : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    exact Real.sq_sqrt hξ
  have e1 : Real.sqrt (ξ / 2 * w) = Real.sqrt (ξ / 2) * Real.sqrt w := Real.sqrt_mul (by positivity) _
  have e3 : Real.sqrt (ξ / 2 * v) = Real.sqrt (ξ / 2) * Real.sqrt v := Real.sqrt_mul (by positivity) _
  have e2 : Real.sqrt ((α' * β * op) ^ 2) = α' * β * op :=
    Real.sqrt_sq (mul_nonneg (mul_nonneg hα' hβ) hop)
  have e4 : Real.sqrt ((Cm * om) ^ 2) = Cm * om := Real.sqrt_sq (mul_nonneg hC hom)
  rw [e1, e2, e3, e4]
  have lhs : Real.sqrt (2 * ξ) * (Real.sqrt (ξ / 2) * Real.sqrt w) +
      Real.sqrt (2 * ξ) * (α' * β * op) +
      Real.sqrt (2 * ξ) * (Real.sqrt (ξ / 2) * Real.sqrt v) +
      Real.sqrt (2 * ξ) * (Cm * om) =
      ξ * Real.sqrt w + ξ * Real.sqrt v + Real.sqrt (2 * ξ) * (α' * β * op) +
        Real.sqrt (2 * ξ) * (Cm * om) := by
    have := e0
    linear_combination (Real.sqrt w + Real.sqrt v) * this
  have rhs : (Real.sqrt ξ * (Real.sqrt w + Real.sqrt v) / Real.sqrt 2 +
      (63 / 50) * β * op + Cm * om) * Real.sqrt (2 * ξ) =
      ξ * Real.sqrt w + ξ * Real.sqrt v + Real.sqrt (2 * ξ) * ((63 / 50) * β * op) +
        Real.sqrt (2 * ξ) * (Cm * om) := by
    have := e0'
    linear_combination (Real.sqrt w + Real.sqrt v) * this
  have hmono : Real.sqrt (2 * ξ) * (α' * β * op) ≤ Real.sqrt (2 * ξ) * ((63 / 50) * β * op) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hα'le hβ) hop) hs0
  rw [lhs, mul_assoc (2 * kd) _ (Real.sqrt (2 * ξ)), rhs]
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end
end ASDExplicitGamma.Main
