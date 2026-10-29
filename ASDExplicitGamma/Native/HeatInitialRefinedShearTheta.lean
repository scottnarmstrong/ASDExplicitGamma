module

public import ASDExplicitGamma.Native.HeatInitialRefinedShear
public import ASDExplicitGamma.Native.HeatInitialRefinedFrameTheta

/-! The theta-scaled refined lag-minus-one child shear moments at the completed cutoff `m+1`:
the squared `L^k` cap is `θ` times the endpoint cap (the fixed rare amplitude multiplies the
theta-scaled `L^20` trace cap). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Variational ASDExplicitGamma.Response
open ASDExplicitGamma.Numerics.Native
open Algsuperdiff.Section3.Provider.BadEvents
open scoped ENNReal

set_option linter.constructorNameAsVariable false

/-- The `L²⁰` cap `hp` for any translated refined child trace. -/
theorem nativeHeatRefined_coldTrace_L20_theta
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (m : ℤ) (hpast : ∀ j < m + 1, nativeInductionState M h j)
    (Q : TriadicCube 2) (hscale : Q.scale = m) :
    eLpNorm' (Cold.coldNativeCellTrace M (m + 1) Q) 20
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (theta M * ((nativeHeatParametersData.hp : ℚ) : ℝ)) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hdist := Cold.coldNativeCellTrace_identDistrib M (m + 1) Q
  have hf : AEStronglyMeasurable (Cold.coldNativeCellTrace M (m + 1) Q) μ :=
    (Cold.coldNativeCellTrace_measurable M (m + 1) Q).aestronglyMeasurable
  have hg' : AEStronglyMeasurable (cutoffTraceDefect M (m + 1) Q.scale) μ :=
    (Variational.cutoffTraceDefect_measurable M (m + 1) Q.scale).aestronglyMeasurable
  have h1 : eLpNorm' (Cold.coldNativeCellTrace M (m + 1) Q) 20 μ =
      eLpNorm (Cold.coldNativeCellTrace M (m + 1) Q) (20 : ℝ≥0∞) μ := by
    simpa using (eLpNorm_eq_eLpNorm' (p := (20 : ℝ≥0∞)) (by norm_num) (by norm_num) hf).symm
  have h2 : eLpNorm' (cutoffTraceDefect M (m + 1) Q.scale) 20 μ =
      eLpNorm (cutoffTraceDefect M (m + 1) Q.scale) (20 : ℝ≥0∞) μ := by
    simpa using (eLpNorm_eq_eLpNorm' (p := (20 : ℝ≥0∞)) (by norm_num) (by norm_num) hg').symm
  rw [h1, hdist.eLpNorm_eq (20 : ℝ≥0∞), ← h2, hscale]
  exact nativeHeatRefined_childTrace_L20_le_hp_theta M h hM hg m hpast

/-- The mean `qstar` of any translated refined child trace (completed `q1`). -/
theorem nativeHeatRefined_coldTrace_L1_theta
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (m : ℤ) (hpast : ∀ j < m + 1, nativeInductionState M h j)
    (Q : TriadicCube 2) (hscale : Q.scale = m) :
    eLpNorm' (Cold.coldNativeCellTrace M (m + 1) Q) 1
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (theta M * ((nativeQstar : ℚ) : ℝ)) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  let f := Cold.coldNativeCellTrace M (m + 1) Q
  have hint : Integrable f μ := Cold.coldNativeCellTrace_integrable M (m + 1) Q
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω => Cold.coldNativeCellTrace_nonneg M (m + 1) Q ω
  have hnorm : eLpNorm' f 1 μ = ∫⁻ ω, ‖f ω‖ₑ ∂μ := by
    simpa using (lintegral_rpow_enorm_eq_rpow_eLpNorm' (f := f) (q := (1 : ℝ)) (μ := μ)
      (by norm_num)).symm
  have hlin : ∫⁻ ω, ‖f ω‖ₑ ∂μ = ENNReal.ofReal (∫ ω, f ω ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hf0)]
    apply lintegral_congr
    intro ω
    exact Real.enorm_eq_ofReal (hf0 ω)
  have hq1 := native_completed_q1_integral_carried M h hM hg (m + 1) hpast
  have hmean : (∫ ω, f ω ∂μ) = ∫ ω, cutoffTraceDefect M (m + 1) (m + 1 - 1) ω ∂μ := by
    have := Cold.coldNativeCellTrace_integral M (m + 1) Q
    rw [hscale] at this
    simpa [f, μ] using this
  have htheta1 : theta M ≤ 1 := by
    rw [theta]
    exact (div_le_one₀ (by norm_num [gammaZero])).2 hg
  have hq0 : (0 : ℝ) ≤ (nativeQstar : ℝ) := by norm_num [nativeQstar]
  have hθ0 : 0 ≤ theta M := (Cold.cold_theta_pos M).le
  rw [hnorm, hlin]
  apply ENNReal.ofReal_le_ofReal
  rw [hmean]
  simpa [Rat.cast_div] using hq1

/-- The refined child shear moment at the completed cutoff `m+1`, with the source
`hp`, `qstar`, depth-four bank and `RQ`-scaled baseline. -/
theorem nativeHeatRefined_childShear_eLpNorm_theta
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (m : ℤ) (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (Q : TriadicCube 2) (hscale : Q.scale = m)
    (k : ℕ) (hk2 : 2 ≤ k) (hk20 : k ≤ 20) :
    eLpNorm' (fun ω => shearTraceLinear (coarseBlockMatrix (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)) (k : ℝ)
        (Cutoff.cutoffSampleLaw M).toMeasure ^ 2 ≤
      ENNReal.ofReal (theta M * (2 * ((nativeHeatB : ℝ) *
        nativeHeatHnReal nativeHeatParametersData ((k : ℚ) / 2) +
        ((nativeHeatEps * nativeHeatParametersData.hp : ℚ) : ℝ)))) := by
  classical
  obtain ⟨hτ0, hτ1⟩ := theta_pos_le_one M hg
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  let z : Cutoff.CutoffSample 2 → ℝ := fun ω => shearTraceLinear
    (coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)
  let T : Cutoff.CutoffSample 2 → ℝ := Cold.coldNativeCellTrace M (m + 1) Q
  let R : Cutoff.CutoffSample 2 → ℝ := nativeHeatOldInverseRemainderDepth4 M Q (m + 1)
  have hprofile := nativeHeatRefined_oldInverseTraceProfileDepth4_of_states
    M h hM hg Q (m + 1) (by omega) hpast
  have hL20 := nativeHeatRefined_coldTrace_L20_theta M h hM hg m hpast Q hscale
  have hL1 := nativeHeatRefined_coldTrace_L1_theta M h hM hg m hpast Q hscale
  have hf : AEStronglyMeasurable T μ :=
    (Cold.coldNativeCellTrace_measurable M (m + 1) Q).aestronglyMeasurable
  have hq1 : 1 ≤ (k : ℝ) / 2 := by
    have hk : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    linarith
  have hq20 : (k : ℝ) / 2 ≤ 20 := by
    have hk : (k : ℝ) ≤ 20 := by exact_mod_cast hk20
    linarith
  have hTmoment := nativeHeat_eLpNorm'_interp_1_20 hf ((k : ℝ) / 2) hq1 hq20 hL20 hL1
  have hbankDisc : ∀ᵐ ω ∂μ,
      z ω ^ 2 ≤ 2 * ((inverseBankCap .localInverse : ℝ) + R ω) * T ω := by
    filter_upwards [hprofile.2.2.1] with ω hbound
    let kω := nativeHeatOldResponseCoefficient Q (m + 1) ω
    let σ := (Annealed.sigmaBar M (m + 1) : ℝ)
    have hσ : 0 < σ := (Annealed.sigmaBar_characterization M (m + 1)).1
    have hdisc := shearTraceLinear_sq_le Q M.nu σ M.nu_pos hσ kω
    have hmat := nativeHeat_oldResponseCoarse_eq_cutoff M Q (m + 1) ω
    have hz : shearTraceLinear (coarseBlockMatrix (cubeSet Q)
          (responsePlanarCoefficientField M.nu kω)) = z ω :=
      congrArg shearTraceLinear hmat
    have hD : Matrix.trace (frameMatrix σ
        (coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField M.nu kω))).lowerRight =
        Matrix.trace (frameMatrix σ (coarseBlockMatrix (cubeSet Q)
            (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)).lowerRight :=
      congrArg (fun A : BlockMat 2 => Matrix.trace (frameMatrix σ A).lowerRight) hmat
    have hT : traceDefect (cubeSet Q) (responsePlanarCoefficientField M.nu kω) σ = T ω := by
      change traceDefect (cubeSet Q) (responsePlanarCoefficientField M.nu kω) σ =
        traceDefect (cubeSet Q) (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun σ
      unfold traceDefect
      rw [hmat]
    have hzsq : z ω ^ 2 ≤ Matrix.trace (frameMatrix σ (coarseBlockMatrix (cubeSet Q)
            (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)).lowerRight * T ω := by
      calc
        z ω ^ 2 = (shearTraceLinear (coarseBlockMatrix (cubeSet Q)
              (responsePlanarCoefficientField M.nu kω))) ^ 2 := by rw [hz]
        _ ≤ Matrix.trace (frameMatrix σ (coarseBlockMatrix (cubeSet Q)
                (responsePlanarCoefficientField M.nu kω))).lowerRight *
              traceDefect (cubeSet Q) (responsePlanarCoefficientField M.nu kω) σ := hdisc
        _ = _ := by rw [hD, hT]
    exact hzsq.trans (mul_le_mul_of_nonneg_right hbound
      (Cold.coldNativeCellTrace_nonneg M (m + 1) Q ω))
  have hcap : 0 ≤ (inverseBankCap .localInverse : ℝ) := by norm_num [inverseBankCap]
  have hR128 : eLpNorm' R 128 μ ≤
      ENNReal.ofReal (inverseBankReserve .localInverse : ℝ) := by
    have hR128' : eLpNorm R (128 : ℝ≥0∞) μ ≤
        ENNReal.ofReal (inverseBankReserve .localInverse : ℝ) := by
      simpa [R, μ] using hprofile.2.2.2
    rw [eLpNorm_eq_eLpNorm' (p := (128 : ℝ≥0∞)) (by norm_num) (by norm_num)
      hprofile.1.aestronglyMeasurable] at hR128'
    exact hR128'
  have hgeneric := nativeHeat_shearTraceMoment_of_positive_profile
    μ z T R k hk2 hk20 (b := (inverseBankCap .localInverse : ℝ))
    (ε := ENNReal.ofReal (inverseBankReserve .localInverse : ℝ))
    (Hk := ENNReal.ofReal (theta M * ((nativeHeatParametersData.hp : ℚ) : ℝ)) ^
      (20 * ((k : ℝ) / 2 - 1) / (19 * ((k : ℝ) / 2))) *
      ENNReal.ofReal (theta M * ((nativeQstar : ℚ) : ℝ)) ^ ((20 - (k : ℝ) / 2) /
        (19 * ((k : ℝ) / 2))))
    (H20 := ENNReal.ofReal (theta M * ((nativeHeatParametersData.hp : ℚ) : ℝ))) hcap
    (Cold.coldNativeCellTrace_nonneg M (m + 1) Q)
    hprofile.2.1 hbankDisc hf hprofile.1.aestronglyMeasurable hTmoment hL20 hR128
  have hH := nativeHeatRefined_Hn_dominates k hk2 hk20
  have hB : (inverseBankCap .localInverse : ℝ) ≤ (nativeHeatB : ℝ) := by
    exact_mod_cast nativeHeat_localInverseCap_le_nativeHeatB
  have hε : (inverseBankReserve .localInverse : ℝ) ≤ (nativeHeatEps : ℝ) := by
    have : inverseBankReserve .localInverse ≤ nativeHeatEps := by
      norm_num [inverseBankReserve, nativeHeatEps, nativeHeatRQ, nativeE, nativeGamma, nativeEps]
    exact_mod_cast this
  have hhp : (0 : ℝ) ≤ (nativeHeatParametersData.hp : ℝ) := by
    norm_num [nativeHeatParametersData]
  have hB0 : 0 ≤ (inverseBankCap .localInverse : ℝ) := hcap
  have hε0 : 0 ≤ (inverseBankReserve .localInverse : ℝ) := by
    norm_num [inverseBankReserve]
  have hB1 : 0 ≤ (nativeHeatB : ℝ) := hB0.trans hB
  have hε1 : 0 ≤ (nativeHeatEps : ℝ) := hε0.trans hε
  have hH0 : 0 ≤ nativeHeatHnReal nativeHeatParametersData ((k : ℚ) / 2) := by
    have hq0 : (0 : ℚ) ≤ nativeQstar := by norm_num [nativeQstar]
    have hhpQ : (0 : ℚ) ≤ nativeHeatParametersData.hp := by
      norm_num [nativeHeatParametersData]
    have hratioQ : (0 : ℚ) ≤ nativeHeatParametersData.hp / nativeQstar :=
      div_nonneg hhpQ hq0
    unfold nativeHeatHnReal
    exact mul_nonneg (by exact_mod_cast hq0) (Real.rpow_nonneg (by exact_mod_cast hratioQ) _)
  have hk1' : 1 ≤ (k : ℝ) / 2 := hq1
  have hα0 : 0 ≤ 20 * ((k : ℝ) / 2 - 1) / (19 * ((k : ℝ) / 2)) := by
    have : 0 ≤ (k : ℝ) / 2 - 1 := by linarith
    positivity
  have hβ0 : 0 ≤ (20 - (k : ℝ) / 2) / (19 * ((k : ℝ) / 2)) := by
    have : 0 ≤ 20 - (k : ℝ) / 2 := by linarith
    have : 0 < (k : ℝ) / 2 := by linarith
    positivity
  have hαβ : 20 * ((k : ℝ) / 2 - 1) / (19 * ((k : ℝ) / 2)) +
      (20 - (k : ℝ) / 2) / (19 * ((k : ℝ) / 2)) = 1 := by
    have : (k : ℝ) / 2 ≠ 0 := by linarith
    field_simp
    ring
  have hHθ : ENNReal.ofReal (theta M * ((nativeHeatParametersData.hp : ℚ) : ℝ)) ^
        (20 * ((k : ℝ) / 2 - 1) / (19 * ((k : ℝ) / 2))) *
      ENNReal.ofReal (theta M * ((nativeQstar : ℚ) : ℝ)) ^
        ((20 - (k : ℝ) / 2) / (19 * ((k : ℝ) / 2))) ≤
      ENNReal.ofReal (theta M) *
        ENNReal.ofReal (nativeHeatHnReal nativeHeatParametersData ((k : ℚ) / 2)) := by
    set α := 20 * ((k : ℝ) / 2 - 1) / (19 * ((k : ℝ) / 2)) with hα
    set β := (20 - (k : ℝ) / 2) / (19 * ((k : ℝ) / 2)) with hβ
    have hθne : ENNReal.ofReal (theta M) ≠ 0 := (ENNReal.ofReal_pos.mpr hτ0).ne'
    have e : ENNReal.ofReal (theta M * ((nativeHeatParametersData.hp : ℚ) : ℝ)) ^ α *
        ENNReal.ofReal (theta M * ((nativeQstar : ℚ) : ℝ)) ^ β =
        ENNReal.ofReal (theta M) *
          (ENNReal.ofReal ((nativeHeatParametersData.hp : ℚ) : ℝ) ^ α *
            ENNReal.ofReal ((nativeQstar : ℚ) : ℝ) ^ β) := by
      rw [ENNReal.ofReal_mul hτ0.le, ENNReal.ofReal_mul hτ0.le,
        ENNReal.mul_rpow_of_nonneg _ _ hα0, ENNReal.mul_rpow_of_nonneg _ _ hβ0]
      calc _ = (ENNReal.ofReal (theta M) ^ α * ENNReal.ofReal (theta M) ^ β) *
            (ENNReal.ofReal ((nativeHeatParametersData.hp : ℚ) : ℝ) ^ α *
              ENNReal.ofReal ((nativeQstar : ℚ) : ℝ) ^ β) := by ring
        _ = _ := by
          rw [← ENNReal.rpow_add _ _ hθne ENNReal.ofReal_ne_top, hαβ, ENNReal.rpow_one]
    rw [e]
    exact mul_le_mul' le_rfl hH
  have hbaseθ :
      ENNReal.ofReal (2 * (inverseBankCap .localInverse : ℝ)) *
          (ENNReal.ofReal (theta M * ((nativeHeatParametersData.hp : ℚ) : ℝ)) ^
            (20 * ((k : ℝ) / 2 - 1) / (19 * ((k : ℝ) / 2))) *
            ENNReal.ofReal (theta M * ((nativeQstar : ℚ) : ℝ)) ^ ((20 - (k : ℝ) / 2) /
              (19 * ((k : ℝ) / 2)))) ≤
        ENNReal.ofReal (theta M * (2 * (nativeHeatB : ℝ) *
          nativeHeatHnReal nativeHeatParametersData ((k : ℚ) / 2))) := by
    calc
      _ ≤ ENNReal.ofReal (2 * (nativeHeatB : ℝ)) *
          (ENNReal.ofReal (theta M) *
            ENNReal.ofReal (nativeHeatHnReal nativeHeatParametersData ((k : ℚ) / 2))) := by
        apply mul_le_mul
        · exact ENNReal.ofReal_le_ofReal (by nlinarith [hB])
        · exact hHθ
        · simp
        · simp
      _ = _ := by
        rw [← ENNReal.ofReal_mul hτ0.le, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
  have hrareθ :
      2 * ENNReal.ofReal (inverseBankReserve .localInverse : ℝ) *
          ENNReal.ofReal (theta M * ((nativeHeatParametersData.hp : ℚ) : ℝ)) ≤
        ENNReal.ofReal (theta M * (2 * (nativeHeatEps : ℝ) * (nativeHeatParametersData.hp : ℝ))) := by
    have hprod :
        2 * ENNReal.ofReal (inverseBankReserve .localInverse : ℝ) *
            ENNReal.ofReal (theta M * ((nativeHeatParametersData.hp : ℚ) : ℝ)) =
          ENNReal.ofReal (2 * (inverseBankReserve .localInverse : ℝ) *
            (theta M * ((nativeHeatParametersData.hp : ℚ) : ℝ))) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num]
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [← ENNReal.ofReal_mul (by positivity)]
    rw [hprod]
    apply ENNReal.ofReal_le_ofReal
    have := mul_le_mul_of_nonneg_right hε (mul_nonneg hτ0.le hhp)
    nlinarith [this]
  calc
    _ ≤ ENNReal.ofReal (2 * (inverseBankCap .localInverse : ℝ)) *
        (ENNReal.ofReal (theta M * ((nativeHeatParametersData.hp : ℚ) : ℝ)) ^
          (20 * ((k : ℝ) / 2 - 1) / (19 * ((k : ℝ) / 2))) *
          ENNReal.ofReal (theta M * ((nativeQstar : ℚ) : ℝ)) ^ ((20 - (k : ℝ) / 2) /
            (19 * ((k : ℝ) / 2)))) +
        2 * ENNReal.ofReal (inverseBankReserve .localInverse : ℝ) *
          ENNReal.ofReal (theta M * ((nativeHeatParametersData.hp : ℚ) : ℝ)) := hgeneric
    _ ≤ ENNReal.ofReal (theta M * (2 * (nativeHeatB : ℝ) *
          nativeHeatHnReal nativeHeatParametersData ((k : ℚ) / 2))) +
        ENNReal.ofReal (theta M * (2 * (nativeHeatEps : ℝ) * (nativeHeatParametersData.hp : ℝ))) :=
      add_le_add hbaseθ hrareθ
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply congrArg ENNReal.ofReal
      rw [Rat.cast_mul]
      ring

end ASDExplicitGamma.Native
