module

public import ASDExplicitGamma.Main.HotCovExpectG
public import ASDExplicitGamma.Main.HotObsSplitOfHist
public import ASDExplicitGamma.Main.HotObsVl2OfHist

/-! Successors of `HotCovExpectG` declarations with the history envelope as a parameter `Hfun`. -/



@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational ASDExplicitGamma.Inverse
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

/-- Successor of `hotCov_expect_G` with the history envelope `Hfun`. -/
theorem hotCov_expect_G_ofHist
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ) (h1 : 1 ≤ hobs) (h40 : hobs ≤ 40)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (b B0 : ℝ)
    (hB : oldSignedFlatBoundaryEnergy (originCube 2 (m + hobs)) b (q3ModelLength (m + 1)) ≤ B0)
    (Hfun : ℝ → ℝ)
    (hHist : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω < ⊤) ∧
      MemLp (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ Hfun s)
    :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let xi := mainEnvelopeXi
      ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2)
      M.gamma mainSourceInversePrefix (theta M) t
    let X2 := mainBeta * (inSourceMeanActual M m 5 t - modelTraceHeatAverage (m + hobs) M m t) +
      mainEpsNew * (Hfun t / (1 - mainAlpha))
    0 ≤ X2 ∧ Integrable (hotCovGObs M m hobs t b) μ ∧
    (∫ ω, hotCovGObs M m hobs t b ω ∂μ) ≤
      (b ^ 2 / 2) * X2 +
      2 * Real.sqrt X2 * Real.sqrt (xi / 2 * (mainFlatBoundaryEPlus (b ^ 2) B0 ^ 2 +
        mainFlatBoundaryEMinus (b ^ 2) B0 ^ 2)) +
      2 * (mainKrem (b ^ 2) * Real.sqrt X2 + mainKd (b ^ 2) * Real.sqrt xi) *
        Real.sqrt (xi / 2 * (2 * b ^ 2 + B0 / 2)) := by
  intro μ xi X2
  have hpastM : ∀ n ≤ m, nativeInductionState M h n :=
    fun n hn => hpast n (lt_of_le_of_lt hn hm)
  obtain ⟨hYint, hYle, -, -⟩ := main_hot_obs_positive_split_ofHist (Hfun := Hfun) (hHist := hHist) M h hM hγ N hpast m hm hobs t ht
  have hBeq : mixedGlobalHistoryMax M m t = mixedBridgeBstar M m t :=
    funext (main_hot_bstar_eq M m t ht)
  simp only [hBeq] at hYint hYle
  have hD0 (ω : Cutoff.CutoffSample 2) : 0 ≤ mainHotDropObs M m hobs t ω :=
    (main_hot_drop_obs_pathwise M m hobs t ω).2
  have hB0 (ω : Cutoff.CutoffSample 2) : 0 ≤ mixedBridgeBstar M m t ω := by
    rw [← main_hot_bstar_eq M m t ht ω]
    exact ENNReal.toReal_nonneg
  have hY0 (ω : Cutoff.CutoffSample 2) :
      0 ≤ mixedBridgeBstar M m t ω * mainHotDropObs M m hobs t ω :=
    mul_nonneg (hB0 ω) (hD0 ω)
  obtain ⟨hPEint, hPEle⟩ := hotCov_pe_expect M h hM hγ N hpast m hm hobs t ht b B0
    (q3ModelLength (m + 1)) (hotCov_scale_arith m hobs).le hB
  obtain ⟨hPAint, hPAle⟩ := hotCov_pa_expect M h hM hγ N hpast m hm hobs t ht b B0
    (q3ModelLength (m + 1)) hB
  obtain ⟨-, hVint, hV0, -, hVle⟩ := main_hot_obs_vl2_moment_ofHist (Hfun := Hfun) (hHist := hHist) M h hM hγ N hpast m hm hobs
    h1 h40 t ht
  have c1 := hotCov_cs_sqrt hYint hPEint hY0 (hotCov_pe_nonneg M m hobs t b _)
  have c2 := hotCov_cs_sqrt hYint hPAint hY0 (hotCov_pa_nonneg M m hobs t b _)
  have c3 := hotCov_cs_sqrt hVint hPAint hV0 (hotCov_pa_nonneg M m hobs t b _)
  let Yf : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    mixedBridgeBstar M m t ω * mainHotDropObs M m hobs t ω
  let PEf : Cutoff.CutoffSample 2 → ℝ := hotCovPE M m hobs t b (q3ModelLength (m + 1))
  let PAf : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    ∑ c : BlockCoord 2, hotCovPA M m hobs t b (q3ModelLength (m + 1)) c ω
  let Vf : Cutoff.CutoffSample 2 → ℝ := mainHotObsVl2 M m hobs t
  have hGfun : hotCovGObs M m hobs t b = fun ω =>
      ((b ^ 2 / 2) * Yf ω + 2 * (Real.sqrt (Yf ω) * Real.sqrt (PEf ω))) +
      ((2 * mainKrem (b ^ 2)) * (Real.sqrt (Yf ω) * Real.sqrt (PAf ω)) +
       (2 * mainKd (b ^ 2)) * (Real.sqrt (Vf ω) * Real.sqrt (PAf ω))) := by
    funext ω
    unfold hotCovGObs
    ring
  have i1 : Integrable (fun ω => (b ^ 2 / 2) * Yf ω + 2 * (Real.sqrt (Yf ω) * Real.sqrt (PEf ω))) μ :=
    (hYint.const_mul _).add (c1.1.const_mul _)
  have i2 : Integrable (fun ω => (2 * mainKrem (b ^ 2)) * (Real.sqrt (Yf ω) * Real.sqrt (PAf ω)) +
       (2 * mainKd (b ^ 2)) * (Real.sqrt (Vf ω) * Real.sqrt (PAf ω))) μ :=
    (c2.1.const_mul _).add (c3.1.const_mul _)
  have hi : Integrable (hotCovGObs M m hobs t b) μ := by
    rw [hGfun]
    exact i1.add i2
  have hY0'' : 0 ≤ ∫ ω, mixedBridgeBstar M m t ω * mainHotDropObs M m hobs t ω ∂μ :=
    integral_nonneg hY0
  refine ⟨hY0''.trans hYle, hi, ?_⟩
  rw [hGfun]
  rw [integral_add i1 i2, integral_add (hYint.const_mul _) (c1.1.const_mul _),
    integral_add (c2.1.const_mul _) (c3.1.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  have hxi : 0 ≤ xi := hotCov_xi_nonneg M h hγ m t ht
  have hY0' : 0 ≤ ∫ ω, mixedBridgeBstar M m t ω * mainHotDropObs M m hobs t ω ∂μ :=
    integral_nonneg hY0
  have hs1 : Real.sqrt (∫ ω, mixedBridgeBstar M m t ω * mainHotDropObs M m hobs t ω ∂μ) ≤
      Real.sqrt X2 := Real.sqrt_le_sqrt hYle
  have hs2 : Real.sqrt (∫ ω, hotCovPE M m hobs t b (q3ModelLength (m + 1)) ω ∂μ) ≤
      Real.sqrt (xi / 2 * (mainFlatBoundaryEPlus (b ^ 2) B0 ^ 2 +
        mainFlatBoundaryEMinus (b ^ 2) B0 ^ 2)) := Real.sqrt_le_sqrt hPEle
  have hs3 : Real.sqrt (∫ ω, ∑ c : BlockCoord 2, hotCovPA M m hobs t b
      (q3ModelLength (m + 1)) c ω ∂μ) ≤ Real.sqrt (xi / 2 * (2 * b ^ 2 + B0 / 2)) :=
    Real.sqrt_le_sqrt hPAle
  have hs4 : Real.sqrt (∫ ω, mainHotObsVl2 M m hobs t ω ∂μ) ≤ Real.sqrt xi :=
    Real.sqrt_le_sqrt hVle
  have k1 := mainKrem_nonneg (b ^ 2)
  have k2 := mainKd_nonneg (b ^ 2)
  have t1 : (∫ ω, Real.sqrt (mixedBridgeBstar M m t ω * mainHotDropObs M m hobs t ω) *
      Real.sqrt (hotCovPE M m hobs t b (q3ModelLength (m + 1)) ω) ∂μ) ≤
      Real.sqrt X2 * Real.sqrt (xi / 2 * (mainFlatBoundaryEPlus (b ^ 2) B0 ^ 2 +
        mainFlatBoundaryEMinus (b ^ 2) B0 ^ 2)) :=
    c1.2.trans (mul_le_mul hs1 hs2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have t2 : (∫ ω, Real.sqrt (mixedBridgeBstar M m t ω * mainHotDropObs M m hobs t ω) *
      Real.sqrt (∑ c : BlockCoord 2, hotCovPA M m hobs t b (q3ModelLength (m + 1)) c ω) ∂μ) ≤
      Real.sqrt X2 * Real.sqrt (xi / 2 * (2 * b ^ 2 + B0 / 2)) :=
    c2.2.trans (mul_le_mul hs1 hs3 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have t3 : (∫ ω, Real.sqrt (mainHotObsVl2 M m hobs t ω) *
      Real.sqrt (∑ c : BlockCoord 2, hotCovPA M m hobs t b (q3ModelLength (m + 1)) c ω) ∂μ) ≤
      Real.sqrt xi * Real.sqrt (xi / 2 * (2 * b ^ 2 + B0 / 2)) :=
    c3.2.trans (mul_le_mul hs4 hs3 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hb2 : (0 : ℝ) ≤ b ^ 2 / 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hYle hb2, mul_le_mul_of_nonneg_left t1 (by norm_num : (0:ℝ) ≤ 2),
    mul_le_mul_of_nonneg_left t2 (by positivity : (0:ℝ) ≤ 2 * mainKrem (b ^ 2)),
    mul_le_mul_of_nonneg_left t3 (by positivity : (0:ℝ) ≤ 2 * mainKd (b ^ 2))]

end
end ASDExplicitGamma.Main
end
