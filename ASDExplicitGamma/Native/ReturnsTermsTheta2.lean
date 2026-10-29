module

public import ASDExplicitGamma.Native.ReturnsTermsTheta

/-! NA-RETURNS at smaller gamma: the theta-scaled individual terms of the native histories (heat
terms `9 ≤ g ≤ 160`, raw OLD envelope terms `g ≤ 1334`). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Set Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Numerics.Native ASDExplicitGamma.Variational
open scoped ENNReal

/-- Heat terms `9 ≤ g ≤ 160`, with the carrier index `m` (label `m+1`, cube `m+10`, cutoff `m+1+g`). -/
theorem nativeReturns_term_heat_m_theta (g : ℕ) [NeZero g] (hg9 : 9 ≤ g) (hg160 : g ≤ 160)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hgam : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ j < m + 1, nativeInductionState M h j)
    (hstate : nativeInductionState M h (m + 1))
    (hq0 : 0 ≤ (nativeHeatResultGen g).1) :
    eLpNorm (cutoffTraceDefect M (m + 1 + (g : ℤ)) (m + 10)) 20
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (theta M * nativeFrameReal (((11 / 10) * (2 * nativeGamma * (g : ℚ)) : ℚ) : ℝ)
        (((nativeHeatResultGen g).1 : ℚ) : ℝ)) := by
  have hheat := (nativeRefinedHeatStep_theta g hg9 hg160 M h hM hgam m hpast hstate).1
  exact nativeReturns_cutoffTrace_frame_theta M hgam (m + 1) g (by omega) (m + 10)
    ((nativeHeatResultGen g).1) (by exact_mod_cast hq0) hheat

/-- Heat terms at the frozen indices: cube `N-(g-9)`, cutoff `N`, from the states below `N`. -/
theorem nativeReturns_term_heat_theta (g : ℕ) (hg9 : 9 ≤ g) (hg160 : g ≤ 160)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hgam : M.gamma ≤ gammaZero) (N : ℤ)
    (hN : ∀ n < N, nativeInductionState M h n)
    (hq0 : 0 ≤ (nativeHeatResultGen g).1) :
    eLpNorm (cutoffTraceDefect M N (N - ((g - 9 : ℕ) : ℤ))) 20
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (theta M * nativeFrameReal (((11 / 10) * (2 * nativeGamma * (g : ℚ)) : ℚ) : ℝ)
        (((nativeHeatResultGen g).1 : ℚ) : ℝ)) := by
  haveI : NeZero g := ⟨by omega⟩
  have key := nativeReturns_term_heat_m_theta g hg9 hg160 M h hM hgam (N - (g : ℤ) - 1)
    (fun j hj => hN j (by omega)) (hN _ (by omega)) hq0
  have e1 : N - (g : ℤ) - 1 + 1 + (g : ℤ) = N := by ring
  have e2 : N - (g : ℤ) - 1 + 10 = N - ((g - 9 : ℕ) : ℤ) := by
    rw [Nat.cast_sub hg9]; push_cast; ring
  rw [e1, e2] at key
  exact key

/-- Raw terms `g ≤ 1334` at the endpoint: the exponential raw OLD envelope on the child, the sharp
frame map, and the coarse subadditivity to the parent cube. -/
theorem nativeReturns_term_raw_theta (g : ℕ) (hg9 : 9 ≤ g) (hg1334 : g ≤ 1334)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hgam : M.gamma ≤ gammaZero) (N : ℤ)
    (hN : ∀ n < N, nativeInductionState M h n) :
    eLpNorm (cutoffTraceDefect M N (N - ((g - 9 : ℕ) : ℤ))) 20
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (theta M * nativeFrameReal (((11 / 10) * (2 * nativeGamma * (g : ℚ)) : ℚ) : ℝ)
        (((nativeAvg * nativeA + (nativeRaw g).2.2 : ℚ) : ℝ))) := by
  obtain ⟨hτ0, hτ1⟩ := theta_pos_le_one M hgam
  set K : ℤ := N - (g : ℤ) with hK
  have hpast : ∀ j < K, nativeInductionState M h j := fun j hj => hN j (by omega)
  have hstate : nativeInductionState M h K := hN K (by omega)
  have hraw := native_source_band_trace_raw_allowance M h hM hgam K hpast hstate g hg9
  have hrawle := nativeReturns_rawInput_theta_le M hgam g hg1334
  have hq0 := nativeReturns_raw_entry_nonneg_theta M hgam g hg1334
  -- the child trace, in the old frame, as an extended `L^20` norm
  have hfun : (fun ω : Cutoff.CutoffSample 2 => modelTraceObservable K M.nu (Annealed.sigmaBar M K)
      (nativeSourceBandScalar K g 1 ω)) = fun ω : Cutoff.CutoffSample 2 =>
      traceDefect (cubeSet (originCube 2 K))
        (Cutoff.coefficientCutoff M.nu (K + (g : ℤ)) ω).toFun (Annealed.sigmaBar M K : ℝ) := by
    funext ω
    exact native_source_band_trace_one M K g ω
  rw [hfun] at hraw
  have hTm := nativeReturns_traceDefect_measurable M (K + (g : ℤ)) K (Annealed.sigmaBar M K : ℝ)
  have hchild : eLpNorm (fun ω : Cutoff.CutoffSample 2 =>
      traceDefect (cubeSet (originCube 2 K))
        (Cutoff.coefficientCutoff M.nu (K + (g : ℤ)) ω).toFun (Annealed.sigmaBar M K : ℝ))
      20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (theta M * ((nativeAvg * nativeA + (nativeRaw g).2.2 : ℚ) : ℝ)) := by
    rw [eLpNorm_eq_eLpNorm' (by norm_num : (20 : ℝ≥0∞) ≠ 0) (by norm_num : (20 : ℝ≥0∞) ≠ ⊤)
      hTm.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat]
    exact hraw.trans (ENNReal.ofReal_le_ofReal hrawle)
  have hfr := nativeReturns_cutoffTrace_frame_theta M hgam K g hg1334 K _ hq0 hchild
  have hA : 0 ≤ theta M * nativeFrameReal (((11 / 10) * (2 * nativeGamma * (g : ℚ)) : ℚ) : ℝ)
      (((nativeAvg * nativeA + (nativeRaw g).2.2 : ℚ) : ℝ)) := by
    refine mul_nonneg hτ0.le ?_
    refine nativeFrameReal_nonneg _ _ (by push_cast; norm_num [nativeGamma]) ?_ hq0
    push_cast
    have hgR : (g : ℝ) ≤ 1334 := by exact_mod_cast hg1334
    norm_num [nativeGamma]
    nlinarith
  have hTn := cutoffTraceDefect_measurable M (K + (g : ℤ)) K
  rw [eLpNorm_eq_eLpNorm' (by norm_num : (20 : ℝ≥0∞) ≠ 0) (by norm_num : (20 : ℝ≥0∞) ≠ ⊤)
    hTn.aestronglyMeasurable] at hfr
  simp only [ENNReal.toReal_ofNat] at hfr
  have hscale : (originCube 2 (K + 9)).scale - ((9 : ℕ) : ℤ) = K := by
    simp [originCube]
  have hpar := native_source_parent_L20_cap M (K + (g : ℤ)) (originCube 2 (K + 9)) 9 _ hA
    (by rw [hscale]; exact hfr)
  have hpar' : eLpNorm (cutoffTraceDefect M (K + (g : ℤ)) (originCube 2 (K + 9)).scale) 20
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (theta M * nativeFrameReal
        (((11 / 10) * (2 * nativeGamma * (g : ℚ)) : ℚ) : ℝ)
        (((nativeAvg * nativeA + (nativeRaw g).2.2 : ℚ) : ℝ))) := by
    rw [eLpNorm_eq_eLpNorm' (by norm_num : (20 : ℝ≥0∞) ≠ 0) (by norm_num : (20 : ℝ≥0∞) ≠ ⊤)
      (cutoffTraceDefect_measurable M (K + (g : ℤ)) (originCube 2 (K + 9)).scale).aestronglyMeasurable]
    simpa only [ENNReal.toReal_ofNat] using hpar
  have e1 : K + (g : ℤ) = N := by rw [hK]; ring
  have e2 : (originCube 2 (K + 9)).scale = N - ((g - 9 : ℕ) : ℤ) := by
    simp only [originCube]
    rw [hK, Nat.cast_sub hg9]; push_cast; ring
  rw [e1, e2] at hpar'
  exact hpar'

end ASDExplicitGamma.Native
