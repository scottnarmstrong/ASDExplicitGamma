module

public import ASDExplicitGamma.Native.HeatInitialRefinedCross
public import ASDExplicitGamma.Native.HeatInitialRefinedShearTheta

/-! Theta-scaled old-shear / fresh-centre cross moment: the shear `L^k` cap carries `√θ` and the
fresh RMS cap is an arbitrary `freshCap`, so the cross row is `√θ · cross_k · freshCap`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Variational ASDExplicitGamma.Response
open ASDExplicitGamma.Numerics.Native
open Algsuperdiff.Section3.Provider.BadEvents
open scoped ENNReal

set_option linter.constructorNameAsVariable false

/-- The state-driven child-shear cross-scale estimate supplies both the
finite p-moment and the real Lp cap used by the old/fresh type-two adapter. -/
theorem nativeHeatRefined_childShear_lpCap_theta
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (m : ℤ)
    (hscale : Q.scale = m)
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (k : ℕ) (hk2 : 2 ≤ k) (hk20 : k ≤ 20) :
    MemLp (fun ω : Cutoff.CutoffSample 2 =>
      Variational.shearTraceLinear (coarseBlockMatrix (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)) (ENNReal.ofReal (k : ℝ))
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (fun ω : Cutoff.CutoffSample 2 =>
        Variational.shearTraceLinear (coarseBlockMatrix (cubeSet Q)
          (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)) (ENNReal.ofReal (k : ℝ))
          (Cutoff.cutoffSampleLaw M).toMeasure ≤
        Real.sqrt (theta M * (2 * ((nativeHeatB : ℝ) *
          nativeHeatHnReal nativeHeatParametersData ((k : ℚ) / 2) +
          ((nativeHeatEps * nativeHeatParametersData.hp : ℚ) : ℝ)))) := by
  obtain ⟨hτ0, hτ1⟩ := theta_pos_le_one M hgamma
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let z : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    Variational.shearTraceLinear (coarseBlockMatrix (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)
  let B : ℝ := theta M * (2 * ((nativeHeatB : ℝ) *
    nativeHeatHnReal nativeHeatParametersData ((k : ℚ) / 2) +
    ((nativeHeatEps * nativeHeatParametersData.hp : ℚ) : ℝ)))
  have hkpos : 0 < (k : ℝ) := by
    have hk : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    linarith
  have hp0 : ENNReal.ofReal (k : ℝ) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hkpos)
  have hptop : ENNReal.ofReal (k : ℝ) ≠ ∞ := ENNReal.ofReal_ne_top
  have hzmeas : Measurable z := by
    let shear : FullBlockMat 2 → ℝ := fun A =>
      A (Sum.inl 1) (Sum.inr 0) - A (Sum.inl 0) (Sum.inr 1)
    have hs : Measurable shear := by fun_prop
    have hEq (ω : Cutoff.CutoffSample 2) : z ω =
        shear (Cold.coldNativeResponse M (m + 1) Q ω) := by
      simp [z, shear, Cold.coldNativeResponse, Variational.shearTraceLinear,
        Variational.frameMatrix, Homogenization.toFullBlockMat]
    rw [show z = fun ω => shear (Cold.coldNativeResponse M (m + 1) Q ω) from funext hEq]
    exact hs.comp (Cold.coldNativeResponse_measurable M (m + 1) Q)
  have hcross := nativeHeatRefined_childShear_eLpNorm_theta
    M h hM hgamma m hpast Q hscale k hk2 hk20
  have hcrossZ : eLpNorm' z (k : ℝ) μ ^ 2 ≤ ENNReal.ofReal B := by
    simpa [z, μ, B] using hcross
  have hprime : eLpNorm' z (k : ℝ) μ < ∞ := by
    apply lt_top_iff_ne_top.mpr
    intro htop
    have htopSq : eLpNorm' z (k : ℝ) μ ^ 2 = ∞ := by simp [htop]
    rw [htopSq] at hcrossZ
    exact (not_le_of_gt ENNReal.ofReal_lt_top) hcrossZ
  have hmem : MemLp z (ENNReal.ofReal (k : ℝ)) μ := by
    rw [memLp_iff]
    rw [eLpNorm_eq_eLpNorm' hp0 hptop hzmeas.aestronglyMeasurable]
    simpa [ENNReal.toReal_ofReal hkpos.le] using hprime
  have hnormEq : ENNReal.ofReal (lpNorm z (ENNReal.ofReal (k : ℝ)) μ) =
      eLpNorm' z (k : ℝ) μ := by
    calc
      _ = eLpNorm z (ENNReal.ofReal (k : ℝ)) μ := ofReal_lpNorm hmem
      _ = eLpNorm' z (k : ℝ) μ := by
        rw [eLpNorm_eq_eLpNorm' hp0 hptop hzmeas.aestronglyMeasurable,
          ENNReal.toReal_ofReal hkpos.le]
  have hB0 : 0 ≤ B := by
    dsimp [B]
    have hBq : (0 : ℚ) ≤ nativeHeatB := by decide +kernel
    have hEq : (0 : ℚ) ≤ nativeHeatEps := by decide +kernel
    have hhpq : (0 : ℚ) ≤ nativeHeatParametersData.hp := by
      norm_num [nativeHeatParametersData]
    have hqstar : (0 : ℚ) ≤ nativeQstar := by norm_num [nativeQstar]
    have hH : 0 ≤ nativeHeatHnReal nativeHeatParametersData ((k : ℚ) / 2) := by
      rw [nativeHeatHnReal]
      apply mul_nonneg (by exact_mod_cast hqstar)
      apply Real.rpow_nonneg
      exact_mod_cast (div_nonneg hhpq hqstar)
    exact mul_nonneg hτ0.le (mul_nonneg (by norm_num)
      (add_nonneg (mul_nonneg (by exact_mod_cast hBq) hH)
        (by exact_mod_cast mul_nonneg hEq hhpq)))
  have hsqENN : ENNReal.ofReal (lpNorm z (ENNReal.ofReal (k : ℝ)) μ) ^ 2 ≤
      ENNReal.ofReal B := by
    rw [hnormEq]
    exact hcrossZ
  have hsq : (lpNorm z (ENNReal.ofReal (k : ℝ)) μ) ^ 2 ≤ B :=
    (ENNReal.ofReal_le_ofReal_iff hB0).mp (by simpa [ENNReal.ofReal_pow] using hsqENN)
  refine ⟨hmem, ?_⟩
  exact Real.le_sqrt_of_sq_le (by simpa [z, μ, B] using hsq)


/-- A fresh vector RMS moment bound composes with the actual state-driven
four-colour shear estimate and the literal generated cross row. The fresh RMS
premise is deliberately stated on the pushforward fresh law, so the q3 grid
moment theorem can discharge it without any old-field hypotheses. -/
theorem nativeHeatRefined_oldShear_fresh_average_initialCrossMoment_theta
    {ι Η : Type*} [MeasurableSpace Η] [Fintype ι] [Nonempty ι]
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero) (m : ℤ) (C : ι → TriadicCube 2)
    (hC : Function.Injective C) (hcard : Fintype.card ι = 9^10)
    (hscale : ∀ i, (C i).scale = m)
    (J : Set ℤ) (hJ : Disjoint (Set.Iic (m + 1)) J)
    (k : ℕ) (hk2 : 2 ≤ k) (hk20 : k ≤ 20)
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    {Fresh : Cutoff.CutoffSample 2 → Η}
    (hFreshLocal : @Measurable (Cutoff.CutoffSample 2) Η
      ((Cutoff.shellIndexSigma J).comap Subtype.val) _ Fresh)
    (hFreshMeas : Measurable Fresh) (coeff : ι → Η → ℝ)
    (hcoeff : ∀ i, Measurable (coeff i)) (freshCap : ℝ) (_hfreshCap : 0 ≤ freshCap)
    (hfresh :
      ∫⁻ η, (ENNReal.ofReal (Real.sqrt
        ((Fintype.card ι : ℝ)⁻¹ * ∑ i, (coeff i η)^2))) ^ (k : ℝ)
        ∂((Cutoff.cutoffSampleLaw M).toMeasure.map Fresh) ≤
        (ENNReal.ofReal freshCap) ^ (k : ℝ)) :
    ∫⁻ ω, ‖(2 * (∑ i, coeff i (Fresh ω) *
        Variational.shearTraceLinear (coarseBlockMatrix (cubeSet (C i))
          (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun))) /
          (Fintype.card ι : ℝ)‖ₑ ^ (k : ℝ)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      (ENNReal.ofReal
        (Real.sqrt (theta M) * ((nativeHeatParametersData.cross.getD k 0 : ℚ) * freshCap))) ^ (k : ℝ) := by
  obtain ⟨hτ0, hτ1⟩ := theta_pos_le_one M hgamma
  have hk2R : 2 ≤ (k : ℝ) := by exact_mod_cast hk2
  have hkR0 : 0 ≤ (k : ℝ) := by positivity
  have hCross := nativeHeat_cross_bound_all k hk2 hk20
  let shearCap0 : ℝ := Real.sqrt (2 * ((nativeHeatB : ℝ) *
    nativeHeatHnReal nativeHeatParametersData ((k : ℚ) / 2) +
      ((nativeHeatEps * nativeHeatParametersData.hp : ℚ) : ℝ)))
  let shearCap : ℝ := Real.sqrt (theta M * (2 * ((nativeHeatB : ℝ) *
    nativeHeatHnReal nativeHeatParametersData ((k : ℚ) / 2) +
      ((nativeHeatEps * nativeHeatParametersData.hp : ℚ) : ℝ))))
  have hsc : shearCap = Real.sqrt (theta M) * shearCap0 := by
    simp only [shearCap, shearCap0]
    rw [Real.sqrt_mul hτ0.le]
  let c0 : ℝ := Real.sqrt (theta M) * ((nativeHeatParametersData.cross.getD k 0 : ℚ) : ℝ)
  let N : ℝ := (Fintype.card ι : ℝ)
  let rms : Η → ℝ := fun η => Real.sqrt (N⁻¹ * ∑ i, (coeff i η)^2)
  let coeff₂ : ι → Η → ℝ := fun i η => 2 * coeff i η
  have hshearCap : 0 ≤ shearCap := by exact Real.sqrt_nonneg _
  have hN : N = (9 : ℝ)^10 := by
    dsimp [N]
    exact_mod_cast hcard
  have hrms (η : Η) : 0 ≤ rms η := by exact Real.sqrt_nonneg _
  have hrms₂ (η : Η) :
      Real.sqrt (N⁻¹ * ∑ i, (coeff₂ i η)^2) = 2 * rms η := by
    have hsum : ∑ i, (coeff₂ i η)^2 = 4 * ∑ i, (coeff i η)^2 := by
      dsimp [coeff₂]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsum, show N⁻¹ * (4 * ∑ i, (coeff i η)^2) =
      4 * (N⁻¹ * ∑ i, (coeff i η)^2) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show (4 : ℝ) = 2^2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hfactor (η : Η) :
      Real.sqrt (Fintype.card (Fin 9 × Fin 9) : ℝ) * Real.sqrt ((k : ℝ) - 1) *
          Real.sqrt (∑ i, (|coeff₂ i η| * shearCap) ^ 2) / N ≤
        c0 * rms η := by
    have heq := nativeHeat_typeTwoFactor_eq_source hcard k hk2 coeff₂ η shearCap hshearCap
    have hCrossReal :
        nativeHeatCrossReal nativeHeatParametersData k =
          2 * Real.sqrt ((((k - 1) * 9^2 : ℕ) / (9^10 : ℚ) : ℚ) : ℝ) * shearCap0 := rfl
    have hbound := mul_le_mul_of_nonneg_right hCross (hrms η)
    calc
      _ = Real.sqrt ((((k - 1) * 9^2 : ℕ) / (9^10 : ℚ) : ℚ) : ℝ) *
          shearCap * Real.sqrt (N⁻¹ * ∑ i, (coeff₂ i η)^2) := heq
      _ = Real.sqrt (theta M) * (nativeHeatCrossReal nativeHeatParametersData k * rms η) := by
        rw [hrms₂ η, hsc, hCrossReal]
        ring
      _ ≤ Real.sqrt (theta M) * (((nativeHeatParametersData.cross.getD k 0 : ℚ) : ℝ) * rms η) :=
        mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg _)
      _ = c0 * rms η := by simp only [c0]; ring
  have hrow00 :
      0 ≤ ((nativeHeatParametersData.cross.getD k 0 : ℚ) : ℝ) := by
    have hsource0 : 0 ≤ nativeHeatCrossReal nativeHeatParametersData k := by
      unfold nativeHeatCrossReal
      positivity
    exact hsource0.trans hCross
  have hrow0 : 0 ≤ c0 := mul_nonneg (Real.sqrt_nonneg _) hrow00
  have hcoeff₂ (i : ι) : Measurable (coeff₂ i) := by
    dsimp [coeff₂]
    exact measurable_const.mul (hcoeff i)
  have htrace : ∀ i, MemLp (Cold.coldNativeCellTrace M (m + 1) (C i)) 2
      (Cutoff.cutoffSampleLaw M).toMeasure := fun i =>
    nativeHeatRefined_childTrace_memLp_two M h hM hgamma m hpast (C i) (hscale i)
  have hcaps (i : ι) := nativeHeatRefined_childShear_lpCap_theta M h hM hgamma (C i) m (hscale i)
    hpast k hk2 hk20
  have hIndep := nativeHeatRefined_shear_colour_independent M h hM m C hC hscale
  have hAdapter := nativeHeat_oldShear_fresh_average_moment_of_caps M (m + 1) J hJ C
    (fun i => nativeHeatRefinedColor81 (C i)) (k : ℝ) hk2R htrace
    (fun i => (hcaps i).1) hIndep (fun _ => shearCap) (fun _ => hshearCap)
    (fun i => (hcaps i).2) hFreshLocal hFreshMeas coeff₂ hcoeff₂
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let ν := μ.map Fresh
  have hsumEq (ω : Cutoff.CutoffSample 2) :
      (∑ i, coeff₂ i (Fresh ω) *
        Variational.shearTraceLinear (coarseBlockMatrix (cubeSet (C i))
          (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)) =
      2 * (∑ i, coeff i (Fresh ω) *
        Variational.shearTraceLinear (coarseBlockMatrix (cubeSet (C i))
          (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)) := by
    calc
      _ = ∑ i, 2 * (coeff i (Fresh ω) *
          Variational.shearTraceLinear (coarseBlockMatrix (cubeSet (C i))
            (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [coeff₂]
          ring
      _ = _ := by rw [Finset.mul_sum]
  have hAdapter' :
      ∫⁻ ω, ‖(2 * (∑ i, coeff i (Fresh ω) *
          Variational.shearTraceLinear (coarseBlockMatrix (cubeSet (C i))
            (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun))) /
            (Fintype.card ι : ℝ)‖ₑ ^ (k : ℝ) ∂μ ≤
        ∫⁻ η, (ENNReal.ofReal (Real.sqrt (Fintype.card (Fin 9 × Fin 9) : ℝ) * Real.sqrt ((k : ℝ) - 1) *
          Real.sqrt (∑ i, (|coeff₂ i η| * shearCap) ^ 2) / N)) ^
            (k : ℝ) ∂ν := by
    calc
      _ = ∫⁻ ω, ‖(∑ i, coeff₂ i (Fresh ω) *
            Variational.shearTraceLinear (coarseBlockMatrix (cubeSet (C i))
              (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)) /
              (Fintype.card ι : ℝ)‖ₑ ^ (k : ℝ) ∂μ := by
          apply lintegral_congr
          intro ω
          rw [← hsumEq ω]
      _ ≤ _ := by simpa only [μ, ν, N, shearCap] using hAdapter
  have hpoint (η : Η) :
      (ENNReal.ofReal (Real.sqrt (Fintype.card (Fin 9 × Fin 9) : ℝ) * Real.sqrt ((k : ℝ) - 1) *
        Real.sqrt (∑ i, (|coeff₂ i η| * shearCap)^2) / N)) ^ (k : ℝ) ≤
      (ENNReal.ofReal (c0 *
        rms η)) ^ (k : ℝ) := by
    exact ENNReal.rpow_le_rpow
      (ENNReal.ofReal_le_ofReal (hfactor η)) hkR0
  have hIntegral := hAdapter'.trans (lintegral_mono hpoint)
  have hsumMeas : Measurable (fun η => ∑ i, coeff i η ^ 2) := by
    apply Finset.measurable_sum
    intro i hi
    exact (hcoeff i).pow_const 2
  have hrmsMeas : Measurable rms := by
    dsimp [rms]
    exact Real.continuous_sqrt.measurable.comp (measurable_const.mul hsumMeas)
  have hpowMeas : Measurable (fun η => (ENNReal.ofReal (rms η)) ^ (k : ℝ)) :=
    ENNReal.continuous_rpow_const.measurable.comp
      (ENNReal.measurable_ofReal.comp hrmsMeas)
  have hFactorization :
      ∫⁻ η, (ENNReal.ofReal (c0 *
        rms η)) ^ (k : ℝ) ∂ν =
        (ENNReal.ofReal c0) ^
            (k : ℝ) *
          ∫⁻ η, (ENNReal.ofReal (rms η)) ^ (k : ℝ) ∂ν := by
    calc
      _ = ∫⁻ η, (ENNReal.ofReal c0) ^
            (k : ℝ) * (ENNReal.ofReal (rms η)) ^ (k : ℝ) ∂ν := by
          apply lintegral_congr_ae
          filter_upwards with η
          calc
            (ENNReal.ofReal (c0 *
              rms η)) ^ (k : ℝ) =
                (ENNReal.ofReal c0 *
                  ENNReal.ofReal (rms η)) ^ (k : ℝ) := by
                    rw [← ENNReal.ofReal_mul hrow0]
            _ = (ENNReal.ofReal c0) ^
                  (k : ℝ) * (ENNReal.ofReal (rms η)) ^ (k : ℝ) :=
                ENNReal.mul_rpow_of_nonneg _ _ hkR0
      _ = _ := lintegral_const_mul _ hpowMeas
  calc
    _ ≤ (ENNReal.ofReal c0) ^
          (k : ℝ) * ∫⁻ η, (ENNReal.ofReal (rms η)) ^ (k : ℝ) ∂ν :=
        hIntegral.trans_eq hFactorization
    _ ≤ (ENNReal.ofReal c0) ^
          (k : ℝ) * (ENNReal.ofReal freshCap) ^ (k : ℝ) :=
        by
          gcongr
    _ = (ENNReal.ofReal (c0 *
          freshCap)) ^ (k : ℝ) := by
        calc
          _ = (ENNReal.ofReal c0 *
                ENNReal.ofReal freshCap) ^ (k : ℝ) := by
              rw [← ENNReal.mul_rpow_of_nonneg _ _ hkR0]
          _ = _ := by rw [← ENNReal.ofReal_mul hrow0]
    _ = _ := by simp only [c0, mul_assoc]


end ASDExplicitGamma.Native
