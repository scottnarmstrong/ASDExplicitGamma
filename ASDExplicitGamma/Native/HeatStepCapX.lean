module

public import ASDExplicitGamma.Native.HeatStepPasses
public import ASDExplicitGamma.Native.HeatStepCapFAux
public import ASDExplicitGamma.Native.HeatRefinedAugmentedRaw
public import ASDExplicitGamma.Native.HeatRefinedTranslatedLaw
public import ASDExplicitGamma.Native.HeatAuxiliaryGaussianLaw
public import ASDExplicitGamma.Numerics.Native.HeatParametersData
public import ASDExplicitGamma.Inverse.ParentGapCenteredDepth
public import ASDExplicitGamma.Native.HeatRefinedObserverAugment

/-! The heat-augmented individual cap `X` of the refined child traces from the actual
individual `L^20` cap `y₀` of the child along the heat path, the OLD local bank and the
Gaussian auxiliary shear: `X = (√y₀ + √(2 B GM V))²`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Set Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Numerics.Native ProbabilityTheory ASDExplicitGamma.Inverse
open scoped ENNReal NNReal Topology Nat

/-- The actual `L^20` cap of the refined child trace along the heat path at heat time `t`
(old cutoff `m+1`, frame `σ̄_{m+1}`, shells `m+2, …, m+ns+1`, child cube of scale `m`). -/
def NativeHeatStepChildAllTimeCap (M : ABKModel 2) (m : ℤ) (ns : ℕ) (y0 : ℝ) : Prop :=
  ∀ t ∈ Ioo (0 : ℝ) 1,
    eLpNorm (fun ω : Cutoff.CutoffSample 2 =>
      modelTraceObservable (m + 1 - 1) M.nu (Annealed.sigmaBar M (m + 1))
        (parentBoundaryObserverBandScalar (m + 1 - 1) (m + 1) ns t ω)) 20
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal y0

/-- The Gaussian even-moment constant of order twenty is below the tabulated `gm₂₀`. -/
theorem nativeHeatStep_df20_le_gm :
    Real.rpow ((2 * 20 - 1)‼ : ℝ) ((20 : ℝ)⁻¹) ≤
      ((nativeHeatParametersData.gm.getD 20 0 : ℚ) : ℝ) := by
  have hdouble : Nat.factorial (2 * 20) = (2 ^ 20 * Nat.factorial 20) * (2 * 20 - 1)‼ := by
    have h := Nat.factorial_eq_mul_doubleFactorial (2 * 20 - 1)
    rw [show 2 * 20 - 1 + 1 = 2 * 20 by norm_num, Nat.doubleFactorial_two_mul] at h
    exact h
  have hdoubleR : (Nat.factorial (2 * 20) : ℝ) =
      (2 : ℝ) ^ 20 * (Nat.factorial 20 : ℝ) * ((2 * 20 - 1)‼ : ℝ) := by
    exact_mod_cast hdouble
  have hratio : ((2 * 20 - 1)‼ : ℝ) =
      ((Nat.factorial (2 * 20) : ℝ) / ((2 : ℝ) ^ 20 * (Nat.factorial 20 : ℝ))) := by
    have hden : (2 : ℝ) ^ 20 * (Nat.factorial 20 : ℝ) ≠ 0 := by positivity
    rw [hdoubleR]
    field_simp
  have hgmQ : (Nat.factorial (2 * 20) : ℚ) / (2 ^ 20 * Nat.factorial 20) ≤
      (nativeHeatParametersData.gm.getD 20 0) ^ 20 := by
    simpa using nativeHeatGM20_powers.2
  have hgmR : ((2 * 20 - 1)‼ : ℝ) ≤ ((nativeHeatParametersData.gm.getD 20 0 : ℚ) : ℝ) ^ 20 := by
    rw [hratio]
    have := (Rat.cast_le (K := ℝ)).2 hgmQ
    push_cast at this
    exact this
  have hgm0 : 0 ≤ ((nativeHeatParametersData.gm.getD 20 0 : ℚ) : ℝ) := by
    exact_mod_cast nativeHeatGM20_powers.1
  calc Real.rpow ((2 * 20 - 1)‼ : ℝ) ((20 : ℝ)⁻¹)
      ≤ Real.rpow (((nativeHeatParametersData.gm.getD 20 0 : ℚ) : ℝ) ^ 20) ((20 : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) hgmR (by norm_num)
    _ = ((nativeHeatParametersData.gm.getD 20 0 : ℚ) : ℝ) := by
        have := Real.pow_rpow_inv_natCast hgm0 (n := 20) (by norm_num)
        simpa using this

/-- A centered Gaussian has `L^40` norm at most `√(v gm₂₀)`. -/
theorem nativeHeatStep_gaussian40_le {Ξ : Type*} [MeasurableSpace Ξ] (η : Measure Ξ)
    (G : Ξ → ℝ) (hG : Measurable G) (v : ℝ≥0) (hlaw : η.map G = gaussianReal 0 v) :
    eLpNorm G (ENNReal.ofReal (2 * 20)) η ≤
      ENNReal.ofReal (Real.sqrt ((v : ℝ) * ((nativeHeatParametersData.gm.getD 20 0 : ℚ) : ℝ))) := by
  have h := (heat_auxiliary_gaussian_even_norm η G hG v hlaw 20 (by norm_num)).2
  have e : ENNReal.ofReal (2 * ((20 : ℕ) : ℝ)) = ENNReal.ofReal (2 * 20) := by norm_num
  rw [e] at h
  refine h.trans (ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_))
  exact mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_ofNat] using nativeHeatStep_df20_le_gm) v.2

/-- The heat-augmented translated child trace obeys `‖T(A + gJ)‖₂₀ ≤ (√y₀ + √(2 (b+ε) v gm₂₀))²`
from the actual child cap `y₀` at heat time `t`. -/
theorem nativeHeatStep_translatedTrace_L20_le (ns : ℕ) [NeZero ns]
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ j < m + 1, nativeInductionState M h j) (t : ℝ) (ht : t ≤ 1)
    (y0 : ℝ) (hy0 : 0 ≤ y0)
    (hchild : eLpNorm (fun ω : Cutoff.CutoffSample 2 =>
      modelTraceObservable (m + 1 - 1) M.nu (Annealed.sigmaBar M (m + 1))
        (parentBoundaryObserverBandScalar (m + 1 - 1) (m + 1) ns t ω)) 20
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal y0)
    (x : Vec 2) (g : (ℕ → ℝ) → ℝ) (hgm : Measurable g) (v : ℝ≥0)
    (hlaw : standardGaussianInfinitePi.map (fun ξ => g ξ / (Annealed.sigmaBar M (m + 1) : ℝ)) =
      gaussianReal 0 v) :
    eLpNorm (heatRefinedTranslatedTrace M (m + 1) ns t x g) 20
        (nativeHeatRemainderJointLaw M) ≤
      ENNReal.ofReal ((Real.sqrt y0 + Real.sqrt (2 * ((3683 / 2500 : ℝ) + 3 / 10 ^ 46) *
        ((v : ℝ) * ((nativeHeatParametersData.gm.getD 20 0 : ℚ) : ℝ)))) ^ 2) := by
  rw [heat_refined_translated_trace_norm_eq M (m + 1) ns t x g hgm 20]
  have hq : originCube 2 (m + 1 - 1) ∈ descendantsAtDepth (originCube 2 (m + 1)) 1 := by
    simpa only [Nat.cast_one] using originCube_mem_descendantsAtDepth' 2 (m + 1) 1
  have ha := heat_refined_observer_augmented_Lp M h hM hg (m + 1 - 1) (m + 1) 1 (by norm_num) hq
    ns hpast t ht g hgm 20 (by norm_num) (by norm_num)
  have e20 : ENNReal.ofReal (20 : ℝ) = 20 := by simp
  rw [e20] at ha
  have hG := nativeHeatStep_gaussian40_le standardGaussianInfinitePi
    (fun ξ => g ξ / (Annealed.sigmaBar M (m + 1) : ℝ)) (hgm.div_const _) v hlaw
  have hbound := ha.trans (pow_le_pow_left' (add_le_add
    (ENNReal.rpow_le_rpow hchild (by norm_num : (0 : ℝ) ≤ 1 / 2))
    (mul_le_mul' le_rfl hG)) 2)
  refine hbound.trans_eq ?_
  have hgm0 : 0 ≤ ((nativeHeatParametersData.gm.getD 20 0 : ℚ) : ℝ) := by
    exact_mod_cast nativeHeatGM20_powers.1
  have hprod : 0 ≤ (v : ℝ) * ((nativeHeatParametersData.gm.getD 20 0 : ℚ) : ℝ) :=
    mul_nonneg v.2 hgm0
  rw [ENNReal.ofReal_rpow_of_nonneg hy0 (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.ofReal_rpow_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ((3683 / 2500 : ℝ) + 3 / 10 ^ 46))
      (by norm_num : (0 : ℝ) ≤ 1 / 2), ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * ((3683 / 2500 : ℝ) + 3 / 10 ^ 46)),
    ← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
    ← ENNReal.ofReal_pow (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]

/-- Each auxiliary variance is below the configured variance clock. -/
theorem nativeHeatStep_auxVariance_le_genVar (ns : ℕ) [NeZero ns] (hgen : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hstate : nativeInductionState M h (m + 1)) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    ((nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns
        (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
        (nativeHeatTheta : ℝ) t i : NNReal) : ℝ) ≤ (nativeHeatGenVariance ns : ℝ) := by
  have hg0 := M.shellPrefix.gamma_pos.le
  have hv := nativeHeatStep_auxVariance_le ns M h hM m hstate t ht i
  have heold : (heatVHEATDriftEGen ns) M ≤ ((nativeHeatOldRowGen ns).e : ℝ) := by
    unfold heatVHEATDriftEGen
    exact hgen.efactor M.gamma hg0 hg
  have hθ : (0 : ℝ) ≤ 1 + (nativeHeatTheta : ℝ) := by norm_num [nativeHeatTheta]
  refine hv.trans ?_
  rw [nativeHeatGenVariance_eq]
  have h1 := (Rat.cast_le (K := ℝ)).2
    (nativeUp_ge ((1 + nativeHeatTheta) * (nativeHeatOldRowGen ns).e * (ns : ℚ)))
  push_cast at h1
  refine le_trans ?_ h1
  have : (ns : ℝ) * (heatVHEATDriftEGen ns) M ≤ (ns : ℝ) * ((nativeHeatOldRowGen ns).e : ℝ) :=
    mul_le_mul_of_nonneg_left heold (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left this hθ]

theorem nativeHeatStep_rootValid_nonneg (q : ℚ) {n : ℕ} (h : nativeRootValid q n = true) :
    0 ≤ q := (of_decide_eq_true h).2.1

/-- The heat-augmented individual cap: `X = frames.x` bounds every actual translated, sheared
child trace in `L^20`, for all heat times, from the all-time actual child cap `y₀`. -/
theorem nativeHeatStep_xCap (ns : ℕ) [NeZero ns] (hnum : NativeHeatStepPassNum ns)
    (hfr : NativeHeatStepFrameNum ns) (hgen : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ j < m + 1, nativeInductionState M h j)
    (hstate : nativeInductionState M h (m + 1))
    (hchild : NativeHeatStepChildAllTimeCap M m ns (nativeHeatY0Gen ns : ℝ)) :
    ∀ t ∈ Ioo (0 : ℝ) 1,
      ((heatVHEATDriftRefinedPhysicalXExtendedGen ns) M m t
        (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen M m ns
          (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
          (nativeHeatTheta : ℝ) t)).toReal ≤ ((nativeHeatFramesGen ns).x : ℝ) := by
  classical
  intro t ht
  let Ffam := nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns
  let g := nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen M m ns Ffam (nativeHeatTheta : ℝ) t
  have hy0q := nativeHeatStep_rootValid_nonneg _ hfr.y0_root
  have hy0 : (0 : ℝ) ≤ (nativeHeatY0Gen ns : ℝ) := by exact_mod_cast hy0q
  have hgm0 : 0 ≤ ((nativeHeatParametersData.gm.getD 20 0 : ℚ) : ℝ) := by
    exact_mod_cast nativeHeatGM20_powers.1
  have hBn : (0 : ℝ) ≤ (nativeHeatB : ℝ) := by
    have : (0 : ℚ) ≤ nativeHeatB := by
      norm_num [nativeHeatB, nativeHeatRQ, nativeE, nativeGamma, nativeB]
    exact_mod_cast this
  have hB : (2 * ((3683 / 2500 : ℝ) + 3 / 10 ^ 46)) ≤ 2 * (nativeHeatB : ℝ) := by
    have : (3683 / 2500 + 3 / 10 ^ 46 : ℚ) ≤ nativeHeatB := by
      norm_num [nativeHeatB, nativeHeatRQ, nativeE, nativeGamma, nativeB]
    have h2 := (Rat.cast_le (K := ℝ)).2 this
    push_cast at h2
    linarith
  have hxp : ((nativeHeatFramesGen ns).x : ℚ) =
      nativeUp ((nativeRootUp (nativeHeatY0Gen ns) +
        nativeRootUp (2 * nativeHeatB * nativeHeatParametersData.gm.getD 20 0 *
          nativeHeatGenVariance ns)) ^ 2) := by
    simp [nativeHeatFramesGen, nativeHeatFrames, nativeHeatY0Gen]
  have hnu := (Rat.cast_le (K := ℝ)).2
    (nativeUp_ge ((nativeRootUp (nativeHeatY0Gen ns) +
        nativeRootUp (2 * nativeHeatB * nativeHeatParametersData.gm.getD 20 0 *
          nativeHeatGenVariance ns)) ^ 2))
  rw [← hxp] at hnu
  push_cast at hnu
  have hxnonneg : (0 : ℝ) ≤ ((nativeHeatFramesGen ns).x : ℝ) := by
    exact_mod_cast hnum.x_pos.le
  have hXe : (heatVHEATDriftRefinedPhysicalXExtendedGen ns) M m t g =
      (heatVHEATDriftSourceXExtendedGen ns) Finset.univ M (m + 1) t
        (heatVHEATDriftRefinedShift m) g :=
    heatVHEATDrift_refined_physical_norm_eq_Gen ns M m t g
  have hle : (heatVHEATDriftRefinedPhysicalXExtendedGen ns) M m t g ≤
      ENNReal.ofReal ((nativeHeatFramesGen ns).x : ℝ) := by
    rw [hXe]
    unfold heatVHEATDriftSourceXExtendedGen heatVHEATDriftXExtended
    apply Finset.sup_le
    intro i _
    have hgmeas := nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen_measurable M m ns Ffam
      (nativeHeatTheta : ℝ) t i
    have hlaw := nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen_law M m ns Ffam
      (nativeHeatTheta : ℝ) t i
    have hT := nativeHeatStep_translatedTrace_L20_le ns M h hM hg m hpast t ht.2.le
      (nativeHeatY0Gen ns : ℝ) hy0 (hchild t ht) (heatVHEATDriftRefinedShift m i) (g i)
      hgmeas _ hlaw
    refine hT.trans (ENNReal.ofReal_le_ofReal ?_)
    have hvar := nativeHeatStep_auxVariance_le_genVar ns hgen M h hM hg m hstate t
      ⟨ht.1.le, ht.2.le⟩ i
    have t1 : Real.sqrt ((nativeHeatY0Gen ns : ℚ) : ℝ) ≤ (nativeRootUp (nativeHeatY0Gen ns) : ℝ) :=
      nativeHeatStep_sqrt_le_rootUp _ hfr.y0_root
    have hv0 : (0 : ℝ) ≤ ((nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns Ffam
        (nativeHeatTheta : ℝ) t i : NNReal) : ℝ) := NNReal.coe_nonneg _
    have t2 : Real.sqrt (2 * ((3683 / 2500 : ℝ) + 3 / 10 ^ 46) *
        (((nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns Ffam
          (nativeHeatTheta : ℝ) t i : NNReal) : ℝ) *
          ((nativeHeatParametersData.gm.getD 20 0 : ℚ) : ℝ))) ≤
        (nativeRootUp (2 * nativeHeatB * nativeHeatParametersData.gm.getD 20 0 *
          nativeHeatGenVariance ns) : ℝ) := by
      refine le_trans (Real.sqrt_le_sqrt ?_) (nativeHeatStep_sqrt_le_rootUp _ hfr.xp_root)
      push_cast
      have e1 := mul_le_mul_of_nonneg_right hB (mul_nonneg hv0 hgm0)
      have e2 := mul_le_mul_of_nonneg_right hvar hgm0
      have e3 := mul_le_mul_of_nonneg_left e2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hBn)
      nlinarith [e1, e3]
    have hs0 : 0 ≤ Real.sqrt ((nativeHeatY0Gen ns : ℚ) : ℝ) + Real.sqrt (2 * ((3683 / 2500 : ℝ) + 3 / 10 ^ 46) *
        (((nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns Ffam
          (nativeHeatTheta : ℝ) t i : NNReal) : ℝ) *
          ((nativeHeatParametersData.gm.getD 20 0 : ℚ) : ℝ))) :=
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hsq := pow_le_pow_left₀ hs0 (add_le_add t1 t2) 2
    refine hsq.trans ?_
    push_cast at hnu ⊢
    exact hnu
  exact ENNReal.toReal_le_of_le_ofReal hxnonneg hle

end ASDExplicitGamma.Native

end
