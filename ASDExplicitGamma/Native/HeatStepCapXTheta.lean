module

public import ASDExplicitGamma.Native.HeatStepCapX
public import ASDExplicitGamma.Native.HeatStepThetaRow
public import ASDExplicitGamma.Native.HeatStepAllTimeCapTheta

/-! The theta-scaled heat-augmented individual cap `X ≤ θ · frames.x` of the refined child traces,
from the theta-scaled all-time child cap `θ · y₀`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Set Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Numerics.Native ProbabilityTheory ASDExplicitGamma.Inverse
open scoped ENNReal NNReal Topology Nat

/-- Each auxiliary variance is below `θ` times the configured variance clock. -/
theorem nativeHeatStep_auxVariance_le_genVar_theta (ns : ℕ) [NeZero ns]
    (hgen : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hstate : nativeInductionState M h (m + 1)) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    ((nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns
        (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
        (nativeHeatTheta : ℝ) t i : NNReal) : ℝ) ≤ theta M * (nativeHeatGenVariance ns : ℝ) := by
  obtain ⟨hτ0, hτ1⟩ := theta_pos_le_one M hg
  have hv := nativeHeatStep_auxVariance_le ns M h hM m hstate t ht i
  have heold : (heatVHEATDriftEGen ns) M ≤ theta M * ((nativeHeatOldRowGen ns).e : ℝ) :=
    (nativeHeatStep_driftTheta ns M hgen hg).1.2
  have hθ : (0 : ℝ) ≤ 1 + (nativeHeatTheta : ℝ) := by norm_num [nativeHeatTheta]
  refine hv.trans ?_
  rw [nativeHeatGenVariance_eq]
  have h1 := (Rat.cast_le (K := ℝ)).2
    (nativeUp_ge ((1 + nativeHeatTheta) * (nativeHeatOldRowGen ns).e * (ns : ℚ)))
  push_cast at h1
  have hmul := mul_le_mul_of_nonneg_left h1 hτ0.le
  have : (ns : ℝ) * (heatVHEATDriftEGen ns) M ≤
      (ns : ℝ) * (theta M * ((nativeHeatOldRowGen ns).e : ℝ)) :=
    mul_le_mul_of_nonneg_left heold (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left this hθ, hmul]

theorem nativeHeatStep_xCap_theta (ns : ℕ) [NeZero ns] (hnum : NativeHeatStepPassNum ns)
    (hfr : NativeHeatStepFrameNum ns) (hgen : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ j < m + 1, nativeInductionState M h j)
    (hstate : nativeInductionState M h (m + 1))
    (hchild : NativeHeatStepChildAllTimeCap M m ns (theta M * (nativeHeatY0Gen ns : ℝ))) :
    ∀ t ∈ Ioo (0 : ℝ) 1,
      ((heatVHEATDriftRefinedPhysicalXExtendedGen ns) M m t
        (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen M m ns
          (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
          (nativeHeatTheta : ℝ) t)).toReal ≤ theta M * ((nativeHeatFramesGen ns).x : ℝ) := by
  classical
  intro t ht
  obtain ⟨hτ0, hτ1⟩ := theta_pos_le_one M hg
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
  have hxnonneg : (0 : ℝ) ≤ theta M * ((nativeHeatFramesGen ns).x : ℝ) :=
    mul_nonneg hτ0.le (by exact_mod_cast hnum.x_pos.le)
  have hXe : (heatVHEATDriftRefinedPhysicalXExtendedGen ns) M m t g =
      (heatVHEATDriftSourceXExtendedGen ns) Finset.univ M (m + 1) t
        (heatVHEATDriftRefinedShift m) g :=
    heatVHEATDrift_refined_physical_norm_eq_Gen ns M m t g
  have hle : (heatVHEATDriftRefinedPhysicalXExtendedGen ns) M m t g ≤
      ENNReal.ofReal (theta M * ((nativeHeatFramesGen ns).x : ℝ)) := by
    rw [hXe]
    unfold heatVHEATDriftSourceXExtendedGen heatVHEATDriftXExtended
    apply Finset.sup_le
    intro i _
    have hgmeas := nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen_measurable M m ns Ffam
      (nativeHeatTheta : ℝ) t i
    have hlaw := nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen_law M m ns Ffam
      (nativeHeatTheta : ℝ) t i
    have hT := nativeHeatStep_translatedTrace_L20_le ns M h hM hg m
      hpast t ht.2.le
      (theta M * (nativeHeatY0Gen ns : ℝ)) (mul_nonneg hτ0.le hy0) (hchild t ht)
      (heatVHEATDriftRefinedShift m i) (g i)
      hgmeas _ hlaw
    refine hT.trans (ENNReal.ofReal_le_ofReal ?_)
    have hvar := nativeHeatStep_auxVariance_le_genVar_theta ns hgen M h hM hg m hstate t
      ⟨ht.1.le, ht.2.le⟩ i
    have t1 : Real.sqrt ((nativeHeatY0Gen ns : ℚ) : ℝ) ≤ (nativeRootUp (nativeHeatY0Gen ns) : ℝ) :=
      nativeHeatStep_sqrt_le_rootUp _ hfr.y0_root
    have hv0 : (0 : ℝ) ≤ ((nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns Ffam
        (nativeHeatTheta : ℝ) t i : NNReal) : ℝ) := NNReal.coe_nonneg _
    have t2 : Real.sqrt (2 * ((3683 / 2500 : ℝ) + 3 / 10 ^ 46) *
        (((nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns Ffam
          (nativeHeatTheta : ℝ) t i : NNReal) : ℝ) *
          ((nativeHeatParametersData.gm.getD 20 0 : ℚ) : ℝ))) ≤
        Real.sqrt (theta M) * (nativeRootUp (2 * nativeHeatB * nativeHeatParametersData.gm.getD 20 0 *
          nativeHeatGenVariance ns) : ℝ) := by
      have hs := nativeHeatStep_sqrt_le_rootUp _ hfr.xp_root
      have h3 : Real.sqrt (2 * ((3683 / 2500 : ℝ) + 3 / 10 ^ 46) *
        (((nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns Ffam
          (nativeHeatTheta : ℝ) t i : NNReal) : ℝ) *
          ((nativeHeatParametersData.gm.getD 20 0 : ℚ) : ℝ))) ≤
          Real.sqrt (theta M * (2 * nativeHeatB * nativeHeatParametersData.gm.getD 20 0 *
          nativeHeatGenVariance ns : ℝ)) := by
        apply Real.sqrt_le_sqrt
        push_cast
        have e1 := mul_le_mul_of_nonneg_right hB (mul_nonneg hv0 hgm0)
        have e2 := mul_le_mul_of_nonneg_right hvar hgm0
        have e3 := mul_le_mul_of_nonneg_left e2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hBn)
        nlinarith [e1, e3]
      rw [Real.sqrt_mul hτ0.le] at h3
      refine h3.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
      push_cast at hs ⊢
      exact hs
    have hs0 : 0 ≤ Real.sqrt (theta M * ((nativeHeatY0Gen ns : ℚ) : ℝ)) +
        Real.sqrt (2 * ((3683 / 2500 : ℝ) + 3 / 10 ^ 46) *
        (((nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns Ffam
          (nativeHeatTheta : ℝ) t i : NNReal) : ℝ) *
          ((nativeHeatParametersData.gm.getD 20 0 : ℚ) : ℝ))) :=
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have t1' : Real.sqrt (theta M * ((nativeHeatY0Gen ns : ℚ) : ℝ)) ≤
        Real.sqrt (theta M) * (nativeRootUp (nativeHeatY0Gen ns) : ℝ) := by
      rw [Real.sqrt_mul hτ0.le]
      exact mul_le_mul_of_nonneg_left t1 (Real.sqrt_nonneg _)
    have hsq := pow_le_pow_left₀ hs0 (add_le_add t1' t2) 2
    refine hsq.trans ?_
    have hsqθ : Real.sqrt (theta M) ^ 2 = theta M := Real.sq_sqrt hτ0.le
    calc (Real.sqrt (theta M) * (nativeRootUp (nativeHeatY0Gen ns) : ℝ) +
          Real.sqrt (theta M) * (nativeRootUp (2 * nativeHeatB * nativeHeatParametersData.gm.getD 20 0 *
          nativeHeatGenVariance ns) : ℝ)) ^ 2
        = Real.sqrt (theta M) ^ 2 * ((nativeRootUp (nativeHeatY0Gen ns) : ℝ) +
          (nativeRootUp (2 * nativeHeatB * nativeHeatParametersData.gm.getD 20 0 *
          nativeHeatGenVariance ns) : ℝ)) ^ 2 := by ring
      _ = theta M * ((nativeRootUp (nativeHeatY0Gen ns) : ℝ) +
          (nativeRootUp (2 * nativeHeatB * nativeHeatParametersData.gm.getD 20 0 *
          nativeHeatGenVariance ns) : ℝ)) ^ 2 := by rw [hsqθ]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hτ0.le
        push_cast at hnu ⊢
        exact hnu
  exact ENNReal.toReal_le_of_le_ofReal hxnonneg hle

end ASDExplicitGamma.Native
