module

public import ASDExplicitGamma.Native.HeatStepRows

/-! The pass row on `[0,1]`: from VHEAT at the configured caps to the inequality
`mp_j ≤ c j m_j + 4 c j m_{j-1} + forcing(y)` consumed by `heat_finite_passes_uniform_cap`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Set Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Numerics.Native ProbabilityTheory
open scoped ENNReal Topology

section Rows2

variable (ns : ℕ) [NeZero ns] (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)

theorem nativeHeatStep_row (hns9 : 9 ≤ ns) (hns160 : ns ≤ 160)
    (hnum : NativeHeatStepPassNum ns) (hgen : NativeHeatGenNum ns)
    (hg : M.gamma ≤ gammaZero)
    (hpast : ∀ l < m + 1, nativeInductionState M h l)
    (hstate : nativeInductionState M h (m + 1))
    (hX : ∀ t ∈ Ioo (0 : ℝ) 1,
      ((heatVHEATDriftRefinedPhysicalXExtendedGen ns) M m t
        (nativeHeatStepAux ns M h hM m t)).toReal ≤ ((nativeHeatFramesGen ns).x : ℝ))
    (hF : ∀ t ∈ Ioo (0 : ℝ) 1,
      heatRefinedRawEnvelope ns
        (heatVHEATDriftAuxVariance Finset.univ
          (nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns
            (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
            (nativeHeatTheta : ℝ) t)) ≤ ((nativeHeatFramesGen ns).raw : ℝ))
    (y : ℚ) (hy : 0 ≤ y)
    (hcapY : ∀ t ∈ Ioo (0 : ℝ) 1, nativeHeatStepMoment ns M h hM m 20 t ≤ (y : ℝ) ^ 20) :
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ 20,
      nativeHeatStepCurveDeriv ns M h hM m j s ≤
        (nativeHeatExpArgGen ns : ℝ) * (j : ℝ) * nativeHeatStepCurve ns M h hM m j s +
        4 * (nativeHeatExpArgGen ns : ℝ) * (j : ℝ) *
          nativeHeatStepCurve ns M h hM m (j - 1) s +
        (if j = 0 then 0 else
          (nativeHeatForcingAt (nativeHeatOldRowGen ns) (nativeHeatFramesGen ns)
            (nativeHeatFixedGen ns) y j : ℝ)) := by
  classical
  have hns1331 : ns ≤ 1331 := by omega
  have hy0 : (0 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hcaps : ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
      ((heatVHEATDriftRefinedPhysicalXExtendedGen ns) M m t
        (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen M m ns
          (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
          (nativeHeatTheta : ℝ) t)).toReal ≤ ((nativeHeatFramesGen ns).x : ℝ) ∧
      (nativeHeatQ3RefinedCarrierSourceAverageNormGen ns) M h hM m
        (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
        (nativeHeatTheta : ℝ) t ≤ (y : ℝ) ∧
      heatRefinedRawEnvelope ns
        (heatVHEATDriftAuxVariance Finset.univ
          (nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns
            (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
            (nativeHeatTheta : ℝ) t)) ≤ ((nativeHeatFramesGen ns).raw : ℝ) := by
    intro t ht
    exact ⟨hX t ht, nativeHeatStep_avgNorm_le_of_moment_le ns M h hM m hns1331 hg hpast t ht
      (y : ℝ) hy0 (hcapY t ht), hF t ht⟩
  have hv := nativeHeatVHEATBackwardInequality_source_gen ns hns9 (by omega) M h hM hg m
    hpast hstate ((nativeHeatFramesGen ns).x : ℝ) (y : ℝ) ((nativeHeatFramesGen ns).raw : ℝ)
    hcaps
  obtain ⟨⟨he0, heold⟩, hdrift⟩ := nativeHeatStep_drift_le ns M hgen hg
  intro s hs j hj
  by_cases hj0 : j = 0
  · subst j
    have e1 : nativeHeatStepCurveDeriv ns M h hM m 0 s = 0 := by
      simp [nativeHeatStepCurveDeriv]
    simp [e1]
  · have hj1 : 1 ≤ j := by omega
    rw [nativeHeatStep_curveDeriv_eq_generator ns M h hM m j hj0, if_neg hj0]
    -- the open-interval inequality
    have hopen : ∀ t ∈ Ioo (0 : ℝ) 1,
        nativeHeatStepGenerator ns M h hM m j t ≤
          (nativeHeatExpArgGen ns : ℝ) * (j : ℝ) * nativeHeatStepCurve ns M h hM m j t +
          4 * (nativeHeatExpArgGen ns : ℝ) * (j : ℝ) *
            nativeHeatStepCurve ns M h hM m (j - 1) t +
          (nativeHeatForcingAt (nativeHeatOldRowGen ns) (nativeHeatFramesGen ns)
            (nativeHeatFixedGen ns) y j : ℝ) := by
      intro t ht
      obtain ⟨hder, hineq⟩ := hv j hj1 hj t ht
      rw [hder.deriv] at hineq
      have hE := nativeHeatStep_vheatError_le_forcingAt ns hnum j hj1 hj
        ((heatVHEATDriftEGen ns) M) he0 heold y hy
      have hmj := nativeHeatStep_moment_nonneg ns M h hM m hns1331 hg hpast t ht j hj1 hj
      have hcurve_nonneg : 0 ≤ nativeHeatStepCurve ns M h hM m (j - 1) t := by
        by_cases hjm : j - 1 = 0
        · rw [hjm]; simp [nativeHeatStepCurve]
        · rw [nativeHeatStep_curve_eq_moment ns M h hM m (j - 1) hjm]
          exact nativeHeatStep_moment_nonneg ns M h hM m hns1331 hg hpast t ht (j - 1)
            (by omega) (by omega)
      have hlow : nativeHeatStepMoment ns M h hM m (j - 1) t =
          nativeHeatStepCurve ns M h hM m (j - 1) t := by
        by_cases hjm : j - 1 = 0
        · rw [hjm, nativeHeatStep_moment_zero]; simp [nativeHeatStepCurve]
        · rw [nativeHeatStep_curve_eq_moment ns M h hM m (j - 1) hjm]
      have hcur : nativeHeatStepCurve ns M h hM m j t = nativeHeatStepMoment ns M h hM m j t :=
        by rw [nativeHeatStep_curve_eq_moment ns M h hM m j hj0]
      change nativeHeatStepGenerator ns M h hM m j t ≤
        (j : ℝ) * (heatVHEATDriftEGen ns) M *
          (2 * (nativeHeatK : ℝ) * (3683 / 2500 : ℝ) +
            (nativeHeatM : ℝ) * (3683 / 2500 : ℝ) ^ 2) *
          (nativeHeatStepMoment ns M h hM m j t +
            4 * nativeHeatStepMoment ns M h hM m (j - 1) t) +
        nativeHeatVHEATErrorEk j 20 ((heatVHEATDriftEGen ns) M) (nativeHeatK : ℝ)
          (nativeHeatM : ℝ) (nativeHeatSB : ℝ) (nativeHeatTheta : ℝ) (3683 / 2500 : ℝ)
          ((nativeHeatFramesGen ns).x : ℝ) (y : ℝ) (3 / 10 ^ 46 : ℝ)
          ((nativeHeatFramesGen ns).raw : ℝ) at hineq
      rw [hlow] at hineq
      rw [hcur]
      have hjR : (0 : ℝ) ≤ (j : ℝ) := by positivity
      have hcoef : (j : ℝ) * ((heatVHEATDriftEGen ns) M *
          (2 * (nativeHeatK : ℝ) * (3683 / 2500 : ℝ) +
            (nativeHeatM : ℝ) * (3683 / 2500 : ℝ) ^ 2)) ≤
          (j : ℝ) * (nativeHeatExpArgGen ns : ℝ) := mul_le_mul_of_nonneg_left hdrift hjR
      have hstep : (j : ℝ) * ((heatVHEATDriftEGen ns) M *
            (2 * (nativeHeatK : ℝ) * (3683 / 2500 : ℝ) +
              (nativeHeatM : ℝ) * (3683 / 2500 : ℝ) ^ 2)) *
            (nativeHeatStepMoment ns M h hM m j t +
              4 * nativeHeatStepCurve ns M h hM m (j - 1) t) ≤
          (j : ℝ) * (nativeHeatExpArgGen ns : ℝ) *
            (nativeHeatStepMoment ns M h hM m j t +
              4 * nativeHeatStepCurve ns M h hM m (j - 1) t) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      have hshape : (j : ℝ) * (heatVHEATDriftEGen ns) M *
          (2 * (nativeHeatK : ℝ) * (3683 / 2500 : ℝ) +
            (nativeHeatM : ℝ) * (3683 / 2500 : ℝ) ^ 2) *
          (nativeHeatStepMoment ns M h hM m j t +
            4 * nativeHeatStepCurve ns M h hM m (j - 1) t) =
          (j : ℝ) * ((heatVHEATDriftEGen ns) M *
            (2 * (nativeHeatK : ℝ) * (3683 / 2500 : ℝ) +
              (nativeHeatM : ℝ) * (3683 / 2500 : ℝ) ^ 2)) *
            (nativeHeatStepMoment ns M h hM m j t +
              4 * nativeHeatStepCurve ns M h hM m (j - 1) t) := by ring
      rw [hshape] at hineq
      nlinarith [hineq, hstep, hE]
    have hcontL := (nativeHeatStep_regular ns M h hM m j hj1).2.1
    have hcontR : ContinuousOn (fun t =>
        (nativeHeatExpArgGen ns : ℝ) * (j : ℝ) * nativeHeatStepCurve ns M h hM m j t +
          4 * (nativeHeatExpArgGen ns : ℝ) * (j : ℝ) *
            nativeHeatStepCurve ns M h hM m (j - 1) t +
          (nativeHeatForcingAt (nativeHeatOldRowGen ns) (nativeHeatFramesGen ns)
            (nativeHeatFixedGen ns) y j : ℝ)) (Icc (0 : ℝ) 1) := by
      have h1 := nativeHeatStep_curve_contOn ns M h hM m j hj
      have h2 := nativeHeatStep_curve_contOn ns M h hM m (j - 1) (by omega)
      exact ((continuousOn_const.mul h1).add (continuousOn_const.mul h2)).add continuousOn_const
    exact nativeHeatStep_le_on_Icc_of_Ioo hcontL hcontR hopen s hs

end Rows2

end ASDExplicitGamma.Native

end
