module

public import ASDExplicitGamma.Native.HeatStepCurves2

/-! The physical average of the refined child traces at heat time `t ∈ (0,1)`: nonnegativity,
measurability, `L^20` membership, the identification of the source moments with its moments,
and the relation between the `L^20` average norm of the VHEAT caps and the 20th moment. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Set Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Numerics.Native ProbabilityTheory
open scoped ENNReal Topology

section Avg

variable (ns : ℕ) [NeZero ns] (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)

/-- The auxiliary center coordinates at heat time `t`. -/
noncomputable abbrev nativeHeatStepAux (t : ℝ) :=
  nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen M m ns
    (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
    (nativeHeatTheta : ℝ) t

/-- The physical average of the child traces at heat time `t`. -/
noncomputable abbrev nativeHeatStepAverage (t : ℝ) :=
  (heatVHEATDriftRefinedPhysicalAverageGen ns) M m t (nativeHeatStepAux ns M h hM m t)

theorem nativeHeatStep_avgFacts (hns : ns ≤ 1331) (hg : M.gamma ≤ gammaZero)
    (hpast : ∀ l < m + 1, nativeInductionState M h l) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∀ z, 0 ≤ nativeHeatStepAverage ns M h hM m t z) ∧
      Measurable (nativeHeatStepAverage ns M h hM m t) ∧
      MemLp (nativeHeatStepAverage ns M h hM m t) 20 (nativeHeatRemainderJointLaw M) ∧
      (nativeHeatQ3RefinedCarrierSourceAverageNormGen ns) M h hM m
        (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
        (nativeHeatTheta : ℝ) t =
        (eLpNorm (nativeHeatStepAverage ns M h hM m t) 20
          (nativeHeatRemainderJointLaw M)).toReal := by
  classical
  let Ffam := nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns
  let θ : ℝ := nativeHeatTheta
  let g := nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen M m ns Ffam θ t
  let A := (heatVHEATDriftRefinedPhysicalAverageGen ns) M m t g
  let μ := nativeHeatRemainderJointLaw M
  letI : IsProbabilityMeasure μ := inferInstanceAs
    (IsProbabilityMeasure ((Cutoff.cutoffSampleLaw M).toMeasure.prod standardGaussianInfinitePi))
  have hgm : ∀ i : nativeHeatQ3RefinedCarrierIndex, Measurable (g i) := by
    intro i
    exact nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen_measurable M m ns Ffam θ t i
  have hlaw : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      standardGaussianInfinitePi.map
        (fun ξ => g i ξ / (Annealed.sigmaBar M (m + 1) : ℝ)) =
        gaussianReal 0 (nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns Ffam θ t i) := by
    intro i
    exact nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen_law M m ns Ffam θ t i
  let v := nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns Ffam θ t
  have hnorms := (heatVHEATDrift_source_norms_Gen ns hns) M h hM hg (m + 1) hpast t ht.2.le
    Finset.univ (fun _ => heatVHEATDriftRefinedWeight)
    (fun _ _ => heatVHEATDrift_refined_weights.1)
    heatVHEATDrift_refined_weights.2
    (heatVHEATDriftRefinedShift m) g (fun i _ => hgm i) v
    (fun i _ => hlaw i)
  have hAvgEq : A = (heatVHEATDriftRefinedAverageGen ns) M m t g := by
    funext z
    exact ((heatVHEATDrift_refined_physical_family_eq_Gen ns) M h m t 0 g z).1
  have hA0 : ∀ z, 0 ≤ A z := by
    intro z
    rw [hAvgEq]
    unfold heatVHEATDriftRefinedAverageGen heatVHEATDriftRefinedWeight
      heatRefinedTraceAverage
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg heatVHEATDrift_refined_weights.1
      ((heat_refined_translated_trace_measurable_nonneg M (m + 1) ns t
        (heatVHEATDriftRefinedShift m i) (g i) (hgm i)).2 z)
  have hAmeas : Measurable A := by
    rw [hAvgEq]
    unfold heatVHEATDriftRefinedAverageGen heatVHEATDriftRefinedWeight
      heatRefinedTraceAverage
    exact Finset.measurable_sum Finset.univ (fun i hi =>
      ((heat_refined_translated_trace_measurable_nonneg M (m + 1) ns t
        (heatVHEATDriftRefinedShift m i) (g i) (hgm i)).1).const_mul
        ((9 ^ 10 : ℝ)⁻¹))
  have hA20 : eLpNorm A 20 μ ≤ ENNReal.ofReal
      ((heatVHEATDriftSourceXExtendedGen ns) Finset.univ M (m + 1) t
        (heatVHEATDriftRefinedShift m) g).toReal := by
    rw [hAvgEq]
    simpa [heatVHEATDriftRefinedAverageGen] using hnorms.2.2.2.1
  have hMem20 : MemLp A 20 μ := by
    rw [memLp_iff]
    exact hA20.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hA0, hAmeas, hMem20, ?_⟩
  unfold nativeHeatQ3RefinedCarrierSourceAverageNormGen
  rw [← hAvgEq]

/-- On `(0,1)` the source moments are the moments of the physical average. -/
theorem nativeHeatStep_moment_eq (hns : ns ≤ 1331) (hg : M.gamma ≤ gammaZero)
    (hpast : ∀ l < m + 1, nativeInductionState M h l) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (k : ℕ) (hk : 1 ≤ k) (hk20 : k ≤ 20) :
    nativeHeatStepMoment ns M h hM m k t =
      ∫ z, (nativeHeatStepAverage ns M h hM m t z) ^ k ∂nativeHeatRemainderJointLaw M :=
  nativeHeatQ3RefinedCarrierSourceMoment_eq_physicalAverage_integral_Gen ns hns M h hM hg m
    (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns) hpast
    (nativeHeatTheta : ℝ) t (by norm_num [nativeHeatTheta]) ht k hk hk20

theorem nativeHeatStep_moment_nonneg (hns : ns ≤ 1331) (hg : M.gamma ≤ gammaZero)
    (hpast : ∀ l < m + 1, nativeInductionState M h l) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (k : ℕ) (hk : 1 ≤ k) (hk20 : k ≤ 20) :
    0 ≤ nativeHeatStepMoment ns M h hM m k t := by
  rw [nativeHeatStep_moment_eq ns M h hM m hns hg hpast t ht k hk hk20]
  exact integral_nonneg fun z => pow_nonneg
    ((nativeHeatStep_avgFacts ns M h hM m hns hg hpast t ht).1 z) k

/-- The VHEAT average norm is the 20th root of the twentieth moment. -/
theorem nativeHeatStep_avgNorm_pow (hns : ns ≤ 1331) (hg : M.gamma ≤ gammaZero)
    (hpast : ∀ l < m + 1, nativeInductionState M h l) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    ((nativeHeatQ3RefinedCarrierSourceAverageNormGen ns) M h hM m
        (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
        (nativeHeatTheta : ℝ) t) ^ 20 = nativeHeatStepMoment ns M h hM m 20 t := by
  obtain ⟨hA0, hAm, hMem, hnorm⟩ := nativeHeatStep_avgFacts ns M h hM m hns hg hpast t ht
  rw [nativeHeatStep_moment_eq ns M h hM m hns hg hpast t ht 20 (by norm_num) le_rfl, hnorm]
  have hmem' : MemLp (nativeHeatStepAverage ns M h hM m t) (ENNReal.ofReal (20 : ℝ))
      (nativeHeatRemainderJointLaw M) := by
    simpa using hMem
  have := positiveLpNorm_eq_eLpNorm_toReal (nativeHeatRemainderJointLaw M)
    (p := (20 : ℝ)) (by norm_num) _ hA0 hmem'
  have h20 : ENNReal.ofReal (20 : ℝ) = 20 := by simp
  rw [h20] at this
  rw [← this]
  unfold positiveLpNorm
  have hint : 0 ≤ ∫ z, (nativeHeatStepAverage ns M h hM m t z) ^ (20 : ℝ)
      ∂nativeHeatRemainderJointLaw M :=
    integral_nonneg fun z => Real.rpow_nonneg (hA0 z) _
  rw [← Real.rpow_natCast, ← Real.rpow_mul hint]
  have e20 : ((20 : ℝ)⁻¹ * ((20 : ℕ) : ℝ)) = 1 := by norm_num
  rw [e20, Real.rpow_one]
  apply integral_congr_ae
  filter_upwards with z
  rw [← Real.rpow_natCast]
  norm_num

theorem nativeHeatStep_avgNorm_nonneg (hns : ns ≤ 1331) (hg : M.gamma ≤ gammaZero)
    (hpast : ∀ l < m + 1, nativeInductionState M h l) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 ≤ (nativeHeatQ3RefinedCarrierSourceAverageNormGen ns) M h hM m
        (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
        (nativeHeatTheta : ℝ) t := by
  rw [(nativeHeatStep_avgFacts ns M h hM m hns hg hpast t ht).2.2.2]
  exact ENNReal.toReal_nonneg

theorem nativeHeatStep_avgNorm_le_of_moment_le (hns : ns ≤ 1331) (hg : M.gamma ≤ gammaZero)
    (hpast : ∀ l < m + 1, nativeInductionState M h l) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (y : ℝ) (hy : 0 ≤ y) (hM20 : nativeHeatStepMoment ns M h hM m 20 t ≤ y ^ 20) :
    (nativeHeatQ3RefinedCarrierSourceAverageNormGen ns) M h hM m
        (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
        (nativeHeatTheta : ℝ) t ≤ y := by
  have hp := nativeHeatStep_avgNorm_pow ns M h hM m hns hg hpast t ht
  have h0 := nativeHeatStep_avgNorm_nonneg ns M h hM m hns hg hpast t ht
  rw [← hp] at hM20
  exact le_of_pow_le_pow_left₀ (by norm_num : (20 : ℕ) ≠ 0) hy hM20

theorem nativeHeatStep_moment_le_of_avgNorm_le (hns : ns ≤ 1331) (hg : M.gamma ≤ gammaZero)
    (hpast : ∀ l < m + 1, nativeInductionState M h l) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (y : ℝ) (hY : (nativeHeatQ3RefinedCarrierSourceAverageNormGen ns) M h hM m
        (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
        (nativeHeatTheta : ℝ) t ≤ y) :
    nativeHeatStepMoment ns M h hM m 20 t ≤ y ^ 20 := by
  rw [← nativeHeatStep_avgNorm_pow ns M h hM m hns hg hpast t ht]
  exact pow_le_pow_left₀ (nativeHeatStep_avgNorm_nonneg ns M h hM m hns hg hpast t ht) hY 20

end Avg

end ASDExplicitGamma.Native

end
