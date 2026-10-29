module

public import ASDExplicitGamma.Native.HeatStepErrorForcing
public import ASDExplicitGamma.Native.HeatVHEATSourceNodeFinalGen
public import ASDExplicitGamma.Native.HeatInitialRefinedRangeFinalGen
public import ASDExplicitGamma.Native.HeatFinitePasses
public import ASDExplicitGamma.Native.HeatMomentUniformBound
public import ASDExplicitGamma.Native.StepEndpointLp

/-! The moment curves of the `ns`-shell refined carrier in the form consumed by the finite
pass lemmas of `HeatFinitePasses`: regularity on `[0,1]`, the exact derivative on `(0,1)`,
integrability of the backward pairing derivative, nonnegativity and the time-zero start row. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Set Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Numerics.Native
open scoped ENNReal Topology

local instance nativeHeatStepIndexNeZero : NeZero (3 ^ 10 * 3 ^ 10) := ⟨by norm_num⟩

local instance nativeHeatStepChildFinite (m : ℤ) (i : nativeHeatQ3RefinedCarrierIndex) :
    IsFiniteMeasure (volumeMeasureOn (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  ((isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isBoundedDomain).isFiniteMeasure_restrict_volume

section Curves

variable (ns : ℕ) [NeZero ns] (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)

/-- The degree-`k` source moment of the chosen `ns`-shell carrier at the configured heat
parameter. -/
noncomputable abbrev nativeHeatStepMoment (k : ℕ) (t : ℝ) : ℝ :=
  nativeHeatQ3RefinedCarrierSourceMomentGen M m ns
    (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns) k
    (nativeHeatTheta : ℝ) t

/-- Its exact cancelled generator. -/
noncomputable abbrev nativeHeatStepGenerator (k : ℕ) (t : ℝ) : ℝ :=
  nativeHeatQ3RefinedCarrierSourceMomentGeneratorGen M m ns
    (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns) k
    (nativeHeatTheta : ℝ) t

/-- The curve family of the pass lemmas: degree zero is the constant `1`. -/
noncomputable def nativeHeatStepCurve (j : ℕ) (t : ℝ) : ℝ :=
  if j = 0 then 1 else nativeHeatStepMoment ns M h hM m j t

noncomputable def nativeHeatStepCurveDeriv (j : ℕ) (t : ℝ) : ℝ :=
  if j = 0 then 0 else nativeHeatStepGenerator ns M h hM m j t

/-- Continuity, exact generator and derivative of every positive degree moment. -/
theorem nativeHeatStep_regular (k : ℕ) (hk : 1 ≤ k) :
    ContinuousOn (nativeHeatStepMoment ns M h hM m k) (Icc (0 : ℝ) 1) ∧
    ContinuousOn (nativeHeatStepGenerator ns M h hM m k) (Icc (0 : ℝ) 1) ∧
    ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (nativeHeatStepMoment ns M h hM m k)
        (nativeHeatStepGenerator ns M h hM m k t) t := by
  classical
  have hθ : 0 < (nativeHeatTheta : ℝ) := by norm_num [nativeHeatTheta]
  have hk0 : k ≠ 0 := by omega
  let F := nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns
  have hbands : ∀ d : Fin ns, m + 1 < nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns d :=
    fun d => nativeHeatQ3RefinedCarrierPhysicalShellsGen_gt m d
  have hreg := nativeHeat_childBandMoment_regular_of_realization
    (fun i : nativeHeatQ3RefinedCarrierIndex =>
      cubeSet (nativeHeatQ3RefinedCarrierChild m i))
    (fun i => measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i))
    (fun i => volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i))
    M.nu (Annealed.sigmaBar M (m + 1) : ℝ) M.nu_pos
    (Annealed.sigmaBar_characterization M (m + 1)).1
    (nativeHeatQ3RefinedCarrierDomain m) M (m + 1)
    (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns) hbands
    (nativeHeatQ3RefinedCarrierOldMap m)
    (nativeHeatQ3RefinedCarrierSourceCenterMapGen m)
    (nativeHeatQ3RefinedCarrierFreshShellSeriesSummableGen F)
    (nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen F)
    (nativeHeatQ3RefinedCarrierFreshShellSeriesLawGen F) hθ k
  have hgen : nativeHeatStepGenerator ns M h hM m k = fun t =>
      bandModelBackwardAverage (nativeHeatQ3RefinedCarrierDomain m) M (m + 1)
        (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns) (nativeHeatQ3RefinedCarrierOldMap m)
        (nativeHeatQ3RefinedCarrierFreshShellSeriesSummableGen F)
        (((childConstantMap fun i => closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))).comp
          (nativeHeatQ3RefinedCarrierSourceCenterMapGen m)).comp
          (nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen F))
        (cancelledGenerator
          (fun j => (nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen F)
            (nativeHeatQ3RefinedCarrierFreshShellSeriesDirectionsGen F j))
          (nativeHeatQ3RefinedCarrierOldMap m) (nativeHeatQ3RefinedCarrierSourceCenterMapGen m)
          (childConstantMap fun i => closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)))
          (childPower (fun i => cubeSet (nativeHeatQ3RefinedCarrierChild m i))
            (fun i => measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i))
            (fun i => volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i))
            M.nu (Annealed.sigmaBar M (m + 1) : ℝ) M.nu_pos
            (Annealed.sigmaBar_characterization M (m + 1)).1 k)
          (nativeHeatTheta : ℝ)) (nativeHeatTheta : ℝ) t := by
    funext t
    simp [nativeHeatStepGenerator, nativeHeatQ3RefinedCarrierSourceMomentGeneratorGen,
      nativeHeatChildBandMomentGenerator, F, hk0]
    try rfl
  refine ⟨?_, ?_, ?_⟩
  · exact hreg.1
  · rw [hgen]; exact hreg.2.1
  · intro t ht
    rw [hgen]
    exact hreg.2.2 t ht

/-- The degree-zero moment is identically one. -/
theorem nativeHeatStep_moment_zero (t : ℝ) :
    nativeHeatStepMoment ns M h hM m 0 t = 1 := by
  simp [nativeHeatStepMoment, nativeHeatQ3RefinedCarrierSourceMomentGen,
    nativeHeatChildBandMoment, bandModelBackwardAverage, bandModelAverage,
    backwardTest, gaussianSeriesHeatAverage, childPower, childMeanTrace]

end Curves

end ASDExplicitGamma.Native

end
