module

public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceTransport
public import ASDExplicitGamma.Native.HeatVHEATSourceCarrierGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedShellLawGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceClocksGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceProfilesGen

/-! The `ns`-shell refined source transport rows. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open Algsuperdiff.Section3 ASDExplicitGamma.Model
open ASDExplicitGamma.Inverse ASDExplicitGamma.Response
open ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open ProbabilityTheory

variable (ns : ℕ) [NeZero ns]

local instance nativeHeatRefinedSourceOriginCompactGenRefinedSourceTransport (n : ℤ) :
    CompactSpace (closure (cubeSet (originCube 2 n))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure

/-- The selected refined-shell factor, restricted to one actual child. -/
noncomputable def nativeHeatQ3RefinedCarrierChildShellMapGen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns) (i : nativeHeatQ3RefinedCarrierIndex) (d : Fin ns) :
    GaussianFactorL2 ℕ →L[ℝ]
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ) :=
  ((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun j : nativeHeatQ3RefinedCarrierIndex =>
        C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)) i).comp
    (nativeHeatQ3RefinedCarrierOldMap m)).comp
      ((Ffam).factor d)

theorem nativeHeatQ3RefinedCarrierChildDriftAndBracketRows_Gen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns) (i : nativeHeatQ3RefinedCarrierIndex) (d : Fin ns)
    (σ : ℝ) (hσ : 0 < σ)
    (x : C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) :
    let Q := nativeHeatQ3RefinedCarrierChild m i
    let s := d.val + 2
    let P := (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun j : nativeHeatQ3RefinedCarrierIndex =>
        C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)) i).comp
      (nativeHeatQ3RefinedCarrierOldMap m)
    let A := nativeHeat_translateTriadicFieldToOrigin Q
    ((Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction
          (closure (cubeSet (originCube 2 Q.scale)))
          (ω.1 (Q.scale + (s : ℤ)))) =
      standardGaussianInfinitePi.map
        (gaussianSeriesLimitE (Ffam.squareSummable d)
          (A.comp (P.comp (Ffam.factor d))))) ∧
      nativeHeatSourceDriftAndBracketConclusion M h Q.scale s σ
        (A.comp (P.comp (Ffam.factor d))) (Ffam.direction d) (A x) := by
  classical
  let Q := nativeHeatQ3RefinedCarrierChild m i
  let s := d.val + 2
  let P : C(nativeHeatQ3RefinedCarrierDomain m, ℝ) →L[ℝ]
      C(closure (cubeSet Q), ℝ) :=
    (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun j : nativeHeatQ3RefinedCarrierIndex =>
        C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)) i).comp
      (nativeHeatQ3RefinedCarrierOldMap m)
  let A := nativeHeat_translateTriadicFieldToOrigin Q
  have hscale : Q.scale = m := by
    simpa [Q] using nativeHeatQ3RefinedCarrierChild_scale m i
  have hlaw₀ :
      (Cutoff.cutoffSampleLaw M).toMeasure.map
        (fun ω : Cutoff.CutoffSample 2 =>
          shellFieldScalarRestriction
            (closure (cubeSet (originCube 2 Q.scale)))
            (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns d))) =
      standardGaussianInfinitePi.map
        (gaussianSeriesLimitE (Ffam.squareSummable d)
          (A.comp (P.comp (Ffam.factor d)))) := by
    simpa [P, A, Q] using
      (nativeHeatQ3RefinedCarrierChildFreshShellOriginLawGen M m ns Ffam i d)
  have hlabel : nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns d =
      Q.scale + (s : ℤ) := by
    rw [nativeHeatQ3RefinedCarrierPhysicalShellsGen_offset, hscale]
  have hlaw :
      (Cutoff.cutoffSampleLaw M).toMeasure.map
        (fun ω : Cutoff.CutoffSample 2 =>
          shellFieldScalarRestriction
            (closure (cubeSet (originCube 2 Q.scale)))
            (ω.1 (Q.scale + (s : ℤ)))) =
      standardGaussianInfinitePi.map
        (gaussianSeriesLimitE (Ffam.squareSummable d)
          (A.comp (P.comp (Ffam.factor d)))) := by
    simpa only [hlabel] using hlaw₀
  refine ⟨hlaw, ?_⟩
  have hrows := nativeHeat_sourceFreshShellDriftAndBracket_le_profile
    M h hM Q.scale s (by dsimp [s]; omega) σ hσ
    (A.comp (P.comp (Ffam.factor d))) (Ffam.direction d) (Ffam.squareSummable d)
    hlaw (A x)
  simpa [nativeHeatSourceDriftAndBracketConclusion, Q, s, P, A] using hrows

/-- Covariance trace on one refined child splits over the nine actual shell
factors, with no independence assumption between children. -/
theorem nativeHeatQ3RefinedCarrierChildCovariance_eq_sum_shellRows_Gen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns) (i : nativeHeatQ3RefinedCarrierIndex)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (x : C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) :
    let Q := nativeHeatQ3RefinedCarrierChild m i
    let E := fun j : nativeHeatQ3RefinedCarrierIndex =>
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)
    let π := ContinuousLinearMap.proj (R := ℝ) (φ := E) i
    let P := π.comp (nativeHeatQ3RefinedCarrierOldMap m)
    let H := nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen Ffam
    let w := nativeHeatQ3RefinedCarrierFreshShellSeriesDirectionsGen Ffam
    modelCovarianceTrace
        (childTraceObservable (measurableSet_cubeSet Q)
          (volume_cubeSet_toReal_pos Q) ν σ hν hσ)
        (fun j => P (H (w j))) x =
      ∑ d : Fin ns, modelCovarianceTrace
        (childTraceObservable (measurableSet_cubeSet Q)
          (volume_cubeSet_toReal_pos Q) ν σ hν hσ)
        (fun j => P (Ffam.factor d (Ffam.direction d j))) x := by
  classical
  let Q := nativeHeatQ3RefinedCarrierChild m i
  let E : nativeHeatQ3RefinedCarrierIndex → Type := fun j =>
    C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)
  let π : (∀ j, E j) →L[ℝ] E i :=
    ContinuousLinearMap.proj (R := ℝ) (φ := E) i
  let P : C(nativeHeatQ3RefinedCarrierDomain m, ℝ) →L[ℝ] E i :=
    π.comp (nativeHeatQ3RefinedCarrierOldMap m)
  let H := nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen Ffam
  let w := nativeHeatQ3RefinedCarrierFreshShellSeriesDirectionsGen Ffam
  let φ : E i → ℝ := childTraceObservable (measurableSet_cubeSet Q)
    (volume_cubeSet_toReal_pos Q) ν σ hν hσ
  have hφ : HasPolynomiallyBoundedC2Derivatives φ :=
    childTraceObservable_polynomial (measurableSet_cubeSet Q)
      (volume_cubeSet_toReal_pos Q) ν σ hν hσ
  have hφ' : ContDiff ℝ 2 (fun y : E i => φ y) := by
    simpa [E, φ, Q] using hφ.1
  have hW : Summable (fun j => ‖w j‖ ^ 2) :=
    nativeHeatQ3RefinedCarrierFreshShellSeriesSummableGen Ffam
  have hPall : Summable (fun j => ‖P (H (w j))‖ ^ 2) :=
    summable_sq_bounded_image _ hW (P.comp H)
  have hPd (d : Fin ns) : Summable (fun j =>
      ‖P (Ffam.factor d (Ffam.direction d j))‖ ^ 2) :=
    summable_sq_bounded_image _ (Ffam.squareSummable d) (P.comp (Ffam.factor d))
  have hcovTotal := modelCovarianceTrace_eq_bilinearTraceMap
    (fun j => P (H (w j))) hPall hφ' x
  have hcovD (d : Fin ns) := modelCovarianceTrace_eq_bilinearTraceMap
    (fun j => P (Ffam.factor d (Ffam.direction d j))) (hPd d) hφ' x
  have hcomp : P.comp (finiteFactor (fun _ : Fin ns => GaussianFactorL2 ℕ)
      Ffam.factor) = finiteFactor (fun _ : Fin ns => GaussianFactorL2 ℕ)
        (fun d => P.comp (Ffam.factor d)) := by
    ext z
    simp [finiteFactor]
  have hmap : (fun j => P (H (w j))) =
      (fun j => finiteFactor (fun _ : Fin ns => GaussianFactorL2 ℕ)
        (fun d => P.comp (Ffam.factor d))
        (finiteDirections (fun _ : Fin ns => GaussianFactorL2 ℕ)
          Ffam.direction j)) := by
    funext j
    have hh := congrArg (fun T => T
      (finiteDirections (fun _ : Fin ns => GaussianFactorL2 ℕ)
        Ffam.direction j)) hcomp
    simpa [H, w, nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen,
      nativeHeatQ3RefinedCarrierFreshShellSeriesDirectionsGen,
      ContinuousLinearMap.comp_apply] using hh
  have hmapPoint j := congrFun hmap j
  calc
    modelCovarianceTrace φ (fun j => P (H (w j))) x =
      bilinearTraceMap (fun j => P (H (w j))) hPall
        (fderiv ℝ (fderiv ℝ φ) x) := hcovTotal
    _ = ∑ d : Fin ns, bilinearTraceMap
        (fun j => P (Ffam.factor d (Ffam.direction d j))) (hPd d)
        (fderiv ℝ (fderiv ℝ φ) x) := by
          simp only [bilinearTraceMap_apply]
          change (∑' j, (fderiv ℝ (fderiv ℝ φ) x) (P (H (w j)))
              (P (H (w j)))) = _
          simp_rw [hmapPoint]
          simpa [H, w, nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen,
            nativeHeatQ3RefinedCarrierFreshShellSeriesDirectionsGen] using
            (finiteFactor_bilinearTrace_eq_sum Ffam.direction
              Ffam.squareSummable (fun d => P.comp (Ffam.factor d))
              (fderiv ℝ (fderiv ℝ φ) x))
    _ = ∑ d : Fin ns, modelCovarianceTrace φ
        (fun j => P (Ffam.factor d (Ffam.direction d j))) x := by
          apply Finset.sum_congr rfl
          intro d hd
          exact (hcovD d).symm

theorem nativeHeatQ3RefinedCarrierChildSignedCovariance_le_sourceProfiles_Gen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns) (i : nativeHeatQ3RefinedCarrierIndex)
    (σ : ℝ) (hσ : 0 < σ)
    (x : C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) :
    (1 / 2 : ℝ) * modelCovarianceTrace
      (childTraceObservable
        (measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i))
        (volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i))
        M.nu σ M.nu_pos hσ)
      (fun j => (nativeHeatQ3RefinedCarrierOldMap m
        (nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen Ffam
          (nativeHeatQ3RefinedCarrierFreshShellSeriesDirectionsGen Ffam j))) i) x ≤
      ∑ d : Fin ns,
        (nativeHeatQ3RefinedCarrierChildSignedDriftProfileGen ns) M h m i d σ x := by
  classical
  let Q := nativeHeatQ3RefinedCarrierChild m i
  let E : nativeHeatQ3RefinedCarrierIndex → Type := fun j =>
    C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)
  let π := ContinuousLinearMap.proj (R := ℝ) (φ := E) i
  let P := π.comp (nativeHeatQ3RefinedCarrierOldMap m)
  let H := nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen Ffam
  let w := nativeHeatQ3RefinedCarrierFreshShellSeriesDirectionsGen Ffam
  let φ : E i → ℝ := childTraceObservable (measurableSet_cubeSet Q)
    (volume_cubeSet_toReal_pos Q) M.nu σ M.nu_pos hσ
  have hsplit := (nativeHeatQ3RefinedCarrierChildCovariance_eq_sum_shellRows_Gen ns)
    M h hM m Ffam i M.nu σ M.nu_pos hσ x
  have hsplit' : modelCovarianceTrace φ (fun j => P (H (w j))) x =
      ∑ d : Fin ns, modelCovarianceTrace φ
        (fun j => P (Ffam.factor d (Ffam.direction d j))) x := by
    simpa [Q, E, π, P, H, w, φ] using hsplit
  have hC (d : Fin ns) :
      (1 / 2 : ℝ) * modelCovarianceTrace
        (modelTraceObservable Q.scale M.nu σ)
        (fun j => nativeHeat_translateTriadicFieldToOrigin Q
          ((nativeHeatQ3RefinedCarrierChildShellMapGen ns) M h hM m Ffam i d
            ((Ffam).direction d j)))
        (nativeHeat_translateTriadicFieldToOrigin Q x) ≤
        (nativeHeatQ3RefinedCarrierChildSignedDriftProfileGen ns) M h m i d σ x := by
    have hrows := (nativeHeatQ3RefinedCarrierChildDriftAndBracketRows_Gen ns)
      M h hM m Ffam i d σ hσ x
    have hsource := hrows.2
    unfold nativeHeatSourceDriftAndBracketConclusion at hsource
    simpa [nativeHeatQ3RefinedCarrierChildSignedDriftProfileGen,
      nativeHeatQ3RefinedCarrierChildShellMapGen, Function.comp_apply] using hsource.1
  have htransport (d : Fin ns) :
      modelCovarianceTrace φ (fun j => P (Ffam.factor d (Ffam.direction d j))) x =
        modelCovarianceTrace (modelTraceObservable Q.scale M.nu σ)
          (fun j => nativeHeat_translateTriadicFieldToOrigin Q
            (P (Ffam.factor d (Ffam.direction d j))))
          (nativeHeat_translateTriadicFieldToOrigin Q x) := by
    have hfun : childTraceObservable
        (measurableSet_cubeSet Q) (volume_cubeSet_toReal_pos Q)
        M.nu σ M.nu_pos hσ =
      modelTraceObservable Q.scale M.nu σ ∘
        nativeHeat_translateTriadicFieldToOrigin Q := by
      funext y
      exact nativeHeatQ3RefinedCarrierChildTraceObservable_toOrigin
        Q M.nu σ M.nu_pos hσ y
    have hdir : Summable (fun j => ‖P (Ffam.factor d (Ffam.direction d j))‖ ^ 2) :=
      summable_sq_bounded_image _ (Ffam.squareSummable d) (P.comp (Ffam.factor d))
    change modelCovarianceTrace
        (childTraceObservable
          (measurableSet_cubeSet Q) (volume_cubeSet_toReal_pos Q)
          M.nu σ M.nu_pos hσ)
        (fun j => P (Ffam.factor d (Ffam.direction d j))) x = _
    rw [hfun]
    exact nativeHeat_modelCovarianceTrace_comp_continuousLinearMap
      (nativeHeat_translateTriadicFieldToOrigin Q)
      (fun j => P (Ffam.factor d (Ffam.direction d j))) hdir
      (modelTraceObservable Q.scale M.nu σ)
      (modelTraceObservable_hasPolynomiallyBoundedC2Derivatives Q.scale
        M.nu σ M.nu_pos hσ).1 x
  change (1 / 2 : ℝ) * modelCovarianceTrace φ
      (fun j => P (H (w j))) x ≤ _
  rw [hsplit', Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  rw [htransport d]
  exact hC d

/-- After subtracting the exact diagonal center contribution, the refined
child covariance is bounded by the signed off-diagonal profiles alone. -/
theorem nativeHeatQ3RefinedCarrierChildCenteredCovariance_le_offDiagonalProfiles_Gen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns) (i : nativeHeatQ3RefinedCarrierIndex)
    (σ : ℝ) (hσ : 0 < σ)
    (x : C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) :
    (1 / 2 : ℝ) * modelCovarianceTrace
      (childTraceObservable
        (measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i))
        (volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i))
        M.nu σ M.nu_pos hσ)
      (fun j => (nativeHeatQ3RefinedCarrierOldMap m
        (nativeHeatQ3RefinedCarrierFreshShellSeriesFactorGen Ffam
          (nativeHeatQ3RefinedCarrierFreshShellSeriesDirectionsGen Ffam j))) i) x -
      ∑ d : Fin ns,
        (nativeHeatQ3RefinedCarrierChildCenterDriftProfileGen ns) M h m i d σ x ≤
    ∑ d : Fin ns,
      (nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfileGen ns) M h m i d σ x := by
  have hfull := (nativeHeatQ3RefinedCarrierChildSignedCovariance_le_sourceProfiles_Gen ns)
    M h hM m Ffam i σ hσ x
  have hsum :
      (∑ d : Fin ns,
        (nativeHeatQ3RefinedCarrierChildSignedDriftProfileGen ns) M h m i d σ x) -
        ∑ d : Fin ns,
          (nativeHeatQ3RefinedCarrierChildCenterDriftProfileGen ns) M h m i d σ x =
      ∑ d : Fin ns,
        (nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfileGen ns) M h m i d σ x := by
    rw [← Finset.sum_sub_distrib]
    rfl
  calc
    _ ≤ (∑ d : Fin ns,
        (nativeHeatQ3RefinedCarrierChildSignedDriftProfileGen ns) M h m i d σ x) -
        ∑ d : Fin ns,
          (nativeHeatQ3RefinedCarrierChildCenterDriftProfileGen ns) M h m i d σ x :=
      sub_le_sub_right hfull _
    _ = _ := hsum

end ASDExplicitGamma.Native
