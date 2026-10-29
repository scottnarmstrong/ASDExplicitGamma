module

public import ASDExplicitGamma.Native.HeatVHEATCarrierSourceTransport
public import ASDExplicitGamma.Native.HeatVHEATRefinedShellLaw
public import ASDExplicitGamma.Native.HeatVHEATSourceTransport
public import ASDExplicitGamma.Native.HeatVHEATShellTranslation

/-! Transport the signed source drift and bracket rows to the refined
depth-ten carrier and its shifted physical shells. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open Algsuperdiff.Section3 ASDExplicitGamma.Model
open ASDExplicitGamma.Inverse ASDExplicitGamma.Response
open ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open ProbabilityTheory

local instance nativeHeatRefinedSourceChildCompact (Q : TriadicCube 2) :
    CompactSpace (closure (cubeSet Q)) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet Q).isCompact_closure

local instance nativeHeatRefinedSourceOriginCompact (n : ℤ) :
    CompactSpace (closure (cubeSet (originCube 2 n))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure

/-- The selected refined-shell factor, restricted to one actual child. -/
noncomputable def nativeHeatQ3RefinedCarrierChildShellMap
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (i : nativeHeatQ3RefinedCarrierIndex) (d : Fin 9) :
    GaussianFactorL2 ℕ →L[ℝ]
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ) :=
  ((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun j : nativeHeatQ3RefinedCarrierIndex =>
        C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)) i).comp
    (nativeHeatQ3RefinedCarrierOldMap m)).comp
      ((nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m).factor d)

/-- The refined physical child trace is the origin-cube model trace of the
same field pulled back by the triadic translation. -/
theorem nativeHeatQ3RefinedCarrierChildTraceObservable_toOrigin
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (x : C(closure (cubeSet Q), ℝ)) :
    childTraceObservable
        (measurableSet_cubeSet Q) (volume_cubeSet_toReal_pos Q) ν σ hν hσ x =
      modelTraceObservable Q.scale ν σ
        (nativeHeat_translateTriadicFieldToOrigin Q x) := by
  classical
  let Q0 := originCube 2 Q.scale
  let U := cubeSet Q
  let U0 := cubeSet Q0
  let z := triadicCubeShift Q
  let A := nativeHeat_translateTriadicFieldToOrigin Q
  let kQ := ContinuousMap.linearIsometryBoundedOfCompact (closure U) ℝ ℝ x
  let k0 := ContinuousMap.linearIsometryBoundedOfCompact (closure U0) ℝ ℝ (A x)
  have hset : U = translateSet z U0 := by
    simpa [U, U0, z, Q0] using cubeSet_eq_translateSet_originCube_of_triadicCube Q
  have hcoeff : translateCoeffField z
      (responsePlanarCoefficientField ν kQ) =ᵐ[volume.restrict U0]
        responsePlanarCoefficientField ν k0 := by
    filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_cubeSet Q0)] with y hy
    have hyQ : y + z ∈ U := by
      rw [hset, mem_translateSet_iff_sub_mem]
      simpa [sub_eq_add_neg, add_assoc] using hy
    have hQval := responseCoefficientExtension_eq kQ hyQ
    have h0val := responseCoefficientExtension_eq k0 hy
    have hfieldval : kQ ⟨y + z, subset_closure hyQ⟩ =
        k0 ⟨y, subset_closure hy⟩ := by
      simp only [kQ, k0, ContinuousMap.linearIsometryBoundedOfCompact_apply_apply]
      simp [A, nativeHeat_translateTriadicFieldToOrigin,
        ContinuousMap.compCLM_apply, z, Q0]
    change responsePlanarCoefficient ν
        (responseCoefficientExtension kQ (y + z)) =
      responsePlanarCoefficient ν (responseCoefficientExtension k0 y)
    rw [hQval, h0val, hfieldval]
  have hmatrix := coarseBlockMatrix_congr_of_ae_eq hcoeff
  rw [nativeHeat_childTrace_eq_traceDefect
    (measurableSet_cubeSet Q) (volume_cubeSet_toReal_pos Q) ν σ hν hσ x]
  change traceDefect U (responsePlanarCoefficientField ν kQ) σ = _
  let aQ := responsePlanarCoefficientField ν kQ
  let a0 := responsePlanarCoefficientField ν k0
  have htrace : traceDefect U0 (translateCoeffField z
      (responsePlanarCoefficientField ν kQ)) σ =
      traceDefect U0 (responsePlanarCoefficientField ν k0) σ := by
    unfold traceDefect
    rw [hmatrix]
  calc
    traceDefect U aQ σ = traceDefect (translateSet z U0) aQ σ := by
      congr 1
    _ = traceDefect U0 (translateCoeffField z aQ) σ :=
      Model.traceDefect_translate U0 z aQ σ
    _ = traceDefect U0 a0 σ := by
      simpa [aQ, a0] using htrace
    _ = modelTraceObservable Q.scale ν σ (A x) := rfl

/-- Every refined shell factor, restricted to a child and translated to its
origin cube, satisfies the source's signed drift and bracket row. -/
theorem nativeHeatQ3RefinedCarrierChildDriftAndBracketRows
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (i : nativeHeatQ3RefinedCarrierIndex) (d : Fin 9)
    (σ : ℝ) (hσ : 0 < σ)
    (x : C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) :
    let Q := nativeHeatQ3RefinedCarrierChild m i
    let s := d.val + 2
    let F := nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m
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
        (gaussianSeriesLimitE (F.squareSummable d)
          (A.comp (P.comp (F.factor d))))) ∧
      nativeHeatSourceDriftAndBracketConclusion M h Q.scale s σ
        (A.comp (P.comp (F.factor d))) (F.direction d) (A x) := by
  classical
  let Q := nativeHeatQ3RefinedCarrierChild m i
  let s := d.val + 2
  let F := nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m
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
            (ω.1 (nativeHeatQ3RefinedCarrierPhysicalShells m d))) =
      standardGaussianInfinitePi.map
        (gaussianSeriesLimitE (F.squareSummable d)
          (A.comp (P.comp (F.factor d)))) := by
    simpa [F, P, A, Q] using
      (nativeHeatQ3RefinedCarrierChildFreshShellOriginLaw M h hM m i d)
  have hlabel : nativeHeatQ3RefinedCarrierPhysicalShells m d =
      Q.scale + (s : ℤ) := by
    rw [nativeHeatQ3RefinedCarrierPhysicalShells_offset, hscale]
  have hlaw :
      (Cutoff.cutoffSampleLaw M).toMeasure.map
        (fun ω : Cutoff.CutoffSample 2 =>
          shellFieldScalarRestriction
            (closure (cubeSet (originCube 2 Q.scale)))
            (ω.1 (Q.scale + (s : ℤ)))) =
      standardGaussianInfinitePi.map
        (gaussianSeriesLimitE (F.squareSummable d)
          (A.comp (P.comp (F.factor d)))) := by
    simpa only [hlabel] using hlaw₀
  refine ⟨hlaw, ?_⟩
  have hrows := nativeHeat_sourceFreshShellDriftAndBracket_le_profile
    M h hM Q.scale s (by dsimp [s]; omega) σ hσ
    (A.comp (P.comp (F.factor d))) (F.direction d) (F.squareSummable d)
    hlaw (A x)
  simpa [nativeHeatSourceDriftAndBracketConclusion, Q, s, F, P, A] using hrows

/-- Covariance trace on one refined child splits over the nine actual shell
factors, with no independence assumption between children. -/
theorem nativeHeatQ3RefinedCarrierChildCovariance_eq_sum_shellRows
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (i : nativeHeatQ3RefinedCarrierIndex)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (x : C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) :
    let Q := nativeHeatQ3RefinedCarrierChild m i
    let E := fun j : nativeHeatQ3RefinedCarrierIndex =>
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)
    let π := ContinuousLinearMap.proj (R := ℝ) (φ := E) i
    let P := π.comp (nativeHeatQ3RefinedCarrierOldMap m)
    let F := nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m
    let H := nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m
    let w := nativeHeatQ3RefinedCarrierFreshShellSeriesDirections M h hM m
    modelCovarianceTrace
        (childTraceObservable (measurableSet_cubeSet Q)
          (volume_cubeSet_toReal_pos Q) ν σ hν hσ)
        (fun j => P (H (w j))) x =
      ∑ d : Fin 9, modelCovarianceTrace
        (childTraceObservable (measurableSet_cubeSet Q)
          (volume_cubeSet_toReal_pos Q) ν σ hν hσ)
        (fun j => P (F.factor d (F.direction d j))) x := by
  classical
  let Q := nativeHeatQ3RefinedCarrierChild m i
  let E : nativeHeatQ3RefinedCarrierIndex → Type := fun j =>
    C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)
  let π : (∀ j, E j) →L[ℝ] E i :=
    ContinuousLinearMap.proj (R := ℝ) (φ := E) i
  let P : C(nativeHeatQ3RefinedCarrierDomain m, ℝ) →L[ℝ] E i :=
    π.comp (nativeHeatQ3RefinedCarrierOldMap m)
  let F := nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m
  let H := nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m
  let w := nativeHeatQ3RefinedCarrierFreshShellSeriesDirections M h hM m
  let φ : E i → ℝ := childTraceObservable (measurableSet_cubeSet Q)
    (volume_cubeSet_toReal_pos Q) ν σ hν hσ
  have hφ : HasPolynomiallyBoundedC2Derivatives φ :=
    childTraceObservable_polynomial (measurableSet_cubeSet Q)
      (volume_cubeSet_toReal_pos Q) ν σ hν hσ
  have hφ' : ContDiff ℝ 2 (fun y : E i => φ y) := by
    simpa [E, φ, Q] using hφ.1
  have hW : Summable (fun j => ‖w j‖ ^ 2) :=
    nativeHeatQ3RefinedCarrierFreshShellSeriesSummable M h hM m
  have hPall : Summable (fun j => ‖P (H (w j))‖ ^ 2) :=
    summable_sq_bounded_image _ hW (P.comp H)
  have hPd (d : Fin 9) : Summable (fun j =>
      ‖P (F.factor d (F.direction d j))‖ ^ 2) :=
    summable_sq_bounded_image _ (F.squareSummable d) (P.comp (F.factor d))
  have hcovTotal := modelCovarianceTrace_eq_bilinearTraceMap
    (fun j => P (H (w j))) hPall hφ' x
  have hcovD (d : Fin 9) := modelCovarianceTrace_eq_bilinearTraceMap
    (fun j => P (F.factor d (F.direction d j))) (hPd d) hφ' x
  have hcomp : P.comp (finiteFactor (fun _ : Fin 9 => GaussianFactorL2 ℕ)
      F.factor) = finiteFactor (fun _ : Fin 9 => GaussianFactorL2 ℕ)
        (fun d => P.comp (F.factor d)) := by
    ext z
    simp [finiteFactor]
  have hmap : (fun j => P (H (w j))) =
      (fun j => finiteFactor (fun _ : Fin 9 => GaussianFactorL2 ℕ)
        (fun d => P.comp (F.factor d))
        (finiteDirections (fun _ : Fin 9 => GaussianFactorL2 ℕ)
          F.direction j)) := by
    funext j
    have hh := congrArg (fun T => T
      (finiteDirections (fun _ : Fin 9 => GaussianFactorL2 ℕ)
        F.direction j)) hcomp
    simpa [H, w, F, nativeHeatQ3RefinedCarrierFreshShellSeriesFactor,
      nativeHeatQ3RefinedCarrierFreshShellSeriesDirections,
      ContinuousLinearMap.comp_apply] using hh
  have hmapPoint j := congrFun hmap j
  calc
    modelCovarianceTrace φ (fun j => P (H (w j))) x =
      bilinearTraceMap (fun j => P (H (w j))) hPall
        (fderiv ℝ (fderiv ℝ φ) x) := hcovTotal
    _ = ∑ d : Fin 9, bilinearTraceMap
        (fun j => P (F.factor d (F.direction d j))) (hPd d)
        (fderiv ℝ (fderiv ℝ φ) x) := by
          simp only [bilinearTraceMap_apply]
          change (∑' j, (fderiv ℝ (fderiv ℝ φ) x) (P (H (w j)))
              (P (H (w j)))) = _
          simp_rw [hmapPoint]
          simpa [F, H, w, nativeHeatQ3RefinedCarrierFreshShellFamily,
            nativeHeatQ3RefinedCarrierFreshShellSeriesFactor,
            nativeHeatQ3RefinedCarrierFreshShellSeriesDirections] using
            (finiteFactor_bilinearTrace_eq_sum F.direction
              F.squareSummable (fun d => P.comp (F.factor d))
              (fderiv ℝ (fderiv ℝ φ) x))
    _ = ∑ d : Fin 9, modelCovarianceTrace φ
        (fun j => P (F.factor d (F.direction d j))) x := by
          apply Finset.sum_congr rfl
          intro d hd
          exact (hcovD d).symm

/-- The source's diagonal center contribution for one refined child shell. -/
noncomputable def nativeHeatQ3RefinedCarrierChildCenterDriftProfile
    (M : ABKModel 2) (h : ℝ) (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) (d : Fin 9) (σ : ℝ)
    (x : C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) : ℝ :=
  let n := (nativeHeatQ3RefinedCarrierChild m i).scale
  let s := d.val + 2
  let Q := originCube 2 n
  let Acoef := coarseBlockMatrix (cubeSet Q)
    (responsePlanarCoefficientField M.nu
      (ContinuousMap.linearIsometryBoundedOfCompact
        (closure (cubeSet Q)) ℝ ℝ
        (nativeHeat_translateTriadicFieldToOrigin
          (nativeHeatQ3RefinedCarrierChild m i) x)))
  let D := Matrix.trace (frameMatrix σ Acoef).lowerRight
  let v₀ := (q3ModelAmplitude M h (n + (s : ℤ))) ^ 2 / σ ^ 2
  v₀ * D

/-- The signed center/mixed/remainder source drift profile for one refined
child and one physical shell. -/
noncomputable def nativeHeatQ3RefinedCarrierChildSignedDriftProfile
    (M : ABKModel 2) (h : ℝ) (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) (d : Fin 9) (σ : ℝ)
    (x : C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) : ℝ :=
  let n := (nativeHeatQ3RefinedCarrierChild m i).scale
  let s := d.val + 2
  let Q := originCube 2 n
  let Φ := modelTraceObservable n M.nu σ
  let k := pureFluxOpenResponseRestriction n
    (nativeHeat_translateTriadicFieldToOrigin
      (nativeHeatQ3RefinedCarrierChild m i) x)
  let Bmix := lemmaVTileHistory Q (pureFluxBankSourceDepth s)
    (responseFramePlanarCoefficientField M.nu σ k)
  let Brem := pureFluxSourceTileHistory Q (pureFluxBankSourceDepth s)
    (responseFramePlanarCoefficientField M.nu σ k)
  let B := max Bmix Brem
  let ρ := cubeScaleFactor Q / (q3ModelLength (n + (s : ℤ))).1
  let δ := diagMeshRadius Q (pureFluxBankSourceDepth s) /
    (q3ModelLength (n + (s : ℤ))).1
  let κ := lemmaVH2kn ρ δ
  let μ := pureFluxCovarianceMu (pureFluxCovarianceA 0 (s - 1))
    (pureFluxCovarianceB 0 (s - 1))
  let v₀ := (q3ModelAmplitude M h (n + (s : ℤ))) ^ 2 / σ ^ 2
  let Acoef := coarseBlockMatrix (cubeSet Q)
    (responsePlanarCoefficientField M.nu
      (ContinuousMap.linearIsometryBoundedOfCompact
        (closure (cubeSet Q)) ℝ ℝ
        (nativeHeat_translateTriadicFieldToOrigin
          (nativeHeatQ3RefinedCarrierChild m i) x)))
  let D := Matrix.trace (frameMatrix σ Acoef).lowerRight
  v₀ * D + (2 * v₀ * κ * B + v₀ * μ * B ^ 2) *
    (Φ (nativeHeat_translateTriadicFieldToOrigin
      (nativeHeatQ3RefinedCarrierChild m i) x) + 4)

/-- Removing the source's diagonal center part leaves precisely its signed
off-diagonal drift/mixed payment. -/
noncomputable def nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfile
    (M : ABKModel 2) (h : ℝ) (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) (d : Fin 9) (σ : ℝ)
    (x : C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) : ℝ :=
  nativeHeatQ3RefinedCarrierChildSignedDriftProfile M h m i d σ x -
    nativeHeatQ3RefinedCarrierChildCenterDriftProfile M h m i d σ x

/-- The covariance of an actual refined carrier child is bounded by the
sum of its nine signed source drift profiles. -/
theorem nativeHeatQ3RefinedCarrierChildSignedCovariance_le_sourceProfiles
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (i : nativeHeatQ3RefinedCarrierIndex)
    (σ : ℝ) (hσ : 0 < σ)
    (x : C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) :
    (1 / 2 : ℝ) * modelCovarianceTrace
      (childTraceObservable
        (measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i))
        (volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i))
        M.nu σ M.nu_pos hσ)
      (fun j => (nativeHeatQ3RefinedCarrierOldMap m
        (nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m
          (nativeHeatQ3RefinedCarrierFreshShellSeriesDirections M h hM m j))) i) x ≤
      ∑ d : Fin 9,
        nativeHeatQ3RefinedCarrierChildSignedDriftProfile M h m i d σ x := by
  classical
  let Q := nativeHeatQ3RefinedCarrierChild m i
  let E : nativeHeatQ3RefinedCarrierIndex → Type := fun j =>
    C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)
  let π := ContinuousLinearMap.proj (R := ℝ) (φ := E) i
  let P := π.comp (nativeHeatQ3RefinedCarrierOldMap m)
  let F := nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m
  let H := nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m
  let w := nativeHeatQ3RefinedCarrierFreshShellSeriesDirections M h hM m
  let φ : E i → ℝ := childTraceObservable (measurableSet_cubeSet Q)
    (volume_cubeSet_toReal_pos Q) M.nu σ M.nu_pos hσ
  have hsplit := nativeHeatQ3RefinedCarrierChildCovariance_eq_sum_shellRows
    M h hM m i M.nu σ M.nu_pos hσ x
  have hsplit' : modelCovarianceTrace φ (fun j => P (H (w j))) x =
      ∑ d : Fin 9, modelCovarianceTrace φ
        (fun j => P (F.factor d (F.direction d j))) x := by
    simpa [Q, E, π, P, F, H, w, φ] using hsplit
  have hC (d : Fin 9) :
      (1 / 2 : ℝ) * modelCovarianceTrace
        (modelTraceObservable Q.scale M.nu σ)
        (fun j => nativeHeat_translateTriadicFieldToOrigin Q
          (nativeHeatQ3RefinedCarrierChildShellMap M h hM m i d
            ((nativeHeatQ3RefinedCarrierFreshShellFamily M h hM m).direction d j)))
        (nativeHeat_translateTriadicFieldToOrigin Q x) ≤
        nativeHeatQ3RefinedCarrierChildSignedDriftProfile M h m i d σ x := by
    have hrows := nativeHeatQ3RefinedCarrierChildDriftAndBracketRows
      M h hM m i d σ hσ x
    have hsource := hrows.2
    unfold nativeHeatSourceDriftAndBracketConclusion at hsource
    simpa [nativeHeatQ3RefinedCarrierChildSignedDriftProfile,
      nativeHeatQ3RefinedCarrierChildShellMap, Function.comp_apply] using hsource.1
  have htransport (d : Fin 9) :
      modelCovarianceTrace φ (fun j => P (F.factor d (F.direction d j))) x =
        modelCovarianceTrace (modelTraceObservable Q.scale M.nu σ)
          (fun j => nativeHeat_translateTriadicFieldToOrigin Q
            (P (F.factor d (F.direction d j))))
          (nativeHeat_translateTriadicFieldToOrigin Q x) := by
    have hfun : childTraceObservable
        (measurableSet_cubeSet Q) (volume_cubeSet_toReal_pos Q)
        M.nu σ M.nu_pos hσ =
      modelTraceObservable Q.scale M.nu σ ∘
        nativeHeat_translateTriadicFieldToOrigin Q := by
      funext y
      exact nativeHeatQ3RefinedCarrierChildTraceObservable_toOrigin
        Q M.nu σ M.nu_pos hσ y
    have hdir : Summable (fun j => ‖P (F.factor d (F.direction d j))‖ ^ 2) :=
      summable_sq_bounded_image _ (F.squareSummable d) (P.comp (F.factor d))
    change modelCovarianceTrace
        (childTraceObservable
          (measurableSet_cubeSet Q) (volume_cubeSet_toReal_pos Q)
          M.nu σ M.nu_pos hσ)
        (fun j => P (F.factor d (F.direction d j))) x = _
    rw [hfun]
    exact nativeHeat_modelCovarianceTrace_comp_continuousLinearMap
      (nativeHeat_translateTriadicFieldToOrigin Q)
      (fun j => P (F.factor d (F.direction d j))) hdir
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
theorem nativeHeatQ3RefinedCarrierChildCenteredCovariance_le_offDiagonalProfiles
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (i : nativeHeatQ3RefinedCarrierIndex)
    (σ : ℝ) (hσ : 0 < σ)
    (x : C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) :
    (1 / 2 : ℝ) * modelCovarianceTrace
      (childTraceObservable
        (measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i))
        (volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i))
        M.nu σ M.nu_pos hσ)
      (fun j => (nativeHeatQ3RefinedCarrierOldMap m
        (nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m
          (nativeHeatQ3RefinedCarrierFreshShellSeriesDirections M h hM m j))) i) x -
      ∑ d : Fin 9,
        nativeHeatQ3RefinedCarrierChildCenterDriftProfile M h m i d σ x ≤
    ∑ d : Fin 9,
      nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfile M h m i d σ x := by
  have hfull := nativeHeatQ3RefinedCarrierChildSignedCovariance_le_sourceProfiles
    M h hM m i σ hσ x
  have hsum :
      (∑ d : Fin 9,
        nativeHeatQ3RefinedCarrierChildSignedDriftProfile M h m i d σ x) -
        ∑ d : Fin 9,
          nativeHeatQ3RefinedCarrierChildCenterDriftProfile M h m i d σ x =
      ∑ d : Fin 9,
        nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfile M h m i d σ x := by
    rw [← Finset.sum_sub_distrib]
    rfl
  calc
    _ ≤ (∑ d : Fin 9,
        nativeHeatQ3RefinedCarrierChildSignedDriftProfile M h m i d σ x) -
        ∑ d : Fin 9,
          nativeHeatQ3RefinedCarrierChildCenterDriftProfile M h m i d σ x :=
      sub_le_sub_right hfull _
    _ = _ := hsum

end ASDExplicitGamma.Native
