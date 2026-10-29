module

public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedRemainder
public import ASDExplicitGamma.Native.HeatVHEATSourceCarrierGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedShellLawGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceClocksGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceProfilesGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceTransportGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceGeometryGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceBankGen
public import ASDExplicitGamma.Native.HeatVHEATDriftBankIdentityGen
public import ASDExplicitGamma.Native.HeatVHEATDriftBankMeasurableGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceIntegrandGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceNormsGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceExpectationGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedCoefficientsGen
public import ASDExplicitGamma.Native.HeatVHEATDriftConfiguredCoefficientsGen
public import ASDExplicitGamma.Native.HeatVHEATDriftConfiguredExpectationGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedProfileGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedExpectationGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedPhysicalGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedBindingGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceObserverGen
public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedActualGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedAssemblyGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedRowGen
public import ASDExplicitGamma.Native.Q3GridOverlapGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedSupportGeometryGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedGeometryGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedObservationGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedParentLawGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedSourceMapGen
public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedMeanVarianceGen
import ASDExplicitGamma.Gaussian.BilinearCovariance
import ASDExplicitGamma.Gaussian.ModelHeatPower

/-! The `ns`-shell generalization of `HeatVHEATBracketRefinedRemainder`. -/

@[expose] public section


namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Inverse
open ASDExplicitGamma.Response
open ASDExplicitGamma.Variational ASDExplicitGamma.Triadic
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped ENNReal

variable (ns : ℕ) [NeZero ns]

local instance nativeHeatQ3RefinedOriginCompact_bracket_GenBracketRefinedRemainder (m : ℤ) :
    CompactSpace (closure (cubeSet (originCube 2 m))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (originCube 2 m)).isCompact_closure

/-- The sharp SHEAR remainder-bracket row transfers from the canonical q3
series to the actual centered refined carrier shell, at the true source frame. -/
theorem nativeHeatQ3RefinedCarrierChildCenteredFreshShellBracket_le_Gen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ)
    (Ffam : NativeHeatQ3RefinedCarrierFreshShellFamilyGen M m ns) (i : nativeHeatQ3RefinedCarrierIndex) (d : Fin ns)
    (σ : ℝ) (hσ : 0 < σ)
    (x : C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) :
    let Q := nativeHeatQ3RefinedCarrierChild m i
    let P := (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun j : nativeHeatQ3RefinedCarrierIndex =>
        C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)) i).comp
      (nativeHeatQ3RefinedCarrierOldMap m)
    let A := nativeHeat_translateTriadicFieldToOrigin Q
    let C₀ := centeringMap (pureFluxParentCenter Q.scale)
    let s := d.val + 2
    let b := q3ModelAmplitude M h (Q.scale + (s : ℤ))
    let L := q3ModelLength (Q.scale + (s : ℤ))
    let B := lemmaVTileHistory (originCube 2 Q.scale)
      (pureFluxBankSourceDepth s)
      (responseFramePlanarCoefficientField M.nu σ
        (pureFluxOpenResponseRestriction Q.scale (A x)))
    let ρ := cubeScaleFactor (originCube 2 Q.scale) / L.1
    let δ := diagMeshRadius (originCube 2 Q.scale)
      (pureFluxBankSourceDepth s) / L.1
    modelGradientSquareTrace (modelTraceObservable Q.scale M.nu σ)
      (fun j => C₀ (A (P (Ffam.factor d (Ffam.direction d j))))) (A x) ≤
      4 * (b ^ 2 / σ ^ 2) * (lemmaVH2Bn ρ δ) ^ 2 * B ^ 2 *
        (modelTraceObservable Q.scale M.nu σ (A x)) *
          (modelTraceObservable Q.scale M.nu σ (A x) + 4) := by
  classical
  dsimp only
  let Q := nativeHeatQ3RefinedCarrierChild m i
  let P := (ContinuousLinearMap.proj (R := ℝ)
    (φ := fun j : nativeHeatQ3RefinedCarrierIndex =>
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m j)), ℝ)) i).comp
    (nativeHeatQ3RefinedCarrierOldMap m)
  let A := nativeHeat_translateTriadicFieldToOrigin Q
  let C₀ := centeringMap (pureFluxParentCenter Q.scale)
  let s : ℕ := d.val + 2
  let b := q3ModelAmplitude M h (Q.scale + (s : ℤ))
  let L := q3ModelLength (Q.scale + (s : ℤ))
  let T : GaussianFactorL2 ℕ →L[ℝ]
      C(closure (cubeSet (originCube 2 Q.scale)), ℝ) :=
    A.comp (P.comp (Ffam.factor d))
  let B := lemmaVTileHistory (originCube 2 Q.scale)
      (pureFluxBankSourceDepth s)
      (responseFramePlanarCoefficientField M.nu σ
        (pureFluxOpenResponseRestriction Q.scale (A x)))
  let ρ := cubeScaleFactor (originCube 2 Q.scale) / L.1
  let δ := diagMeshRadius (originCube 2 Q.scale)
      (pureFluxBankSourceDepth s) / L.1
  let Φ := modelTraceObservable Q.scale M.nu σ
  have hrows := (nativeHeatQ3RefinedCarrierChildDriftAndBracketRows_Gen ns)
    M h hM m Ffam i d σ hσ x
  have hlawActual : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction
          (closure (cubeSet (originCube 2 Q.scale)))
          (ω.1 (Q.scale + (s : ℤ)))) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE (Ffam.squareSummable d) T) := by
    simpa [Q, P, A, s, T] using hrows.1
  have hlawCanonical : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction
          (closure (cubeSet (originCube 2 Q.scale)))
          (ω.1 (Q.scale + (s : ℤ)))) =
      standardGaussianInfinitePi.map (mainCubeQ3Series Q.scale b L) := by
    simpa [s, b, L, sub_add_cancel] using
      (main_actual_fresh_cube_factor_law Q.scale M h hM
        (Q.scale + (s : ℤ) - 1))
  have hlaw : standardGaussianInfinitePi.map (mainCubeQ3Series Q.scale b L) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE (Ffam.squareSummable d) T) :=
    hlawCanonical.symm.trans hlawActual
  let D := fderiv ℝ Φ (A x)
  let Bform : C(closure (cubeSet (originCube 2 Q.scale)), ℝ) →L[ℝ]
      C(closure (cubeSet (originCube 2 Q.scale)), ℝ) →L[ℝ] ℝ :=
    (D.comp C₀).smulRight (D.comp C₀)
  have hbil := @bilinearTrace_eq_of_law
    (GaussianFactorL2 ℕ) (MainCubeH3 Q.scale b L)
    (C(closure (cubeSet (originCube 2 Q.scale)), ℝ))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance (mainCubeH3InnerProductSpace Q.scale b L) inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (Ffam.direction d) (Ffam.squareSummable d) T
    (mainCubeQ3Directions Q.scale b L) (mainCubeQ3Directions_summable Q.scale b L)
    (mainCubeH3Value Q.scale b L) hlaw.symm Bform
  have hgrad : modelGradientSquareTrace Φ
      (fun j => C₀ (A (P (Ffam.factor d (Ffam.direction d j))))) (A x) =
      modelGradientSquareTrace Φ
        (fun j => C₀ (pureFluxMainCubeQ3Directions Q.scale b L j)) (A x) := by
    change (∑' j, (D (C₀ (T (Ffam.direction d j)))) ^ 2) =
      ∑' j, (D (C₀ (mainCubeH3Value Q.scale b L
        (mainCubeQ3Directions Q.scale b L j))) ^ 2)
    convert hbil using 1 <;>
      simp [Bform, T, D, Φ, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.comp_apply, smul_eq_mul, pow_two] <;> rfl
  rw [hgrad]
  have hrow := raw_trace_model_q3_remainder_bracket_row_tight
    Q.scale s M.nu σ b M.nu_pos hσ (A x)
  change modelGradientSquareTrace Φ
      (fun j => C₀ (pureFluxMainCubeQ3Directions Q.scale b L j)) (A x) ≤
      4 * (b ^ 2 / σ ^ 2) * (lemmaVH2Bn ρ δ) ^ 2 * B ^ 2 *
        Φ (A x) * (Φ (A x) + 4)
  exact hrow.2

end ASDExplicitGamma.Native
