module

public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceTransport
public import ASDExplicitGamma.Native.HeatVHEATSourceCarrierGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedShellLawGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceClocksGen

/-! The `ns`-shell child drift profiles. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open Algsuperdiff.Section3 ASDExplicitGamma.Model
open ASDExplicitGamma.Inverse ASDExplicitGamma.Response
open ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open ProbabilityTheory

variable (ns : ℕ)

local instance nativeHeatRefinedSourceOriginCompactGenRefinedSourceProfiles (n : ℤ) :
    CompactSpace (closure (cubeSet (originCube 2 n))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure

noncomputable def nativeHeatQ3RefinedCarrierChildCenterDriftProfileGen
    (M : ABKModel 2) (h : ℝ) (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) (d : Fin ns) (σ : ℝ)
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
noncomputable def nativeHeatQ3RefinedCarrierChildSignedDriftProfileGen
    (M : ABKModel 2) (h : ℝ) (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) (d : Fin ns) (σ : ℝ)
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
noncomputable def nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfileGen
    (M : ABKModel 2) (h : ℝ) (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) (d : Fin ns) (σ : ℝ)
    (x : C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) : ℝ :=
  (nativeHeatQ3RefinedCarrierChildSignedDriftProfileGen ns) M h m i d σ x -
    (nativeHeatQ3RefinedCarrierChildCenterDriftProfileGen ns) M h m i d σ x
