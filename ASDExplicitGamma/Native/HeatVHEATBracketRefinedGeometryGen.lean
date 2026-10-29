module

public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedGeometry
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
import ASDExplicitGamma.Native.HeatCenterCovariance
import ASDExplicitGamma.Native.HeatFiniteBandCenters
import ASDExplicitGamma.Gaussian.DerivativeLawValueCovariance
import ASDExplicitGamma.Gaussian.BilinearCovariance
import ASDExplicitGamma.Gaussian.WholeRoot

/-! The `ns`-shell generalization of `HeatVHEATBracketRefinedGeometry`. -/

@[expose] public section


namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Model ASDExplicitGamma.Triadic
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ProbabilityTheory
open scoped RealInnerProductSpace

variable (ns : ℕ) [NeZero ns]

theorem nativeHeatQ3RefinedCarrierShellKernel_eq_Gen
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (d : Fin ns)
    (ij jl : Fin (3 ^ 10) × Fin (3 ^ 10)) :
    q3ShellCovariance M h
      (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns d)
      (cubeCenter (nativeHeatQ3RefinedCarrierChild m
        (finProdFinEquiv ij)))
      (cubeCenter (nativeHeatQ3RefinedCarrierChild m
        (finProdFinEquiv jl))) =
      ⟪q3Section
          (q3ModelAmplitude M h
            (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns d))
          (q3GridKernelScale 10 (d.val + 2)) h3Zero
          (q3GridCenterVector 10 ij),
        q3Section
          (q3ModelAmplitude M h
            (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns d))
          (q3GridKernelScale 10 (d.val + 2)) h3Zero
          (q3GridCenterVector 10 jl)⟫ := by
  let I := Fin (3 ^ 10) × Fin (3 ^ 10)
  let e : I ≃ nativeHeatQ3RefinedCarrierIndex := finProdFinEquiv
  let Q := originCube 2 (m + 10)
  let k := nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns d
  let n := d.val + 2
  let β := q3ModelAmplitude M h k
  let x : I → Vec 2 := fun p =>
    cubeCenter (nativeHeatQ3RefinedCarrierChild m (e p))
  have hcenter (p : I) :
      cubeCenter (nativeHeatQ3RefinedCarrierChild m (e p)) =
        fun a => cubeCenter Q a + cubeScaleFactor Q *
          (q3GridCenterVector 10 p a - (1 / 2 : ℝ)) := by
    simpa [Q, e, nativeHeatQ3RefinedCarrierChild] using
      nativeHeatQ3RefinedChildCube_center' Q p
  have hQscale : cubeScaleFactor Q = (3 : ℝ) ^ (m + 10) := by
    simp [Q, Homogenization.cubeScaleFactor, originCube]
  have hk : k = m + (n : ℤ) := by
    simpa [k, n] using nativeHeatQ3RefinedCarrierPhysicalShellsGen_offset m d
  have hGridScale : (q3GridKernelScale 10 n).1 =
      (3 : ℝ) ^ ((n : ℤ) - 10) :=
    nativeHeat_q3GridKernelScale_eq_zpow_any 10 n
  have hscale : cubeScaleFactor Q / (3 : ℝ) ^ k =
      ((q3GridKernelScale 10 n).1)⁻¹ := by
    rw [hQscale, hGridScale, hk]
    calc
      (3 : ℝ) ^ (m + 10) / (3 : ℝ) ^ (m + (n : ℤ)) =
          (3 : ℝ) ^ ((m + 10) - (m + (n : ℤ))) := by
            rw [← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
      _ = (3 : ℝ) ^ (10 - (n : ℤ)) := by
            rw [show (m + 10) - (m + (n : ℤ)) = 10 - (n : ℤ) by omega]
      _ = ((3 : ℝ) ^ ((n : ℤ) - 10))⁻¹ := by
            rw [show 10 - (n : ℤ) = -((n : ℤ) - 10) by omega]
            rw [zpow_neg]
  have hcenterDiff (p q : I) (a : Fin 2) :
      (x p - x q) a = cubeScaleFactor Q *
        (q3GridCenterVector 10 p - q3GridCenterVector 10 q) a := by
    change (cubeCenter (nativeHeatQ3RefinedCarrierChild m (e p)) -
      cubeCenter (nativeHeatQ3RefinedCarrierChild m (e q))) a = _
    rw [hcenter p, hcenter q]
    simp only [Pi.sub_apply]
    ring
  have hcoord (p q : I) (a : Fin 2) :
      ((3 : ℝ) ^ k)⁻¹ * (x p - x q) a =
        (q3GridCenterVector 10 p - q3GridCenterVector 10 q) a /
          (q3GridKernelScale 10 n).1 := by
    rw [hcenterDiff p q a]
    calc
      ((3 : ℝ) ^ k)⁻¹ *
          (cubeScaleFactor Q *
            (q3GridCenterVector 10 p - q3GridCenterVector 10 q) a) =
        (cubeScaleFactor Q / (3 : ℝ) ^ k) *
          (q3GridCenterVector 10 p - q3GridCenterVector 10 q) a := by ring
      _ = _ := by rw [hscale]; ring
  have hAmp : β ^ 2 = h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) :=
    q3ModelAmplitude_sq M h k
  have hrect (p : I) :
      (q3GridRectangleCenter 10 p : Vec 2) = q3GridCenterVector 10 p := rfl
  rw [Gaussian.q3ShellCovariance, ← hAmp, hcoord ij jl 0, hcoord ij jl 1]
  simp only [Pi.sub_apply]
  simpa only [β, k, n, x, e, hrect] using
    (Gaussian.q3Section_covariance β (q3GridKernelScale 10 n)
      (q3GridCenterVector 10 ij) (q3GridCenterVector 10 jl)).symm

end ASDExplicitGamma.Native
