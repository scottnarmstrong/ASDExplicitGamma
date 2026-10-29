module

public import ASDExplicitGamma.Native.HeatRefinedGridProfile
public import ASDExplicitGamma.Native.HeatVHEATRefinedAssembly
import ASDExplicitGamma.Native.HeatCenterCovariance
import ASDExplicitGamma.Native.HeatFiniteBandCenters
import ASDExplicitGamma.Gaussian.DerivativeLawValueCovariance
import ASDExplicitGamma.Gaussian.BilinearCovariance
import ASDExplicitGamma.Gaussian.WholeRoot

/-! Parent-grid coordinates for the actual depth-ten carrier and its shell
covariance kernel. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Model ASDExplicitGamma.Triadic
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ProbabilityTheory
open scoped RealInnerProductSpace

/-- The actual depth-ten child center in parent coordinates. -/
theorem nativeHeatQ3RefinedChildCube_center'
    (Q : TriadicCube 2)
    (ij : Fin (3 ^ 10) × Fin (3 ^ 10)) :
    cubeCenter (nativeHeatQ3RefinedChildCube Q ij) =
      fun a => cubeCenter Q a + cubeScaleFactor Q *
        (q3GridCenterVector 10 ij a - (1 / 2 : ℝ)) := by
  let k := nativeHeatQ3RefinedChildDigits ij
  let C := Triadic.diagMeshCell Q 10 k
  have hcorner := Triadic.diagMeshCell_corner Q 10 k
  have hside := Triadic.diagMeshCell_side Q 10 k
  funext a
  fin_cases a
  · change cubeCenter C 0 = _
    rw [show cubeCenter C 0 = Triadic.cubeCorner C 0 +
        cubeScaleFactor C / 2 by
      simp [cubeCenter, Triadic.cubeCorner]
      ring,
      hcorner 0, hside]
    simp [k, nativeHeatQ3RefinedChildDigits, Triadic.cubeCorner,
      Triadic.diagMeshRadius, cubeCenter, cubeScaleFactor,
      q3GridCenterVector, q3GridCenterAxis]
    field_simp
    ring_nf
  · change cubeCenter C 1 = _
    rw [show cubeCenter C 1 = Triadic.cubeCorner C 1 +
        cubeScaleFactor C / 2 by
      simp [cubeCenter, Triadic.cubeCorner]
      ring,
      hcorner 1, hside]
    simp [k, nativeHeatQ3RefinedChildDigits, Triadic.cubeCorner,
      Triadic.diagMeshRadius, cubeCenter, cubeScaleFactor,
      q3GridCenterVector, q3GridCenterAxis]
    field_simp
    ring_nf

/-- The normalized linear observation of the actual refined child-center
vector. -/
noncomputable def nativeHeatQ3FiniteCenterObservation
    {I : Type*} [Fintype I] {K : Set (Vec 2)}
    (x : I → K) (a : I → ℝ) : C(K, ℝ) →L[ℝ] ℝ :=
  ∑ i, a i • ContinuousMap.evalCLM ℝ (x i)

@[simp]
theorem nativeHeatQ3FiniteCenterObservation_apply
    {I : Type*} [Fintype I] {K : Set (Vec 2)}
    (x : I → K) (a : I → ℝ) (f : C(K, ℝ)) :
    nativeHeatQ3FiniteCenterObservation x a f =
      ∑ i, a i * f (x i) := by
  classical
  simp only [nativeHeatQ3FiniteCenterObservation,
    smul_apply, smul_eq_mul, sum_apply, ContinuousMap.evalCLM_apply]

/-- A finite linear combination of Gaussian section vectors, kept abstract in
its finite index so callers can instantiate it without expanding the carrier. -/
noncomputable def nativeHeatQ3FiniteSectionSum {I : Type*} [Fintype I]
    (a : I → ℝ) (v : I → Gaussian.WhiteNoise) : Gaussian.WhiteNoise :=
  ∑ i, a i • v i

/-- The norm-square identity for the abstract finite section sum. -/
theorem nativeHeatQ3FiniteSectionSum_norm_sq {I : Type*} [Fintype I]
    (a : I → ℝ) (v : I → Gaussian.WhiteNoise) :
    ‖nativeHeatQ3FiniteSectionSum a v‖ ^ 2 =
      ∑ i, ∑ j, a i * a j * ⟪v i, v j⟫ := by
  simpa only [nativeHeatQ3FiniteSectionSum] using
    nativeHeat_norm_sum_smul_sq v a

/-- At the actual depth-ten centers, a physical shell covariance is exactly
the inner product of the corresponding normalized q3 grid sections. -/
theorem nativeHeatQ3RefinedCarrierShellKernel_eq
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (d : Fin 9)
    (ij jl : Fin (3 ^ 10) × Fin (3 ^ 10)) :
    q3ShellCovariance M h
      (nativeHeatQ3RefinedCarrierPhysicalShells m d)
      (cubeCenter (nativeHeatQ3RefinedCarrierChild m
        (finProdFinEquiv ij)))
      (cubeCenter (nativeHeatQ3RefinedCarrierChild m
        (finProdFinEquiv jl))) =
      ⟪q3Section
          (q3ModelAmplitude M h
            (nativeHeatQ3RefinedCarrierPhysicalShells m d))
          (q3GridKernelScale 10 (d.val + 2)) h3Zero
          (q3GridCenterVector 10 ij),
        q3Section
          (q3ModelAmplitude M h
            (nativeHeatQ3RefinedCarrierPhysicalShells m d))
          (q3GridKernelScale 10 (d.val + 2)) h3Zero
          (q3GridCenterVector 10 jl)⟫ := by
  let I := Fin (3 ^ 10) × Fin (3 ^ 10)
  let e : I ≃ nativeHeatQ3RefinedCarrierIndex := finProdFinEquiv
  let Q := originCube 2 (m + 10)
  let k := nativeHeatQ3RefinedCarrierPhysicalShells m d
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
    simpa [k, n] using nativeHeatQ3RefinedCarrierPhysicalShells_offset m d
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
