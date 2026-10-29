module

public import ASDExplicitGamma.Main.InverseObservable
public import ASDExplicitGamma.Variational.AdapterConstantSkew

/-! Constant-skew gauge invariance of the fixed-frame inverse observable. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Variational

/-- The inverse trace is unchanged by adding a constant to the scalar skew
coefficient. -/
theorem mainInverseObservable_add_const (n : ℤ) (ν σ g : ℝ) (hν : 0 < ν)
    (k : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    mainInverseObservable n ν σ
      (k + ContinuousMap.const (closure (cubeSet (originCube 2 n))) g) =
        mainInverseObservable n ν σ k := by
  let Q := originCube 2 n
  let U := cubeSet Q
  let K := closure U
  let L := ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ
  have hL : L (k + ContinuousMap.const K g) =
      L k + BoundedContinuousFunction.const K g := by
    ext x
    simp [L]
  have hmatrix :
      coarseBlockMatrix U (responsePlanarCoefficientField ν (L (k + ContinuousMap.const K g))) =
        constantSkewCongruence g
          (coarseBlockMatrix U (responsePlanarCoefficientField ν (L k))) := by
    rw [hL]
    have hfield : responsePlanarCoefficientField ν (L k + BoundedContinuousFunction.const K g) =ᵐ[
        volume.restrict U] fun x => responsePlanarCoefficient ν
          (responseCoefficientExtension (L k) x + g) := by
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_cubeSet Q)] with x hx
      simp only [responsePlanarCoefficientField]
      rw [responseCoefficientExtension_add_on (L k)
        (BoundedContinuousFunction.const K g) hx]
      rw [responseCoefficientExtension_eq
        (BoundedContinuousFunction.const K g) hx]
      rfl
    rw [coarseBlockMatrix_congr_of_ae_eq hfield]
    exact response_coarseBlockMatrix_constantSkew Q ν hν (L k) g
  unfold mainInverseObservable
  rw [hmatrix, constantSkewCongruence_lowerRight]

end ASDExplicitGamma.Main

end
