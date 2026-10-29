module

public import ASDExplicitGamma.Gaussian.ChildResponse
public import ASDExplicitGamma.Native.VanishingBracket
public import ASDExplicitGamma.Native.HeatShearMoment
public import ASDExplicitGamma.Variational.AdapterMu

/-! The child response is the true-frame trace defect used by VHEAT. -/

@[expose] public section

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Response
open ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Variational

namespace ASDExplicitGamma.Native

/-- The four-load child response is exactly the true-frame coarse trace
defect on every triadic child cube. -/
theorem nativeHeat_childTrace_eq_traceDefect {Q : TriadicCube 2}
    [CompactSpace (closure (cubeSet Q))]
    (hU : MeasurableSet (cubeSet Q))
    (hvol : 0 < (volume (cubeSet Q)).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : C(closure (cubeSet Q), ℝ)) :
    childTraceObservable hU hvol ν σ hν hσ k =
      traceDefect (cubeSet Q)
        (responsePlanarCoefficientField ν
          (ContinuousMap.linearIsometryBoundedOfCompact
            (closure (cubeSet Q)) ℝ ℝ k)) σ := by
  let L := ContinuousMap.linearIsometryBoundedOfCompact
    (closure (cubeSet Q)) ℝ ℝ
  let A := coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField ν (L k))
  have hPlus (i : Fin 2) :
      responseFrameEnergyObservable hU hvol ν σ hν hσ
          (orthonormalFrameLoad i 1) (L k) =
        (σ⁻¹ * A.upperLeft i i + σ * A.lowerRight i i +
          (A.upperRight i i + A.lowerLeft i i)) / 2 := by
    rw [responseFrameEnergyObservable_eq_frameCoarseQuadratic
      hU hvol ν σ hν hσ (orthonormalFrameLoad i 1) (L k)]
    change blockVecDot (orthonormalFrameLoad i 1)
      (blockMatVecMul (frameMatrix σ A) (orthonormalFrameLoad i 1)) = _
    simpa using orthonormalFrameLoad_energy A σ i 1 (by norm_num)
  have hMinus (i : Fin 2) :
      responseFrameEnergyObservable hU hvol ν σ hν hσ
          (orthonormalFrameLoad i (-1)) (L k) =
        (σ⁻¹ * A.upperLeft i i + σ * A.lowerRight i i -
          (A.upperRight i i + A.lowerLeft i i)) / 2 := by
    rw [responseFrameEnergyObservable_eq_frameCoarseQuadratic
      hU hvol ν σ hν hσ (orthonormalFrameLoad i (-1)) (L k)]
    change blockVecDot (orthonormalFrameLoad i (-1))
      (blockMatVecMul (frameMatrix σ A) (orthonormalFrameLoad i (-1))) = _
    convert orthonormalFrameLoad_energy A σ i (-1) (by norm_num) using 1
    ring
  have hLoadSum :
      (∑ i : Fin 2,
        (responseFrameEnergyObservable hU hvol ν σ hν hσ
            (orthonormalFrameLoad i 1) (L k) +
          responseFrameEnergyObservable hU hvol ν σ hν hσ
            (orthonormalFrameLoad i (-1)) (L k))) =
        (∑ i : Fin 2, (σ⁻¹ * A.upperLeft i i + σ * A.lowerRight i i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hPlus i, hMinus i]
    ring
  have hSum :
      (∑ i : Fin 2, (σ⁻¹ * A.upperLeft i i + σ * A.lowerRight i i)) =
        σ⁻¹ * Matrix.trace A.upperLeft + σ * Matrix.trace A.lowerRight := by
    simp only [Matrix.trace, Matrix.diag_apply]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    childTraceObservable hU hvol ν σ hν hσ k =
        (∑ i : Fin 2,
          (responseFrameEnergyObservable hU hvol ν σ hν hσ
              (orthonormalFrameLoad i 1) (L k) +
            responseFrameEnergyObservable hU hvol ν σ hν hσ
              (orthonormalFrameLoad i (-1)) (L k))) - 4 := by
          rfl
    _ = (∑ i : Fin 2, (σ⁻¹ * A.upperLeft i i + σ * A.lowerRight i i)) - 4 := by
          rw [hLoadSum]
    _ = traceDefect (cubeSet Q) (responsePlanarCoefficientField ν (L k)) σ := by
          rw [hSum]
          rfl

/-- The literal four-load child response is nonnegative for every
continuous coefficient lift, by ellipticity of its response field. -/
theorem nativeHeat_childTrace_nonneg {Q : TriadicCube 2}
    [CompactSpace (closure (cubeSet Q))]
    (hU : MeasurableSet (cubeSet Q))
    (hvol : 0 < (volume (cubeSet Q)).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : C(closure (cubeSet Q), ℝ)) :
    0 ≤ childTraceObservable hU hvol ν σ hν hσ k := by
  rw [nativeHeat_childTrace_eq_traceDefect hU hvol ν σ hν hσ k]
  exact traceDefect_nonneg_of_ellipticFieldOn_triCube hν
    (responsePlanarCoefficientField_isElliptic hU ν hν
      (ContinuousMap.linearIsometryBoundedOfCompact
        (closure (cubeSet Q)) ℝ ℝ k)) hσ

/-- Lemma V's exact quadratic shear row, including its discriminant bound,
holds for the literal four-load child observable. -/
theorem nativeHeat_childTrace_shear_rows {Q : TriadicCube 2}
    [CompactSpace (closure (cubeSet Q))]
    (hU : MeasurableSet (cubeSet Q))
    (hvol : 0 < (volume (cubeSet Q)).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : C(closure (cubeSet Q), ℝ)) :
    let k' := ContinuousMap.linearIsometryBoundedOfCompact
      (closure (cubeSet Q)) ℝ ℝ k
    let A := coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField ν k')
    let T := traceDefect (cubeSet Q) (responsePlanarCoefficientField ν k') σ
    let D := Matrix.trace (frameMatrix σ A).lowerRight / σ ^ 2
    let z := Variational.shearTraceLinear A / σ
    0 ≤ T ∧ 0 < D ∧ z ^ 2 ≤ D * T ∧
      (∀ g : ℝ,
        childTraceObservable hU hvol ν σ hν hσ
          (k + BoundedContinuousFunction.const (closure (cubeSet Q)) g) =
        T + 2 * g * z + g ^ 2 * D) := by
  classical
  let L := ContinuousMap.linearIsometryBoundedOfCompact
    (closure (cubeSet Q)) ℝ ℝ
  let k' := L k
  let A := coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField ν k')
  let T := traceDefect (cubeSet Q) (responsePlanarCoefficientField ν k') σ
  let D := Matrix.trace (frameMatrix σ A).lowerRight / σ ^ 2
  let z := Variational.shearTraceLinear A / σ
  change 0 ≤ T ∧ 0 < D ∧ z ^ 2 ≤ D * T ∧
    (∀ g : ℝ,
      childTraceObservable hU hvol ν σ hν hσ
        (k + BoundedContinuousFunction.const (closure (cubeSet Q)) g) =
      T + 2 * g * z + g ^ 2 * D)
  have hrows := nativeTraceShearDefectRows Q ν σ hν hσ k'
  refine ⟨hrows.1, hrows.2.1, hrows.2.2.1, ?_⟩
  intro g
  have hL : L (k + BoundedContinuousFunction.const (closure (cubeSet Q)) g) =
      L k + BoundedContinuousFunction.const (closure (cubeSet Q)) g := by
    ext x
    simp [L]
  have hfield : responsePlanarCoefficientField ν
      (L (k + BoundedContinuousFunction.const (closure (cubeSet Q)) g)) =ᵐ[
        volume.restrict (cubeSet Q)]
        (fun x => responsePlanarCoefficient ν
          (responseCoefficientExtension k' x + g)) := by
    filter_upwards [ae_restrict_mem (μ := volume) hU] with x hx
    simp only [responsePlanarCoefficientField]
    rw [hL]
    rw [responseCoefficientExtension_add_on
      k' (BoundedContinuousFunction.const (closure (cubeSet Q)) g) hx]
    rw [responseCoefficientExtension_eq
      (BoundedContinuousFunction.const (closure (cubeSet Q)) g) hx]
    rfl
  have hobs :
      childTraceObservable hU hvol ν σ hν hσ
        (k + BoundedContinuousFunction.const (closure (cubeSet Q)) g) =
      traceDefect (cubeSet Q)
        (fun x => responsePlanarCoefficient ν
          (responseCoefficientExtension k' x + g)) σ := by
    rw [nativeHeat_childTrace_eq_traceDefect hU hvol ν σ hν hσ
      (k + BoundedContinuousFunction.const (closure (cubeSet Q)) g)]
    unfold traceDefect
    rw [coarseBlockMatrix_congr_of_ae_eq hfield]
  rw [hobs]
  exact hrows.2.2.2 g

/-- The averaged true-frame trace on any finite family of triadic children is
nonnegative, so every natural power is a valid nonnegative VHEAT test. -/
theorem nativeHeat_childMeanTrace_nonneg
    {n : ℕ} [NeZero n] (Q : Fin n → TriadicCube 2)
    [∀ i, IsFiniteMeasure (volumeMeasureOn (cubeSet (Q i)))]
    [∀ i, CompactSpace (closure (cubeSet (Q i)))]
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ∀ i, C(closure (cubeSet (Q i)), ℝ)) :
    0 ≤ childMeanTrace (fun i => cubeSet (Q i))
      (fun i => measurableSet_cubeSet (Q i))
      (fun i => volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ k := by
  classical
  unfold childMeanTrace
  apply mul_nonneg
  · positivity
  · apply Finset.sum_nonneg
    intro i hi
    exact nativeHeat_childTrace_nonneg
      (measurableSet_cubeSet (Q i)) (volume_cubeSet_toReal_pos (Q i))
      ν σ hν hσ (k i)

/-- A joint constant center shift of the finite child product evaluates as
the normalized sum of the corresponding individual child observables. -/
theorem nativeHeat_childMeanTrace_constantShift_sum
    {n : ℕ} [NeZero n] (Q : Fin n → TriadicCube 2)
    [∀ i, IsFiniteMeasure (volumeMeasureOn (cubeSet (Q i)))]
    [∀ i, CompactSpace (closure (cubeSet (Q i)))]
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ∀ i, C(closure (cubeSet (Q i)), ℝ)) (g : Fin n → ℝ) :
    childMeanTrace (fun i => cubeSet (Q i))
        (fun i => measurableSet_cubeSet (Q i))
        (fun i => volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ
        (k + childConstantMap (fun i => closure (cubeSet (Q i))) g) =
      (n : ℝ)⁻¹ * ∑ i : Fin n,
        childTraceObservable (measurableSet_cubeSet (Q i))
          (volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ
          (k i + BoundedContinuousFunction.const
            (closure (cubeSet (Q i))) (g i)) := by
  classical
  unfold childMeanTrace
  apply congrArg (fun s : ℝ => (n : ℝ)⁻¹ * s)
  apply Finset.sum_congr rfl
  intro i hi
  have hconst :
      (childConstantMap (fun i => closure (cubeSet (Q i))) g) i =
        BoundedContinuousFunction.const (closure (cubeSet (Q i))) (g i) := by
    ext x
    simp [childConstantMap]
  change childTraceObservable (measurableSet_cubeSet (Q i))
    (volume_cubeSet_toReal_pos (Q i)) ν σ hν hσ
    (k i + (childConstantMap (fun i => closure (cubeSet (Q i))) g) i) = _
  rw [hconst]

end ASDExplicitGamma.Native
