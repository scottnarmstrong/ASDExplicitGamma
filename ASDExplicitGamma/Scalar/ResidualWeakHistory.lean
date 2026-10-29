module

public import ASDExplicitGamma.Scalar.ResidualProjectionEnergy
public import ASDExplicitGamma.Scalar.QuarterHaarDuality
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! Complete source-history control of the actual projection residual's weak Haar energy. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response Variational MeasureTheory Triadic
open scoped ENNReal

/-- Abel's identity for the genuine vector weak energy, with the complete quarter discount. -/
theorem vector_weak_energy_abel (Q : TriadicCube 2) (r : Vec 2 → Vec 2)
    (hr : ∀ i,MemLp (fun x => r x i) 2 (normalizedCubeMeasure Q)) :
    (∑ i,dualEnergy Q sourceHaarBase (fun x => r x i))=
      (1-inverseHistoryDiscount)*∑' j : ℕ,inverseHistoryDiscount^j*
        ∑ i,energy Q (cubeProjection Q j (fun x => r x i)) := by
  have hinv : sourceHaarBase⁻¹=inverseHistoryDiscount := by
    exact inverse_history_discount_eq.symm
  simp_rw [dualEnergy_eq Q source_haar_base_gt_one (hr _),hinv]
  rw [← Finset.mul_sum]
  have hs (i : Fin 2) : Summable (fun j : ℕ => inverseHistoryDiscount^j *
      energy Q (cubeProjection Q j (fun x => r x i))) := by
    simpa only [hinv] using
      summable_weighted_projections Q source_haar_base_gt_one (hr i)
  rw [← (Summable.tsum_finsetSum (fun i _ => hs i))]
  congr 1
  apply tsum_congr
  intro j
  rw [Finset.mul_sum]

/-- The complete full-response history controls the exchanged residual's weak Haar energy.
The extended sum retains all levels. -/
theorem scalar_residual_weak_history_bound (Q : TriadicCube 2) (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient (openCubeSet Q))
    (F : HilbertBlockL2 (openCubeSet Q)) :
    ENNReal.ofReal (∑ i,dualEnergy Q sourceHaarBase (fun x =>
      (scalarCoefficientFlux (responseFramePlanarCoefficientField ν σ k)
        (scalarResidualField Q ν σ hν hσ k F) x).1 i)) ≤
    completeFullResponseHistory Q (responseFramePlanarCoefficientField ν σ k)*
      ENNReal.ofReal (cubeAverage Q (fun x => blockVecDot (scalarResidualField Q ν σ hν hσ k F x)
        (scalarCoefficientFlux (responseFramePlanarCoefficientField ν σ k)
          (scalarResidualField Q ν σ hν hσ k F) x))) := by
  let a := responseFramePlanarCoefficientField ν σ k
  let Z : Vec 2 → BlockVec 2 := scalarResidualField Q ν σ hν hσ k F
  let r : Vec 2 → Vec 2 := fun x => (scalarCoefficientFlux a Z x).1
  let E : ℝ := cubeAverage Q (fun x => blockVecDot (Z x) (scalarCoefficientFlux a Z x))
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) ν σ hν hσ k
  have hflux := scalar_coefficient_flux_memL2 Q a hEll (Lp.memLp (scalarResidualField Q ν σ hν hσ k F))
  have hr (i : Fin 2) : MemLp (fun x => r x i) 2 (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On (Homogenization.memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hflux) i)
  have hinv : sourceHaarBase⁻¹=inverseHistoryDiscount := inverse_history_discount_eq.symm
  have hα : 0 ≤ inverseHistoryDiscount := inverse_history_discount_range.1.le
  have h1 : 0 ≤ 1-inverseHistoryDiscount := sub_nonneg.mpr inverse_history_discount_range.2.le
  have hseries : Summable (fun j : ℕ => inverseHistoryDiscount^j *
      ∑ i,energy Q (cubeProjection Q j (fun x => r x i))) := by
    simp_rw [Finset.mul_sum]
    apply summable_sum
    intro i _
    simpa only [hinv] using
      summable_weighted_projections Q source_haar_base_gt_one (hr i)
  have henergy : 0 ≤ E := by
    dsimp [E]
    rw [cubeAverage_eq_integralAverage_openCubeSet]
    simpa [integralAverage, volumeAverage, volume_openCubeSet_toReal] using
      (scalar_coefficient_energy_average_nonneg Q a hEll Z)
  have hweak := vector_weak_energy_abel Q r hr
  have hpoint (j : ℕ) :
      (∑ i,energy Q (cubeProjection Q j (fun x => r x i))) ≤ fullResponseDepthMax Q a j * E := by
    dsimp [E,r,Z,a]
    exact scalar_residual_projection_energy_bound Q ν σ hν hσ k F j
  rw [hweak,ENNReal.ofReal_mul h1,
    ENNReal.ofReal_tsum_of_nonneg
      (fun j => mul_nonneg (pow_nonneg hα _) (Finset.sum_nonneg (fun i _ => energy_nonneg Q _))) hseries]
  unfold completeFullResponseHistory
  let C : ℝ≥0∞ := ENNReal.ofReal (1-inverseHistoryDiscount)
  have hsum :
      (∑' j,ENNReal.ofReal (inverseHistoryDiscount^j *
        ∑ i,energy Q (cubeProjection Q j (fun x => r x i)))) ≤
      ∑' j,ENNReal.ofReal (inverseHistoryDiscount^j *
        fullResponseDepthMax Q a j) * ENNReal.ofReal E := by
    apply ENNReal.tsum_le_tsum
    intro j
    have hterm : inverseHistoryDiscount^j *
        (∑ i,energy Q (cubeProjection Q j (fun x => r x i))) ≤
        inverseHistoryDiscount^j * (fullResponseDepthMax Q a j * E) :=
      mul_le_mul_of_nonneg_left (hpoint j) (pow_nonneg hα j)
    have hmul : ENNReal.ofReal (inverseHistoryDiscount^j *
        (fullResponseDepthMax Q a j * E)) =
        ENNReal.ofReal (inverseHistoryDiscount^j * fullResponseDepthMax Q a j) * ENNReal.ofReal E := by
      rw [show inverseHistoryDiscount^j * (fullResponseDepthMax Q a j * E) =
        (inverseHistoryDiscount^j * fullResponseDepthMax Q a j) * E by ring,
        ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hα j) (full_response_depth_max_nonneg Q a j))]
    rw [← hmul]
    exact ENNReal.ofReal_le_ofReal hterm
  calc
    C * (∑' j,ENNReal.ofReal (inverseHistoryDiscount^j *
        ∑ i,energy Q (cubeProjection Q j (fun x => r x i)))) ≤
      C * (∑' j,ENNReal.ofReal (inverseHistoryDiscount^j *
        fullResponseDepthMax Q a j) * ENNReal.ofReal E) := by
      calc
        _ = (∑' j,ENNReal.ofReal (inverseHistoryDiscount^j *
            ∑ i,energy Q (cubeProjection Q j (fun x => r x i)))) * C := by rw [mul_comm]
        _ ≤ (∑' j,ENNReal.ofReal (inverseHistoryDiscount^j *
            fullResponseDepthMax Q a j) * ENNReal.ofReal E) * C := mul_le_mul_left hsum C
        _ = _ := by rw [mul_comm]
    _ = C * ((∑' j,ENNReal.ofReal (inverseHistoryDiscount^j * fullResponseDepthMax Q a j)) * ENNReal.ofReal E) := by
      rw [ENNReal.tsum_mul_right]
    _ = completeFullResponseHistory Q a * ENNReal.ofReal E := by
      dsimp [C,completeFullResponseHistory]
      rw [mul_assoc]

end ASDExplicitGamma.Scalar
