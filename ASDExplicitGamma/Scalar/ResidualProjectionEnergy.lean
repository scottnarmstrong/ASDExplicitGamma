module

public import ASDExplicitGamma.Scalar.FullResponseHistory
public import ASDExplicitGamma.Triadic.PoincareCell

/-! Exact depthwise projection-energy bound by the complete physical response maximum. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response Variational MeasureTheory Triadic

/-- The vector projection energy is exactly the cell-mean square average. -/
theorem vector_projection_energy_eq_means (Q : TriadicCube 2) (j : ℕ) (r : Vec 2 → Vec 2)
    (hr : ∀ i,MemLp (fun x => r x i) 2 (normalizedCubeMeasure Q)) :
    (∑ i,energy Q (cubeProjection Q j (fun x => r x i)))=
      descendantsAverage Q j (fun R => vecNormSq (fun i => cubeAverage R (fun x => r x i))) := by
  simp_rw [← pairing_projection_energy Q j (hr _),pairing_projection_right Q j _ (hr _)]
  simp only [descendantsAverage,vecNormSq,vecDot]
  rw [← Finset.mul_sum,Finset.sum_comm]

/-- Every projected exchanged-field level is controlled by the actual full-response depth maximum. -/
theorem scalar_residual_projection_energy_bound (Q : TriadicCube 2) (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient (openCubeSet Q))
    (F : HilbertBlockL2 (openCubeSet Q)) (j : ℕ) :
    (∑ i,energy Q (cubeProjection Q j (fun x =>
      (scalarCoefficientFlux (responseFramePlanarCoefficientField ν σ k)
        (scalarResidualField Q ν σ hν hσ k F) x).1 i))) ≤
    fullResponseDepthMax Q (responseFramePlanarCoefficientField ν σ k) j*
      cubeAverage Q (fun x => blockVecDot (scalarResidualField Q ν σ hν hσ k F x)
        (scalarCoefficientFlux (responseFramePlanarCoefficientField ν σ k)
          (scalarResidualField Q ν σ hν hσ k F) x)) := by
  let a := responseFramePlanarCoefficientField ν σ k
  let Z : Vec 2 → BlockVec 2 := scalarResidualField Q ν σ hν hσ k F
  let r : Vec 2 → Vec 2 := fun x => (scalarCoefficientFlux a Z x).1
  let E : Vec 2 → ℝ := fun x => blockVecDot (Z x) (scalarCoefficientFlux a Z x)
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) ν σ hν hσ k
  have hZ := Lp.memLp (scalarResidualField Q ν σ hν hσ k F)
  have hFlux := scalar_coefficient_flux_memL2 Q a hEll hZ
  have hr (i : Fin 2) : MemLp (fun x => r x i) 2 (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On (Homogenization.memScalarL2_coord_of_memVectorL2
      (memVectorL2_fst_of_memBlockL2 hFlux) i)
  have hInt : IntegrableOn E (cubeSet Q) volume := integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr
    (scalar_coefficient_energy_integrable Q a hEll hZ)
  change (∑ i,energy Q (cubeProjection Q j (fun x => r x i))) ≤ fullResponseDepthMax Q a j*cubeAverage Q E
  rw [vector_projection_energy_eq_means Q j r hr,
    cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q j E hInt]
  have hpoint (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q j) :
      vecNormSq (fun i => cubeAverage R (fun x => r x i)) ≤ fullResponseDepthMax Q a j*cubeAverage R E := by
    have hsub := openCubeSet_subset_of_mem_descendantsAtDepth hR
    have hm := scalar_residual_cell_mean_bound Q R hsub ν σ hν hσ k F
    change vecNormSq (fun i => cubeAverage R (fun x => r x i)) ≤
      fullResponseOperatorNorm R a * integralAverage (openCubeSet R) E at hm
    rw [← cubeAverage_eq_integralAverage_openCubeSet] at hm
    apply hm.trans
    apply mul_le_mul_of_nonneg_right (full_response_norm_le_depth_max Q R a j hR)
    rw [cubeAverage_eq_integralAverage_openCubeSet]
    exact scalar_coefficient_energy_average_nonneg R a (hEll.mono (measurableSet_openCubeSet R) hsub) Z
  unfold descendantsAverage
  calc
    _ ≤ ((descendantsAtDepth Q j).card:ℝ)⁻¹*∑ R ∈ descendantsAtDepth Q j,
        fullResponseDepthMax Q a j*cubeAverage R E :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpoint) (by positivity)
    _ = _ := by rw [← Finset.mul_sum];ring

end ASDExplicitGamma.Scalar
