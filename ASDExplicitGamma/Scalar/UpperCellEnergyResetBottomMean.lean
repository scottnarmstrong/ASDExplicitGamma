module

public import ASDExplicitGamma.Scalar.UpperCellEnergyResetFrame
public import ASDExplicitGamma.Scalar.CellResidualMean

/-! Bottom-component mean estimate for the full physical RESET residual. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response MeasureTheory

/-- Constant bottom loads read the literal normalized bottom-field mean. -/
theorem upper_cell_reset_bottom_pairing_mean (Q : TriadicCube 2) {G : Vec 2 → BlockVec 2}
    (hG : MemBlockL2 (openCubeSet Q) G) (e : Vec 2) :
    volumeAverage (openCubeSet Q) (fun x => blockVecDot (0,e) (G x))=
      vecDot e (fun i => cubeAverage Q (fun x => (G x).2 i)) := by
  have hi (i : Fin 2) : IntegrableOn (fun x => (G x).2 i) (openCubeSet Q) :=
    ((Homogenization.memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hG) i).integrable (by norm_num))
  simp only [blockVecDot,zero_add,vecDot,Pi.zero_apply,zero_mul,Finset.sum_const_zero]
  rw [volumeAverage_sum Finset.univ (fun i x => e i*(G x).2 i) (fun i _ => (hi i).const_mul (e i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [cubeAverage_eq_integralAverage_openCubeSet]
  exact volumeAverage_smul (openCubeSet Q) (e i) (fun x => (G x).2 i)

/-- The exact local mean of the exchanged residual costs at most the full physical response norm. -/
theorem upper_cell_reset_bottom_cell_mean (Q R : TriadicCube 2) (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient (openCubeSet Q))
    (F : HilbertBlockL2 (openCubeSet Q)) :
    vecNormSq (fun i => cubeAverage R (fun x =>
      (scalarCoefficientFlux (responseFramePlanarCoefficientField ν σ k)
        (scalarResidualField Q ν σ hν hσ k F) x).2 i)) ≤
    fullResponseOperatorNorm R (responseFramePlanarCoefficientField ν σ k)*
      volumeAverage (openCubeSet R) (fun x => blockVecDot (scalarResidualField Q ν σ hν hσ k F x)
        (scalarCoefficientFlux (responseFramePlanarCoefficientField ν σ k)
          (scalarResidualField Q ν σ hν hσ k F) x)) := by
  let a := responseFramePlanarCoefficientField ν σ k
  let Z : Vec 2 → BlockVec 2 := scalarResidualField Q ν σ hν hσ k F
  let r : Vec 2 := fun i => cubeAverage R (fun x => (scalarCoefficientFlux a Z x).2 i)
  let E := volumeAverage (openCubeSet R) (fun x => blockVecDot (Z x) (scalarCoefficientFlux a Z x))
  have hEll := (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) ν σ hν hσ k).mono
    (measurableSet_openCubeSet R) hRQ
  have hZ : MemBlockL2 (openCubeSet R) Z :=
    (Lp.memLp (scalarResidualField Q ν σ hν hσ k F)).mono_measure (Measure.restrict_mono_set volume hRQ)
  have hFlux := scalar_coefficient_flux_memL2 R a hEll hZ
  have hp := scalar_residual_cell_pairing_bound Q R hRQ ν σ hν hσ k F (0,r)
  have hmean := upper_cell_reset_bottom_pairing_mean R hFlux r
  change volumeAverage (openCubeSet R) (fun x => blockVecDot (0,r) (scalarCoefficientFlux a Z x))=vecNormSq r at hmean
  change (volumeAverage (openCubeSet R) (fun x => blockVecDot (0,r) (scalarCoefficientFlux a Z x)))^2 ≤
    E*blockVecDot (0,r) (blockMatVecMul (coarseBlockMatrix (cubeSet R) a) (0,r)) at hp
  rw [hmean] at hp
  have hE : 0 ≤ E := by
    apply mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
    by_cases hz : Z x=0
    · change 0 ≤ blockVecDot (Z x) (blockMatVecMul (blockMatrixOfCoeff (a x)) (Z x))
      rw [hz]
      simp [blockVecDot,vecDot]
    · exact (blockMatrixOfCoeff_quadratic_pos_of_isEllipticMatrix (hEll.2 x hx) hz).le
  have hquad : blockVecDot (0,r) (blockMatVecMul (coarseBlockMatrix (cubeSet R) a) (0,r)) ≤
      fullResponseOperatorNorm R a*vecNormSq r := by
    simpa only [fullResponseOperatorNorm,blockVecDot,vecDot_zero_left,zero_add,vecNormSq]
      using block_quadratic_le_operator_norm (coarseBlockMatrix (cubeSet R) a) (0,r)
  have hupper := mul_le_mul_of_nonneg_left hquad hE
  have hbound := hp.trans hupper
  change vecNormSq r ≤ fullResponseOperatorNorm R a*E
  by_cases hz : vecNormSq r=0
  · rw [hz]
    exact mul_nonneg (full_response_operator_norm_nonneg R a) hE
  · have hr : 0 < vecNormSq r := lt_of_le_of_ne (vecNormSq_nonneg r) (Ne.symm hz)
    nlinarith only [hbound,hr]

end ASDExplicitGamma.Scalar
