module

public import ASDExplicitGamma.Scalar.LocalProjectionOrthogonality
public import ASDExplicitGamma.Scalar.CellEnergyCauchy

/-! The full physical coarse response controls every cell mean of the exchanged residual. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response MeasureTheory

/-- Every constant doubled load tests the actual global residual with the exact local coarse quadratic cost. -/
theorem scalar_residual_cell_pairing_bound (Q R : TriadicCube 2) (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient (openCubeSet Q))
    (F : HilbertBlockL2 (openCubeSet Q)) (P : BlockVec 2) :
    (volumeAverage (openCubeSet R) (fun x => blockVecDot P
      (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField ν σ k) x)
        (scalarResidualField Q ν σ hν hσ k F x))))^2 ≤
    volumeAverage (openCubeSet R) (fun x => blockVecDot (scalarResidualField Q ν σ hν hσ k F x)
      (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField ν σ k) x)
        (scalarResidualField Q ν σ hν hσ k F x)))*
      blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet R) (responseFramePlanarCoefficientField ν σ k)) P) := by
  let a := responseFramePlanarCoefficientField ν σ k
  have hEll := (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) ν σ hν hσ k).mono
    (measurableSet_openCubeSet R) hRQ
  let Z : Vec 2 → BlockVec 2 := scalarResidualField Q ν σ hν hσ k F
  let S := scalarCellResponseTest R a hEll P
  let finiteResidualCellVolume : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
    (isOpenBoundedConvexDomain_openCubeSet R).isFiniteMeasure_restrict_volume
  have hZ : MemBlockL2 (openCubeSet R) Z :=
    (Lp.memLp (scalarResidualField Q ν σ hν hσ k F)).mono_measure
      (Measure.restrict_mono_set volume hRQ)
  have hS := scalar_cell_response_test_memL2 R a hEll P
  have hp : MemBlockL2 (openCubeSet R) (fun _ : Vec 2 => P) := memLp_const P
  have hpair := scalar_residual_local_orthogonal Q R hRQ ν σ hν hσ k F _
    (scalar_cell_response_test_variation R a hEll P)
  let stateZ : BlockState 2 := ⟨fun x => (Z x).1,fun x => (Z x).2⟩
  let stateP : BlockState 2 := ⟨fun _ => P.1,fun _ => P.2⟩
  have hsInt := blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn hS
    (show MemBlockL2 (openCubeSet R) stateZ.eval from hZ) hEll
  have hpInt := blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
    (show MemBlockL2 (openCubeSet R) stateP.eval from hp)
    (show MemBlockL2 (openCubeSet R) stateZ.eval from hZ) hEll
  change IntegrableOn (fun x => blockVecDot (S.eval x)
    (blockMatVecMul (blockCoeffField a x) (Z x))) (openCubeSet R) at hsInt
  change IntegrableOn (fun x => blockVecDot P
    (blockMatVecMul (blockCoeffField a x) (Z x))) (openCubeSet R) at hpInt
  have he : (fun x => blockVecDot ((scalarCellResponseTest R a hEll P).eval x-P)
      (blockMatVecMul (blockCoeffField a x) (Z x)))=
      (fun x => blockVecDot (S.eval x) (blockMatVecMul (blockCoeffField a x) (Z x)))-
      (fun x => blockVecDot P (blockMatVecMul (blockCoeffField a x) (Z x))) := by
    funext x
    simp [blockVecDot,vecDot,Fin.sum_univ_two]
    ring
  change volumeAverage (openCubeSet R) (fun x => blockVecDot ((scalarCellResponseTest R a hEll P).eval x-P)
    (blockMatVecMul (blockCoeffField a x) (Z x)))=0 at hpair
  rw [he,volumeAverage_sub hsInt hpInt] at hpair
  have hh := scalar_cell_field_cauchy R a hEll hZ hS
  have hePair := sub_eq_zero.mp hpair
  rw [hePair] at hh
  have hE := scalar_cell_response_test_energy R a hEll P
  change volumeAverage (openCubeSet R) (fun x => blockVecDot (S.eval x)
    (blockMatVecMul (blockCoeffField a x) (S.eval x)))=_ at hE
  rw [hE] at hh
  exact hh

end ASDExplicitGamma.Scalar
