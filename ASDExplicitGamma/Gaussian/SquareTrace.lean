module

public import ASDExplicitGamma.Gaussian.SquareMinimizer
public import ASDExplicitGamma.Variational.CubeOpen
public import ASDExplicitGamma.Variational.LemmaVTrace

/-! The literal full trace and its four physical loads on any triadic square. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Variational
open scoped BigOperators
noncomputable section

local instance squareTraceFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The literal normalized trace defect on the specified translated square. -/
def squareTrace (Q : TriadicCube 2) (ν σ : ℝ) :
    ResponseCoefficient (openCubeSet Q) → ℝ :=
  fun k => traceDefect (cubeSet Q) (responseFramePlanarCoefficientField ν σ k) 1

/-- One of the four physical affine-load energies on that same square. -/
def squareLoadEnergy (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (p : Fin 2 × Bool) : ResponseCoefficient (openCubeSet Q) → ℝ :=
  responseFrameEnergyObservable (measurableSet_openCubeSet Q) (square_volume_pos Q)
    ν σ hν hσ (orthonormalFrameLoad p.1 (lemmaVLoadSign p.2))

theorem square_traceDefect_eq_sum_load_defects (Q : TriadicCube 2) {a : CoeffField 2}
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) :
    traceDefect (cubeSet Q) a 1 =
      ∑ i : Fin 2,
        ((2 * Mu (cubeSet Q) (orthonormalFrameLoad i 1) a - 1) +
          (2 * Mu (cubeSet Q) (orthonormalFrameLoad i (-1)) a - 1)) := by
  have hload (i : Fin 2) (ε : ℝ) (hε : ε ^ 2 = 1) :
      2 * Mu (cubeSet Q) (orthonormalFrameLoad i ε) a =
        ((coarseBlockMatrix (cubeSet Q) a).upperLeft i i +
          (coarseBlockMatrix (cubeSet Q) a).lowerRight i i +
          ε * ((coarseBlockMatrix (cubeSet Q) a).upperRight i i +
            (coarseBlockMatrix (cubeSet Q) a).lowerLeft i i)) / 2 := by
    rw [mu_eq_half_coarseBlockMatrix_elliptic_triCube hlam hEll]
    have h := orthonormalFrameLoad_energy
      (coarseBlockMatrix (cubeSet Q) a) 1 i ε hε
    simpa [frameMatrix] using h
  simp_rw [hload _ 1 (by norm_num), hload _ (-1) (by norm_num)]
  simp [traceDefect, Matrix.trace, Fin.sum_univ_two]
  ring

theorem squareTrace_eq_load_sum (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) :
    squareTrace Q ν σ k = (∑ p : Fin 2 × Bool, squareLoadEnergy Q ν σ hν hσ p k) - 4 := by
  let U := openCubeSet Q
  let a := responseFramePlanarCoefficientField ν σ k
  let hv := square_volume_pos Q
  have hEllO := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) ν σ hν hσ k
  have hE (P : BlockVec 2) :
      responseFrameEnergyObservable (measurableSet_openCubeSet Q) hv ν σ hν hσ P k =
        2 * Mu U P a := by
    rw [lemmaV_observable_eq_twice_muCandidate, ← lemmaV_responseSystem_eq_canonical]
    congr 1
    exact lemmaV_canonical_muCandidate_eq_Mu (isOpenBoundedConvexDomain_openCubeSet Q) hEllO hv P
  have hEll := lemmaV_frameCoefficient_isEllipticOn (measurableSet_cubeSet Q) ν σ hν hσ k
  have ht := square_traceDefect_eq_sum_load_defects Q (div_pos hν hσ) hEll
  simp_rw [Mu_cubeSet_eq_openCubeSet_of_triadicCube] at ht
  dsimp only [U, a, hv] at hE
  simp_rw [← hE] at ht
  unfold squareTrace
  rw [ht]
  simp [squareLoadEnergy, Fintype.sum_prod_type, lemmaVLoadSign,
    Fin.sum_univ_two]
  ring

end
end ASDExplicitGamma.Gaussian
