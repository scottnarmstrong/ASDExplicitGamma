module

public import ASDExplicitGamma.Triadic.SensitivityLambda
public import ASDExplicitGamma.Variational.LemmaVMinimizer
public import ASDExplicitGamma.Response.Analytic
public import Homogenization.Book.Ch02.Theorems.DoubledMu

/-! Bridge the sensitivity response energy to the public coarse block quadratic. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Variational

noncomputable section

/-- On a triadic square, the fixed-frame response observable is the quadratic
form of the public Book coarse block matrix. -/
theorem sensitivity_response_observable_eq_coarseQuadratic
    (Q : TriadicCube 2) (ν : ℝ) (hν : 0 < ν)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    responseFrameEnergyObservable
        (measurableSet_openCubeSet Q)
        (by
          rw [volume_openCubeSet_toReal]
          exact cubeVolume_pos Q)
        ν 1 hν one_pos P k =
      blockVecDot P (blockMatVecMul
        (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
          (sensitivityBookCoeffOn Q ν hν k)) P) := by
  let U := openCubeSet Q
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  let hvol : 0 < (volume U).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  let a := responseFramePlanarCoefficientField ν 1 k
  let aBook := sensitivityBookCoeffOn Q ν hν k
  have hEll : IsEllipticFieldOn ν ((ν ^ 2 + ‖k‖ ^ 2) / ν) U a := by
    simpa [U, a, div_one] using
      responseFramePlanarCoefficientField_isElliptic
        (measurableSet_openCubeSet Q) ν 1 hν one_pos k
  have hMuCandidate :
      (responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q) hvol
        ν 1 hν one_pos k).toMuHilbertRealization.muCandidate P =
        Mu U P a := by
    simpa [U, a, responseFrameMuOperatorSystemData] using
      lemmaV_canonical_muCandidate_eq_Mu hU hEll hvol P
  have hObs : responseFrameEnergyObservable
      (measurableSet_openCubeSet Q) hvol ν 1 hν one_pos P k =
        2 * Mu U P a := by
    have hObs' : responseFrameEnergyObservable
        (measurableSet_openCubeSet Q) hvol ν 1 hν one_pos P k =
        2 * (responseFrameMuOperatorSystemData
          (measurableSet_openCubeSet Q) hvol ν 1 hν one_pos k).toMuHilbertRealization.muCandidate P := by
      simp only [responseFrameEnergyObservable, responseFrameEnergy]
      exact congrArg (fun z : ResponseCoefficient U =>
        2 * (responseFrameMuOperatorSystemData
          (measurableSet_openCubeSet Q) hvol ν 1 hν one_pos z).toMuHilbertRealization.muCandidate P)
        (zero_add k)
    rw [hObs', hMuCandidate]
  have hBookMu : Book.Ch02.doubledMu (Book.Ch02.cubeDomain Q) aBook P = Mu U P a := by
    rw [Homogenization.Internal.Ch02.BookCh02.book_doubledMu_eq_Mu]
    rfl
  calc
    responseFrameEnergyObservable
        (measurableSet_openCubeSet Q) hvol ν 1 hν one_pos P k =
        2 * Mu U P a := hObs
    _ = 2 * Book.Ch02.doubledMu (Book.Ch02.cubeDomain Q) aBook P := by
      rw [hBookMu]
    _ = blockVecDot P (blockMatVecMul
        (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) aBook) P) := by
      rw [(Book.Ch02.doubledMuTheory (Book.Ch02.cubeDomain Q) aBook).doubledMu_eq_coarseBlockMatrix P]
      ring

end

end ASDExplicitGamma.Triadic
