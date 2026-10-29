module

public import ASDExplicitGamma.Scalar.OldHessianTrialIntegratedFrozenSplit

/-! Complete signed frozen covariance on the actual cell carrier. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section

/-- Complete physical white covariance, with its negative principal and
retained finite-parent error after integration. No signed contraction is assumed. -/
theorem old_hessian_frozen_cell_contraction (Q : TriadicCube 2) (fine : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (U : TriadicCube 2) (hU : U∈descendantsAtDepth Q fine)
    (z : Fin 2 → Vec 2 → Vec 2) (T : Vec 2 → Mat 2)
    (hz : ∀ i k,MemLp (fun x => z i x k) 2 (normalizedCubeMeasure U))
    (hT : ∀ i j,MemLp (fun x => T x i j) 2 (normalizedCubeMeasure U)) (lam : ℝ) :
    HasSum (fun j : whiteBasisIndex => 2*lam*(∑ i : Fin 2,cubeAverage U (fun x =>
      vecDot ((cubeAverage U (q3Convolution b L h3Zero (whiteBasis j))) •
        matVecMul responsePlanarJ (z i x))
        (matVecMul (T x) (oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L j i)).1))))
      (-lam*b^2*(∑ i : Fin 2,cubeAverage U (fun x => vecDot (z i x)
        (matVecMul responsePlanarJ (matVecMul (T x) (matVecMul responsePlanarJ (basisVec i))))))-
       2*lam*(∑ i : Fin 2,cubeAverage U (fun x => vecDot (z i x)
        (matVecMul responsePlanarJ (matVecMul (T x)
          (matVecMul (oldHessianMeanCovarianceError Q U b L) (basisVec i))))))) := by
  have hJz (i k : Fin 2) : MemLp (fun x => matVecMul responsePlanarJ (z i x) k) 2 (normalizedCubeMeasure U) := by
    fin_cases k
    · simpa [matVecMul,responsePlanarJ,Fin.sum_univ_two,Pi.neg_def] using (hz i 1).neg
    · simpa [matVecMul,responsePlanarJ,Fin.sum_univ_two] using hz i 0
  have hh := old_hessian_integrated_mean_covariance_hasSum Q fine b L U hU
    (fun i x => matVecMul responsePlanarJ (z i x)) T hJz hT lam
  rw [old_hessian_mean_covariance_split] at hh
  rw [old_hessian_integrated_frozen_split U z T (oldHessianMeanCovarianceError Q U b L)
    (b^2) lam hz hT] at hh
  exact hh

end
end ASDExplicitGamma.Scalar
