module

public import ASDExplicitGamma.Scalar.OldHessianTrialCenteredMixedEnergy

/-! Actual centered mixed source on each genuine fine tile, before pairing. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section

/-- The complete centered row plus genuine coarse product is square
integrable and positive-Haar finite on every fine descendant. -/
theorem old_hessian_centered_mixed_source_regular (Q : TriadicCube 2) (fine : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (v phi : H10Function (openCubeSet Q))
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth Q fine) (j : whiteBasisIndex) (k : Fin 2) :
    MemLp (fun x => oldHessianCenteredMixedSource Q fine b L v phi U j x k)
      2 (normalizedCubeMeasure U) ∧
    Summable (fun d => (Real.sqrt 3)^(d+1)*energy U (cubeIncrement U (d+1)
      (fun x => oldHessianCenteredMixedSource Q fine b L v phi U j x k))) := by
  let R := mainQ3ResidualCoordinate whiteBasis b L Q fine (v-phi).toH1Function U j
  let F := fun x => planarQuarterTurn (R x)
  let G := oldHessianCoarseProduct Q b L phi (whiteBasis j)
  have hFm (i : Fin 2) : MemLp (fun x => F x i) 2 (normalizedCubeMeasure U) := by
    fin_cases i
    · change MemLp (fun x => -R x 1) 2 (normalizedCubeMeasure U)
      exact (main_q3_residual_coordinate_memLp whiteBasis b L Q fine (v-phi).toH1Function U hU j 1).neg
    · change MemLp (fun x => R x 0) 2 (normalizedCubeMeasure U)
      exact main_q3_residual_coordinate_memLp whiteBasis b L Q fine (v-phi).toH1Function U hU j 0
  have hFp := positive_series_quarterTurn U R (old_hessian_centered_row_positive Q fine b L (v-phi) U hU j)
  have hGm (i : Fin 2) := (old_hessian_coarse_product_regular Q fine b L phi j U hU i).1
  have hGp (i : Fin 2) := (old_hessian_coarse_product_regular Q fine b L phi j U hU i).2
  have hp := (vectorPositiveHaar_add_le U F G hFm hGm hFp hGp).1
  have he : oldHessianCenteredMixedSource Q fine b L v phi U j=(fun x i => F x i+G x i) := by
    rw [old_hessian_centered_mixed_source_split]
    rfl
  rw [he]
  exact ⟨(hFm k).add (hGm k),hp k⟩

end
end ASDExplicitGamma.Scalar
