module

public import ASDExplicitGamma.Scalar.OldHessianTrialMeanCovariancePairing
public import ASDExplicitGamma.Native.OldSignedDualReflection

/-! Actual local TOP reciprocal fields and their rotated pairing carriers. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section

/-- The original coefficient's local TOP reciprocal map at an arbitrary
constant load, represented by the genuine complementary minimizer. -/
def oldHessianCellTopReciprocal (Q U : TriadicCube 2) (hU : openCubeSet U⊆openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) : Vec 2 → Vec 2 :=
  let kU := oldSignedCellCoefficient Q U hU k
  let S := oldSignedFrameCanonicalField U nu sigma hnu hsigma kU (e,0)
  fun x => (oldSignedDualReflection U nu sigma kU S x).1

theorem old_hessian_cell_top_reciprocal_memLp (Q U : TriadicCube 2)
    (hU : openCubeSet U⊆openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) (i : Fin 2) :
    MemLp (fun x => oldHessianCellTopReciprocal Q U hU nu sigma hnu hsigma k e x i)
      2 (normalizedCubeMeasure U) := by
  have hh := old_signed_dual_reflection_memL2 U nu sigma hnu hsigma
    (oldSignedCellCoefficient Q U hU k)
    (Lp.memLp (oldSignedFrameCanonicalField U nu sigma hnu hsigma (oldSignedCellCoefficient Q U hU k) (e,0)))
  exact memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hh) i)

/-- Spatial quarter turn preserves the actual receiver's square membership. -/
theorem old_hessian_cell_top_reciprocal_rotate_memLp (Q U : TriadicCube 2)
    (hU : openCubeSet U⊆openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) (i : Fin 2) :
    MemLp (fun x => planarQuarterTurn (oldHessianCellTopReciprocal Q U hU nu sigma hnu hsigma k e x) i)
      2 (normalizedCubeMeasure U) := by
  fin_cases i
  · change MemLp (fun x => -oldHessianCellTopReciprocal Q U hU nu sigma hnu hsigma k e x 1)
      2 (normalizedCubeMeasure U)
    exact (old_hessian_cell_top_reciprocal_memLp Q U hU nu sigma hnu hsigma k e 1).neg
  · change MemLp (fun x => oldHessianCellTopReciprocal Q U hU nu sigma hnu hsigma k e x 0)
      2 (normalizedCubeMeasure U)
    exact old_hessian_cell_top_reciprocal_memLp Q U hU nu sigma hnu hsigma k e 0

end
end ASDExplicitGamma.Scalar
