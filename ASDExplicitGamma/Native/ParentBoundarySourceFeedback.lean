module

public import ASDExplicitGamma.Native.ParentBoundarySourceBudget
public import ASDExplicitGamma.Native.OldSignedCompleteCellFeedback
public import ASDExplicitGamma.Native.OldSignedReciprocalLoadBudget

/-! Complete derivative-only feedback of the actual four-load parent
source lifts. The source and reciprocal fields keep their common cells. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main ASDExplicitGamma.Response ASDExplicitGamma.Variational
noncomputable section

private theorem square_summable_component {I A : Type*} [Fintype A]
    (f : I → A → ℝ) (hs : Summable (fun n => ∑ a : A,f n a^2)) (a : A) :
    Summable (fun n => f n a^2) := by
  apply hs.of_nonneg_of_le (fun _ => sq_nonneg _)
  intro n
  exact Finset.single_le_sum (f := fun a : A => f n a^2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ a)

/-- The complete source feedback retains the exact cellwise inverse
history and reciprocal-gradient budget; all convergence is discharged. -/
theorem parent_boundary_cell_source_feedback (Q U : TriadicCube 2) (depth : ℕ)
    (hU : U ∈ descendantsAtDepth Q depth)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    let a := responseFramePlanarCoefficientField nu sigma k
    let kU := oldSignedCellCoefficient Q U hsub k
    let R := fun n c => oldSignedCellResidual Q U hsub nu sigma hnu hsigma k
      (parentBoundaryOldSource Q nu sigma hnu hsigma k b L n (blockBasis c))
      (parent_boundary_old_source_memL2 Q nu sigma hnu hsigma k b L n (blockBasis c))
    let f := fun n => ∑ c : BlockCoord 2,oldSignedEnergyPairing U nu sigma kU
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis c))
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n)) (R n c))
    Summable f ∧ |∑' n,f n|≤oldSignedDerivativeKappa (cubeScaleFactor U) b L.1*
      (Real.sqrt 2+oldSignedReciprocalErrorSize Q U nu sigma hnu hsigma k)*
      ((1+inverseHistoryDiscount)*oldSignedInverseHistory U a*
        parentBoundaryCellSourceSize Q U nu sigma hnu hsigma k b L) := by
  intro hsub a kU R f
  let F := fun n c => parentBoundaryOldSource Q nu sigma hnu hsigma k b L n (blockBasis c)
  have hF (n : whiteBasisIndex) (c : BlockCoord 2) : MemBlockL2 (openCubeSet Q) (F n c) :=
    parent_boundary_old_source_memL2 Q nu sigma hnu hsigma k b L n (blockBasis c)
  let v := fun n c => parentBoundaryCellSourcePotential Q U hsub nu sigma hnu hsigma k b L n (blockBasis c)
  have hbudget := parent_boundary_cell_source_budget Q U depth hU nu sigma hnu hsigma k b L
  have hK : Summable (fun n => ∑ c : BlockCoord 2,vectorWeakHaarNorm U (v n c).toH1Function.grad^2) :=
    hbudget.2.2.1
  have hv (c : BlockCoord 2) : Summable (fun n => vectorWeakHaarNorm U (v n c).toH1Function.grad^2) :=
    square_summable_component (fun n c => vectorWeakHaarNorm U (v n c).toH1Function.grad) hK c
  have hh := old_signed_complete_cell_correction_feedback Q U hsub nu sigma hnu hsigma k blockBasis b L F hF hv
  have hz (n : whiteBasisIndex) (c : BlockCoord 2) :
      oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n)) (F n c)=0 := by
    funext x
    change (0,-(_ • matVecMul responsePlanarJ 0))=(0,0)
    rw [matVecMul_zero,smul_zero,neg_zero]
  let fc := fun n => ∑ c : BlockCoord 2,oldSignedEnergyPairing U nu sigma kU
    (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis c))
    (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
      ((R n c : Vec 2 → BlockVec 2)-F n c))
  have hfc : fc=f := by
    funext n
    apply Finset.sum_congr rfl
    intro c _
    rw [map_sub,hz,sub_zero]
  have hresult : Summable fc ∧ |∑' n,fc n|≤oldSignedDerivativeKappa (cubeScaleFactor U) b L.1*
      Real.sqrt (∑ c : BlockCoord 2,vectorWeakHaarNorm U
        (oldSignedCellReciprocalPotential Q U hsub nu sigma hnu hsigma k (blockBasis c)).grad^2)*
      Real.sqrt (∑ c : BlockCoord 2,∑' n,vectorWeakHaarNorm U (v n c).toH1Function.grad^2) := hh
  rw [hfc,←Summable.tsum_finsetSum (fun c _ => hv c)] at hresult
  have hg := old_signed_actual_reciprocal_load_budget Q U hsub nu sigma hnu hsigma k
  have hκ := old_signed_derivative_kappa_nonneg (Triadic.cubeScaleFactor_pos' U).le b L.1
  exact ⟨hresult.1,hresult.2.trans (mul_le_mul (mul_le_mul_of_nonneg_left hg hκ) hbudget.2.2.2
    (Real.sqrt_nonneg _) (mul_nonneg hκ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))))⟩

end
end ASDExplicitGamma.Native
