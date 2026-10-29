module

public import ASDExplicitGamma.Scalar.OldHessianTrialCellDirectionalWeights
public import ASDExplicitGamma.Native.OldSignedFlatProfileCaps

/-! The original finite-parent minus means pay the complete affine receiver. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Original finite-parent minus-flat cell mean, retaining both physical
load columns and every actual white mode. -/
def oldHessianMinusMeanColumn (Q : TriadicCube 2) (fine : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (p : whiteBasisIndex×Fin 2) (U : OldSignedCellIndex Q fine) : Vec 2 :=
  (oldSignedBlockMean U.val (oldSignedFlatMinusBlock Q b L p.1 p.2)).1

/-- The complete original minus-mode means are square summable and their
actual spatial mean-square budget is at most the physical variance b². -/
theorem old_hessian_minus_mean_bank (Q : TriadicCube 2) (fine : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    Summable (fun p : whiteBasisIndex×Fin 2 => oldSignedCellAverage Q fine
      (fun U => vecNormSq (oldHessianMinusMeanColumn Q fine b L p U))) ∧
      (∑' p : whiteBasisIndex×Fin 2,oldSignedCellAverage Q fine
        (fun U => vecNormSq (oldHessianMinusMeanColumn Q fine b L p U)))≤b^2 := by
  let V := fun (p : whiteBasisIndex×Fin 2) (U : OldSignedCellIndex Q fine) =>
    oldSignedBlockMean U.val (oldSignedFlatMinusBlock Q b L p.1 p.2)
  let F := fun (p : whiteBasisIndex×Fin 2) (U : OldSignedCellIndex Q fine) => blockVecDot (V p U) (V p U)
  let G := fun (p : whiteBasisIndex×Fin 2) (U : OldSignedCellIndex Q fine) => vecNormSq (V p U).1
  have hF0 (p) (U) : 0≤F p U := add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _)
  have hG0 (p) (U) : 0≤G p U := vecNormSq_nonneg _
  have hGF (p) (U) : G p U≤F p U := le_add_of_nonneg_right (vecNormSq_nonneg _)
  have hFs (U : OldSignedCellIndex Q fine) : Summable (fun p => F p U) := by
    apply (summable_prod_of_nonneg (fun p => hF0 p U)).2
    refine ⟨fun _ => Summable.of_finite,?_⟩
    simpa only [tsum_fintype,oldSignedFlatInput,Bool.false_eq_true,ite_false,F,V] using
      old_signed_flat_mean_budget_series Q fine b L false U.val U.property
  have hGs (U : OldSignedCellIndex Q fine) : Summable (fun p => G p U) :=
    (hFs U).of_nonneg_of_le (fun p => hG0 p U) (fun p => hGF p U)
  have havg := old_signed_cell_average_series Q fine G hGs
  refine ⟨havg.1,?_⟩
  change (∑' p,oldSignedCellAverage Q fine (G p))≤b^2
  rw [havg.2]
  have hmean (U : OldSignedCellIndex Q fine) : (∑' p,G p U)≤oldSignedFlatMeanSize Q U.val b L false^2 := by
    have hh := (hGs U).tsum_le_tsum (fun p => hGF p U) (hFs U)
    have he : (∑' p,F p U)=oldSignedFlatMeanSize Q U.val b L false^2 := by
      rw [(hFs U).tsum_prod]
      simp only [tsum_fintype]
      simpa only [oldSignedFlatInput,Bool.false_eq_true,ite_false,F,V] using
        (old_signed_flat_mean_size_sq Q U.val b L false).symm
    exact hh.trans_eq he
  have hh := old_signed_cell_average_mono Q fine hmean
  have hle := old_signed_cell_average_mono Q fine (fun U =>
    pow_le_pow_left₀ (Real.sqrt_nonneg _) (old_signed_flat_mean_size_le_l2 Q fine b L false U.val U.property) 2)
  apply (hh.trans hle).trans
  rw [old_signed_cell_average_eq_descendantsAverage Q fine (fun U => oldSignedFlatL2Size Q U b L false^2)]
  exact old_signed_flat_minus_partition_l2_cap Q fine b L

end
end ASDExplicitGamma.Scalar
