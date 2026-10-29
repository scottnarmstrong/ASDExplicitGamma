module

public import ASDExplicitGamma.Scalar.OldHessianTrialCellSeriesExtraction
public import ASDExplicitGamma.Scalar.OldHessianTrialFirstFeedback

/-! Complete actual fine first-corrector energy for the mixed source. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The genuine first corrector of the actual mixed source on one original fine cell. -/
def oldHessianMixedCellFirstPotential (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (p : whiteBasisIndex×Fin 2) (U : OldSignedCellIndex Q (coarse+1)) : H10Function (openCubeSet U.val) :=
  oldSignedCellFirstCorrector Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
    nu sigma hnu hsigma k
    (oldHessianMixedBottomSource Q coarse (coarse+1) nu sigma hnu hsigma k b L p.1 p.2)
    (old_hessian_mixed_bottom_source_memL2 Q coarse (coarse+1) nu sigma hnu hsigma k b L p.1 p.2)

/-- Both actual bottom mixed first-corrector families have genuine complete
weak-energy convergence and the sharp Df times original inverse-history root bound. -/
theorem old_hessian_mixed_cell_first_series (n : ℤ) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n))) (b : ℝ) (L : {l : ℝ // 0<l})
    (U : OldSignedCellIndex (originCube 2 n) (coarse+1)) :
    let Q := originCube 2 n
    let v := fun p => oldHessianMixedCellFirstPotential Q coarse nu sigma hnu hsigma k b L p U
    let E := fun p => vectorPositiveHaarEnergy U.val (oldHessianFullModeColumn Q coarse nu sigma hnu hsigma k b L p)
    (∀ i : Fin 2,Summable (fun j : whiteBasisIndex => vectorWeakHaarNorm U.val (v (j,i)).toH1Function.grad^2)) ∧
    Real.sqrt (∑ i : Fin 2,∑' j : whiteBasisIndex,vectorWeakHaarNorm U.val (v (j,i)).toH1Function.grad^2)≤
      ((63/50:ℝ)*oldSignedInverseHistory U.val (responseFramePlanarCoefficientField nu sigma k))*Real.sqrt (∑' p,E p) := by
  intro Q v E
  let C := (63/50:ℝ)*oldSignedInverseHistory U.val (responseFramePlanarCoefficientField nu sigma k)
  let g := fun p => vectorWeakHaarNorm U.val (v p).toH1Function.grad^2
  have hC : 0≤C := mul_nonneg (by norm_num) (lemmaVInverseHistory_nonneg U.val _
    (Real.one_lt_rpow (by norm_num) (by norm_num)))
  have hs := old_hessian_full_source_cell_series n coarse nu sigma hnu hsigma k b L U
  have hbound (p : whiteBasisIndex×Fin 2) : g p≤C^2*E p := by
    have hh := old_hessian_actual_mixed_first_feedback n coarse (coarse+1)
      nu sigma hnu hsigma k b L p.1 p.2 U.val U.property
    have hcolumn : oldHessianFullModeColumn Q coarse nu sigma hnu hsigma k b L p=
        (fun x => (oldHessianMixedBottomSource Q coarse (coarse+1) nu sigma hnu hsigma k b L p.1 p.2 x).2) := rfl
    have hEp : E p=(vectorPositiveHaarNorm U.val (oldHessianFullModeColumn Q coarse nu sigma hnu hsigma k b L p))^2 :=
      (Real.sq_sqrt (vectorPositiveHaarEnergy_nonneg U.val _)).symm
    rw [hEp,hcolumn]
    exact (pow_le_pow_left₀ (Real.sqrt_nonneg _) hh 2).trans_eq (mul_pow _ _ 2)

  have hgs : Summable g := (hs.mul_left (C^2)).of_nonneg_of_le (fun _ => sq_nonneg _) hbound
  have hfixed (i : Fin 2) : Summable (fun j : whiteBasisIndex => g (j,i)) :=
    hgs.comp_injective (show Function.Injective (fun j : whiteBasisIndex => (j,i)) from by
      intro x y hxy
      exact congrArg Prod.fst hxy)
  have hsum : (∑ i : Fin 2,∑' j : whiteBasisIndex,g (j,i))=∑' p,g p := by
    rw [←Summable.tsum_finsetSum (fun i _ => hfixed i)]
    simpa only [tsum_fintype] using hgs.tsum_prod.symm
  refine ⟨hfixed,?_⟩
  change Real.sqrt (∑ i : Fin 2,∑' j : whiteBasisIndex,g (j,i))≤_
  rw [hsum]
  have hh := Real.sqrt_le_sqrt (hgs.tsum_le_tsum hbound (hs.mul_left (C^2)))
  rw [tsum_mul_left,Real.sqrt_mul (sq_nonneg C),Real.sqrt_sq hC] at hh
  exact hh

end
end ASDExplicitGamma.Scalar
