module

public import ASDExplicitGamma.Scalar.OldHessianTrialFullModeColumns

/-! Qualitative cell convergence follows from the genuine positive spatial series. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- A nonnegative physical spatial series controls each actual cell's
series. The finite cardinal is used only for qualitative convergence. -/
theorem old_hessian_cell_series_of_average {I : Type*} (Q : TriadicCube 2) (fine : ℕ)
    (f : I → OldSignedCellIndex Q fine → ℝ) (hn : ∀ p U,0≤f p U)
    (hs : Summable (fun p => oldSignedCellAverage Q fine (f p))) (U : OldSignedCellIndex Q fine) :
    Summable (fun p => f p U) := by
  let d : ℝ := (descendantsAtDepth Q fine).card
  have hd : d≠0 := ne_of_gt (show 0<d by
    dsimp only [d]
    exact_mod_cast Finset.card_pos.mpr (descendantsAtDepth_nonempty Q fine))
  have hb (p) : f p U≤d*oldSignedCellAverage Q fine (f p) := by
    calc
      _ ≤ ∑ V,f p V := Finset.single_le_sum (fun V _ => hn p V) (Finset.mem_univ U)
      _ = _ := by
        unfold oldSignedCellAverage
        change _=d*(d⁻¹*_)
        rw [←mul_assoc,mul_inv_cancel₀ hd,one_mul]
  exact (hs.mul_left d).of_nonneg_of_le (fun p => hn p U) hb

/-- Every actual mixed source has complete positive-energy convergence on
each unchanged fine cell, derived before applying any projection feedback. -/
theorem old_hessian_full_source_cell_series (n : ℤ) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n))) (b : ℝ) (L : {l : ℝ // 0<l})
    (U : OldSignedCellIndex (originCube 2 n) (coarse+1)) :
    Summable (fun p => vectorPositiveHaarEnergy U.val
      (oldHessianFullModeColumn (originCube 2 n) coarse nu sigma hnu hsigma k b L p)) := by
  have hs := old_hessian_full_mode_series n coarse nu sigma hnu hsigma k b L
  exact old_hessian_cell_series_of_average (originCube 2 n) (coarse+1)
    (fun p U => vectorPositiveHaarEnergy U.val
      (oldHessianFullModeColumn (originCube 2 n) coarse nu sigma hnu hsigma k b L p))
    (fun _ U => vectorPositiveHaarEnergy_nonneg U.val _) hs.1 U

end
end ASDExplicitGamma.Scalar
