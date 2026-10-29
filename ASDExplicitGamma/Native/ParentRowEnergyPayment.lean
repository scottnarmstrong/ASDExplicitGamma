module

public import ASDExplicitGamma.Native.ParentRowWeightedFields

/-! Payment of the literal parent Dirichlet energy by its exact source field. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Algsuperdiff.Section3
noncomputable section

/-- Each shell retains its own geometric energy weight in the exact stored Y field. -/
theorem parent_row_actual_dirichlet_energy
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (j : Fin 16) :
    parentBoundaryBandDirichletEnergy M h n (j.val+1)≤
      theta M*(parentRowFields j).getD 16 0 := by
  apply le_trans _ (parent_row_actual_y_weighted_variance M h hg n hstate j)
  unfold parentBoundaryBandDirichletEnergy
  apply Finset.sum_le_sum
  intro i _
  have hi := parent_boundary_model_dirichlet_clock n (i.val+1)
    (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
  apply hi.trans_eq
  simp only [parentRowYWeight,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,Rat.cast_pow,Rat.cast_one]
  ring

end
end ASDExplicitGamma.Native
