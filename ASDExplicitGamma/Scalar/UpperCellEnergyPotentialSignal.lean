module

public import ASDExplicitGamma.Scalar.UpperCellEnergyPotentialVariance
public import ASDExplicitGamma.Scalar.UpperCellEnergySignal

/-! Identification of the genuine projected finite-band variance with the
frozen signal. The shell index is allowed to be negative. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Probability.Stationary Algsuperdiff.Section3.Provider.Corrector
noncomputable section

/-- The frozen prefix variance gains exactly the next shell variance. -/
theorem upper_cell_variance_increment (h gamma : ℝ) (hg : 0 < gamma) (n : ℤ) :
    shellVarianceSum h gamma (n+1)-shellVarianceSum h gamma n =
      h^2*(3:ℝ)^(2*gamma*((n+1:ℤ):ℝ)) := by
  have hd : 1-(3:ℝ)^(-(2*gamma)) ≠ 0 := ne_of_gt (sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)))
  have ht : (3:ℝ)^(2*gamma)*(3:ℝ)^(-(2*gamma)) = 1 := by
    rw [←Real.rpow_add (by norm_num : (0:ℝ)<3),add_neg_cancel,Real.rpow_zero]
  have he : 2*gamma*((n+1:ℤ):ℝ) = 2*gamma*(n:ℝ)+2*gamma := by push_cast; ring
  simp only [shellVarianceSum,he,Real.rpow_add (by norm_num : (0:ℝ)<3)]
  field_simp [hd]
  linear_combination h^2 * ht

/-- The actual finite band is the difference of the two frozen prefix variances. -/
theorem upper_cell_variance_band_sum
    (h gamma : ℝ) (hg : 0 < gamma) (n : ℤ) (height : ℕ) :
    h^2 * ∑ k ∈ Finset.Ioc n (n+height), (3:ℝ)^(2*gamma*(k:ℝ)) =
      shellVarianceSum h gamma (n+height)-shellVarianceSum h gamma n := by
  rw [←upper_cell_physical_band_sum' n height
    (fun k => (3:ℝ)^(2*gamma*(k:ℝ))),Finset.mul_sum]
  have he (i : Fin height) : h^2*(3:ℝ)^(2*gamma*(upperCellPhysicalBandLabel n height i:ℝ)) =
      shellVarianceSum h gamma (n+(i.val:ℤ)+1)-shellVarianceSum h gamma (n+(i.val:ℤ)) := by
    rw [upper_cell_variance_increment h gamma hg]
    have hl : upperCellPhysicalBandLabel n height i = n+(i.val:ℤ)+1 := by
      simp only [upperCellPhysicalBandLabel,Nat.cast_add,Nat.cast_one,add_assoc]
    rw [hl]
  simp_rw [he]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    shellVarianceSum h gamma (n+(j:ℤ)+1)-shellVarianceSum h gamma (n+(j:ℤ)))]
  have hs := Finset.sum_range_sub (fun j : ℕ => shellVarianceSum h gamma (n+(j:ℤ))) height
  simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,add_zero,add_assoc] using hs

/-- The normalized actual potential correction has exactly the source signal
variance, before taking any cell average. -/
theorem upper_cell_potential_variance_signal
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) {e : Vec 2} (he : Book.Ch02.vecNorm e = 1) :
    ‖-stationaryPotentialProjection (upperCellResetBandForcing M n (n+height)
      (Annealed.sigmaBar M n:ℝ)⁻¹ e)‖^2 =
      (shellVarianceSum h M.gamma (n+height)-shellVarianceSum h M.gamma n)/
        (2*(Annealed.sigmaBar M n:ℝ)^2) := by
  rw [upper_cell_potential_variance M h hM n (n+height) _ he]
  have hs := upper_cell_variance_band_sum h M.gamma M.shellPrefix.gamma_pos n height
  rw [←hs]
  ring

/-- The actual source-block correction meets the variance gate using only the
completed left endpoint state. -/
theorem upper_cell_potential_variance_gate
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (hg : M.gamma ≤ gammaZero) (hstate : nativeInductionState M h n)
    {e : Vec 2} (he : Book.Ch02.vecNorm e = 1) :
    ‖-stationaryPotentialProjection (upperCellResetBandForcing M n
      (n+(⌊(17/50:ℝ)/M.gamma⌋.toNat:ℕ)) (Annealed.sigmaBar M n:ℝ)⁻¹ e)‖^2 < (9/10:ℝ) := by
  have hfloor : 0 ≤ ⌊(17/50:ℝ)/M.gamma⌋ := Int.floor_nonneg.mpr
    (div_nonneg (by norm_num) M.shellPrefix.gamma_pos.le)
  rw [upper_cell_potential_variance_signal M h hM n _ he,Int.toNat_of_nonneg hfloor]
  exact upper_cell_sigmaBar_signal_le M h n hg hstate

end
end ASDExplicitGamma.Scalar
