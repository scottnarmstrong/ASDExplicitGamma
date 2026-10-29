module

public import ASDExplicitGamma.Scalar.UpperCellEnergyBandEnvelope
public import ASDExplicitGamma.Scalar.UpperCellEnergyDerivativeVariance

/-! Literal normalized future-band labels and covariance on the physical cell. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Gaussian Model
open Algsuperdiff.Section3
open scoped BigOperators
noncomputable section

/-- The future band consists of exactly n+1,...,n+height. -/
def upperCellPhysicalBandLabel (n : ℤ) (height : ℕ) (i : Fin height) : ℤ :=
  n + ((i.val + 1 : ℕ) : ℤ)

/-- Distinct physical shells remain distinct in the finite-band Gaussian family. -/
theorem upper_cell_physical_band_label_injective (n : ℤ) (height : ℕ) :
    Function.Injective (upperCellPhysicalBandLabel n height) := by
  intro i j hij
  apply Fin.ext
  dsimp only [upperCellPhysicalBandLabel] at hij
  omega

/-- Normalizing by the OLD sigma gives exactly the covariance sum already
bounded using the completed OLD lower corridor. -/
theorem upper_cell_physical_band_variance_eq
    (M : ABKModel 2) (h : ℝ) (n : ℤ) (height r : ℕ) :
    upperCellBandVariance M h (upperCellPhysicalBandLabel n height)
      (fun _ => (Annealed.sigmaBar M n : ℝ)⁻¹) r =
      ∑ j ∈ Finset.Ico 1 (height+1),
        (h^2*(3:ℝ)^(2*M.gamma*((n+(j:ℤ):ℤ):ℝ))/(Annealed.sigmaBar M n:ℝ)^2)*
          (3:ℝ)^(-2*(r:ℝ)*((n+(j:ℤ):ℤ):ℝ)) := by
  unfold upperCellBandVariance upperCellPhysicalBandLabel
  dsimp only
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    (Annealed.sigmaBar M n : ℝ)⁻¹^2 *
      (h^2*(3:ℝ)^(2*M.gamma*((n+((j+1:ℕ):ℤ):ℤ):ℝ)) /
        ((3:ℝ)^(n+((j+1:ℕ):ℤ)))^(2*r))) height,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm 1]
  apply Finset.sum_congr rfl
  intro j _
  have hp : (((3:ℝ)^(n+((j+1:ℕ):ℤ)))^(2*r))⁻¹ =
      (3:ℝ)^(-2*(r:ℝ)*((n+((j+1:ℕ):ℤ):ℤ):ℝ)) := by
    rw [← Real.rpow_intCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ)≤3),
      ← Real.rpow_neg (by norm_num : (0:ℝ)≤3)]
    congr 1
    push_cast
    ring
  simp only [div_eq_mul_inv, inv_pow]
  rw [← inv_pow, hp]
  ring

/-- Exact physical scaling of the actual full-band covariance. -/
theorem upper_cell_physical_band_variance_le
    (M : ABKModel 2) (h : ℝ) (n : ℤ) (hg : M.gamma ≤ gammaZero)
    (hstate : nativeInductionState M h n) (r height : ℕ) (hr : 1 ≤ r) :
    (3:ℝ)^(2*(r:ℝ)*((n:ℝ)-14))*
      upperCellBandVariance M h (upperCellPhysicalBandLabel n height)
        (fun _ => (Annealed.sigmaBar M n : ℝ)⁻¹) r ≤
      M.gamma*(3:ℝ)^(-28*(r:ℝ)) := by
  rw [upper_cell_physical_band_variance_eq]
  exact upper_cell_band_derivative_variance_le M h n hg hstate r height hr


/-- Positive variance for every derivative order of a nonempty physical band. -/
theorem upper_cell_physical_band_variance_pos
    (M : ABKModel 2) (h : ℝ) (hh : 0 < h) (n : ℤ) (height r : ℕ)
    (hhgt : 0 < height) :
    0 < upperCellBandVariance M h (upperCellPhysicalBandLabel n height)
      (fun _ => (Annealed.sigmaBar M n : ℝ)⁻¹) r := by
  exact upper_cell_band_variance_pos M h hh _ _ r ⟨0, hhgt⟩
    (inv_ne_zero (ne_of_gt (Annealed.sigmaBar M n).property))

/-- The physical side powers agree exactly with the real-power covariance scale. -/
theorem upper_cell_physical_scale_power (z : ℤ) (r : ℕ) :
    ((3:ℝ)^z)^(2*r) = (3:ℝ)^(2*(r:ℝ)*(z:ℝ)) := by
  rw [← Real.rpow_intCast, ← Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3)]
  congr 1
  push_cast
  ring

/-- The covariance square root is taken only after the entire physical band has
been summed. This is the scale bound used by the compact envelope. -/
theorem upper_cell_physical_band_root_variance_le
    (M : ABKModel 2) (h : ℝ) (n : ℤ) (hg : M.gamma ≤ gammaZero)
    (hstate : nativeInductionState M h n) (r height : ℕ) (hr : 1 ≤ r) :
    ((3:ℝ)^(n-14))^r * Real.sqrt (upperCellBandVariance M h
      (upperCellPhysicalBandLabel n height)
        (fun _ => (Annealed.sigmaBar M n : ℝ)⁻¹) r) ≤
      Real.sqrt M.gamma * ((3:ℝ)^(-14:ℤ))^r := by
  have hV := upper_cell_band_variance_nonneg M h
    (upperCellPhysicalBandLabel n height)
    (fun _ => (Annealed.sigmaBar M n : ℝ)⁻¹) r
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt hV, Real.sq_sqrt M.shellPrefix.gamma_pos.le,
    ← pow_mul, ← pow_mul]
  rw [Nat.mul_comm r 2, upper_cell_physical_scale_power,
    upper_cell_physical_scale_power]
  push_cast
  convert upper_cell_physical_band_variance_le M h n hg hstate r height hr using 1
  congr 2
  ring

end
end ASDExplicitGamma.Scalar
