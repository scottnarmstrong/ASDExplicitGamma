module

public import ASDExplicitGamma.Scalar.UpperCellEnergyBandKernel
public import ASDExplicitGamma.Gaussian.SupMeanKernelMeanIncrement

/-! Full-band increment traces from the physical weak-kernel estimates. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Gaussian Model
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped BigOperators RealInnerProductSpace
noncomputable section

/-- The exact weighted derivative-variance sum before spatial scaling. -/
def upperCellBandVariance {b : ℕ} (M : ABKModel 2) (h : ℝ)
    (k : Fin b → ℤ) (w : Fin b → ℝ) (r : ℕ) : ℝ :=
  ∑ i,w i^2*(h^2*(3:ℝ)^(2*M.gamma*(k i:ℝ))/((3:ℝ)^(k i))^(2*r))

/-- Physical band covariance is nonnegative for arbitrary deterministic weights. -/
theorem upper_cell_band_variance_nonneg {b : ℕ} (M : ABKModel 2) (h : ℝ)
    (k : Fin b → ℤ) (w : Fin b → ℝ) (r : ℕ) :
    0 ≤ upperCellBandVariance M h k w r := by
  unfold upperCellBandVariance
  positivity

/-- A single nonzero weight gives positive variance at every derivative order.
This discharges the structural nondegeneracy input of physical band chaining. -/
theorem upper_cell_band_variance_pos {b : ℕ} (M : ABKModel 2) (h : ℝ) (hh : 0 < h)
    (k : Fin b → ℤ) (w : Fin b → ℝ) (r : ℕ) (j : Fin b) (hj : w j ≠ 0) :
    0 < upperCellBandVariance M h k w r := by
  apply Finset.sum_pos'
  · intro i _
    positivity
  · exact ⟨j,Finset.mem_univ _,mul_pos (sq_pos_of_ne_zero hj) (by positivity)⟩

/-- Orthogonality of physical shell white-noise slots gives an exact sum
of squared increment norms in the full-band kernel. -/
theorem upper_cell_band_kernel_difference_norm {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (k : Fin b → ℤ) (w : Fin b → ℝ)
    (o : Q3SpatialJet) (x y : Vec 2) :
    ‖upperCellBandKernel M h k w o y-upperCellBandKernel M h k w o x‖^2 =
      ∑ i,w i^2*‖supMeanShellJetKernel M h (k i) o y-supMeanShellJetKernel M h (k i) o x‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i _
  change ‖w i • supMeanShellJetKernel M h (k i) o y-
    w i • supMeanShellJetKernel M h (k i) o x‖^2 = _
  rw [← smul_sub,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]

/-- The tensor trace commutes with the finite direct-sum shell trace. -/
theorem upper_cell_band_kernel_increment_trace_sum {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (k : Fin b → ℤ) (w : Fin b → ℝ)
    {ι : Type} [Fintype ι] (o : ι → Q3SpatialJet) (x y : Vec 2) :
    (∑ a,‖upperCellBandKernel M h k w (o a) y-upperCellBandKernel M h k w (o a) x‖^2) =
      ∑ i,w i^2*∑ a,‖supMeanShellJetKernel M h (k i) (o a) y-
        supMeanShellJetKernel M h (k i) (o a) x‖^2 := by
  simp_rw [upper_cell_band_kernel_difference_norm]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

/-- The full-band gradient increment trace has the exact tau_2/2 factor. -/
theorem upper_cell_band_first_increment_trace {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (k : Fin b → ℤ) (w : Fin b → ℝ) (x y : Vec 2) :
    (∑ a : Fin 2,‖upperCellBandKernel M h k w (.first a) y-
      upperCellBandKernel M h k w (.first a) x‖^2) ≤
      (waveTau2/2)*upperCellBandVariance M h k w 2*((y-x) 0^2+(y-x) 1^2) := by
  rw [upper_cell_band_kernel_increment_trace_sum]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left
      (supMean_kernel_first_increment_trace (supMeanShellKernelAmplitude M h (k i))
        (supMeanShellKernelLength (k i)) x y) (sq_nonneg (w i)))
  change (∑ i,w i^2*∑ a : Fin 2,‖supMeanShellJetKernel M h (k i) (.first a) y-
    supMeanShellJetKernel M h (k i) (.first a) x‖^2) ≤ _ at hh
  refine hh.trans_eq ?_
  simp only [supMean_shell_kernel_amplitude_sq,supMeanShellKernelLength,upperCellBandVariance,
    Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  norm_num only [Nat.reduceMul]
  ring

/-- The full-band Hessian increment trace uses tau_3/2 from the third weak
kernel, without a third-derivative assumption on the random field. -/
theorem upper_cell_band_second_increment_trace {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (k : Fin b → ℤ) (w : Fin b → ℝ) (x y : Vec 2) :
    (∑ a : Fin 2 × Fin 2,‖upperCellBandKernel M h k w (.second a.1 a.2) y-
      upperCellBandKernel M h k w (.second a.1 a.2) x‖^2) ≤
      (waveTau3/2)*upperCellBandVariance M h k w 3*((y-x) 0^2+(y-x) 1^2) := by
  rw [upper_cell_band_kernel_increment_trace_sum]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left
      (supMean_kernel_second_increment_trace (supMeanShellKernelAmplitude M h (k i))
        (supMeanShellKernelLength (k i)) x y) (sq_nonneg (w i)))
  change (∑ i,w i^2*∑ a : Fin 2 × Fin 2,‖supMeanShellJetKernel M h (k i) (.second a.1 a.2) y-
    supMeanShellJetKernel M h (k i) (.second a.1 a.2) x‖^2) ≤ _ at hh
  refine hh.trans_eq ?_
  simp only [supMean_shell_kernel_amplitude_sq,supMeanShellKernelLength,upperCellBandVariance,
    Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  norm_num only [Nat.reduceMul]
  ring

end
end ASDExplicitGamma.Scalar
