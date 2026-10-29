module

public import ASDExplicitGamma.Gaussian.SupMeanShellSupremum
public import ASDExplicitGamma.Gaussian.SupMeanNormalization

/-! Exact GA-SUP-MEAN unit-variance normalization, with rho=side/shell length. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 MeasureTheory
noncomputable section

/-- The unit-amplitude derivative tensor uses L^r/B times the actual stored
physical r-th tensor. Its observation square has dimensionless side rho=s/L. -/
def supMeanShellUnitSquareTensor (M : ABKModel 2) (h : ℝ) (k : ℤ) (r : ℕ)
    {ι : Type} [Fintype ι] (o : ι → Q3SpatialJet) (c : Vec 2) (s : ℝ) (j : ShellField 2) :
    C(supMeanClosedSquare c s,EuclideanSpace ℝ ι) :=
  (((3:ℝ)^k)^r/supMeanShellKernelAmplitude M h k) • supMeanShellSquareTensor o c s j

/-- Exact tensor norm scaling, including the zero-amplitude total convention. -/
theorem supMean_shell_unit_square_norm (M : ABKModel 2) (h : ℝ) (k : ℤ) (r : ℕ)
    {ι : Type} [Fintype ι] (o : ι → Q3SpatialJet) (c : Vec 2) (s : ℝ) (j : ShellField 2) :
    ‖supMeanShellUnitSquareTensor M h k r o c s j‖ =
      (((3:ℝ)^k)^r/supMeanShellKernelAmplitude M h k)*‖supMeanShellSquareTensor o c s j‖ := by
  unfold supMeanShellUnitSquareTensor
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg]
  exact div_nonneg (by positivity) (Real.sqrt_nonneg _)

/-- A frozen q3 Gaussian shell has strictly positive physical amplitude. -/
theorem supMean_shell_kernel_amplitude_pos (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : ℤ) : 0 < supMeanShellKernelAmplitude M h k := by
  unfold supMeanShellKernelAmplitude
  apply Real.sqrt_pos.mpr
  have hh := hM.1
  positivity

/-- The exact source first-tensor mean, normalized to unit covariance amplitude
and unit shell coordinates. The only spatial factor is rho=s/3^k. -/
theorem supMean_shell_unit_first_supremum_mean (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : ℤ) (c : Vec 2) (s : ℝ) (hs : 0 < s) :
    Integrable (fun j => ‖supMeanShellUnitSquareTensor M h k 1 Q3SpatialJet.first c s j‖)
      (ShellField.shellMarginalLaw M.P k).toMeasure ∧
    (∫ j, ‖supMeanShellUnitSquareTensor M h k 1 Q3SpatialJet.first c s j‖
      ∂(ShellField.shellMarginalLaw M.P k).toMeasure) ≤
        Real.sqrt waveTau1+(s/(3:ℝ)^k)*(Real.sqrt waveTau2/2+2*Real.sqrt (Real.log 2)*waveEll2) := by
  obtain ⟨hi,hb⟩ := supMean_shell_first_supremum_mean M h hM k c s hs
  let L : ℝ := (3:ℝ)^k
  let B := supMeanShellKernelAmplitude M h k
  let V := h^2*(3:ℝ)^(2*M.gamma*(k:ℝ))
  have hL : 0 < L := by dsimp only [L]; positivity
  have hB : 0 < B := supMean_shell_kernel_amplitude_pos M h hM k
  have hBsq : B^2 = V := supMean_shell_kernel_amplitude_sq M h k
  have hT : 0 ≤ waveTau1 := by norm_num [waveTau1, waveMu1, waveR1]
  have hbase : Real.sqrt (waveTau1*(V/L^2)) = (B/L)*Real.sqrt waveTau1 := by
    rw [← hBsq]
    exact supMean_sqrt_variance_scale _ _ _ hT hB.le hL
  have hnext : Real.sqrt (V/L^4) = B/L^2 := by
    rw [← hBsq, show L^4 = (L^2)^2 by ring]
    exact supMean_sqrt_variance_quotient B (L^2) hB.le (by positivity)
  simp only [supMean_shell_unit_square_norm, pow_one]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul]
  calc
    _ ≤ (L/B)*(Real.sqrt (waveTau1*(V/L^2))+
      (s*Real.sqrt (V/L^4))*(Real.sqrt waveTau2/2+2*Real.sqrt (Real.log 2)*waveEll2)) :=
      mul_le_mul_of_nonneg_left hb (div_pos hL hB).le
    _ = _ := by
      rw [hbase,hnext]
      change _ = Real.sqrt waveTau1+(s/L)*(Real.sqrt waveTau2/2+2*Real.sqrt (Real.log 2)*waveEll2)
      field_simp [hL.ne',hB.ne']

/-- The exact source second-tensor mean, with rho=s/3^k and the third weak
covariance constants. No random C3-shell assumption occurs. -/
theorem supMean_shell_unit_second_supremum_mean (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : ℤ) (c : Vec 2) (s : ℝ) (hs : 0 < s) :
    Integrable (fun j => ‖supMeanShellUnitSquareTensor M h k 2
      (fun i : Fin 2 × Fin 2 => .second i.1 i.2) c s j‖) (ShellField.shellMarginalLaw M.P k).toMeasure ∧
    (∫ j, ‖supMeanShellUnitSquareTensor M h k 2 (fun i : Fin 2 × Fin 2 => .second i.1 i.2) c s j‖
      ∂(ShellField.shellMarginalLaw M.P k).toMeasure) ≤
        Real.sqrt waveTau2+(s/(3:ℝ)^k)*(Real.sqrt waveTau3/2+2*Real.sqrt (Real.log 2)*waveEll3) := by
  obtain ⟨hi,hb⟩ := supMean_shell_second_supremum_mean M h hM k c s hs
  let L : ℝ := (3:ℝ)^k
  let B := supMeanShellKernelAmplitude M h k
  let V := h^2*(3:ℝ)^(2*M.gamma*(k:ℝ))
  have hL : 0 < L := by dsimp only [L]; positivity
  have hB : 0 < B := supMean_shell_kernel_amplitude_pos M h hM k
  have hBsq : B^2 = V := supMean_shell_kernel_amplitude_sq M h k
  have hT : 0 ≤ waveTau2 := by norm_num [waveTau2, waveMu2, waveR1, waveR2]
  have hbase : Real.sqrt (waveTau2*(V/L^4)) = (B/L^2)*Real.sqrt waveTau2 := by
    rw [← hBsq, show L^4 = (L^2)^2 by ring]
    exact supMean_sqrt_variance_scale _ _ _ hT hB.le (by positivity)
  have hnext : Real.sqrt (V/L^6) = B/L^3 := by
    rw [← hBsq, show L^6 = (L^3)^2 by ring]
    exact supMean_sqrt_variance_quotient B (L^3) hB.le (by positivity)
  simp only [supMean_shell_unit_square_norm]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul]
  calc
    _ ≤ (L^2/B)*(Real.sqrt (waveTau2*(V/L^4))+
      (s*Real.sqrt (V/L^6))*(Real.sqrt waveTau3/2+2*Real.sqrt (Real.log 2)*waveEll3)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by
      rw [hbase,hnext]
      change _ = Real.sqrt waveTau2+(s/L)*(Real.sqrt waveTau3/2+2*Real.sqrt (Real.log 2)*waveEll3)
      field_simp [hL.ne',hB.ne']

end
end ASDExplicitGamma.Gaussian
