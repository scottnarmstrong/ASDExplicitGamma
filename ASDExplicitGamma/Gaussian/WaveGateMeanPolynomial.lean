module

public import ASDExplicitGamma.Gaussian.WaveGateConstants

/-! Exact source mean and metric polynomials at a general dimensionless side. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian

/-- The source combined gradient/Hessian mean coefficient at side ratio rho. -/
noncomputable def waveMeanAt (ρ : ℝ) : ℝ :=
  Real.sqrt waveTau1+ρ*((3/2:ℝ)*Real.sqrt waveTau2+2*Real.sqrt (Real.log 2)*waveEll2)+
    ρ^2*(Real.sqrt waveTau3/2+2*Real.sqrt (Real.log 2)*waveEll3)

/-- The source combined gradient/Hessian Cameron-Martin coefficient. -/
noncomputable def waveEllAt (ρ : ℝ) : ℝ := waveEll1+ρ*waveEll2

theorem wave_mean_at_buffer : waveMeanAt waveBufferRho = waveBufferMean := by
  unfold waveMeanAt waveBufferMean
  ring

theorem wave_ell_at_buffer : waveEllAt waveBufferRho = waveBufferEll := rfl

/-- The two separate source means assemble without replacing either constant. -/
theorem wave_mean_at_assembly (ρ : ℝ) :
    (Real.sqrt waveTau1+ρ*(Real.sqrt waveTau2/2+2*Real.sqrt (Real.log 2)*waveEll2))+
      ρ*(Real.sqrt waveTau2+ρ*(Real.sqrt waveTau3/2+2*Real.sqrt (Real.log 2)*waveEll3)) =
      waveMeanAt ρ := by unfold waveMeanAt; ring

theorem wave_mean_at_mono {ρ r : ℝ} (hρ : 0 ≤ ρ) (hr : ρ ≤ r) : waveMeanAt ρ ≤ waveMeanAt r := by
  have h1 : 0 ≤ (3/2:ℝ)*Real.sqrt waveTau2+2*Real.sqrt (Real.log 2)*waveEll2 := by
    unfold waveEll2; positivity
  have h2 : 0 ≤ Real.sqrt waveTau3/2+2*Real.sqrt (Real.log 2)*waveEll3 := by
    unfold waveEll3; positivity
  exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hr h1))
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hρ hr 2) h2)

theorem wave_ell_at_mono {ρ r : ℝ} (hr : ρ ≤ r) : waveEllAt ρ ≤ waveEllAt r :=
  add_le_add le_rfl (mul_le_mul_of_nonneg_right hr (Real.sqrt_nonneg _))

theorem wave_ell_at_pos {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 < waveEllAt ρ := by
  have h1 : 0 < waveEll1 := by norm_num [waveEll1,waveR1]
  have h2 : 0 ≤ waveEll2 := Real.sqrt_nonneg _
  exact add_pos_of_pos_of_nonneg h1 (mul_nonneg hρ h2)

theorem wave_mean_at_pos {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 < waveMeanAt ρ := by
  have ht : 0 < waveTau1 := by norm_num [waveTau1,waveMu1,waveR1]
  unfold waveMeanAt waveEll2 waveEll3
  positivity

theorem wave_buffer_mean_pos : 0 < waveBufferMean := by
  rw [← wave_mean_at_buffer]
  exact wave_mean_at_pos (by unfold waveBufferRho; positivity)

theorem wave_buffer_ell_pos : 0 < waveBufferEll := by
  rw [← wave_ell_at_buffer]
  exact wave_ell_at_pos (by unfold waveBufferRho; positivity)

end ASDExplicitGamma.Gaussian
