module

public import ASDExplicitGamma.Gaussian.WaveGateMeanPolynomial

/-! Rational majorants for the depth-fourteen full-band envelope constants. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Gaussian
noncomputable section

/-- The physical depth-fourteen side ratio is far below one percent. -/
theorem upper_cell_depth_ratio_le :
    (0:ℝ) ≤ (3:ℝ)^(-14:ℤ) ∧ (3:ℝ)^(-14:ℤ) ≤ 1/100 := by
  norm_num

/-- Coarse rational root bounds suffice for the certified 64 sensitivity cap. -/
theorem upper_cell_tensor_root_constants :
    Real.sqrt waveTau1 ≤ 8 ∧ Real.sqrt waveTau2 ≤ 64 ∧
    Real.sqrt waveTau3 ≤ 1000 ∧ waveEll1 ≤ 6 ∧ waveEll2 ≤ 44 ∧ waveEll3 ≤ 1000 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    try dsimp only [waveEll1, waveEll2, waveEll3]
    apply Real.sqrt_le_iff.mpr
    constructor <;> norm_num [waveTau1, waveTau2, waveTau3, waveMu1, waveMu2, waveMu3,
      waveR1, waveR2, waveR3]

/-- Uniform mean coefficient on every side ratio up to one percent. -/
theorem upper_cell_wave_mean_small_ratio {d : ℝ} (hd : 0 ≤ d) (hd1 : d ≤ 1/100) :
    waveMeanAt d ≤ 11 := by
  have ht := upper_cell_tensor_root_constants
  have hl : Real.sqrt (Real.log 2) ≤ 1 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by norm_num, ?_⟩
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh ⊢
    exact hh
  have he2 : 2*Real.sqrt (Real.log 2)*waveEll2 ≤ 88 := by
    have hh := mul_le_mul hl ht.2.2.2.2.1 (Real.sqrt_nonneg _)
      (by norm_num : (0:ℝ)≤1)
    linarith only [hh]
  have he3 : 2*Real.sqrt (Real.log 2)*waveEll3 ≤ 2000 := by
    have hh := mul_le_mul hl ht.2.2.2.2.2 (Real.sqrt_nonneg _)
      (by norm_num : (0:ℝ)≤1)
    linarith only [hh]
  have hb2 : (3/2:ℝ)*Real.sqrt waveTau2+2*Real.sqrt (Real.log 2)*waveEll2 ≤ 184 := by
    linarith only [ht.2.1, he2]
  have hb3 : Real.sqrt waveTau3/2+2*Real.sqrt (Real.log 2)*waveEll3 ≤ 2500 := by
    linarith only [ht.2.2.1, he3]
  have h1 := mul_le_mul_of_nonneg_left hb2 hd
  have h2 := mul_le_mul_of_nonneg_left hb3 (sq_nonneg d)
  have hd2 := pow_le_pow_left₀ hd hd1 2
  unfold waveMeanAt
  linarith only [ht.1,h1,h2,hd1,hd2]

/-- Uniform combined CM coefficient on the same side-ratio interval. -/
theorem upper_cell_wave_cm_small_ratio {d : ℝ} (hd : 0 ≤ d) (hd1 : d ≤ 1/100) :
    waveEllAt d ≤ 7 := by
  have ht := upper_cell_tensor_root_constants
  have hh := mul_le_mul_of_nonneg_left ht.2.2.2.2.1 hd
  unfold waveEllAt
  linarith only [ht.2.2.2.1, hh, hd1]

/-- The full p=6 mean/fluctuation payment lies strictly below 64 squared. -/
theorem upper_cell_envelope_six_constant :
    2*(waveMeanAt ((3:ℝ)^(-14:ℤ)))^2 +
      12*(waveEllAt ((3:ℝ)^(-14:ℤ)))^2 ≤ 64^2 := by
  have hd := upper_cell_depth_ratio_le
  have hm := pow_le_pow_left₀ (wave_mean_at_pos hd.1).le
    (upper_cell_wave_mean_small_ratio hd.1 hd.2) 2
  have he := pow_le_pow_left₀ (wave_ell_at_pos hd.1).le
    (upper_cell_wave_cm_small_ratio hd.1 hd.2) 2
  linarith only [hm,he]

end
end ASDExplicitGamma.Scalar
