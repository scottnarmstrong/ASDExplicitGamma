module

public import ASDExplicitGamma.Gaussian.NormalScaledMoments

/-! Exact even auxiliary Gaussian moments and the source raw factor 255. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory ProbabilityTheory ASDExplicitGamma.Gaussian
open scoped ENNReal NNReal Nat
noncomputable section

/-- The individual Gaussian factor in the VHEAT augmentation is the exact
odd double factorial to the power 1/k, rather than a generic Gaussian cap. -/
theorem nativeHeat_standardGaussian_even_norm_sq (k : ℕ) (hk : 1 ≤ k) :
    (eLpNorm (id : ℝ → ℝ) (ENNReal.ofReal (2 * (k : ℝ))) (gaussianReal 0 1)).toReal ^ 2 =
      Real.rpow ((2*k-1)‼ : ℝ) ((k : ℝ)⁻¹) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hp : 0 < 2 * (k : ℝ) := by positivity
  have hmem := memLp_id_gaussianReal' (μ := 0) (v := 1) (ENNReal.ofReal (2*(k:ℝ))) ENNReal.ofReal_ne_top
  rw [rio_lpNorm_sq hp hmem]
  have he : rioMoment (gaussianReal 0 1) (2*(k:ℝ)) id =
      ∫ x : ℝ, x^(2*k) ∂gaussianReal 0 1 := by
    apply integral_congr_ae
    filter_upwards with x
    change |x| ^ (2*(k:ℝ)) = x^(2*k)
    rw [show 2*(k:ℝ)=((2*k:ℕ):ℝ) by push_cast; rfl, Real.rpow_natCast]
    rw [pow_mul,sq_abs,pow_mul]
  rw [he,normal_even_moment_eq_doubleFactorial k hk]
  have hexp : 2/(2*(k:ℝ))=(k:ℝ)⁻¹ := by field_simp
  rw [hexp]
  exact (Real.rpow_eq_pow _ _).symm

/-- Fixing the target degree in the even-moment recurrence gives the sharp
simple factor 2k-1. At k=128 this is exactly the raw VHEAT factor 255. -/
theorem nativeHeat_standardGaussian_even_norm_sq_le_odd (k : ℕ) (hk : 1 ≤ k) :
    (eLpNorm (id : ℝ → ℝ) (ENNReal.ofReal (2*(k:ℝ))) (gaussianReal 0 1)).toReal ^ 2 ≤
      2*(k:ℝ)-1 := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hbase : 0 < 2*(k:ℝ)-1 := by
    have h : (1:ℝ)≤k := by exact_mod_cast hk
    linarith
  have hmoment (j : ℕ) (hj : j ≤ k) :
      (∫ x : ℝ, x^(2*j) ∂gaussianReal 0 1) ≤ (2*(k:ℝ)-1)^j := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [normal_even_moment_step]
      have hcoeff : (2*j+1:ℝ) ≤ 2*(k:ℝ)-1 := by
        have h : (j:ℝ)+1≤k := by exact_mod_cast hj
        linarith
      have hstep := mul_le_mul_of_nonneg_left (ih (by omega)) (by positivity : (0:ℝ)≤2*j+1)
      have hscale := mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hbase.le j)
      push_cast at hstep ⊢
      rw [pow_succ]
      nlinarith only [hstep,hscale]
  rw [nativeHeat_standardGaussian_even_norm_sq k hk]
  have hodd : (0:ℝ)≤((2*k-1)‼ : ℝ) := by positivity
  have hm : ((2*k-1)‼ : ℝ)≤(2*(k:ℝ)-1)^k := by
    rw [← normal_even_moment_eq_doubleFactorial k hk]
    exact hmoment k le_rfl
  have hh := Real.rpow_le_rpow hodd hm (inv_nonneg.mpr hkR.le)
  have he : ((2*(k:ℝ)-1)^k) ^ ((k:ℝ)⁻¹) = 2*(k:ℝ)-1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase.le, mul_inv_cancel₀ hkR.ne',Real.rpow_one]
  exact hh.trans_eq he

/-- Variance scaling keeps the exact source Gaussian factor. This includes
zero variance and never varies the molecular parameter in the coefficient. -/
theorem nativeHeat_gaussian_even_norm_sq (v : ℝ≥0) (k : ℕ) (hk : 1 ≤ k) :
    (eLpNorm (id : ℝ → ℝ) (ENNReal.ofReal (2*(k:ℝ))) (gaussianReal 0 v)).toReal ^ 2 =
      (v : ℝ) * Real.rpow ((2*k-1)‼ : ℝ) ((k:ℝ)⁻¹) := by
  let s : ℝ := Real.sqrt (v : ℝ)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hmap : eLpNorm (id : ℝ → ℝ) (ENNReal.ofReal (2*(k:ℝ))) (gaussianReal 0 v) =
      eLpNorm (fun x : ℝ => s*x) (ENNReal.ofReal (2*(k:ℝ))) (gaussianReal 0 1) := by
    rw [gaussianReal_eq_map_sqrt]
    exact eLpNorm_map_measure (by fun_prop : AEStronglyMeasurable (id : ℝ → ℝ)
      ((gaussianReal 0 1).map (fun x : ℝ => s*x))) (by fun_prop)
  have hscale : (fun x : ℝ => s*x)=s • (id : ℝ → ℝ) := by funext x; simp
  rw [hmap,hscale,eLpNorm_const_smul,Real.enorm_eq_ofReal hs, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hs,mul_pow,nativeHeat_standardGaussian_even_norm_sq k hk]
  rw [show s^2=(v:ℝ) from Real.sq_sqrt v.property]

/-- The raw auxiliary Gaussian slot of VHEAT (8) has exactly the coefficient
255 in variance units. -/
theorem nativeHeat_gaussian_raw_norm256_sq_le (v : ℝ≥0) :
    (eLpNorm (id : ℝ → ℝ) 256 (gaussianReal 0 v)).toReal ^ 2 ≤ 255*(v:ℝ) := by
  have hs := nativeHeat_standardGaussian_even_norm_sq_le_odd 128 (by norm_num)
  have hg := nativeHeat_gaussian_even_norm_sq v 128 (by norm_num)
  have hstandard := nativeHeat_standardGaussian_even_norm_sq 128 (by norm_num)
  norm_num only [Nat.cast_ofNat,ENNReal.ofReal_ofNat] at hs hg hstandard
  rw [hg,← hstandard]
  have hh := mul_le_mul_of_nonneg_left hs v.property
  norm_num at hh
  nlinarith only [hh]

end
end ASDExplicitGamma.Native
