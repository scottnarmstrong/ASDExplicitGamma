module

public import ASDExplicitGamma.Inverse.StoppedDensityPE

/-! Conservative exact rational caps for the source's all-order density reduction. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

/-- The largest uniform rare-variance coefficient fits the entrance power. -/
theorem uniform_variance_coefficient :
    4*Real.sqrt ((256:ℝ)*63^2*1000000000) ≤ (3:ℝ)^20/4 := by
  have hh : Real.sqrt ((256:ℝ)*63^2*1000000000) ≤ (3:ℝ)^20/16 := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> norm_num
  linarith only [hh]

/-- The largest source linear coefficient fits its entrance power. -/
theorem uniform_linear_coefficient :
    4*(256:ℝ)*63^2*12^4 ≤ (3:ℝ)^30/4 := by norm_num

/-- A single exact Taylor term bounds the entire positive exponential tail. -/
theorem uniform_mismatch_exponential :
    Real.exp (-(3:ℝ)^11/1536) ≤ (Nat.factorial 128:ℝ)/((3:ℝ)^11/1536)^128 := by
  let A : ℝ := (3:ℝ)^11/1536
  have hA : 0 < A := by dsimp only [A]; positivity
  have ht := Real.pow_div_factorial_le_exp A hA.le 128
  have hp : 0 < A^128/(Nat.factorial 128:ℝ) := by positivity
  have hi := one_div_le_one_div_of_le hp ht
  have he : 1/(A^128/(Nat.factorial 128:ℝ)) = (Nat.factorial 128:ℝ)/A^128 := by field_simp
  rw [he] at hi
  simpa only [Real.exp_neg,neg_div,one_div,A] using! hi

/-- The complete conservative mismatch coefficient, including both centering
errors and a coarse bound on the root of 12000, fits its entrance power. -/
theorem uniform_mismatch_numeric :
    2*(81920:ℝ)^4*12000*((Nat.factorial 128:ℝ)/((3:ℝ)^11/1536)^128)*(3:ℝ)^130 ≤
      (3:ℝ)^90/4 := by norm_num

/-- Uniform bound on the actual third retained PE coefficient at every source
order 2<=p<=256 and integer power m<=4. -/
theorem uniform_mismatch_coefficient (m : ℕ) (hm : m ≤ 4)
    (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256) :
    localizationMismatchCoefficient m p ≤ (3:ℝ)^90/4 := by
  have hp0 : 0 < p := by linarith only [hp]
  have hmc : (m:ℝ) ≤ 4 := by exact_mod_cast hm
  have hb0 : 0 ≤ 80*(m:ℝ)*p := by positivity
  have hb : 80*(m:ℝ)*p ≤ 81920 := by
    have hh := mul_le_mul_of_nonneg_right hmc hp0.le
    nlinarith only [hh,hp256]
  have hpow : (80*(m:ℝ)*p)^m ≤ (81920:ℝ)^4 :=
    (pow_le_pow_left₀ hb0 hb m).trans (pow_le_pow_right₀ (by norm_num) hm)
  have hr : (12000:ℝ)^(1/(2*p)) ≤ 12000 := by
    have he : 1/(2*p) ≤ (1:ℝ) := (div_le_one (by positivity)).mpr (by linarith only [hp])
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 12000) he
  have hA : (3:ℝ)^11/1536 ≤ (3:ℝ)^11/(6*p) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith only [hp256])
  have he : Real.exp (-(3:ℝ)^11/(6*p)) ≤
      (Nat.factorial 128:ℝ)/((3:ℝ)^11/1536)^128 := by
    apply (Real.exp_le_exp.mpr _).trans uniform_mismatch_exponential
    simpa only [neg_div] using neg_le_neg hA
  unfold localizationMismatchCoefficient
  apply le_trans _ uniform_mismatch_numeric
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hprod := mul_le_mul hpow hr
    (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 12000) _) (by positivity)
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left hprod (by norm_num : (0:ℝ) ≤ 2)) he
    (Real.exp_pos _).le (by positivity)
  simpa only [mul_assoc] using! hh

end
end ASDExplicitGamma.Inverse
