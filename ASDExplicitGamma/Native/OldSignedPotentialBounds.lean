module

public import ASDExplicitGamma.Native.OldSignedSpectralProjectedModes
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Square-integrable potential differences for the whole-plane gradient.
Subtracting the character at the origin removes the low-frequency pole. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Complex ASDExplicitGamma.Model
noncomputable section

/-- Products of frequency coordinates are controlled by the squared
frequency length, uniformly over both vector components. -/
theorem old_signed_frequency_product_bound (xi : Q3FrequencyPlane) (i j : Fin 2) :
    |oldSignedFrequency xi i| * |oldSignedFrequency xi j| ≤ xi.fst^2+xi.snd^2 := by
  have hc (k : Fin 2) : (oldSignedFrequency xi k)^2 ≤ xi.fst^2+xi.snd^2 := by
    fin_cases k
    · change xi.fst^2 ≤ xi.fst^2+xi.snd^2
      exact le_add_of_nonneg_right (sq_nonneg _)
    · change xi.snd^2 ≤ xi.fst^2+xi.snd^2
      exact le_add_of_nonneg_left (sq_nonneg _)
  nlinarith only [hc i,hc j,sq_nonneg (|oldSignedFrequency xi i| - |oldSignedFrequency xi j|),
    sq_abs (oldSignedFrequency xi i),sq_abs (oldSignedFrequency xi j)]

/-- The inverse-gradient multiplier applied to a character difference.
The canonical zero-frequency value is zero; no zero-mode potential is needed. -/
def oldSignedPotentialValue (x : Vec 2) (j : Fin 2) (xi : Q3FrequencyPlane) : ℂ :=
  (oldSignedFrequency xi j:ℂ)/(((2*Real.pi*(xi.fst^2+xi.snd^2):ℝ):ℂ)*I)*
    (exp ((((2*Real.pi*(xi.fst*x 0+xi.snd*x 1)):ℝ):ℂ)*I)-1)

/-- The potential difference has a uniform frequency bound. This is a
local-in-space potential, without requiring an L2 inverse-gradient multiplier. -/
theorem old_signed_potential_value_norm (x : Vec 2) (j : Fin 2) (xi : Q3FrequencyPlane) :
    ‖oldSignedPotentialValue x j xi‖ ≤ |x 0| + |x 1| := by
  let d := xi.fst^2+xi.snd^2
  let t := xi.fst*x 0+xi.snd*x 1
  have hpi : 0<2*Real.pi := mul_pos (by norm_num) Real.pi_pos
  by_cases hz : d=0
  · simp only [oldSignedPotentialValue,show xi.fst^2+xi.snd^2=0 from hz,mul_zero,
      Complex.ofReal_zero,zero_mul,div_zero,zero_mul,norm_zero]
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hd : 0<d := lt_of_le_of_ne (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Ne.symm hz)
  have hp : ‖exp (((2*Real.pi*t:ℝ):ℂ)*I)-1‖ ≤ 2*Real.pi*|t| := by
    simpa only [mul_comm _ I,Real.norm_eq_abs,abs_mul,abs_of_pos hpi] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi*t))
  have hprod : |oldSignedFrequency xi j| * |t| ≤ d*(|x 0| + |x 1|) := by
    calc
      _ ≤ |oldSignedFrequency xi j| * (|xi.fst| * |x 0| + |xi.snd| * |x 1|) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact (abs_add_le _ _).trans_eq (by rw [abs_mul,abs_mul])
      _ = (|oldSignedFrequency xi j| * |xi.fst|)*|x 0| + 
          (|oldSignedFrequency xi j| * |xi.snd|)*|x 1| := by ring
      _ ≤ d*|x 0| + d*|x 1| := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right
            (by simpa [oldSignedFrequency,d] using
              old_signed_frequency_product_bound xi j 0) (abs_nonneg _)
        · exact mul_le_mul_of_nonneg_right
            (by simpa [oldSignedFrequency,d] using
              old_signed_frequency_product_bound xi j 1) (abs_nonneg _)
      _ = _ := by ring
  have hden : 0≤|oldSignedFrequency xi j| / (2*Real.pi*d) := by positivity
  calc
    _ = (|oldSignedFrequency xi j| / (2*Real.pi*d))*‖exp (((2*Real.pi*t:ℝ):ℂ)*I)-1‖ := by
      rw [oldSignedPotentialValue,norm_mul,norm_div,norm_mul,Complex.norm_real,Complex.norm_I,
        mul_one,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (mul_pos hpi hd)]
    _ ≤ (|oldSignedFrequency xi j| / (2*Real.pi*d))*(2*Real.pi*|t|) :=
      mul_le_mul_of_nonneg_left hp hden
    _ = |oldSignedFrequency xi j| * |t| / d := by field_simp [hpi.ne',hd.ne']
    _ ≤ _ := (div_le_iff₀ hd).mpr (by simpa only [mul_comm d] using hprod)

end
end ASDExplicitGamma.Native
