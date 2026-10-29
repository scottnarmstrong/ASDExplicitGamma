module

public import ASDExplicitGamma.Gaussian.RioPowerEnvelope
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # The sharp Holder bound on the second twentieth-moment derivative -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ASDExplicitGamma.Gaussian

/-- The exact exponents in the second derivative bound, before taking the L20 norm. -/
theorem rio_twentieth_holder {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    {Y X : Ω → ℝ} (hY : MemLp Y 20 ℙ) (hX : MemLp X 20 ℙ) :
    (∫ ω, Y ω^18*X ω^2 ∂ℙ) ≤
      (∫ ω, Y ω^20 ∂ℙ)^((9:ℝ)/10)*(∫ ω, X ω^20 ∂ℙ)^((1:ℝ)/10) := by
  have hy : MemLp (fun ω => |Y ω|^18) (ENNReal.ofReal ((10:ℝ)/9)) ℙ := by
    convert hY.norm_rpow_div 18 using 1 <;> norm_num [Real.norm_eq_abs]
    calc
      ENNReal.ofReal ((10:ℝ)/9) = ENNReal.ofReal ((20:ℝ)/18) := by norm_num
      _ = (20:ℝ≥0∞)/18 := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
  have hx : MemLp (fun ω => |X ω|^2) (ENNReal.ofReal (10:ℝ)) ℙ := by
    convert hX.norm_rpow_div 2 using 1 <;> norm_num [Real.norm_eq_abs]
    have he := ENNReal.ofReal_div_of_pos (x := (20:ℝ)) (by norm_num : (0:ℝ) < 2)
    norm_num at he
    exact he
  have hpq : ((10:ℝ)/9).HolderConjugate 10 := by
    constructor <;> norm_num
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall (fun ω => pow_nonneg (abs_nonneg (Y ω)) 18))
    (Filter.Eventually.of_forall (fun ω => sq_nonneg |X ω|)) hy hx
  have hy20 (ω : Ω) : (|Y ω|^18)^((10:ℝ)/9) = Y ω^20 := by
    rw [← Real.rpow_natCast_mul (abs_nonneg (Y ω))]
    norm_num
    simp only [show (20:ℕ)=2*10 by norm_num,pow_mul,sq_abs]
  have hx20 (ω : Ω) : (|X ω|^2)^(10:ℝ) = X ω^20 := by
    norm_num only [Real.rpow_ofNat]
    rw [← pow_mul]
    norm_num
    simp only [show (20:ℕ)=2*10 by norm_num,pow_mul,sq_abs]
  simp_rw [hy20,hx20] at h
  norm_num at h
  convert h using 1
  apply integral_congr_ae
  filter_upwards with ω
  simp only [show (18:ℕ)=2*9 by norm_num,pow_mul,sq_abs]

end ASDExplicitGamma.Gaussian
