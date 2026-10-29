module

public import ASDExplicitGamma.Gaussian.WaveGatePowerMargins
public import Mathlib.MeasureTheory.Measure.Real

/-! The exact planar extension/block count and its uniform positive-label union cost. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open MeasureTheory

/-- Two-by-two blocks, two generations, and the buffer-volume count. -/
def wavePlanarEventCount : ℕ := 4*(1+9+81)*3^80

theorem wave_planar_event_count : wavePlanarEventCount = 364*3^80 := by decide

/-- The exact elementary-event count fits the source logarithmic allowance. -/
theorem wave_planar_count_log : Real.log (wavePlanarEventCount:ℝ) ≤ 94 := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 6) 12
  have h364 : (364:ℝ) ≤ Real.exp 6 := by
    norm_num [Finset.sum_range_succ, Nat.factorial] at he ⊢
    linarith only [he]
  have hl : Real.log (364:ℝ) ≤ 6 := (Real.log_le_iff_le_exp (by norm_num)).mpr h364
  rw [wave_planar_event_count, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_ofNat,
    Real.log_mul (by norm_num : (364:ℝ) ≠ 0) (by positivity : (3:ℝ)^80 ≠ 0), Real.log_pow]
  have ht := ASDExplicitGamma.Numerics.Scalar.log_three_small.2.le
  norm_num only [Nat.cast_ofNat]
  linarith only [hl,ht]

/-- Every positive label pays the full actual union count after the raw tail. -/
theorem wave_planar_union_cost (Λ : ℤ) (hΛ : 1 ≤ Λ) :
    (wavePlanarEventCount:ℝ) ≤
      Real.exp (((6+(11/5:ℝ)*40)/5)*(3:ℝ)^((3/2:ℝ)*(Λ:ℝ))) := by
  apply (Real.log_le_iff_le_exp (by norm_num [wavePlanarEventCount])).mp
  have hh := wave_rate_power_ge_five Λ hΛ
  apply wave_planar_count_log.trans
  nlinarith only [hh]

/-- The finite union keeps its literal number of elementary events and needs
no independence between its members. -/
theorem wave_finite_union_tail {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : I → Set Ω) (A R : ℝ)
    (hcard : (Fintype.card I:ℝ) ≤ Real.exp A)
    (hE : ∀ i, μ.real (E i) ≤ Real.exp (-(A+R))) :
    μ.real (⋃ i, E i) ≤ Real.exp (-R) := by
  calc
    _ ≤ ∑ i, μ.real (E i) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ _i : I, Real.exp (-(A+R)) := Finset.sum_le_sum fun i _ => hE i
    _ = (Fintype.card I:ℝ)*Real.exp (-(A+R)) := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ Real.exp A*Real.exp (-(A+R)) := mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    _ = Real.exp (-R) := by rw [← Real.exp_add]; congr 1; ring

end ASDExplicitGamma.Gaussian
