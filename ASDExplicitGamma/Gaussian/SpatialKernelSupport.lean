module

public import ASDExplicitGamma.Gaussian.Q3KernelCovariance
public import ASDExplicitGamma.Gaussian.Q3ConvolutionRegularity
public import ASDExplicitGamma.Gaussian.Q3KernelLipschitz
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! # Exact physical support and localization of the q3 white-noise convolution -/

@[expose] public section

open MeasureTheory Homogenization Set ASDExplicitGamma.Model
open scoped Topology RealInnerProductSpace

namespace ASDExplicitGamma.Gaussian

/-- The moving support box is in the ambient product/sup norm, hence has area L². -/
def q3SupportBox (L : {l : ℝ // 0 < l}) (x : Vec 2) : Set (Vec 2) := Metric.closedBall x (L.1 / 2)

theorem measurableSet_q3SupportBox (L : {l : ℝ // 0 < l}) (x : Vec 2) : MeasurableSet (q3SupportBox L x) :=
  Metric.isClosed_closedBall.measurableSet

theorem volume_q3SupportBox (L : {l : ℝ // 0 < l}) (x : Vec 2) :
    volume (q3SupportBox L x) = ENNReal.ofReal (L.1 ^ 2) := by
  rw [q3SupportBox, Real.volume_pi_closedBall x (div_nonneg L.2.le (by norm_num))]
  congr 1
  simp only [Fintype.card_fin]
  ring

/-- The physical value kernel vanishes outside its precise moving support box. -/
theorem q3SectionFunction_zero_outside (β : ℝ) (L : {l : ℝ // 0 < l}) (x y : Vec 2)
    (hy : y ∉ q3SupportBox L x) : q3SectionFunction β L h3Zero x y = 0 := by
  have hnot : ¬ ∀ i : Fin 2, dist (y i) (x i) ≤ L.1 / 2 := by
    intro h
    exact hy ((dist_pi_le_iff (div_nonneg L.2.le (by norm_num))).mpr h)
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  have hi' : 1 / 2 < |(x i - y i) / L.1| := by
    rw [abs_div, abs_of_pos L.2, lt_div_iff₀ L.2]
    have hd : L.1 / 2 < |x i - y i| := by
      simpa only [dist_eq_norm, Real.norm_eq_abs, abs_sub_comm] using lt_of_not_ge hi
    linarith only [hd]
  have hz := q3Derivative_eq_zero hi' (0 : Fin 4)
  fin_cases i
  · change q3Derivative 0 ((x 0 - y 0) / L.1) = 0 at hz
    simp only [q3SectionFunction, h3Zero, Fin.val_zero, add_zero, pow_one]
    rw [hz]
    ring
  · change q3Derivative 0 ((x 1 - y 1) / L.1) = 0 at hz
    simp only [q3SectionFunction, h3Zero, Fin.val_zero, add_zero, pow_one]
    rw [hz]
    ring

/-- Point evaluation uses exactly the scalar physical variance β². -/
theorem q3Section_norm_sq (β : ℝ) (L : {l : ℝ // 0 < l}) (x : Vec 2) :
    ‖q3Section β L h3Zero x‖ ^ 2 = β ^ 2 := by
  rw [gaussQ3Section_norm_sq]
  have hbase : q3DerivativeMoment (0 : Fin 4) = 1 := by norm_num [q3DerivativeMoment]
  simp only [h3Zero, Fin.val_zero, add_zero, pow_one, hbase, mul_one]
  field_simp [L.2.ne']

end ASDExplicitGamma.Gaussian
