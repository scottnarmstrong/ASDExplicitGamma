module

public import ASDExplicitGamma.Gaussian.RioScalar
public import ASDExplicitGamma.Gaussian.RioHolder
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-! # Differentiation of the real Lp moment along an affine random path -/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace ASDExplicitGamma.Gaussian

section
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (p : ℝ) (S X : Ω → ℝ)

noncomputable def rioMomentDerivative (t : ℝ) : ℝ :=
  ∫ ω, p * |S ω + t * X ω| ^ (p - 2) * (S ω + t * X ω) * X ω ∂μ

noncomputable def rioMomentSecondDerivative (t : ℝ) : ℝ :=
  ∫ ω, p * (p - 1) * |S ω + t * X ω| ^ (p - 2) * X ω ^ 2 ∂μ

/-- A fixed integrable envelope works in a whole neighborhood of each time. -/
theorem rio_affine_abs_le (t u s x : ℝ) (hu : u ∈ Metric.ball t 1) :
    |s + u * x| ≤ |s| + (|t| + 1) * |x| := by
  have ht : |u - t| < 1 := hu
  have hu' : |u| ≤ |t| + 1 := by
    calc
      |u| = |u - t + t| := by rw [sub_add_cancel]
      _ ≤ |u - t| + |t| := abs_add_le _ _
      _ ≤ |t| + 1 := by linarith only [ht]
  exact (abs_add_le s (u * x)).trans (by rw [abs_mul]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hu' (abs_nonneg x)))

/-- The first moment derivative is justified by a local integrable Hölder envelope. -/
theorem hasDerivAt_rioMoment [IsProbabilityMeasure μ] (hp : 2 ≤ p)
    (hS : MemLp S (ENNReal.ofReal p) μ) (hX : MemLp X (ENNReal.ofReal p) μ) (t : ℝ) :
    HasDerivAt (fun u => rioMoment μ p (fun ω => S ω + u * X ω))
      (rioMomentDerivative μ p S X t) t := by
  have hp0 : 0 ≤ p := by linarith only [hp]
  have hp1 : 1 < p := by linarith only [hp]
  let W : Ω → ℝ := fun ω => |S ω| + (|t| + 1) * |X ω|
  have hW : MemLp W (ENNReal.ofReal p) μ := hS.norm.add (hX.norm.const_mul _)
  have hWi : Integrable (fun ω => p * (W ω ^ (p - 1) * |X ω|)) μ :=
    (integrable_power_mul hp1 (fun ω => by dsimp [W]; positivity) hW hX.norm).const_mul p
  have hy (u : ℝ) : MemLp (fun ω => S ω + u * X ω) (ENNReal.ofReal p) μ := hS.add (hX.const_mul u)
  have hFi (u : ℝ) : Integrable (fun ω => |S ω + u * X ω| ^ p) μ := by
    simpa only [ENNReal.toReal_ofReal hp0, Real.norm_eq_abs] using (hy u).integrable_norm_rpow'
  have hDmeas (u : ℝ) : AEStronglyMeasurable
      (fun ω => p * |S ω + u * X ω| ^ (p - 2) * (S ω + u * X ω) * X ω) μ :=
    ((continuous_rio_power_derivative hp).comp_aestronglyMeasurable (hy u).aestronglyMeasurable).mul hX.aestronglyMeasurable
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u ω => |S ω + u * X ω| ^ p)
    (F' := fun u ω => p * |S ω + u * X ω| ^ (p - 2) * (S ω + u * X ω) * X ω)
    (bound := fun ω => p * (W ω ^ (p - 1) * |X ω|)) (s := Metric.ball t 1)
    (Metric.ball_mem_nhds t (by norm_num))
    (Filter.Eventually.of_forall fun u => (hFi u).aestronglyMeasurable) (hFi t) (hDmeas t)
    (Filter.Eventually.of_forall fun ω u hu => by
      have h := rio_first_derivative_bound (p := p) (x := X ω) (W := W ω) hp
        (rio_affine_abs_le t u (S ω) (X ω) hu)
      simpa only [mul_assoc] using h)
    hWi (Filter.Eventually.of_forall fun ω u _ => by
      have hpath : HasDerivAt (fun v => S ω + v * X ω) (X ω) u := by
        simpa only [one_mul] using ((hasDerivAt_id' u).mul_const (X ω)).const_add (S ω)
      exact (hasDerivAt_abs_rpow (S ω + u * X ω) hp1).comp u hpath)
  exact hh.2

/-- The second moment derivative has the exact p(p−1) coefficient, including p = 2. -/
theorem hasDerivAt_rioMomentDerivative [IsProbabilityMeasure μ] (hp : 2 ≤ p)
    (hS : MemLp S (ENNReal.ofReal p) μ) (hX : MemLp X (ENNReal.ofReal p) μ) (t : ℝ) :
    HasDerivAt (rioMomentDerivative μ p S X) (rioMomentSecondDerivative μ p S X t) t := by
  let W : Ω → ℝ := fun ω => |S ω| + (|t| + 1) * |X ω|
  have hW0 (ω : Ω) : 0 ≤ W ω := by dsimp only [W]; positivity
  have hW : MemLp W (ENNReal.ofReal p) μ := hS.norm.add (hX.norm.const_mul _)
  have hWi : Integrable (fun ω => (p * (p - 1)) * (W ω ^ (p - 2) * X ω ^ 2)) μ := by
    have hh := (rio_integrable_second_product_ge_two hp hW hX).const_mul (p * (p - 1))
    simpa only [abs_of_nonneg (hW0 _)] using hh
  have hy (u : ℝ) : MemLp (fun ω => S ω + u * X ω) (ENNReal.ofReal p) μ := hS.add (hX.const_mul u)
  have hFi (u : ℝ) : Integrable
      (fun ω => p * |S ω + u * X ω| ^ (p - 2) * (S ω + u * X ω) * X ω) μ :=
    rio_integrable_first_product hp (hy u) hX
  have hSecondCont : Continuous (fun y : ℝ => p * (p - 1) * |y| ^ (p - 2)) :=
    continuous_const.mul (continuous_abs.rpow_const (fun _ => Or.inr (by linarith only [hp])))
  have hDmeas : AEStronglyMeasurable
      (fun ω => p * (p - 1) * |S ω + t * X ω| ^ (p - 2) * X ω ^ 2) μ :=
    (hSecondCont.comp_aestronglyMeasurable (hy t).aestronglyMeasurable).mul (hX.aestronglyMeasurable.pow 2)
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u ω => p * |S ω + u * X ω| ^ (p - 2) * (S ω + u * X ω) * X ω)
    (F' := fun u ω => p * (p - 1) * |S ω + u * X ω| ^ (p - 2) * X ω ^ 2)
    (bound := fun ω => (p * (p - 1)) * (W ω ^ (p - 2) * X ω ^ 2)) (s := Metric.ball t 1)
    (Metric.ball_mem_nhds t (by norm_num))
    (Filter.Eventually.of_forall fun u => (hFi u).aestronglyMeasurable) (hFi t) hDmeas
    (Filter.Eventually.of_forall fun ω u hu => by
      have h := rio_second_derivative_bound (p := p) (x := X ω) (W := W ω) hp
        (rio_affine_abs_le t u (S ω) (X ω) hu)
      simpa only [mul_assoc] using h)
    hWi (Filter.Eventually.of_forall fun ω u _ => by
      have hpath : HasDerivAt (fun v => S ω + v * X ω) (X ω) u := by
        simpa only [one_mul] using ((hasDerivAt_id' u).mul_const (X ω)).const_add (S ω)
      convert ((hasDerivAt_rio_power_derivative hp (S ω + u * X ω)).comp u hpath).mul_const (X ω) using 1
      · funext v
        simp only [Function.comp_apply]
      · ring)
  exact hh.2

/-- Hölder bounds the full moment Hessian by the squared Lp norm of the increment. -/
theorem rioMomentSecondDerivative_le [IsProbabilityMeasure μ] (hp : 2 ≤ p)
    (hS : MemLp S (ENNReal.ofReal p) μ) (hX : MemLp X (ENNReal.ofReal p) μ) (t : ℝ) :
    rioMomentSecondDerivative μ p S X t ≤ p * (p - 1) *
      rioMoment μ p (fun ω => S ω + t * X ω) ^ ((p - 2) / p) *
        (eLpNorm X (ENNReal.ofReal p) μ).toReal ^ 2 := by
  unfold rioMomentSecondDerivative
  simp_rw [mul_assoc]
  rw [integral_const_mul, integral_const_mul]
  have hc : 0 ≤ p * (p - 1) := mul_nonneg (by linarith only [hp]) (by linarith only [hp])
  have hh := mul_le_mul_of_nonneg_left (rio_second_holder (Y := fun ω => S ω + t * X ω) μ hp (hS.add (hX.const_mul t)) hX) hc
  simpa only [mul_assoc] using hh

end
end ASDExplicitGamma.Gaussian
