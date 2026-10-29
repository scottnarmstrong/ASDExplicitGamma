module

public import ASDExplicitGamma.Triadic.DiagSmoothHat
public import ASDExplicitGamma.Triadic.MultiplierTensor
public import ASDExplicitGamma.Triadic.PlanarNeumannBridge
public import Homogenization.Sobolev.Truncation.H10Limit

/-! Sobolev realization of the tensor hats used by DIAG. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory Filter
open scoped Topology

noncomputable section

/-- A tensor hat with physical center `c` and radius `r`. -/
def diagPhysicalHat (c : Vec 2) (r : ℝ) (x : Vec 2) : ℝ :=
  tensorMultiplier (fun i t => diagHat ((t - c i) / r)) x

/-- Coordinatewise weak gradient of a tensor hat. -/
def diagPhysicalHatGradient (c : Vec 2) (r : ℝ) (x : Vec 2) (i : Fin 2) : ℝ :=
  tensorDerivative (fun k t => diagHat ((t - c k) / r))
    (fun k t => diagHatSlope r (t - c k)) x i

theorem diagHatSlope_bound {r : ℝ} (hr : 0 < r) (t : ℝ) :
    |diagHatSlope r t| ≤ 4 / r := by
  unfold diagHatSlope
  rw [abs_div, abs_of_pos hr]
  apply div_le_div_of_nonneg_right _ hr.le
  split_ifs <;> norm_num

/-- Tensor hats are genuine H¹ functions. This construction uses bounded
smooth approximants, not a weak-gradient hypothesis on the hat. -/
def diagPhysicalHatH1 (Q : TriadicCube 2) (c : Vec 2) (r : ℝ) (hr : 0 < r) :
    H1Function (openCubeSet Q) := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
  have hε1 : ∀ n, ε n ≤ 1 := fun n => by
    dsimp [ε]
    exact (div_le_one (by positivity)).2 (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let f : Fin 2 → ℝ → ℝ := fun i t => diagHat ((t - c i) / r)
  let df : Fin 2 → ℝ → ℝ := fun i t => diagHatSlope r (t - c i)
  let fn : ℕ → Fin 2 → ℝ → ℝ := fun n i t => diagSmoothHat r (ε n) (t - c i)
  let M : ℝ := 1 + 12 / r
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have h1M : (1 : ℝ) ≤ M := by dsimp [M]; linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 12) hr.le]
  have h4M : 4 / r ≤ M := by dsimp [M]; have h := div_le_div_of_nonneg_right (by norm_num : (4 : ℝ) ≤ 12) hr.le; linarith only [h]
  have h9M : 1 + 8 / r ≤ M := by
    dsimp [M]
    have h := div_le_div_of_nonneg_right (by norm_num : (8 : ℝ) ≤ 12) hr.le
    linarith only [h]
  have hfn (n : ℕ) (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fn n i) :=
    (diagSmoothHat_contDiff r (ε n)).comp (contDiff_id.sub contDiff_const)
  have hd (n : ℕ) (i : Fin 2) (t : ℝ) :
      deriv (fn n i) t = deriv (diagSmoothHat r (ε n)) (t - c i) := by
    change deriv (fun y => diagSmoothHat r (ε n) (y - c i)) t = _
    rw [(diagSmoothHat_hasDerivAt r (ε n) (t - c i)).deriv]
    simpa only [Function.comp_def, id_eq, mul_one] using
      ((diagSmoothHat_hasDerivAt r (ε n) (t - c i)).comp t
        ((hasDerivAt_id t).sub_const (c i))).deriv
  have hm (i : Fin 2) : Measurable (fun x : Vec 2 => df i (x i)) := by
    have hh (a : ℝ) : Measurable (fun x : Vec 2 => if a < x i - c i then (1 : ℝ) else 0) :=
      measurable_const.ite (measurableSet_lt measurable_const
        ((measurable_pi_apply i).sub measurable_const)) measurable_const
    exact (((hh (-r)).sub (measurable_const.mul (hh 0))).add (hh r)).div_const r
  let u := mulTensorSmoothLimit (h1ConstantOnCube Q 1) f df fn
    (fun i => diagHat_continuous.comp (by fun_prop))
    (fun i => (hm i).aestronglyMeasurable)
    hfn M hM
    (fun i => Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (diagHat_nonneg _)]
      exact (diagHat_le_one _).trans h1M)
    (fun i => Filter.Eventually.of_forall fun x => by
      exact (diagHatSlope_bound hr _).trans h4M)
    (fun n i => Filter.Eventually.of_forall fun x => by
      have hb := diagSmoothHat_error hr (hε n) (x i - c i)
      have hb' := (abs_sub_abs_le_abs_sub _ _).trans hb
      have hf := diagHat_le_one ((x i - c i) / r)
      rw [abs_of_nonneg (diagHat_nonneg _)] at hb'
      have he := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hε1 n) (by norm_num : (0 : ℝ) ≤ 8)) hr.le
      change |diagSmoothHat r (ε n) (x i - c i)| ≤ M
      exact (by linarith only [hb', hf, he] :
        |diagSmoothHat r (ε n) (x i - c i)| ≤ 1 + 8 / r).trans h9M)
    (fun n i => Filter.Eventually.of_forall fun x => by
      rw [hd, Real.norm_eq_abs]
      exact (diagSmoothHat_deriv_bound hr _ _).trans h4M)
    (fun i => Filter.Eventually.of_forall fun x => diagSmoothHat_tendsto hr hε hεlim _)
    (fun i => Filter.Eventually.of_forall fun x => by
      simp only [hd]
      exact diagSmoothHat_deriv_tendsto hε hεlim _)
  have hu : u.toFun = diagPhysicalHat c r := by
    change (fun x => tensorMultiplier f x * 1) = _
    simp only [mul_one]
    rfl
  have hDu : u.grad = diagPhysicalHatGradient c r := by
    change (fun x i => tensorMultiplier f x * (h1ConstantOnCube Q 1).grad x i +
      (h1ConstantOnCube Q 1).toFun x * tensorDerivative f df x i) = _
    rw [h1ConstantOnCube_grad, h1ConstantOnCube_toFun]
    simp only [Pi.zero_apply, mul_zero, one_mul, zero_add]
    rfl
  exact
    { toFun := diagPhysicalHat c r
      grad := diagPhysicalHatGradient c r
      memL2 := hu ▸ u.memL2
      gradMemL2 := hDu ▸ u.gradMemL2
      hasWeakGradient := hu ▸ hDu ▸ u.hasWeakGradient }

@[simp] theorem diagPhysicalHatH1_toFun (Q : TriadicCube 2) (c : Vec 2)
    (r : ℝ) (hr : 0 < r) : (diagPhysicalHatH1 Q c r hr).toFun = diagPhysicalHat c r := rfl

@[simp] theorem diagPhysicalHatH1_grad (Q : TriadicCube 2) (c : Vec 2)
    (r : ℝ) (hr : 0 < r) :
    (diagPhysicalHatH1 Q c r hr).grad = diagPhysicalHatGradient c r := rfl

end

end ASDExplicitGamma.Triadic
