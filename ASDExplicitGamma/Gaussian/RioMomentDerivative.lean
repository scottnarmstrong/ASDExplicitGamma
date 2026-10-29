module

public import ASDExplicitGamma.Gaussian.RioPowerEnvelope
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # Differentiating the actual twentieth moments twice -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace ASDExplicitGamma.Gaussian

/-- The even twentieth moment has an integrable constant-plus-power envelope. -/
theorem rio_integrable_one_add_twentieth {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsFiniteMeasure ℙ] {W : Ω → ℝ} (hW : MemLp W 20 ℙ) :
    Integrable (fun ω => 1+W ω^20) ℙ := by
  have hi := hW.integrable_norm_pow (p := 20) (by norm_num)
  have he : Integrable (fun ω => W ω^20) ℙ := by
    simpa only [Real.norm_eq_abs,show (20:ℕ)=2*10 by norm_num,pow_mul,sq_abs] using hi
  exact (integrable_const 1).add he

/-- Derivative under the integral for every mixed power needed by the cold L20 proof. -/
theorem rio_mixed_moment_hasDerivAt {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsFiniteMeasure ℙ] {S X : Ω → ℝ} (hS : MemLp S 20 ℙ) (hX : MemLp X 20 ℙ)
    {n m : ℕ} (hn : 1 ≤ n) (hnm : n+m ≤ 20) (t : ℝ) :
    HasDerivAt (fun z : ℝ => ∫ ω, (S ω+z*X ω)^n*X ω^m ∂ℙ)
      ((n:ℝ)*(∫ ω, (S ω+t*X ω)^(n-1)*X ω^(m+1) ∂ℙ)) t := by
  let W := fun ω => |S ω|+(|t|+1)*|X ω|
  have hW : MemLp W 20 ℙ := hS.norm.add (hX.norm.const_mul (|t|+1))
  have hWi := (rio_integrable_one_add_twentieth hW).const_mul (n:ℝ)
  let F := fun (z : ℝ) ω => (S ω+z*X ω)^n*X ω^m
  let F' := fun (z : ℝ) ω => (n:ℝ)*(S ω+z*X ω)^(n-1)*X ω^(m+1)
  have hm (z : ℝ) : AEStronglyMeasurable (F z) ℙ :=
    ((hS.aestronglyMeasurable.add (hX.aestronglyMeasurable.const_mul z)).pow n).mul
      (hX.aestronglyMeasurable.pow m)
  have hdm : AEStronglyMeasurable (F' t) ℙ :=
    (((hS.aestronglyMeasurable.add (hX.aestronglyMeasurable.const_mul t)).pow (n-1)).const_mul (n:ℝ)).mul
      (hX.aestronglyMeasurable.pow (m+1))
  have hb : ∀ᵐ ω ∂ℙ, ∀ z ∈ Metric.ball t 1, ‖F' z ω‖ ≤ (n:ℝ)*(1+W ω^20) := by
    filter_upwards with ω z hz
    have hz' : |z| ≤ |t|+1 := by
      have h := abs_add_le (z-t) t
      have hd : |z-t| < 1 := by simpa only [Metric.mem_ball,Real.dist_eq] using hz
      rw [sub_add_cancel] at h
      linarith only [h,hd]
    have hy : |S ω+z*X ω| ≤ W ω := by
      calc
        _ ≤ |S ω|+|z*X ω| := abs_add_le _ _
        _ = |S ω|+|z| * |X ω| := by rw [abs_mul]
        _ ≤ _ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hz' (abs_nonneg _))
    have hx : |X ω| ≤ W ω := by
      dsimp only [W]
      nlinarith only [abs_nonneg (S ω),abs_nonneg t,abs_nonneg (X ω),
        mul_nonneg (abs_nonneg t) (abs_nonneg (X ω))]
    have hw : 0 ≤ W ω := (abs_nonneg _).trans hx
    have h := mul_le_mul_of_nonneg_left (rio_mixed_power_bound hw hy hx
      (show n-1+(m+1) ≤ 20 by omega)) (show (0:ℝ) ≤ n by positivity)
    dsimp only [F']
    rw [Real.norm_eq_abs,show (n:ℝ)*(S ω+z*X ω)^(n-1)*X ω^(m+1) =
      (n:ℝ)*((S ω+z*X ω)^(n-1)*X ω^(m+1)) by ring,abs_mul,abs_of_nonneg (Nat.cast_nonneg n)]
    exact h
  have hd : ∀ᵐ ω ∂ℙ, ∀ z ∈ Metric.ball t 1, HasDerivAt (fun z => F z ω) (F' z ω) z := by
    filter_upwards with ω z _
    have h := (((hasDerivAt_const z (S ω)).add ((hasDerivAt_id z).mul_const (X ω))).pow n).mul_const (X ω^m)
    convert h using 1
    · rfl
    · dsimp only [F',Pi.add_apply,id_eq]
      rw [pow_succ]
      ring
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds t (by norm_num))
    (Filter.Eventually.of_forall hm) (rio_integrable_mixed_power hS hX t hnm) hdm hb hWi hd).2
  dsimp only [F'] at h
  rw [show (fun ω => (n:ℝ)*(S ω+t*X ω)^(n-1)*X ω^(m+1)) =
      (fun ω => (n:ℝ)*((S ω+t*X ω)^(n-1)*X ω^(m+1))) by funext ω; ring,
    integral_const_mul] at h
  exact h

end ASDExplicitGamma.Gaussian
