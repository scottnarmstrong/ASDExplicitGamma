module

public import ASDExplicitGamma.Inverse.StoppedSeriesLp
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Finite deterministic norm envelopes for the actual density and square-root errors. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- Finite weighted Minkowski with an ordinary nonnegative source envelope. -/
theorem finite_density_sum_Lp {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (p : ℝ≥0∞) (hp : 1 ≤ p) (f : I → Ω → ℝ)
    (w c : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hc : ∀ i, 0 ≤ c i)
    (hb : ∀ i, eLpNorm (f i) p μ ≤ ENNReal.ofReal (c i)) :
    eLpNorm (fun ω => ∑ i, w i*f i ω) p μ ≤ ENNReal.ofReal (∑ i, w i*c i) := by
  have he : (fun ω => ∑ i, w i*f i ω) = ∑ i, w i • f i := by
    funext ω
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [he]
  apply (eLpNorm_sum_le hp).trans
  calc
    _ ≤ ∑ i, ENNReal.ofReal (w i*c i) := by
      apply Finset.sum_le_sum
      intro i _
      rw [eLpNorm_const_smul,Real.enorm_eq_ofReal (hw i),ENNReal.ofReal_mul (hw i)]
      exact mul_le_mul_of_nonneg_left (hb i) (zero_le : (0:ℝ≥0∞) ≤ _)
    _ = _ := (ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hw i) (hc i))).symm

/-- Exact square-root norm conversion for nonnegative source errors, with no
independence premise and no change in the density's order p. -/
theorem density_sqrt_Lp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) (hY : AEStronglyMeasurable Y μ)
    (hY0 : ∀ ω, 0 ≤ Y ω) (p C : ℝ) (hp : 0 < p) (hC : 0 ≤ C)
    (hb : eLpNorm Y (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C) :
    eLpNorm (fun ω => Real.sqrt (Y ω)) (ENNReal.ofReal (2*p)) μ ≤
      ENNReal.ofReal (Real.sqrt C) := by
  have he : (fun ω => Real.sqrt (Y ω)) = fun ω => ‖Y ω‖^(1/2:ℝ) := by
    funext ω
    rw [Real.norm_eq_abs,abs_of_nonneg (hY0 ω),Real.sqrt_eq_rpow]
  rw [he,eLpNorm_norm_rpow Y hY (by norm_num : (0:ℝ) < 1/2),
    ← ENNReal.ofReal_mul (show 0 ≤ 2*p by positivity),show (2*p)*(1/2:ℝ)=p by ring]
  apply (ENNReal.rpow_le_rpow hb (by norm_num : (0:ℝ) ≤ 1/2)).trans_eq
  rw [Real.sqrt_eq_rpow]
  exact ENNReal.ofReal_rpow_of_nonneg hC (by norm_num)

end
end ASDExplicitGamma.Inverse
