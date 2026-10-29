module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! # Exact centered L2 sums, the p=2 input of the four-colour cold graph bounds -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Gaussian

/-- Independent centered finite real sums have exactly additive second moments. -/
theorem rio_integral_centered_sum_sq {Ω ι : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsProbabilityMeasure ℙ] (s : Finset ι) {Y : ι → Ω → ℝ}
    (hY : ∀ i, MemLp (Y i) 2 ℙ) (hIndep : ProbabilityTheory.iIndepFun Y ℙ)
    (hCenter : ∀ i, (∫ ω, Y i ω ∂ℙ) = 0) :
    (∫ ω, (∑ i ∈ s, Y i ω)^2 ∂ℙ) = ∑ i ∈ s, ∫ ω, Y i ω^2 ∂ℙ := by
  classical
  have hsum : MemLp (fun ω => ∑ i ∈ s, Y i ω) 2 ℙ := memLp_finsetSum s (fun i _ => hY i)
  have hsum0 : (∫ ω, ∑ i ∈ s, Y i ω ∂ℙ) = 0 := by
    rw [integral_finsetSum _ (fun i _ => (hY i).integrable (by norm_num))]
    simp only [hCenter,Finset.sum_const_zero]
  have hvar := ProbabilityTheory.IndepFun.variance_sum (s := s) (fun i _ => hY i)
    (fun i _ j _ hij => hIndep.indepFun hij)
  have heq : (∑ i ∈ s, Y i) = (fun ω => ∑ i ∈ s, Y i ω) := by
    funext ω
    simp only [Finset.sum_apply]
  rw [heq,ProbabilityTheory.variance_eq_integral hsum.aestronglyMeasurable.aemeasurable,hsum0] at hvar
  simp only [sub_zero] at hvar
  simp_rw [ProbabilityTheory.variance_eq_integral (hY _).aestronglyMeasurable.aemeasurable,hCenter,sub_zero] at hvar
  exact hvar

/-- The ordinary real L2 norm squared is the second moment. -/
theorem rio_lpNorm_two_sq {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    {X : Ω → ℝ} (hX : MemLp X 2 ℙ) :
    (lpNorm X 2 ℙ)^2 = ∫ ω, X ω^2 ∂ℙ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hX.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat,Real.rpow_ofNat]
  have he : (fun ω => ‖X ω‖^2) = (fun ω => X ω^2) := by
    funext ω
    simp only [Real.norm_eq_abs,sq_abs]
  rw [he,← Real.rpow_mul_natCast (integral_nonneg (fun ω => sq_nonneg _))]
  norm_num

/-- Sharp scalar independent centered L2 sums, in ordinary real norm form. -/
theorem rio_lpNorm_two_sum_le {Ω ι : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsProbabilityMeasure ℙ] (s : Finset ι) {Y : ι → Ω → ℝ} {M : ℝ}
    (hY : ∀ i, MemLp (Y i) 2 ℙ) (hIndep : ProbabilityTheory.iIndepFun Y ℙ)
    (hCenter : ∀ i, (∫ ω, Y i ω ∂ℙ) = 0) (hM : 0 ≤ M)
    (hcap : ∀ i ∈ s, lpNorm (Y i) 2 ℙ ≤ M) :
    lpNorm (fun ω => ∑ i ∈ s, Y i ω) 2 ℙ ≤ Real.sqrt (s.card:ℝ)*M := by
  have hm := memLp_finsetSum s (fun i _ => hY i)
  have he := rio_integral_centered_sum_sq s hY hIndep hCenter
  rw [← rio_lpNorm_two_sq hm] at he
  simp_rw [← rio_lpNorm_two_sq (hY _)] at he
  have hc : (∑ i ∈ s, (lpNorm (Y i) 2 ℙ)^2) ≤ (s.card:ℝ)*M^2 := by
    calc
      _ ≤ ∑ _ ∈ s, M^2 := Finset.sum_le_sum (fun i hi =>
        (sq_le_sq₀ lpNorm_nonneg hM).mpr (hcap i hi))
      _ = _ := by simp
  have hr : (Real.sqrt (s.card:ℝ)*M)^2 = (s.card:ℝ)*M^2 := by
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
  apply (sq_le_sq₀ lpNorm_nonneg (mul_nonneg (Real.sqrt_nonneg _) hM)).mp
  rw [he,hr]
  exact hc

end ASDExplicitGamma.Gaussian
