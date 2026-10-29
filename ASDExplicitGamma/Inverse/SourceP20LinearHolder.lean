module

public import ASDExplicitGamma.Gaussian.GaussMomentHolder

/-! Finite linear-factor Holder assembly for the simultaneous p20 source
moment. Each factor keeps its separate actual norm. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory ASDExplicitGamma.Gaussian
open scoped ENNReal

/-- A p20 generator dominated by finitely many positive source factors
integrates to the exact sum of their separate Holder norms. -/
theorem source_p20_integral_linear_factors
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (T G : Ω → ℝ) (F : ι → Ω → ℝ) (a : ι → ℝ)
    (hT0 : ∀ ω, 0 ≤ T ω) (hF0 : ∀ i ω, 0 ≤ F i ω) (ha : ∀ i, 0 ≤ a i)
    (hT : MemLp T (ENNReal.ofReal 20) μ) (hF : ∀ i, MemLp (F i) (ENNReal.ofReal 20) μ)
    (hG : Integrable G μ)
    (hpoint : ∀ᵐ ω ∂μ, G ω ≤ ∑ i, a i*(T ω^(19:ℝ)*F i ω)) :
    (∫ ω, G ω ∂μ) ≤ (∫ ω, T ω^(20:ℝ) ∂μ)^((19:ℝ)/20)*
      ∑ i, a i*positiveLpNorm μ 20 (F i) := by
  have hprod (i : ι) : Integrable (fun ω => T ω^(19:ℝ)*F i ω) μ := by
    simpa only [show (20:ℝ)-1=19 by norm_num] using
      integrable_power_mul (μ := μ) (p := 20) (by norm_num) hT0 hT (hF i)
  have hupper : Integrable (fun ω => ∑ i, a i*(T ω^(19:ℝ)*F i ω)) μ :=
    integrable_finsetSum Finset.univ (fun i _ => (hprod i).const_mul (a i))
  have hholder (i : ι) : (∫ ω, T ω^(19:ℝ)*F i ω ∂μ) ≤
      (∫ ω, T ω^(20:ℝ) ∂μ)^((19:ℝ)/20)*positiveLpNorm μ 20 (F i) := by
    simpa only [show (20:ℝ)-1=19 by norm_num,
      show (1:ℝ)-(20:ℝ)⁻¹=19/20 by norm_num] using
      integral_power_mul_le μ (p := 20) (by norm_num) hT0 (hF0 i) hT (hF i)
  calc
    _ ≤ ∫ ω, ∑ i, a i*(T ω^(19:ℝ)*F i ω) ∂μ := integral_mono_ae hG hupper hpoint
    _ = ∑ i, a i*(∫ ω, T ω^(19:ℝ)*F i ω ∂μ) := by
      rw [integral_finsetSum Finset.univ (fun i _ => (hprod i).const_mul (a i))]
      simp only [integral_const_mul]
    _ ≤ ∑ i, a i*((∫ ω, T ω^(20:ℝ) ∂μ)^((19:ℝ)/20)*positiveLpNorm μ 20 (F i)) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hholder i) (ha i))
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

end ASDExplicitGamma.Inverse
