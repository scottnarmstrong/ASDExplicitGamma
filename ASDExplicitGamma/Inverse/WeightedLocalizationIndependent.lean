module

public import ASDExplicitGamma.Inverse.WeightedLocalizationLp

/-! Independent bounded centered sums at arbitrary real source moment orders. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization.IndependentSums MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A bounded centered independent sum obeys the variance-plus-maximum Lp
estimate with constant two, hence the source's constant four. -/
theorem localization_independent_Lp {Ω ι : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (X : ι → Ω → ℝ) (s : Finset ι)
    (hind : iIndepFun X mu) (hm : ∀ i, Measurable (X i))
    (b V p : ℝ) (hb : 0 < b) (hV : 0 < V) (hp : 1 ≤ p)
    (hbound : ∀ i ∈ s, ∀ᵐ ω ∂mu, |X i ω| ≤ b)
    (hmean : ∀ i ∈ s, ∫ ω, X i ω ∂mu = 0)
    (hvar : (∑ i ∈ s, moment (X i) 2 mu) ≤ V) :
    eLpNorm (fun ω => ∑ i ∈ s, X i ω) (ENNReal.ofReal p) mu ≤
      ENNReal.ofReal (2 * Real.sqrt V * Real.sqrt p + 2 * b * p) := by
  obtain ⟨lam, hl, htilt, hLp, hratio⟩ := localization_Lp_parameters b V p hb hV (by linarith)
  have hnind : iIndepFun (fun i ω => -X i ω) mu := hind.comp (fun _ x => -x) (fun _ => measurable_neg)
  have hP := (localization_sum_mgf_le mu X s hind hm b V lam hb hl.le htilt
    hbound hmean hvar).trans (Real.exp_le_exp.mpr hLp)
  have hN := (localization_sum_mgf_le mu (fun i ω => -X i ω) s hnind (fun i => (hm i).neg)
    b V lam hb hl.le htilt (by simpa only [abs_neg] using hbound)
    (by simpa only [integral_neg, neg_eq_zero] using hmean)
    (by simpa only [moment, Pi.pow_apply, neg_sq] using hvar)).trans (Real.exp_le_exp.mpr hLp)
  have hbm : ∀ᵐ ω ∂mu, |∑ i ∈ s, X i ω| ≤ (s.card : ℝ) * b := by
    filter_upwards [(s.eventually_all).mpr hbound] with ω hω
    calc
      _ ≤ ∑ i ∈ s, |X i ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ s, b := Finset.sum_le_sum hω
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hsmeas : Measurable (fun ω => ∑ i ∈ s, X i ω) := s.measurable_sum (fun i _ => hm i)
  have hiP := integrable_exp_mul_of_abs_le_const hl.le hsmeas.aemeasurable hbm
  have hiN := integrable_exp_mul_of_abs_le_const (μ := mu)
    (X := fun ω => -(∑ i ∈ s, X i ω)) hl.le hsmeas.neg.aemeasurable
    (by simpa only [abs_neg] using hbm)
  change (∫ ω, Real.exp (lam * ∑ i ∈ s, X i ω) ∂mu) ≤ Real.exp p at hP
  change (∫ ω, Real.exp (lam * ∑ i ∈ s, -X i ω) ∂mu) ≤ Real.exp p at hN
  simp only [Finset.sum_neg_distrib, mul_neg, ← neg_mul] at hN hiN
  have hh := localization_eLpNorm_of_exp_bounds mu (fun ω => ∑ i ∈ s, X i ω)
    hsmeas.aemeasurable p lam hp hl hiP hiN hP hN
  rw [hratio] at hh
  convert hh using 1
  congr 1
  ring

end ASDExplicitGamma.Inverse
