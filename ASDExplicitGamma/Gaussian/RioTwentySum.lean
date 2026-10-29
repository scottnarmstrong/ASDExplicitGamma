module

public import ASDExplicitGamma.Gaussian.RioTwenty

/-! # The sharp independent centered sum estimate needed by the cold-start estimate -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ASDExplicitGamma.Gaussian

/-- Rio's sharp squared L20 bound for each finite independent centered family. -/
theorem rio_lpNorm_twenty_sum_sq {Ω ι : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsFiniteMeasure ℙ] (s : Finset ι) {Y : ι → Ω → ℝ}
    (hY : ∀ i, MemLp (Y i) 20 ℙ) (hIndep : ProbabilityTheory.iIndepFun Y ℙ)
    (hCenter : ∀ i, (∫ ω, Y i ω ∂ℙ) = 0) :
    (lpNorm (∑ i ∈ s, Y i) 20 ℙ)^2 ≤ 19*∑ i ∈ s, (lpNorm (Y i) 20 ℙ)^2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hm : MemLp (∑ i ∈ s, Y i) 20 ℙ := memLp_finsetSum' s (fun j _ => hY j)
    have hind := hIndep.indepFun_finsetSum_of_notMem₀ (fun j => (hY j).aestronglyMeasurable.aemeasurable) hi
    have hstep := rio_lpNorm_twenty_independent hm (hY i) hind (hCenter i)
    have ht : (lpNorm ((∑ j ∈ s, Y j)+Y i) 20 ℙ)^2 ≤
        19*(∑ j ∈ s, (lpNorm (Y j) 20 ℙ)^2)+19*(lpNorm (Y i) 20 ℙ)^2 :=
      hstep.trans (add_le_add ih (le_refl _))
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    simpa only [add_comm,mul_add] using ht

/-- The sharp L20 sum bound in the square-root form used within each parity class. -/
theorem rio_lpNorm_twenty_sum_le {Ω ι : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsFiniteMeasure ℙ] (s : Finset ι) {Y : ι → Ω → ℝ} {M : ℝ}
    (hY : ∀ i, MemLp (Y i) 20 ℙ) (hIndep : ProbabilityTheory.iIndepFun Y ℙ)
    (hCenter : ∀ i, (∫ ω, Y i ω ∂ℙ) = 0) (hM : 0 ≤ M)
    (hcap : ∀ i ∈ s, lpNorm (Y i) 20 ℙ ≤ M) :
    lpNorm (∑ i ∈ s, Y i) 20 ℙ ≤ Real.sqrt 19*Real.sqrt (s.card:ℝ)*M := by
  have hs := rio_lpNorm_twenty_sum_sq s hY hIndep hCenter
  have hcap2 := Finset.sum_le_sum (s := s) (fun i hi =>
    (sq_le_sq₀ lpNorm_nonneg hM).mpr (hcap i hi))
  simp only [Finset.sum_const, nsmul_eq_mul] at hcap2
  have hb := hs.trans (mul_le_mul_of_nonneg_left hcap2 (by norm_num : (0:ℝ) ≤ 19))
  have he : (Real.sqrt 19*Real.sqrt (s.card:ℝ)*M)^2 = 19*(s.card:ℝ)*M^2 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 19),Real.sq_sqrt (by positivity)]
  apply (sq_le_sq₀ lpNorm_nonneg (by positivity : 0 ≤ Real.sqrt 19*Real.sqrt (s.card:ℝ)*M)).mp
  rw [he]
  convert hb using 1
  ring

end ASDExplicitGamma.Gaussian
