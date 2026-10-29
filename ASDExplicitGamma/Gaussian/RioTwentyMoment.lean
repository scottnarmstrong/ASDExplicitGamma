module

public import ASDExplicitGamma.Gaussian.RioMomentDerivative
public import ASDExplicitGamma.Gaussian.RioMomentHolder
public import ASDExplicitGamma.Gaussian.RioTenthPower

/-! # Sharp one-step smoothness for the actual twentieth moment -/

@[expose] public section
noncomputable section
open MeasureTheory
namespace ASDExplicitGamma.Gaussian

/-- The cold one-step smoothness estimate under the exact mixed-moment cancellation.
Conditional centering implies this cancellation; no independence is needed here. -/
theorem rio_twentieth_moment_one_step {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsFiniteMeasure ℙ] {S X : Ω → ℝ} (hS : MemLp S 20 ℙ) (hX : MemLp X 20 ℙ)
    (horth : (∫ ω, S ω^19*X ω ∂ℙ) = 0) :
    (∫ ω, (S ω+X ω)^20 ∂ℙ)^((1:ℝ)/10) ≤
      (∫ ω, S ω^20 ∂ℙ)^((1:ℝ)/10)+19*(∫ ω, X ω^20 ∂ℙ)^((1:ℝ)/10) := by
  let f := fun t : ℝ => ∫ ω, (S ω+t*X ω)^20 ∂ℙ
  let g := fun t : ℝ => 20*(∫ ω, (S ω+t*X ω)^19*X ω ∂ℙ)
  let h := fun t : ℝ => 380*(∫ ω, (S ω+t*X ω)^18*X ω^2 ∂ℙ)
  let B := (∫ ω, X ω^20 ∂ℙ)^((1:ℝ)/10)
  have hf (t : ℝ) : HasDerivAt f (g t) t := by
    have hd := rio_mixed_moment_hasDerivAt hS hX (n := 20) (m := 0) (by norm_num) (by norm_num) t
    simpa only [Nat.reduceSub,Nat.reduceAdd,Nat.cast_ofNat,pow_zero,mul_one,pow_one] using hd
  have hg (t : ℝ) : HasDerivAt g (h t) t := by
    have hd := (rio_mixed_moment_hasDerivAt hS hX (n := 19) (m := 1) (by norm_num) (by norm_num) t).const_mul 20
    simp only [Nat.reduceSub,Nat.reduceAdd,pow_one] at hd
    convert hd using 1
    dsimp only [h]
    norm_num
    ring
  have hn (t : ℝ) : 0 ≤ h t := by
    apply mul_nonneg (by norm_num)
    apply integral_nonneg
    intro ω
    exact mul_nonneg (by positivity) (sq_nonneg _)
  have hg0 : g 0 = 0 := by dsimp [g]; simp only [zero_mul,add_zero,horth,mul_zero]
  have hf0 : 0 ≤ f 0 := integral_nonneg (fun ω => by positivity)
  by_cases hz : f 0 = 0
  · have hSi : Integrable (fun ω => S ω^20) ℙ := by
      simpa only [pow_zero,mul_one,zero_mul,add_zero] using
        rio_integrable_mixed_power hS hX 0 (n := 20) (m := 0) (by norm_num)
    have hs : (fun ω => S ω^20) =ᵐ[ℙ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun ω => by positivity) hSi).mp (by
        simpa only [f,zero_mul,add_zero] using hz)
    have hSz : S =ᵐ[ℙ] 0 := hs.mono (fun ω hω => by
      change S ω^20 = 0 at hω
      exact (pow_eq_zero_iff (by norm_num : (20:ℕ) ≠ 0)).mp hω)
    have heq : (∫ ω, (S ω+X ω)^20 ∂ℙ) = ∫ ω, X ω^20 ∂ℙ := integral_congr_ae
      (hSz.mono (fun ω hω => by change S ω = 0 at hω; simp only [hω,zero_add]))
    have heq0 : (∫ ω, S ω^20 ∂ℙ) = 0 := by simpa only [f,zero_mul,add_zero] using hz
    rw [heq,heq0]
    norm_num only [Real.zero_rpow (by norm_num : (1:ℝ)/10 ≠ 0),zero_add]
    have hB : 0 ≤ (∫ ω, X ω^20 ∂ℙ)^((1:ℝ)/10) := Real.rpow_nonneg (integral_nonneg (fun ω => by positivity)) _
    linarith only [hB]
  · have hpos (t : ℝ) : 0 < f t :=
      (lt_of_le_of_ne hf0 (Ne.symm hz)).trans_le (rio_minimum_of_second_nonneg hf hg hn hg0 t)
    have hHolder (t : ℝ) : h t ≤ 380*(f t)^((9:ℝ)/10)*B := by
      have hd := mul_le_mul_of_nonneg_left (rio_twentieth_holder (hS.add (hX.const_mul t)) hX)
        (by norm_num : (0:ℝ) ≤ 380)
      dsimp only [h,f,B]
      dsimp only [Pi.add_apply] at hd
      linarith only [hd]
    have hd := rio_tenth_power_smoothness hf hg hpos hHolder hg0
    simpa only [f,B,one_mul,zero_mul,add_zero] using hd

end ASDExplicitGamma.Gaussian
