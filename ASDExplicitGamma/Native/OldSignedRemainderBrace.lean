module

public import ASDExplicitGamma.Native.OldSignedRemainderDecay

/-! The full64 OLD generator keeps the squared depth decay in its nonlinear bill. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Inverse
noncomputable section

/-- A scalar comparison for the literal physical p20 bracket. It retains
z squared in both response products instead of using a uniform mesh cap. -/
theorem old_signed_full64_generator_brace (z C F : ℝ)
    (hz : 0≤z) (hz1 : z≤1) (hC : 1≤C) (hF : 0≤F) :
    let κ := rawTraceRemainderKappaF (z/729) (z/729)
    let B := rawTraceRemainderB (z/729) (z/729)
    let μR := rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0
      (rawTraceRemainderA (z/729) (z/729)) B
    (78+76*κ)*(C*(3683/2500))+2*κ*(C*(3683/2500))*F+
      (μR+38*(B^2+κ))*(C*(3683/2500))^2*F ≤
      120*C+(7/125)*z^2*C^2*F := by
  intro κ B μR
  have hC0 : 0≤C := zero_le_one.trans hC
  have hz2 : z^2≤1 := pow_le_one₀ hz hz1
  have hκ := old_signed_remainder_kappa_decay z
  have hB := (old_signed_remainder_AB_decay z hz hz1).2
  have hB0 : 0≤B := by dsimp [B,rawTraceRemainderB]; positivity
  have hμ := old_signed_remainder_mu_decay z hz hz1
  have hκ0 : 0≤κ := by dsimp [κ,rawTraceRemainderKappaF]; positivity
  change κ ≤ (1/10000)*z^2 at hκ
  change B ≤ (21/1000)*z at hB
  change μR ≤ (1/200)*z^2 at hμ
  have hB2 := pow_le_pow_left₀ hB0 hB 2
  have hCsq : C≤C^2 := by nlinarith only [mul_nonneg hC0 (sub_nonneg.mpr hC)]
  have hcoef1 : (78+76*κ)*(3683/2500:ℝ) ≤ 120 := by
    nlinarith only [hκ,hz2]
  have hcoef2 : 2*κ*(3683/2500:ℝ) ≤ (3683/12500000)*z^2 := by
    nlinarith only [hκ]
  have hcoef3 : (μR+38*(B^2+κ))*(3683/2500:ℝ)^2 ≤
      ((1/200)+38*((21/1000:ℝ)^2+1/10000))*(3683/2500:ℝ)^2*z^2 := by
    nlinarith only [hμ,hB2,hκ]
  have hfirst : (78+76*κ)*(C*(3683/2500:ℝ)) ≤ 120*C := by
    convert mul_le_mul_of_nonneg_right hcoef1 hC0 using 1
    ring
  have hsecond : 2*κ*(C*(3683/2500:ℝ))*F ≤ (3683/12500000)*z^2*C^2*F := by
    calc
      _ = (2*κ*(3683/2500:ℝ))*(C*F) := by ring
      _ ≤ ((3683/12500000)*z^2)*(C*F) := mul_le_mul_of_nonneg_right hcoef2 (mul_nonneg hC0 hF)
      _ ≤ ((3683/12500000)*z^2)*(C^2*F) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCsq hF) (by positivity)
      _ = _ := by ring
  have hthird : (μR+38*(B^2+κ))*(C*(3683/2500:ℝ))^2*F ≤
      (((1/200)+38*((21/1000:ℝ)^2+1/10000))*(3683/2500:ℝ)^2)*z^2*C^2*F := by
    convert mul_le_mul_of_nonneg_right hcoef3 (mul_nonneg (sq_nonneg C) hF) using 1 <;> ring
  have hs := add_le_add (add_le_add hfirst hsecond) hthird
  have hnumeric : (3683/12500000:ℝ)+
      ((1/200)+38*((21/1000:ℝ)^2+1/10000))*(3683/2500:ℝ)^2 ≤ 7/125 := by norm_num
  have hn := mul_le_mul_of_nonneg_right hnumeric
    (mul_nonneg (mul_nonneg (sq_nonneg z) (sq_nonneg C)) hF)
  nlinarith only [hs,hn]

end
end ASDExplicitGamma.Native
