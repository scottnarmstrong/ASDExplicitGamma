module

public import ASDExplicitGamma.Native.SourceSmallerGammaInterface

/-! Exact physical weights bounded by their finite outward brackets. -/
@[expose] public section
namespace ASDExplicitGamma.Native
noncomputable section

/-- The canonical inverse-history discount is the fourth root bracketed by
the source data, independently of any numerical notation convention. -/
theorem native_source_history_alpha_eq :
    Scalar.inverseHistoryDiscount=(1/3:ℝ)^(1/4:ℝ) := by
  rw [Scalar.inverse_history_discount_eq]
  simpa only [one_div] using (Real.inv_rpow (by norm_num : (0:ℝ)≤3) (1/4:ℝ)).symm

/-- Both the physical normalization and every physical depth weight are
bounded by the outward row weights at the same gamma. -/
theorem native_source_physical_weights (gamma : ℝ) (hg0 : 0 ≤ gamma) (hg : gamma ≤ 17/50000) :
    0 ≤ 1-Scalar.inverseHistoryDiscount^2 ∧
    1-Scalar.inverseHistoryDiscount^2 ≤ 1-nativeSourceAlphaMinus^2 ∧
    ∀ j : ℕ, Scalar.inverseHistoryDiscount^(2*j)*(3:ℝ)^(2*gamma*(j:ℝ)) ≤
      (nativeSourceHistoryWeight gamma)^j := by
  let alpha := Scalar.inverseHistoryDiscount
  have ha0 : 0 ≤ alpha := Scalar.inverse_history_discount_range.1.le
  have ha1 : alpha ≤ 1 := Scalar.inverse_history_discount_range.2.le
  have hal : nativeSourceAlphaMinus ≤ alpha := by
    dsimp only [alpha]
    rw [native_source_history_alpha_eq]
    exact native_completed_prefix_alpha_bracket.1
  have hau : alpha ≤ nativeSourceAlphaPlus := by
    dsimp only [alpha]
    rw [native_source_history_alpha_eq]
    exact native_completed_prefix_alpha_bracket.2
  have ha2 : alpha^2 ≤ nativeSourceAlphaPlus^2 := pow_le_pow_left₀ ha0 hau 2
  have hal2 : nativeSourceAlphaMinus^2 ≤ alpha^2 :=
    pow_le_pow_left₀ (by norm_num [nativeSourceAlphaMinus]) hal 2
  have ha21 : alpha^2 ≤ 1 := (pow_le_pow_left₀ ha0 ha1 2).trans_eq (by norm_num)
  have hE := native_source_E_ge_three_power gamma 1 hg0 hg (by norm_num)
  norm_num only [Nat.cast_one,mul_one] at hE
  have hq : alpha^2*(3:ℝ)^(2*gamma) ≤ nativeSourceHistoryWeight gamma :=
    mul_le_mul ha2 hE (Real.rpow_nonneg (by norm_num) _) (sq_nonneg _)
  refine ⟨sub_nonneg.mpr ha21,sub_le_sub_left hal2 1,?_⟩
  intro j
  have hthree : (3:ℝ)^(2*gamma*(j:ℝ))=((3:ℝ)^(2*gamma))^j := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ)≤3)]
  have hgeom : alpha^(2*j)*(3:ℝ)^(2*gamma*(j:ℝ))=(alpha^2*(3:ℝ)^(2*gamma))^j := by
    rw [hthree,mul_pow,pow_mul]
  rw [hgeom]
  exact pow_le_pow_left₀ (mul_nonneg (sq_nonneg _) (by positivity)) hq j

end
end ASDExplicitGamma.Native
