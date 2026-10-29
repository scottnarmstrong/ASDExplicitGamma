module

public import ASDExplicitGamma.Native.GenericSourceExtraPassNumerics

/-! Real soundness of the auxiliary eight-pass starting-moment enclosure. -/
@[expose] public section
namespace ASDExplicitGamma.Native
noncomputable section

private theorem source_extra_pass_step (i : Fin 8) (x : ℝ) (hx : 0 ≤ x)
    (hcap : x ≤ (nativeSourceExtraPassKnots ⟨i.val,by omega⟩:ℝ)) :
    (21/100:ℝ)+nativeSourceRefinedMomentIncrement 1 (77/50000) 16000 x ≤
      (nativeSourceExtraPassKnots ⟨i.val+1,by omega⟩:ℝ) := by
  let X : ℚ := nativeSourceExtraPassKnots ⟨i.val,by omega⟩
  let u := nativeSourceExtraPassU1 i
  let v := nativeSourceExtraPassU2 i
  have hc := native_source_extra_pass_certificate i
  have hX : (0:ℝ) ≤ X := by exact_mod_cast hc.1
  have hu : (0:ℝ) ≤ u := by exact_mod_cast hc.2.1
  have hv : (0:ℝ) ≤ v := by exact_mod_cast hc.2.2.1
  have hp1 : (X:ℝ)^22*(16000:ℝ)^5 ≤ (u:ℝ)^27 := by exact_mod_cast hc.2.2.2.1
  have hp2 : (X:ℝ)^17*(16000:ℝ)^10 ≤ (v:ℝ)^27 := by exact_mod_cast hc.2.2.2.2.1
  have hpow1 := native_source_rpow_product_cap X 16000 u 22 5 27 hX (by norm_num) hu (by norm_num) hp1
  have hpow2 := native_source_rpow_product_cap X 16000 v 17 10 27 hX (by norm_num) hv (by norm_num) hp2
  have hm := native_source_interpolation_caps_monotone (theta := 1) (by norm_num)
    hx hX (by simpa only [one_mul] using hcap) (by norm_num : (0:ℝ)≤16000) le_rfl
  have hD : nativeSourceInterpolationD x ≤ 2*(3683/2500:ℝ) := min_le_left _ _
  have hU1 : nativeSourceInterpolationU1 x 16000 ≤ 4+(u:ℝ) := by
    apply hm.2.1.trans
    apply (min_le_right _ _).trans
    apply add_le_add le_rfl
    convert hpow1 using 1; norm_num [nativeSourceEll]
  have hU2 : nativeSourceInterpolationU2 x 16000 ≤ 4+(v:ℝ) := by
    apply hm.2.2.trans
    apply (min_le_right _ _).trans
    apply add_le_add le_rfl
    convert hpow2 using 1; norm_num [nativeSourceEll]
  have hterms := add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hD (by norm_num : (0:ℝ)≤39+38*(521/1000)))
    (mul_le_mul_of_nonneg_left hU1 (by norm_num : (0:ℝ)≤2*(521/1000)*(3683/2500))))
    (mul_le_mul_of_nonneg_left hU2 (by norm_num : (0:ℝ)≤((1975/1000)+38*(1565/1000))*(3683/2500)^2))
  have hcost := add_le_add (le_refl (21/100:ℝ))
    (mul_le_mul_of_nonneg_left hterms (by norm_num : (0:ℝ)≤77/50000))
  have hnumeric : (21/100:ℝ)+(77/50000:ℝ)*
      ((39+38*(521/1000:ℝ))*(2*(3683/2500:ℝ))+
        2*(521/1000:ℝ)*(3683/2500:ℝ)*(4+(u:ℝ))+
        ((1975/1000:ℝ)+38*(1565/1000:ℝ))*(3683/2500:ℝ)^2*(4+(v:ℝ))) ≤
      (nativeSourceExtraPassKnots ⟨i.val+1,by omega⟩:ℝ) := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hc.2.2.2.2.2
    norm_num only [Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_div,Rat.cast_ofNat] at hh
    convert hh using 1
    norm_num [u,v]
  apply le_trans ?_ hnumeric
  simpa only [nativeSourceRefinedMomentIncrement,nativeSourceK,nativeSourceM,nativeSourceQ,
    nativeSourceB128,Nat.cast_one,mul_one] using hcost

/-- The auxiliary generic order-20 individual profile is at most 246
at the stated outward variance/full-response inputs, after eight passes. -/
theorem native_source_extra_pass_eight_cap :
    nativeSourceGenericIndividualCap 1 (3/50) (77/50000) 16000 8 ≤ 246 := by
  have hall : ∀ j, ∀ hj : j ≤ 8,
      nativeSourceGenericIndividualCap 1 (3/50) (77/50000) 16000 j ≤
        (nativeSourceExtraPassKnots ⟨j,by omega⟩:ℝ) := by
    intro j
    induction j with
    | zero =>
      intro hj
      norm_num [nativeSourceGenericIndividualCap,nativeSourceGenericPassCap,nativeSourceRawMomentIncrement,
        nativeSourceK,nativeSourceM,nativeSourceQ,nativeSourceB128,nativeSourceExtraPassKnots]
    | succ j ih =>
      intro hj
      have hj0 : j ≤ 8 := by omega
      let i : Fin 8 := ⟨j,by omega⟩
      have hx := native_source_generic_individual_nonneg 1 (3/50) (77/50000) 16000
        (by norm_num) (by norm_num) (by norm_num) j
      have hstep := source_extra_pass_step i
        (nativeSourceGenericIndividualCap 1 (3/50) (77/50000) 16000 j) hx (ih hj0)
      apply le_trans ?_ hstep
      change 7/2*(3/50:ℝ)+min _ _ ≤ (21/100:ℝ)+_
      have hh := add_le_add (le_refl (21/100:ℝ)) (min_le_right
        (nativeSourceGenericPassCap 1 (3/50) (77/50000) 16000 j)
        (nativeSourceRefinedMomentIncrement 1 (77/50000) 16000
          (nativeSourceGenericIndividualCap 1 (3/50) (77/50000) 16000 j)))
      convert hh using 1; norm_num [nativeSourceGenericIndividualCap]
  convert hall 8 le_rfl using 1; norm_num [nativeSourceExtraPassKnots]

end
end ASDExplicitGamma.Native
