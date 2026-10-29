module

public import ASDExplicitGamma.Native.GenericSourcePass
public import Mathlib.Tactic.FinCases

/-! An auxiliary eight-pass p20 enclosure for the one-shell starting law.
Every interpolation radical is paid by a checked integer-power inequality. -/
@[expose] public section
namespace ASDExplicitGamma.Native
noncomputable section

/-- Integer-power soundness for a positive rational interpolation monomial. -/
theorem native_source_rpow_product_cap (x f u : ℝ) (a b n : ℕ)
    (hx : 0 ≤ x) (hf : 0 ≤ f) (hu : 0 ≤ u) (hn : 0<n)
    (hpow : x^a*f^b ≤ u^n) :
    x^((a:ℝ)/(n:ℝ))*f^((b:ℝ)/(n:ℝ)) ≤ u := by
  have hh := Real.rpow_le_rpow (mul_nonneg (pow_nonneg hx a) (pow_nonneg hf b))
    hpow (inv_nonneg.mpr (Nat.cast_nonneg n : (0:ℝ)≤n))
  rw [Real.pow_rpow_inv_natCast hu hn.ne'] at hh
  convert hh using 1
  rw [Real.mul_rpow (pow_nonneg hx a) (pow_nonneg hf b),
    ←Real.rpow_natCast x a,←Real.rpow_natCast f b,←Real.rpow_mul hx,←Real.rpow_mul hf]
  congr 1

/-- Auxiliary integer caps after zero through eight generic source refinements. -/
def nativeSourceExtraPassKnots : Fin 9 → ℚ := ![(3325/1:ℚ),(1234/1:ℚ),(661/1:ℚ),(446/1:ℚ),(349/1:ℚ),(299/1:ℚ),(271/1:ℚ),(255/1:ℚ),(246/1:ℚ)]

/-- Outward power-certified interpolation witnesses for the first Holder monomial. -/
def nativeSourceExtraPassU1 : Fin 8 → ℚ := ![(111196/25:ℚ),(198331/100:ℚ),(119257/100:ℚ),(86549/100:ℚ),(17718/25:ℚ),(31241/50:ℚ),(14418/25:ℚ),(27441/50:ℚ)]

/-- Outward power-certified interpolation witnesses for the second Holder monomial. -/
def nativeSourceExtraPassU2 : Fin 8 → ℚ := ![(118997/20:ℚ),(318761/100:ℚ),(107581/50:ℚ),(167951/100:ℚ),(7196/5:ℚ),(130569/100:ℚ),(122731/100:ℚ),(118117/100:ℚ)]

/-- Every auxiliary step is checked in exact rational arithmetic. This is
an additional comparison enclosure, without changing any source constant. -/
theorem native_source_extra_pass_certificate (i : Fin 8) :
    let x := nativeSourceExtraPassKnots ⟨i.val,by omega⟩
    let y := nativeSourceExtraPassKnots ⟨i.val+1,by omega⟩
    let u := nativeSourceExtraPassU1 i
    let v := nativeSourceExtraPassU2 i
    0 ≤ x ∧ 0 ≤ u ∧ 0 ≤ v ∧ x^22*(16000:ℚ)^5 ≤ u^27 ∧
    x^17*(16000:ℚ)^10 ≤ v^27 ∧
    (21/100:ℚ)+(77/50000:ℚ)*
      ((39+38*(521/1000:ℚ))*(2*(3683/2500:ℚ))+
        2*(521/1000:ℚ)*(3683/2500:ℚ)*(4+u)+
        ((1975/1000:ℚ)+38*(1565/1000:ℚ))*(3683/2500:ℚ)^2*(4+v)) ≤ y := by
  fin_cases i <;> decide +kernel

end
end ASDExplicitGamma.Native
