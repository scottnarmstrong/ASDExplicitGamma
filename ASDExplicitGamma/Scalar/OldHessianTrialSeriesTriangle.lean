module

public import ASDExplicitGamma.Native.OldSignedSeriesPairingBudget
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Complete covariance-column Minkowski from actual square summability.
The same algebra aggregates the full mixed source and its frozen residual. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
noncomputable section

/-- Constant-one square-series triangle with convergence as a conclusion,
for an arbitrary complete covariance index set. -/
theorem old_hessian_series_energy_triangle {I : Type*} (a b c : I → ℝ)
    (ha : ∀ i,0≤a i) (hb : ∀ i,0≤b i) (hc : ∀ i,0≤c i)
    (has : Summable (fun i => a i^2)) (hbs : Summable (fun i => b i^2))
    (hbound : ∀ i,c i≤a i+b i) :
    Summable (fun i => c i^2) ∧
      Real.sqrt (∑' i,c i^2)≤Real.sqrt (∑' i,a i^2)+Real.sqrt (∑' i,b i^2) := by
  have hm := Native.old_signed_series_pairing_budget a b (fun i => a i*b i) ha hb has hbs
    (fun i => le_of_eq (abs_of_nonneg (mul_nonneg (ha i) (hb i))))
  have hp (i : I) : c i^2≤a i^2+2*(a i*b i)+b i^2 :=
    (pow_le_pow_left₀ (hc i) (hbound i) 2).trans_eq (by ring)
  have hs := (has.add (hm.1.mul_left 2)).add hbs
  have hcs := hs.of_nonneg_of_le (fun i => sq_nonneg (c i)) hp
  have ht := hcs.tsum_le_tsum hp hs
  rw [Summable.tsum_add (has.add (hm.1.mul_left 2)) hbs,
    Summable.tsum_add has (hm.1.mul_left 2),tsum_mul_left] at ht
  have hcross := (le_abs_self _).trans hm.2
  refine ⟨hcs,(Real.sqrt_le_iff).2 ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),?_⟩⟩
  calc
    _ ≤ (∑' i,a i^2)+2*(∑' i,a i*b i)+(∑' i,b i^2) := ht
    _ ≤ (∑' i,a i^2)+2*(Real.sqrt (∑' i,a i^2)*Real.sqrt (∑' i,b i^2))+(∑' i,b i^2) :=
      add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hcross (by norm_num))) le_rfl
    _ = _ := by
      rw [add_sq,Real.sq_sqrt (tsum_nonneg (fun i => sq_nonneg (a i))),
        Real.sq_sqrt (tsum_nonneg (fun i => sq_nonneg (b i)))]
      ring

end
end ASDExplicitGamma.Scalar
