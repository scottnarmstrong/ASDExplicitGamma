module

public import ASDExplicitGamma.Native.HeatVHEATDriftRareIntegral

/-! Normalized child averaging preserves one exact first-line VHEAT payment. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- The leading common-bank contribution sums to the actual average's
moments before any Holder bound. No extra trace cap replaces these moments. -/
theorem heatVHEATDrift_leading_average_identity
    {I : Type*} (s : Finset I) (w T : I → ℝ) (k : ℕ) (hk : 1 ≤ k) (c : ℝ) :
    (∑ i∈s,w i*((k:ℝ)*c*(∑ j∈s,w j*T j)^(k-1)*(T i+4))) =
      (k:ℝ)*c*((∑ i∈s,w i*T i)^k+4*(∑ i∈s,w i*T i)^(k-1)*(∑ i∈s,w i)) := by
  let A := ∑ i∈s,w i*T i
  calc
    _ = (k:ℝ)*c*A^(k-1)*(∑ i∈s,w i*(T i+4)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (k:ℝ)*c*A^(k-1)*(A+4*(∑ i∈s,w i)) := by
      congr 1
      simp only [mul_add,Finset.sum_add_distrib]
      rw [←Finset.sum_mul]
      dsimp only [A]
      ring
    _ = _ := by
      have hp : A^k=A^(k-1)*A := by
        conv_lhs => rw [show k=(k-1)+1 by omega]
        rw [pow_succ]
      change _=(k:ℝ)*c*(A^k+4*A^(k-1)*(∑ i∈s,w i))
      rw [hp]
      ring

end
end ASDExplicitGamma.Native
