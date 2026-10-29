module

public import ASDExplicitGamma.Native.OldSignedBankPowerRare
public import ASDExplicitGamma.Native.OldSignedDirectionalRareReserve
public import ASDExplicitGamma.Native.OldSignedNonnegativeSeriesIntegral
public import ASDExplicitGamma.Native.OldSignedHistoryBounds

/-! The complete fourth-order local-bank rare history fits inside delta. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Inverse Algsuperdiff.Section3 Numerics.Inverse
noncomputable section

/-- The source binomial tail is linear in its trace observable. -/
theorem old_signed_rare_tail_linear (b R X : ℝ) (k : ℕ) :
    rareExpansionTail b R X k=rareExpansionTail b R 1 k*X := by
  unfold rareExpansionTail
  simp only [mul_one,Finset.sum_mul]

end
end ASDExplicitGamma.Native
