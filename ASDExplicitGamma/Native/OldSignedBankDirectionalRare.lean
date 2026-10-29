module

public import ASDExplicitGamma.Native.OldSignedActualDirectionalRare
public import ASDExplicitGamma.Inverse.RawShellBandBankInputs

/-! Actual local-bank rare payments with all moment inputs discharged by
the inverse bank and raw-trace transport producers. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Inverse Algsuperdiff.Section3 Numerics.Inverse
open scoped ENNReal
noncomputable section

/-- The literal local-bank remainder on the one-shell OLD insertion. -/
def oldSignedLocalBankRemainder (M : ABKModel 2) (n : ℤ) (t : ℝ) :
    Cutoff.CutoffSample 2 → ℝ :=
  inverseBankPopulationRemainder .localInverse (bankLocalRoots (originCube 2 n) 5)
    M n (n+(1:ℕ)) (bankPartialInsertionWeights n 1 t)

end
end ASDExplicitGamma.Native
