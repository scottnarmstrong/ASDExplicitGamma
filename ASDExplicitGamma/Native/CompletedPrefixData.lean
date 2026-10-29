module

public import ASDExplicitGamma.Native.CompletedPrefixWeights
public import ASDExplicitGamma.Numerics.Native.Certificate

/-! Source-bound completed-prefix data and the positive residual.
The old profiles retain every unreplaced depth, weak rare term and full tail. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open ASDExplicitGamma.Numerics.Native
noncomputable section

/-- The six unchanged refined-source OldMean entries, before prefix replacement. -/
def nativeCompletedPrefixOldMean (r : Fin 6) : ℚ :=
  [nativeSource0OldMean,nativeSource1OldMean,nativeSource2OldMean,nativeSource3OldMean,nativeSource4OldMean,nativeSource5OldMean].getD r.val (0)

/-- The six unchanged refined-source OldXi entries, before prefix replacement. -/
def nativeCompletedPrefixOldXi (r : Fin 6) : ℚ :=
  [nativeSource0OldXi,nativeSource1OldXi,nativeSource2OldXi,nativeSource3OldXi,nativeSource4OldXi,nativeSource5OldXi].getD r.val (0)

/-- The six unchanged refined-source Profile entries, before prefix replacement. -/
def nativeCompletedPrefixProfile (r : Fin 6) : List ℚ :=
  [nativeSource0Profile,nativeSource1Profile,nativeSource2Profile,nativeSource3Profile,nativeSource4Profile,nativeSource5Profile].getD r.val ([])

/-- The corrected boundary-fixed parent endpoints, including the exact
ordinary-mean source at depth zero. -/
def nativeCompletedPrefixParents : List ℚ := nativeSource0Parents

end
end ASDExplicitGamma.Native
