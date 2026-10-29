module
public import ASDExplicitGamma.Numerics.Native.Basic

/-! The completed-prefix arithmetic, with the boundary-fixed OLD parent endpoints.
Step label: NU-NA-SOURCE-ROWS.
-/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

/-- Every input is a source numerical datum, including the r=0 earlier-label mean. -/
def nativeSourcePrefix (r : ℕ) (oldMean oldXi : ℚ) (oldProfile parents : List ℚ) : ℚ × ℚ :=
  let gain := ((List.range (17-r)).map fun j =>
    (3683/2500)*(1-(759836/10^6 : ℚ)^2)*(759835/10^6 : ℚ)^(2*j)*
      max 0 (oldProfile.getD j 0-parents.getD (r+j) 0)).sum
  (min oldMean (parents.getD r 0),oldXi-gain)

end ASDExplicitGamma.Numerics.Native
