module
public import ASDExplicitGamma.Numerics.Native.SystemGap1
public import ASDExplicitGamma.Numerics.Native.Systems10To60
public import ASDExplicitGamma.Numerics.Native.Systems61To111
public import ASDExplicitGamma.Numerics.Native.Systems112To161

/-! All 153 configured native systems, with the separate refined gap-one row retained. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

def nativeAllSystems : List NativeSystemCertificate :=
  nativeSystemGap1 ++ nativeSystems10To60 ++ nativeSystems61To111 ++ nativeSystems112To161

def nativeConfiguredSystem (j : Fin 153) : NativeSystemCertificate :=
  nativeAllSystems.getD j.val nativeGap001Certificate

/-- Every complete outward vector is also retained, for consumers of the returned moments. -/
theorem native_configured_system_replay (j : Fin 153) (i : Fin 21) :
    (NormedSpace.exp (nativeSystemMatrix (nativeConfiguredSystem j).system) *ᵥ
      nativeVectorReal (nativeConfiguredSystem j).system.v) i ≤
    nativeVectorReal (nativeConfiguredSystem j).result i :=
  (nativeConfiguredSystem j).replay i

end ASDExplicitGamma.Numerics.Native
