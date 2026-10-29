module
public import ASDExplicitGamma.Numerics.Native.SystemCertificate
public import ASDExplicitGamma.Numerics.Native.Gap001Certificate

@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeGap001Certificate : NativeSystemCertificate :=
  ⟨1,nativeGap001System,nativeGap001Result,nativeGap001Domain.1,nativeGap001Domain.2.1,
    nativeGap001Domain.2.2.1,nativeGap001Domain.2.2.2,nativeGap001Exp_bound⟩

def nativeSystemGap1 : List NativeSystemCertificate := [
  nativeGap001Certificate
]

end ASDExplicitGamma.Numerics.Native
