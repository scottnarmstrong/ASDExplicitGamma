module
public import ASDExplicitGamma.Numerics.Native.EndpointQ1001
public import ASDExplicitGamma.Numerics.Native.EndpointParent001
public import ASDExplicitGamma.Numerics.Native.EndpointParent002
public import ASDExplicitGamma.Numerics.Native.EndpointParent003
public import ASDExplicitGamma.Numerics.Native.EndpointParent004
public import ASDExplicitGamma.Numerics.Native.EndpointParent005
public import ASDExplicitGamma.Numerics.Native.EndpointParent006
public import ASDExplicitGamma.Numerics.Native.EndpointParent007
public import ASDExplicitGamma.Numerics.Native.EndpointParent008
public import ASDExplicitGamma.Numerics.Native.EndpointParent009
public import ASDExplicitGamma.Numerics.Native.EndpointParent010
public import ASDExplicitGamma.Numerics.Native.EndpointParent011
public import ASDExplicitGamma.Numerics.Native.EndpointParent012
public import ASDExplicitGamma.Numerics.Native.EndpointParent013
public import ASDExplicitGamma.Numerics.Native.EndpointParent014
public import ASDExplicitGamma.Numerics.Native.EndpointParent015
public import ASDExplicitGamma.Numerics.Native.EndpointParent016
public import ASDExplicitGamma.Numerics.Native.Source0
public import ASDExplicitGamma.Numerics.Native.Source1
public import ASDExplicitGamma.Numerics.Native.Source2
public import ASDExplicitGamma.Numerics.Native.Source3
public import ASDExplicitGamma.Numerics.Native.Source4
public import ASDExplicitGamma.Numerics.Native.Source5
public import ASDExplicitGamma.Numerics.Native.PanelReadable

/-! Closed boundary-fixed OLD q1 and parent certificates, linked to all six completed prefixes. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

structure NativeBoundaryEndpointCertificate where
  fields : List ℝ
  frame : ℝ
  b0 : ℝ
  inverseCost : ℝ
  cap : ℚ
  carried : ℚ
  bound : nativePanelEndpoint fields frame b0 inverseCost ≤ (cap : ℝ)
  lt_carried : cap < carried

noncomputable def nativeParent001EndpointCertificate : NativeBoundaryEndpointCertificate :=
  ⟨nativeSetupParent001FieldsR,nativeSetupParent001FrameR,nativeSetupParent001B0R,nativeSetupParent001InvcostR,nativeEndpointParent001Cap,nativeEndpointParent001PublishedCap,
    nativeEndpointParent001_bound,nativeEndpointParent001_carried⟩

noncomputable def nativeParent002EndpointCertificate : NativeBoundaryEndpointCertificate :=
  ⟨nativeSetupParent002FieldsR,nativeSetupParent002FrameR,nativeSetupParent002B0R,nativeSetupParent002InvcostR,nativeEndpointParent002Cap,nativeEndpointParent002PublishedCap,
    nativeEndpointParent002_bound,nativeEndpointParent002_carried⟩

noncomputable def nativeParent003EndpointCertificate : NativeBoundaryEndpointCertificate :=
  ⟨nativeSetupParent003FieldsR,nativeSetupParent003FrameR,nativeSetupParent003B0R,nativeSetupParent003InvcostR,nativeEndpointParent003Cap,nativeEndpointParent003PublishedCap,
    nativeEndpointParent003_bound,nativeEndpointParent003_carried⟩

noncomputable def nativeParent004EndpointCertificate : NativeBoundaryEndpointCertificate :=
  ⟨nativeSetupParent004FieldsR,nativeSetupParent004FrameR,nativeSetupParent004B0R,nativeSetupParent004InvcostR,nativeEndpointParent004Cap,nativeEndpointParent004PublishedCap,
    nativeEndpointParent004_bound,nativeEndpointParent004_carried⟩

noncomputable def nativeParent005EndpointCertificate : NativeBoundaryEndpointCertificate :=
  ⟨nativeSetupParent005FieldsR,nativeSetupParent005FrameR,nativeSetupParent005B0R,nativeSetupParent005InvcostR,nativeEndpointParent005Cap,nativeEndpointParent005PublishedCap,
    nativeEndpointParent005_bound,nativeEndpointParent005_carried⟩

noncomputable def nativeParent006EndpointCertificate : NativeBoundaryEndpointCertificate :=
  ⟨nativeSetupParent006FieldsR,nativeSetupParent006FrameR,nativeSetupParent006B0R,nativeSetupParent006InvcostR,nativeEndpointParent006Cap,nativeEndpointParent006PublishedCap,
    nativeEndpointParent006_bound,nativeEndpointParent006_carried⟩

noncomputable def nativeParent007EndpointCertificate : NativeBoundaryEndpointCertificate :=
  ⟨nativeSetupParent007FieldsR,nativeSetupParent007FrameR,nativeSetupParent007B0R,nativeSetupParent007InvcostR,nativeEndpointParent007Cap,nativeEndpointParent007PublishedCap,
    nativeEndpointParent007_bound,nativeEndpointParent007_carried⟩

noncomputable def nativeParent008EndpointCertificate : NativeBoundaryEndpointCertificate :=
  ⟨nativeSetupParent008FieldsR,nativeSetupParent008FrameR,nativeSetupParent008B0R,nativeSetupParent008InvcostR,nativeEndpointParent008Cap,nativeEndpointParent008PublishedCap,
    nativeEndpointParent008_bound,nativeEndpointParent008_carried⟩

noncomputable def nativeParent009EndpointCertificate : NativeBoundaryEndpointCertificate :=
  ⟨nativeSetupParent009FieldsR,nativeSetupParent009FrameR,nativeSetupParent009B0R,nativeSetupParent009InvcostR,nativeEndpointParent009Cap,nativeEndpointParent009PublishedCap,
    nativeEndpointParent009_bound,nativeEndpointParent009_carried⟩

noncomputable def nativeParent010EndpointCertificate : NativeBoundaryEndpointCertificate :=
  ⟨nativeSetupParent010FieldsR,nativeSetupParent010FrameR,nativeSetupParent010B0R,nativeSetupParent010InvcostR,nativeEndpointParent010Cap,nativeEndpointParent010PublishedCap,
    nativeEndpointParent010_bound,nativeEndpointParent010_carried⟩

noncomputable def nativeParent011EndpointCertificate : NativeBoundaryEndpointCertificate :=
  ⟨nativeSetupParent011FieldsR,nativeSetupParent011FrameR,nativeSetupParent011B0R,nativeSetupParent011InvcostR,nativeEndpointParent011Cap,nativeEndpointParent011PublishedCap,
    nativeEndpointParent011_bound,nativeEndpointParent011_carried⟩

noncomputable def nativeParent012EndpointCertificate : NativeBoundaryEndpointCertificate :=
  ⟨nativeSetupParent012FieldsR,nativeSetupParent012FrameR,nativeSetupParent012B0R,nativeSetupParent012InvcostR,nativeEndpointParent012Cap,nativeEndpointParent012PublishedCap,
    nativeEndpointParent012_bound,nativeEndpointParent012_carried⟩

noncomputable def nativeParent013EndpointCertificate : NativeBoundaryEndpointCertificate :=
  ⟨nativeSetupParent013FieldsR,nativeSetupParent013FrameR,nativeSetupParent013B0R,nativeSetupParent013InvcostR,nativeEndpointParent013Cap,nativeEndpointParent013PublishedCap,
    nativeEndpointParent013_bound,nativeEndpointParent013_carried⟩

noncomputable def nativeParent014EndpointCertificate : NativeBoundaryEndpointCertificate :=
  ⟨nativeSetupParent014FieldsR,nativeSetupParent014FrameR,nativeSetupParent014B0R,nativeSetupParent014InvcostR,nativeEndpointParent014Cap,nativeEndpointParent014PublishedCap,
    nativeEndpointParent014_bound,nativeEndpointParent014_carried⟩

noncomputable def nativeParent015EndpointCertificate : NativeBoundaryEndpointCertificate :=
  ⟨nativeSetupParent015FieldsR,nativeSetupParent015FrameR,nativeSetupParent015B0R,nativeSetupParent015InvcostR,nativeEndpointParent015Cap,nativeEndpointParent015PublishedCap,
    nativeEndpointParent015_bound,nativeEndpointParent015_carried⟩

noncomputable def nativeParent016EndpointCertificate : NativeBoundaryEndpointCertificate :=
  ⟨nativeSetupParent016FieldsR,nativeSetupParent016FrameR,nativeSetupParent016B0R,nativeSetupParent016InvcostR,nativeEndpointParent016Cap,nativeEndpointParent016PublishedCap,
    nativeEndpointParent016_bound,nativeEndpointParent016_carried⟩

noncomputable def nativeParentEndpointCertificates : List NativeBoundaryEndpointCertificate := [
  nativeParent001EndpointCertificate,
  nativeParent002EndpointCertificate,
  nativeParent003EndpointCertificate,
  nativeParent004EndpointCertificate,
  nativeParent005EndpointCertificate,
  nativeParent006EndpointCertificate,
  nativeParent007EndpointCertificate,
  nativeParent008EndpointCertificate,
  nativeParent009EndpointCertificate,
  nativeParent010EndpointCertificate,
  nativeParent011EndpointCertificate,
  nativeParent012EndpointCertificate,
  nativeParent013EndpointCertificate,
  nativeParent014EndpointCertificate,
  nativeParent015EndpointCertificate,
  nativeParent016EndpointCertificate
]

def nativeBoundaryParentCaps : List ℚ := [nativeA,
  nativeEndpointParent001Cap,
  nativeEndpointParent002Cap,
  nativeEndpointParent003Cap,
  nativeEndpointParent004Cap,
  nativeEndpointParent005Cap,
  nativeEndpointParent006Cap,
  nativeEndpointParent007Cap,
  nativeEndpointParent008Cap,
  nativeEndpointParent009Cap,
  nativeEndpointParent010Cap,
  nativeEndpointParent011Cap,
  nativeEndpointParent012Cap,
  nativeEndpointParent013Cap,
  nativeEndpointParent014Cap,
  nativeEndpointParent015Cap,
  nativeEndpointParent016Cap
]

theorem nativeBoundaryParentCaps_source : nativeBoundaryParentCaps = nativeSource0Parents ∧
    nativeBoundaryParentCaps = nativeSource1Parents ∧
    nativeBoundaryParentCaps = nativeSource2Parents ∧
    nativeBoundaryParentCaps = nativeSource3Parents ∧
    nativeBoundaryParentCaps = nativeSource4Parents ∧
    nativeBoundaryParentCaps = nativeSource5Parents := by
  decide +kernel

noncomputable def nativeConfiguredParentEndpoint (j : Fin 16) : NativeBoundaryEndpointCertificate :=
  nativeParentEndpointCertificates.getD j.val nativeParent001EndpointCertificate

theorem native_boundary_parent_endpoint_bound (j : Fin 16) :
    nativePanelEndpoint (nativeConfiguredParentEndpoint j).fields (nativeConfiguredParentEndpoint j).frame
      (nativeConfiguredParentEndpoint j).b0 (nativeConfiguredParentEndpoint j).inverseCost ≤
      ((nativeConfiguredParentEndpoint j).cap : ℝ) :=
  (nativeConfiguredParentEndpoint j).bound

theorem native_boundary_parent_endpoint_carried (j : Fin 16) :
    (nativeConfiguredParentEndpoint j).cap < (nativeConfiguredParentEndpoint j).carried :=
  (nativeConfiguredParentEndpoint j).lt_carried

end ASDExplicitGamma.Numerics.Native
