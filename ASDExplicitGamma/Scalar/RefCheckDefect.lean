module

public import ASDExplicitGamma.Scalar.FwIdentPriv
public import ASDExplicitGamma.Variational.LocalizedBlockSpace
public import ASDExplicitGamma.Scalar.DefectResolventCarriers
public import ASDExplicitGamma.Scalar.FwIdentField
public import ASDExplicitGamma.Scalar.ProjectionCharacterization
public import ASDExplicitGamma.Native.OldSignedCellProjection
public import ASDExplicitGamma.Scalar.PairedTwoSlotRep

/-! Reference check (ii): the zero-coefficient first response of a potential-affine load. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization ASDExplicitGamma.Response ASDExplicitGamma.Variational
  ASDExplicitGamma.Triadic ASDExplicitGamma.Native MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

theorem def_vec_ext {U : Set (Vec 2)} [IsFiniteMeasure (volumeMeasureOn U)]
    {p p' : HilbertVectorL2 U}
    (h : hilbertVectorL2ToVectorL2 p =ᵐ[volumeMeasureOn U] hilbertVectorL2ToVectorL2 p') :
    p = p' := by
  have h1 : hilbertVectorL2ToVectorL2 p = hilbertVectorL2ToVectorL2 p' := Lp.ext h
  rw [← vectorL2ToHilbertVectorL2_hilbertVectorL2ToVectorL2 p,
    ← vectorL2ToHilbertVectorL2_hilbertVectorL2ToVectorL2 p', h1]

variable (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)

end

end ASDExplicitGamma.Scalar
