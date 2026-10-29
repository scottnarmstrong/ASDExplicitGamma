module

public import ASDExplicitGamma.Scalar.PairedTwoSlotRep
public import ASDExplicitGamma.Scalar.PairedTwoSlotAlgebra

/-! Function-level description of the two-slot NEW inverse on the parent cube. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational
open scoped InnerProduct InnerProductSpace

noncomputable section

theorem toHilbert_congr {U : Set (Vec 2)} {f g : Vec 2 → Vec 2}
    (hf : MemVectorL2 U f) (hg : MemVectorL2 U g) (h : f =ᵐ[volumeMeasureOn U] g) :
    toHilbertVectorL2OfVecField hf = toHilbertVectorL2OfVecField hg := by
  apply MeasureTheory.Lp.ext
  filter_upwards [coeFn_toHilbertVectorL2OfVecField hf, coeFn_toHilbertVectorL2OfVecField hg, h]
    with z h1 h2 h3
  rw [h1, h2]
  simp [hilbertifyVecField, h3]

theorem rep_ofField {U : Set (Vec 2)} {f : Vec 2 → Vec 2} (hf : MemVectorL2 U f) :
    rep' (toHilbertVectorL2OfVecField hf) =ᵐ[volumeMeasureOn U] f := by
  have h := hilbertVectorL2ToVectorL2_toHilbertVectorL2 (U := U) hf
  have h2 := coeFn_toVectorL2 hf
  unfold rep'
  rw [h]
  exact h2

theorem ofField_eq' {U : Set (Vec 2)} {f g : Vec 2 → Vec 2}
    (hf : MemVectorL2 U f) (hg : MemVectorL2 U g) (h : f = g) :
    toHilbertVectorL2OfVecField hf = toHilbertVectorL2OfVecField hg := by
  subst h; rfl

end

end ASDExplicitGamma.Scalar
