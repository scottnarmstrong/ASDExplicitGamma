module

public import ASDExplicitGamma.Native.OldSignedFlatDirichletEnergy
public import ASDExplicitGamma.Native.OldSignedComplementaryPhysicalField

/-! Exact source-load sign symmetry of the actual parent Dirichlet
projection, independent of the selected H10 representative. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Main
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
noncomputable section

/-- The actual q3 vector source in the physical Hilbert L2 carrier. -/
def oldSignedRawVectorLoad (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (v : Vec 2) : HilbertVectorL2 (openCubeSet Q) :=
  toHilbertVectorL2OfVecField
    (lambda8H1ComponentField_memVectorL2 (fun k => lambda8Q3GaussianModeLoadH1 Q b L v n k))

/-- The vector source retains its actual convolution representative. -/
theorem old_signed_raw_vector_load_coeFn (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (v : Vec 2) :
    oldSignedRawVectorLoad Q b L n v =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => HilbertVec.ofVec (q3Convolution b L h3Zero (whiteBasis n) x • v) :=
  coeFn_toHilbertVectorL2OfVecField _

/-- Changing the sign of a load changes the actual Hilbert source by its
negative, before the local projection is applied. -/
theorem old_signed_raw_vector_load_neg (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (v : Vec 2) :
    oldSignedRawVectorLoad Q b L n (-v)= -oldSignedRawVectorLoad Q b L n v := by
  apply Lp.ext
  filter_upwards [old_signed_raw_vector_load_coeFn Q b L n (-v),
    Lp.coeFn_neg (oldSignedRawVectorLoad Q b L n v),old_signed_raw_vector_load_coeFn Q b L n v]
    with x hl hn hr
  rw [hl,hn]
  simp only [Pi.neg_apply]
  rw [hr]
  ext k
  simp [HilbertVec.ofVec]

/-- The actual selected parent gradient changes sign in Hilbert L2; this
uses projection linearity and does not equate arbitrary chosen potentials. -/
theorem old_signed_q3_parent_gradient_neg (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (v : Vec 2) :
    (lambda8Q3GaussianModeParentPotential Q b L (-v) n).toH1Function.gradToHilbertVectorL2=
      -(lambda8Q3GaussianModeParentPotential Q b L v n).toH1Function.gradToHilbertVectorL2 := by
  have hneg := (lambda8Q3GaussianModeParentPotential_spec Q b L (-v) n).1
  have hpos := (lambda8Q3GaussianModeParentPotential_spec Q b L v n).1
  change lambda8DirichletProjection _ (oldSignedRawVectorLoad Q b L n (-v))=_ at hneg
  change lambda8DirichletProjection _ (oldSignedRawVectorLoad Q b L n v)=_ at hpos
  rw [←hneg,←hpos,old_signed_raw_vector_load_neg]
  exact map_neg (lambda8H10GradientRange (isOpenBoundedConvexDomain_openCubeSet Q)).toSubmodule.starProjection _

end
end ASDExplicitGamma.Native
