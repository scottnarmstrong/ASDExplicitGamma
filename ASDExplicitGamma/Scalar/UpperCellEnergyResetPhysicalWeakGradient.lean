module

public import ASDExplicitGamma.Scalar.UpperCellEnergyResetPhysicalTest
public import Homogenization.Sobolev.Foundations.H1Graph.Graph

/-! One physical exceptional null set for all weak-gradient tests of a
stationary field with strong horizontal derivatives. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Probability.Stationary
open Algsuperdiff.Section3.Provider.Corrector
noncomputable section

/-- Separable Hilbert duality supplies one exceptional null set for all
continuous linear constraints in an arbitrary prescribed family. -/
theorem upper_cell_reset_ae_all_functionals
    {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SecondCountableTopology H] (Y : Ω → H) (S : Set (H →L[ℝ] ℝ))
    (h : ∀ L ∈ S,∀ᵐ ω ∂μ,L (Y ω)=0) :
    ∀ᵐ ω ∂μ,∀ L ∈ S,L (Y ω)=0 := by
  let v := fun L : H →L[ℝ] ℝ => (InnerProductSpace.toDual ℝ H).symm L
  have ha := Model.ae_forall_inner_eq_zero_of_forall_ae Y (v '' S) (by
    rintro _ ⟨L,hL,rfl⟩
    filter_upwards [h L hL] with ω hω
    rw [real_inner_comm,InnerProductSpace.toDual_symm_apply]
    exact hω)
  filter_upwards [ha] with ω hω L hL
  have hh := hω (v L) ⟨L,hL,rfl⟩
  rw [real_inner_comm,InnerProductSpace.toDual_symm_apply] at hh
  exact hh

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- A true stationary strong horizontal gradient is a physical weak gradient
on each observation cube almost surely, with one null set valid for all tests.
No spatial regularity premise is added to the resulting physical field. -/
theorem upper_cell_reset_horizontal_physical_weak_gradient
    (Q : TriadicCube d) {X : Ω → ℝ} {G : Ω → HilbertVec d}
    (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ)
    (hGm : StronglyMeasurable G) (hG : MemLp G 2 μ)
    (hgrad : HasHorizontalGradient (hX.toLp X) (hG.toLp G)) :
    ∀ᵐ ω ∂μ,HasWeakGradientOn (openCubeSet Q) (realize X ω)
      (fun x => (realize G ω x).toVec) := by
  classical
  let U := openCubeSet Q
  let finiteCell' : IsFiniteMeasure (volumeMeasureOn U) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let separableCell : IsSeparable (volumeMeasureOn U) := inferInstance
  let exponentAtLeastOne : Fact (1 ≤ (2:ENNReal)) := ⟨by norm_num⟩
  let exponentFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
  let H := Homogenization.ScalarL2 U × HilbertVectorL2 U
  let secondCountableCell : SecondCountableTopology H := inferInstance
  let A := fun ω => if hu : MemScalarL2 U (realize X ω) then toScalarL2 hu else 0
  let B := fun ω => if hg : MemVectorL2 U (fun x => (realize G ω x).toVec)
    then toHilbertVectorL2OfVecField hg else 0
  let Y : Ω → H := fun ω => (A ω,B ω)
  have hgood : ∀ᵐ ω ∂μ,MemScalarL2 U (realize X ω) ∧
      MemVectorL2 U (fun x => (realize G ω x).toVec) := by
    filter_upwards [ae_memLp_two_realize (μ := μ) (volume_openCubeSet_lt_top Q).ne hXm hX,
      ae_memLp_two_realize (μ := μ) (volume_openCubeSet_lt_top Q).ne hGm hG] with ω hu hg
    exact ⟨hu,(HilbertVec.continuousLinearEquivVec d).toContinuousLinearMap.comp_memLp' hg⟩
  have ht (i : Fin d) (psi : H1WeakTestFunction U) :
      ∀ᵐ ω ∂μ,h1WeakConstraintCLM i psi (Y ω)=0 := by
    have hd := hgrad i
    rw [vectorL2Coord_toLp hGm hG i] at hd
    have htest := upper_cell_reset_horizontal_physical_test hXm hX
      (stronglyMeasurable_coordField hGm i) (memLp_coordField hGm hG i) i hd
      psi.smooth psi.compactSupport
    filter_upwards [hgood,htest] with ω hω htestω
    obtain ⟨hu,hg⟩ := hω
    have hY : Y ω=(toScalarL2 hu,toHilbertVectorL2OfVecField hg) := by
      simp only [Y,A,B,dite_eq_left hu,dite_eq_left hg]
    rw [hY,h1WeakConstraintCLM_apply_eq_integral]
    have hl : (∫ x in U,(toScalarL2 hu) x*psi.deriv i x)=
        ∫ x in U,realize X ω x*psi.deriv i x := by
      apply integral_congr_ae
      filter_upwards [coeFn_toScalarL2 hu] with x hx
      rw [hx]
    have hr : (∫ x in U,(toHilbertVectorL2OfVecField hg) x i*psi x)=
        ∫ x in U,(realize G ω x).toVec i*psi x := by
      apply integral_congr_ae
      filter_upwards [coeFn_toHilbertVectorL2OfVecField hg] with x hx
      rw [hx]
      rfl
    rw [hl,hr]
    have hleft : (∫ x in U,realize X ω x*psi.deriv i x)=
        ∫ x,realize X ω x*fderiv ℝ psi x (basisVec i) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hx' : x ∉ tsupport psi := fun hh => hx (psi.support_subset hh)
      rw [H1WeakTestFunction.deriv,fderiv_of_notMem_tsupport ℝ hx']
      simp
    have hright : (∫ x in U,(realize G ω x).toVec i*psi x)=
        ∫ x,(realize G ω x).toVec i*psi x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hx' : x ∉ tsupport psi := fun hh => hx (psi.support_subset hh)
      rw [image_eq_zero_of_notMem_tsupport hx',mul_zero]
    rw [hleft,hright]
    change (∫ x,realize X ω x*fderiv ℝ psi x (basisVec i))+
      (∫ x,(realize G ω x).toVec i*psi x)=0
    change (∫ x,realize X ω x*fderiv ℝ psi x (basisVec i))=
      -(∫ x,(realize G ω x).toVec i*psi x) at htestω
    rw [htestω,neg_add_cancel]
  let S : Set (H →L[ℝ] ℝ) := Set.range (fun p : Fin d × H1WeakTestFunction U => h1WeakConstraintCLM p.1 p.2)
  let W := WithLp 2 H
  let e : W ≃L[ℝ] H := WithLp.prodContinuousLinearEquiv 2 ℝ
    (Homogenization.ScalarL2 U) (HilbertVectorL2 U)
  let T : Set (W →L[ℝ] ℝ) := (fun L : H →L[ℝ] ℝ => L.comp e.toContinuousLinearMap) '' S
  have hpacked := upper_cell_reset_ae_all_functionals μ (fun ω => e.symm (Y ω)) T (by
    rintro _ ⟨L,⟨⟨i,psi⟩,rfl⟩,rfl⟩
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply] using ht i psi)
  have hall : ∀ᵐ ω ∂μ,∀ L ∈ S,L (Y ω)=0 := by
    filter_upwards [hpacked] with ω hω L hL
    have hh := hω (L.comp e.toContinuousLinearMap) ⟨L,hL,rfl⟩
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply] using hh
  filter_upwards [hgood,hall] with ω hω hallω
  obtain ⟨hu,hg⟩ := hω
  have hY : Y ω=(toScalarL2 hu,toHilbertVectorL2OfVecField hg) := by
    simp only [Y,A,B,dite_eq_left hu,dite_eq_left hg]
  have hgraph : (toScalarL2 hu,toHilbertVectorL2OfVecField hg) ∈ h1GraphClosedSubmodule (U := U) := by
    rw [mem_h1GraphClosedSubmodule_iff]
    intro i psi
    rw [←hY]
    exact hallω _ ⟨(i,psi),rfl⟩
  obtain ⟨w,hw,hgw⟩ := exists_h1Function_of_toScalarL2_toHilbertVectorL2OfVecField_mem_h1GraphClosedSubmodule hu hg hgraph
  have hh := w.hasWeakGradient
  rw [hw,hgw] at hh
  exact hh

end
end ASDExplicitGamma.Scalar
