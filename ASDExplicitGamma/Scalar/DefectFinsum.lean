module

public import ASDExplicitGamma.Scalar.PairedTwoSlotBound

/-! Finite-sum linearity of the Hilbert class of a field and of the flux/potential sources. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open scoped BigOperators

noncomputable section

section

variable {U : Set (Vec 2)} [IsFiniteMeasure (volumeMeasureOn U)]

theorem toHilbert_smul {f : Vec 2 → Vec 2} (hf : MemVectorL2 U f) (c : ℝ)
    (h : MemVectorL2 U (fun p => c • f p)) :
    toHilbertVectorL2OfVecField h = c • toHilbertVectorL2OfVecField hf := by
  have e : toHilbertVectorL2OfVecField h = toHilbertVectorL2OfVecField (hf.const_smul c) :=
    Algsuperdiff.Section3.Provider.Diffusivity.Corrector.toHilbertVectorL2OfVecField_congr _ _ rfl
  rw [e]
  change toHilbertVectorL2 (memHilbertVectorL2_hilbertifyVecField (hf.const_smul c)) = _
  exact MeasureTheory.MemLp.toLp_const_smul c (memHilbertVectorL2_hilbertifyVecField hf)


theorem toHilbert_zero : toHilbertVectorL2OfVecField (memVectorL2_const (U := U) (0 : Vec 2)) = 0 := by
  apply MeasureTheory.Lp.ext
  filter_upwards [coeFn_toHilbertVectorL2OfVecField (memVectorL2_const (U := U) (0 : Vec 2)),
    MeasureTheory.Lp.coeFn_zero (HilbertVec 2) 2 (volumeMeasureOn U)] with p h1 h2
  rw [h1, h2]
  simp [hilbertifyVecField]

theorem memVectorL2_finsum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → Vec 2 → Vec 2)
    (hf : ∀ i, MemVectorL2 U (f i)) : MemVectorL2 U (fun p => ∑ i ∈ s, c i • f i p) := by
  refine MemLp.of_eval fun k => ?_
  have : (fun p => (∑ i ∈ s, c i • f i p) k) = fun p => ∑ i ∈ s, c i * f i p k := by
    funext p; simp [Finset.sum_apply]
  change MemLp (fun p => (∑ i ∈ s, c i • f i p) k) 2 (volumeMeasureOn U)
  rw [this]
  exact memLp_finset_sum _ fun i _ => (hf i).eval k |>.const_mul (c i)

theorem toHilbert_finsum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → Vec 2 → Vec 2)
    (hf : ∀ i, MemVectorL2 U (f i)) (h : MemVectorL2 U (fun p => ∑ i ∈ s, c i • f i p)) :
    toHilbertVectorL2OfVecField h = ∑ i ∈ s, c i • toHilbertVectorL2OfVecField (hf i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    apply MeasureTheory.Lp.ext
    filter_upwards [coeFn_toHilbertVectorL2OfVecField h, MeasureTheory.Lp.coeFn_zero
      (HilbertVec 2) 2 (volumeMeasureOn U)] with p h1 h2
    rw [h1, h2]
    simp [hilbertifyVecField]
  | insert a s ha ih =>
    have h1 : MemVectorL2 U (fun p => c a • f a p) := (hf a).const_smul (c a)
    have h2 : MemVectorL2 U (fun p => ∑ i ∈ s, c i • f i p) :=
      memVectorL2_finsum s c f hf
    have e : toHilbertVectorL2OfVecField h = toHilbertVectorL2OfVecField (h1.add h2) :=
      Algsuperdiff.Section3.Provider.Diffusivity.Corrector.toHilbertVectorL2OfVecField_congr _ _
        (by funext p; simp [Finset.sum_insert ha])
    rw [e, toHilbertVectorL2OfVecField_add h1 h2, Finset.sum_insert ha,
      toHilbert_smul (hf a) (c a) h1, ih h2]

end

section Sources

variable (Q : TriadicCube 2)

local instance fsFinite' : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

theorem fluxSource_zero :
    fluxSource Q (memVectorL2_const (U := openCubeSet Q) (0 : Vec 2)) = 0 := by
  unfold fluxSource
  rw [toHilbert_zero]; simp

theorem potSource_zero :
    potSource Q (memVectorL2_const (U := openCubeSet Q) (0 : Vec 2)) = 0 := by
  unfold potSource
  rw [toHilbert_zero]; simp

theorem fluxSource_finsum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → Vec 2 → Vec 2)
    (hf : ∀ i, MemVectorL2 (openCubeSet Q) (f i))
    (h : MemVectorL2 (openCubeSet Q) (fun p => ∑ i ∈ s, c i • f i p)) :
    fluxSource Q h = ∑ i ∈ s, c i • fluxSource Q (hf i) := by
  unfold fluxSource
  rw [toHilbert_finsum s c f hf h]
  simp only [map_sum, map_smul]

theorem potSource_finsum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → Vec 2 → Vec 2)
    (hf : ∀ i, MemVectorL2 (openCubeSet Q) (f i))
    (h : MemVectorL2 (openCubeSet Q) (fun p => ∑ i ∈ s, c i • f i p)) :
    potSource Q h = ∑ i ∈ s, c i • potSource Q (hf i) := by
  unfold potSource
  rw [toHilbert_finsum s c f hf h]
  simp only [map_sum, map_smul]

end Sources

end

end ASDExplicitGamma.Scalar
