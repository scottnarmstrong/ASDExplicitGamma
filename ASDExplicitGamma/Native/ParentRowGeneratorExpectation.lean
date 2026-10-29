module

public import ASDExplicitGamma.Native.ParentRowGeneratorSpatial
public import ASDExplicitGamma.Native.ParentRowAffinePanel

/-! Annealed generator assembly with the exact signed inverse observable. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Inverse Main Triadic Variational Algsuperdiff.Section3
noncomputable section

/-- Complete physical finite-shell error cap in the starting frame. -/
def parentRowBandErrorCap (M : ABKModel 2) (h : ℝ) (n : ℤ) (height r : ℕ) (t : ℝ) : ℝ :=
  ∑ i : Fin height,parentRowErrorCap M n height r t
    (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
    (q3ModelLength (n+((i.val+1:ℕ):ℤ)))

/-- The entire actual-law parent error is integrable; expectation commutes
with the finite physical shell sum. -/
theorem parent_row_band_error_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ) (hheight : 1≤height) (hh16 : height≤16)
    (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n)
    (r : ℕ) (hr : r=5) (t : ℝ) (ht : 0≤t ∧ t≤1) :
    Integrable (parentRowBandErrorEnvelope M h n height r t) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,parentRowBandErrorEnvelope M h n height r t ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      parentRowBandErrorCap M h n height r t := by
  have hh (i : Fin height) := parent_row_error_payment M h hM hg n height hheight hh16 hpast hstate r hr t ht
    (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
    (q3ModelLength (n+((i.val+1:ℕ):ℤ)))
  refine ⟨integrable_finsetSum _ (fun i _ => (hh i).1),?_⟩
  unfold parentRowBandErrorEnvelope parentRowBandErrorCap
  rw [integral_finsetSum _ (fun i _ => (hh i).1)]
  exact Finset.sum_le_sum (fun i _ => (hh i).2)

/-- The actual generator has its full affine, error and signed inverse
expectation bound, without any generator estimate premise. -/
theorem parent_row_generator_expectation
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ) (hheight : 1≤height) (hh16 : height≤16)
    (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n)
    (r : ℕ) (hr : r=5) (t : ℝ) (ht : 0≤t ∧ t≤1) :
    (∫ ω,nativeSourceBandMeanGenerator M h n height t ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      (∑ i : Fin height,oldSignedFlatBoundaryEnergy (originCube 2 n)
        (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
        (q3ModelLength (n+((i.val+1:ℕ):ℤ))))+
      (∫ ω,parentBoundaryBandAffineBill M h n height r t ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)-
      parentBoundaryBandDirichletEnergy M h n height*(parentBoundaryBandInverseMean M n height t-2)+
      parentRowBandErrorCap M h n height r t := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let F := parentBoundaryBandAffineBill M h n height r t
  let D := fun ω => mainInverseObservable n M.nu (Annealed.sigmaBar M n) (nativeSourceBandScalar n height t ω)
  let Y := parentBoundaryBandDirichletEnergy M h n height
  let B := ∑ i : Fin height,oldSignedFlatBoundaryEnergy (originCube 2 n)
    (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
    (q3ModelLength (n+((i.val+1:ℕ):ℤ)))
  let E := parentRowBandErrorEnvelope M h n height r t
  have hF : Integrable F μ := integrable_finsetSum _ (fun i _ =>
    (parent_boundary_band_affine_expectation M h hM n height hheight r t
      (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
      (q3ModelLength (n+((i.val+1:ℕ):ℤ)))).1)
  have hD : Integrable D μ := (parent_boundary_inverse_band_integrable M h hM hg n height hpast t ht.2).1
  have hE := parent_row_band_error_payment M h hM hg n height hheight hh16 hpast hstate r hr t ht
  have hBF : Integrable (fun ω => B+F ω) μ := (integrable_const B).add hF
  have hYD : Integrable (fun ω => Y*(D ω-2)) μ := (hD.sub (integrable_const 2)).const_mul Y
  have hbase : Integrable (fun ω => B+F ω-Y*(D ω-2)) μ := hBF.sub hYD
  have hh := integral_mono_ae
    (native_source_band_mean_generator_integrable M h hM n height hheight t)
    (hbase.add hE.1)
    (parent_row_generator_spatial M h hM hg n height r (by omega) hpast t ht)
  change (∫ ω,nativeSourceBandMeanGenerator M h n height t ω ∂μ)≤
    ∫ ω,B+F ω-Y*(D ω-2)+E ω ∂μ at hh
  rw [integral_add hbase hE.1,integral_sub hBF hYD,integral_add (integrable_const B) hF,
    integral_const_mul,integral_sub hD (integrable_const 2)] at hh
  have hB : (∫ _ : Cutoff.CutoffSample 2,B ∂μ)=B := by simp
  have htwo : (∫ _ : Cutoff.CutoffSample 2,(2:ℝ) ∂μ)=2 := by simp
  rw [hB,htwo] at hh
  exact hh.trans (add_le_add le_rfl hE.2)

/-- The exact affine part of the selected numerical parent panel. -/
def parentRowPanelAffine (j : Fin 16) (t : ℝ) : ℝ :=
  let f := fun k => (parentRowFields j).getD k 0
  f 16/2*(f 14+f 11*t)+2*f 0*((3683/2500:ℝ)-1)+
    (4+2*Real.sqrt 2)*((156/5:ℝ)*f 1/9)

/-- All non-error generator terms now fit their exact panel entries. The
remaining finite-shell error cap is displayed, and the inverse contribution
is retained with its original sign and physical coefficient. -/
theorem parent_row_generator_affine_panel
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (hstate : nativeInductionState M h n)
    (hpast : ∀ l<n,nativeInductionState M h l) (j : Fin 16)
    (r : ℕ) (hr : r=5) (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : 0≤t ∧ t≤1) :
    (∫ ω,nativeSourceBandMeanGenerator M h n (j.val+1) t ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      theta M*(parentRowB0 j+parentRowPanelAffine j t)-
        parentBoundaryBandDirichletEnergy M h n (j.val+1)*
          (parentBoundaryBandInverseMean M n (j.val+1) t-2)+
        parentRowBandErrorCap M h n (j.val+1) r t := by
  have hg0 := parent_row_generator_expectation M h hM hg n (j.val+1) (by omega) (by omega)
    hpast hstate r hr t ht
  have hb := parent_row_actual_flat_payment M h hg n hstate j
  have ha := parent_row_actual_affine_panel M h hM hg n hstate hpast j r hr U hU t ht.1 ht.2
  have hh := add_le_add hb ha
  have hh' := add_le_add (sub_le_sub_right hh
    (parentBoundaryBandDirichletEnergy M h n (j.val+1)*
      (parentBoundaryBandInverseMean M n (j.val+1) t-2)))
    (le_refl (parentRowBandErrorCap M h n (j.val+1) r t))
  exact (hg0.trans hh').trans_eq (by dsimp only [parentRowPanelAffine]; ring)

end
end ASDExplicitGamma.Native
