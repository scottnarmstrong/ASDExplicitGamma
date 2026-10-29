module

public import ASDExplicitGamma.Native.ParentBoundaryBandBlockStationarity
public import ASDExplicitGamma.Native.ParentBoundaryBandInverseMeanCap
public import ASDExplicitGamma.Native.ParentBoundaryFlatMeanLoss
public import ASDExplicitGamma.Native.ParentBoundaryInverseBulk

/-! The own-native affine expectation bound, including the genuine cell
variance floor and the complete local inverse-bank reserve. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Triadic Algsuperdiff.Section3
noncomputable section

/-- The actual trace mean is twice the sum of the two actual scalar
block means minus four, in the fixed starting frame. -/
theorem parent_boundary_band_trace_block_means
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (n : ℤ)
    (height : ℕ) (hheight : 1≤height) (r : ℕ) (U : TriadicCube 2)
    (hU : U∈descendantsAtDepth (originCube 2 n) r) (t : ℝ) :
    (∫ omega,traceDefect (cubeSet U)
      (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega)
      (Annealed.sigmaBar M n) ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
      2*(parentBoundaryBandBlockMean M n height t U true+
        parentBoundaryBandBlockMean M n height t U false-2) := by
  let A := fun plus => parentBoundaryBandNormalizedBlock M n height t U plus
  have hi (plus : Bool) := (parent_boundary_band_block_scalar_law M h hM n height hheight r U hU t plus).1
  have hm (plus : Bool) := (parent_boundary_band_block_mean M h hM n height hheight r U hU t plus).2
  have he (omega) : traceDefect (cubeSet U)
      (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega)
      (Annealed.sigmaBar M n)=
      (A true omega 0 0+A true omega 1 1)+(A false omega 0 0+A false omega 1 1)-4 := by
    simp [A,parentBoundaryBandNormalizedBlock,traceDefect,frameMatrix,Matrix.trace,Fin.sum_univ_two]
    ring
  have hs (plus : Bool) : Integrable (fun omega => A plus omega 0 0+A plus omega 1 1)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
    simpa only [Pi.add_def] using (hi plus 0 0).add (hi plus 1 1)
  have hsum : Integrable (fun omega => (A true omega 0 0+A true omega 1 1)+
      (A false omega 0 0+A false omega 1 1)) (Cutoff.cutoffSampleLaw M).toMeasure := by
    simpa only [Pi.add_def] using (hs true).add (hs false)
  simp_rw [he]
  rw [integral_sub hsum (integrable_const _),integral_add (hs true) (hs false),
    integral_add (hi true 0 0) (hi true 1 1),integral_add (hi false 0 0) (hi false 1 1),
    hm true 0 0,hm true 1 1,hm false 0 0,hm false 1 1]
  simp only [ite_true,integral_const,probReal_univ,one_smul]
  ring

end
end ASDExplicitGamma.Native
