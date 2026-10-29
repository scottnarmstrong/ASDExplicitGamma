module

public import ASDExplicitGamma.Native.ParentBoundaryBandDirectionalFrame
public import ASDExplicitGamma.Native.OldSignedDescendantDirectionalMean

/-! Genuine integrability and the unweighted directional half trace for
complete simultaneous-band depth averages. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Inverse Algsuperdiff.Section3
noncomputable section

/-- The physical trace is the sum of the two surplus diagonal entries. -/
theorem parent_boundary_band_surplus_trace
    (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ)
    (U : TriadicCube 2) (omega : Cutoff.CutoffSample 2) :
    traceDefect (cubeSet U)
      (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega)
      (Annealed.sigmaBar M n)=
      parentBoundaryBandSurplus M n height t U omega 0 0+
      parentBoundaryBandSurplus M n height t U omega 1 1 := by
  simp [parentBoundaryBandSurplus,traceDefect,frameMatrix,Matrix.trace,Fin.sum_univ_two]
  ring

/-- Each physical cell trace is integrable under the actual band law. -/
theorem parent_boundary_band_cell_trace_integrable
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (hheight : 1≤height) (depth : ℕ)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 n) depth) (t : ℝ) :
    Integrable (fun omega => traceDefect (cubeSet U)
      (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega)
      (Annealed.sigmaBar M n)) (Cutoff.cutoffSampleLaw M).toMeasure := by
  simp_rw [parent_boundary_band_surplus_trace]
  exact (parent_boundary_band_surplus_entry_integrable M h hM n height hheight depth U hU t 0 0).add
    (parent_boundary_band_surplus_entry_integrable M h hM n height hheight depth U hU t 1 1)

/-- The complete physical trace sequence is integrable at every depth. -/
theorem parent_boundary_band_trace_sequence_integrable
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (hheight : 1≤height) (r : ℕ)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 n) r) (t : ℝ) (j : ℕ) :
    Integrable (parentBoundaryBandCellTrace M n height t U j) (Cutoff.cutoffSampleLaw M).toMeasure := by
  unfold parentBoundaryBandCellTrace descendantsAverage
  dsimp only
  exact (integrable_finsetSum _ (fun V hV => parent_boundary_band_cell_trace_integrable
    M h hM n height hheight (r+j) V (mem_descendantsAtDepth_add hU hV) t)).const_mul _

/-- The actual directional quadratic is integrable without an estimate premise. -/
theorem parent_boundary_band_directional_integrable
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (hheight : 1≤height) (r : ℕ)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (j : ℕ) (e : Vec 2) :
    Integrable (fun omega => vecDot e (matVecMul (oldSignedPairedDepthMatrix U j
      (parentBoundaryBandFrameField M n height t omega)) e)) (Cutoff.cutoffSampleLaw M).toMeasure := by
  simp_rw [parent_boundary_band_directional_matrix M n height r U hU,
    vecDot_matVecMul_descendantsAverageMat]
  unfold descendantsAverage
  dsimp only
  exact (integrable_finsetSum _ (fun V hV => old_signed_quadratic_integrable _ _
    (parent_boundary_band_surplus_entry_integrable M h hM n height hheight (r+j) V
      (mem_descendantsAtDepth_add hU hV) t) e)).const_mul _

/-- The complete unweighted directional mean has the exact half-trace factor,
without applying isotropy to an inverse-weighted quantity. -/
theorem parent_boundary_band_directional_mean
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (hheight : 1≤height) (r : ℕ)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (j : ℕ) (e : Vec 2) :
    (∫ omega,vecDot e (matVecMul (oldSignedPairedDepthMatrix U j
      (parentBoundaryBandFrameField M n height t omega)) e) ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
      (1/2:ℝ)*(∫ omega,parentBoundaryBandCellTrace M n height t U j omega
        ∂(Cutoff.cutoffSampleLaw M).toMeasure)*vecNormSq e := by
  simp_rw [parent_boundary_band_directional_matrix M n height r U hU,
    vecDot_matVecMul_descendantsAverageMat]
  rw [old_signed_integral_descendants_average _ U j _ (fun V hV =>
    old_signed_quadratic_integrable _ _ (parent_boundary_band_surplus_entry_integrable
      M h hM n height hheight (r+j) V (mem_descendantsAtDepth_add hU hV) t) e)]
  have he (V) (hV : V∈descendantsAtDepth U j) := parent_boundary_band_directional_half_trace
    M h hM n height hheight (r+j) V (mem_descendantsAtDepth_add hU hV) t e
  unfold parentBoundaryBandCellTrace
  rw [old_signed_integral_descendants_average _ U j _ (fun V hV =>
    parent_boundary_band_cell_trace_integrable M h hM n height hheight (r+j) V
      (mem_descendantsAtDepth_add hU hV) t)]
  unfold descendantsAverage
  dsimp only
  rw [Finset.sum_congr rfl he]
  rw [←Finset.sum_mul,←Finset.mul_sum]
  ring

end
end ASDExplicitGamma.Native
