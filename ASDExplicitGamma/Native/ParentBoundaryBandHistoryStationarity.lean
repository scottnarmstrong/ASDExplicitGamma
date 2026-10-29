module

public import ASDExplicitGamma.Native.ParentBoundaryBandDepthSeries
public import ASDExplicitGamma.Native.ParentBoundaryBandTraceMoments
public import ASDExplicitGamma.Native.OldSignedSourceDirectionalPayment

/-! Stationarity of the actual simultaneous-band trace payments. Every
source cell retains the same full sample, cutoff band and observer frame. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Main Response Scalar Variational Inverse Algsuperdiff.Section3
noncomputable section

private theorem trace_measurable (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (U : TriadicCube 2) (t : ℝ) :
    Measurable (fun omega => traceDefect (cubeSet U)
      (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega)
      (Annealed.sigmaBar M n)) := by
  have hp (i : Fin 2) := parent_boundary_band_diagonal_entry_measurable
    M n (n+(height:ℤ)) (fun _ => Real.sqrt t) U true i i
  have hm (i : Fin 2) := parent_boundary_band_diagonal_entry_measurable
    M n (n+(height:ℤ)) (fun _ => Real.sqrt t) U false i i
  simp only [traceDefect,Matrix.trace,Fin.sum_univ_two]
  exact (((hp 0).add (hp 1)).const_mul _ |>.add (((hm 0).add (hm 1)).const_mul _)).sub measurable_const

/-- Actual band cell means are the origin-scale means under whole-sample translation. -/
theorem parent_boundary_band_trace_mean_origin (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (U : TriadicCube 2) (t : ℝ) :
    (∫ omega,traceDefect (cubeSet U)
      (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega)
      (Annealed.sigmaBar M n) ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
      ∫ omega,traceDefect (cubeSet (originCube 2 U.scale))
        (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega)
        (Annealed.sigmaBar M n) ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  have he (omega) : traceDefect (cubeSet U)
      (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega)
      (Annealed.sigmaBar M n)=traceDefect (cubeSet (originCube 2 U.scale))
        (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t)
          (Cutoff.translateCutoffSample (triadicCubeShift U) omega)) (Annealed.sigmaBar M n) := by
    unfold traceDefect
    rw [parent_boundary_band_coarse_cell_translate]
  simp_rw [he]
  have hi := integral_map (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
    (Cutoff.measurable_translateCutoffSample (triadicCubeShift U)).aemeasurable
    (trace_measurable M n height (originCube 2 U.scale) t).aestronglyMeasurable
  rw [Cutoff.map_translateCutoffSample_cutoffSampleLaw M (triadicCubeShift U)] at hi
  exact hi.symm

/-- The expected complete descendant trace is independent of source-cell position. -/
theorem parent_boundary_band_trace_mean_depth
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (n : ℤ)
    (height : ℕ) (hheight : 1≤height) (r : ℕ)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 n) r) (t : ℝ) (j : ℕ) :
    (∫ omega,parentBoundaryBandCellTrace M n height t U j omega ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
      ∫ omega,traceDefect (cubeSet (originCube 2 (n-(r:ℤ)-(j:ℤ))))
        (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega)
        (Annealed.sigmaBar M n) ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  unfold parentBoundaryBandCellTrace
  rw [old_signed_integral_descendants_average _ U j _ (fun V hV =>
    parent_boundary_band_cell_trace_integrable M h hM n height hheight (r+j) V
      (mem_descendantsAtDepth_add hU hV) t)]
  have he (V) (hV : V∈descendantsAtDepth U j) : V.scale=n-(r:ℤ)-(j:ℤ) := by
    rw [scale_eq_sub_of_mem_descendantsAtDepth hV,scale_eq_sub_of_mem_descendantsAtDepth hU]
    rfl
  unfold descendantsAverage
  dsimp only
  have hc : (∑ V∈descendantsAtDepth U j,
      ∫ omega,traceDefect (cubeSet V)
        (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega)
        (Annealed.sigmaBar M n) ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
      ∑ _V∈descendantsAtDepth U j,
        ∫ omega,traceDefect (cubeSet (originCube 2 (n-(r:ℤ)-(j:ℤ))))
          (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega)
          (Annealed.sigmaBar M n) ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    apply Finset.sum_congr rfl
    intro V hV
    rw [parent_boundary_band_trace_mean_origin M n height V,he V hV]
  rw [hc,Finset.sum_const,nsmul_eq_mul,←mul_assoc,inv_mul_cancel₀]
  · simp
  · exact_mod_cast (Finset.card_pos.mpr (descendantsAtDepth_nonempty U j)).ne'

end
end ASDExplicitGamma.Native
