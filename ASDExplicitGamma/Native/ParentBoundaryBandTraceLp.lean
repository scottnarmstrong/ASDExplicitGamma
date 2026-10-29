module

public import ASDExplicitGamma.Native.ParentBoundaryBandTraceMoments

/-! Actual full-response trace caps at every order up to the complete bank order. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Inverse Algsuperdiff.Section3 Gaussian
open scoped ENNReal
noncomputable section

/-- Every actual source-cell defect has the full-bank cap at all orders
up to128, without an entry, inverse or response estimate premise. -/
theorem parent_boundary_band_cell_trace_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height depth : ℕ)
    (U : TriadicCube 2) (hU : U.scale=n-(depth:ℤ))
    (hpast : ∀ k<n,nativeInductionState M h k) (t : ℝ) (ht : t≤1)
    (p : ℝ≥0∞) (hp : p≤ENNReal.ofReal 128) :
    eLpNorm (fun omega => traceDefect (cubeSet U)
      (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega)
      (Annealed.sigmaBar M n)) p (Cutoff.cutoffSampleLaw M).toMeasure≤
      ENNReal.ofReal (parentBoundaryBandTraceCap M height depth) := by
  have hh := parent_boundary_band_cell_response_L128 M h hM hg n height depth U hU hpast
    (fun _ => Real.sqrt t) (fun _ _ => ⟨Real.sqrt_nonneg t,Real.sqrt_le_one.mpr ht⟩)
  have hlo := eLpNorm_le_eLpNorm_of_exponent_le (f := nativeSourceFullResponseTrace M U n
    (n+(height:ℤ)) (fun _ => Real.sqrt t)) (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
    hp
  have hdom : eLpNorm (fun omega => traceDefect (cubeSet U)
      (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega)
      (Annealed.sigmaBar M n)) p (Cutoff.cutoffSampleLaw M).toMeasure≤
      eLpNorm (nativeSourceFullResponseTrace M U n (n+(height:ℤ)) (fun _ => Real.sqrt t)) p
        (Cutoff.cutoffSampleLaw M).toMeasure := by
    have hp (i : Fin 2) := parent_boundary_band_diagonal_entry_measurable
      M n (n+(height:ℤ)) (fun _ => Real.sqrt t) U true i i
    have hm (i : Fin 2) := parent_boundary_band_diagonal_entry_measurable
      M n (n+(height:ℤ)) (fun _ => Real.sqrt t) U false i i
    have hmeas : Measurable (fun omega => traceDefect (cubeSet U)
        (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega)
        (Annealed.sigmaBar M n)) := by
      simp only [traceDefect,Matrix.trace,Fin.sum_univ_two]
      exact (((hp 0).add (hp 1)).const_mul _ |>.add (((hm 0).add (hm 1)).const_mul _)).sub measurable_const
    apply eLpNorm_mono_ae hmeas.aestronglyMeasurable
    filter_upwards [] with omega
    have hn := parent_boundary_band_trace_nonneg M n height t U omega
    have he : nativeSourceFullResponseTrace M U n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega=
        traceDefect (cubeSet U)
          (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega)
          (Annealed.sigmaBar M n)+4 := by
      rw [traceDefect_eq_full_framedTrace]
      unfold nativeSourceFullResponseTrace
      ring
    rw [he,Real.norm_of_nonneg hn,Real.norm_of_nonneg (by positivity)]
    linarith

  exact hdom.trans (hlo.trans hh)


end
end ASDExplicitGamma.Native
