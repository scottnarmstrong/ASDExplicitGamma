module

public import ASDExplicitGamma.Native.ParentBoundaryBandMatrixHistory

/-! Exact measurable carrier of the maximum trace history in the OLD panel. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Actual finite maximum of physical fixed-frame band traces. -/
def parentBoundaryBandTraceDepthMax (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (U : TriadicCube 2) (t : ℝ) (j : ℕ) : Cutoff.CutoffSample 2 → ℝ≥0∞ :=
  historyFiniteMax (descendantsAtDepth U j) (fun V omega => ENNReal.ofReal
    (traceDefect (cubeSet V) (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega)
      (Annealed.sigmaBar M n)))

/-- The literal extended maximum history on the simultaneous band. -/
def parentBoundaryBandMaxTraceHistory (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (U : TriadicCube 2) (t : ℝ) (omega : Cutoff.CutoffSample 2) : ℝ≥0∞ :=
  ENNReal.ofReal (1-inverseHistoryDiscount)*∑' j : ℕ,
    ENNReal.ofReal (inverseHistoryDiscount^j)*parentBoundaryBandTraceDepthMax M n height U t j omega

/-- Every finite physical band trace maximum is measurable. -/
theorem parent_boundary_band_trace_depth_max_measurable (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (U : TriadicCube 2) (t : ℝ) (j : ℕ) : Measurable (parentBoundaryBandTraceDepthMax M n height U t j) := by
  apply history_finite_max_measurable
  intro V
  have hp (i : Fin 2) := parent_boundary_band_diagonal_entry_measurable
    M n (n+(height:ℤ)) (fun _ => Real.sqrt t) V true i i
  have hm (i : Fin 2) := parent_boundary_band_diagonal_entry_measurable
    M n (n+(height:ℤ)) (fun _ => Real.sqrt t) V false i i
  apply Measurable.ennreal_ofReal
  simp only [traceDefect,Matrix.trace,Fin.sum_univ_two]
  exact (((hp 0).add (hp 1)).const_mul _ |>.add (((hm 0).add (hm 1)).const_mul _)).sub measurable_const

/-- The complete physical extended history is measurable before conversion. -/
theorem parent_boundary_band_extended_max_trace_measurable (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (U : TriadicCube 2) (t : ℝ) : Measurable (parentBoundaryBandMaxTraceHistory M n height U t) := by
  unfold parentBoundaryBandMaxTraceHistory
  exact (Measurable.tsum (fun j => (parent_boundary_band_trace_depth_max_measurable M n height U t j).const_mul _)).const_mul _

/-- The real maximum is the physical raw maximum in the fixed completed frame. -/
theorem parent_boundary_band_max_trace_depth (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    parentBoundaryBandTraceDepthMax M n height U t j ω =
      ENNReal.ofReal (oldSignedMaxTraceDepth U (parentBoundaryBandFrameField M n height t ω) j) := by
  classical
  let s := descendantsAtDepth U j
  let f := fun V => traceDefect (openCubeSet V) (parentBoundaryBandFrameField M n height t ω) 1
  have hf (V : TriadicCube 2) (hV : V ∈ s) : traceDefect (cubeSet V) (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω) (Annealed.sigmaBar M n)=f V := by
    unfold f traceDefect
    simp only [parentBoundaryBandFrameField,←coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube V]
    rw [native_source_band_coarse_matrix_frame M n height t ω (mem_descendantsAtDepth_add hU hV)]
    simp only [frameMatrix,inv_one,one_mul,Matrix.trace_smul,smul_eq_mul]
  have hfinite : (f '' (s : Set (TriadicCube 2))).Finite := s.finite_toSet.image f
  have hne : (f '' (s : Set (TriadicCube 2))).Nonempty :=
    (descendantsAtDepth_nonempty U j).to_set.image f
  obtain ⟨V,hV,heq⟩ := hne.csSup_mem hfinite
  change s.sup (fun V => ENNReal.ofReal (traceDefect (cubeSet V) (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω) (Annealed.sigmaBar M n))) =
    ENNReal.ofReal (sSup (f '' (s : Set (TriadicCube 2))))
  apply le_antisymm
  · apply Finset.sup_le
    intro W hW
    rw [hf W hW]
    exact ENNReal.ofReal_le_ofReal (le_csSup hfinite.bddAbove ⟨W,hW,rfl⟩)
  · rw [←heq,←hf V hV]
    exact Finset.le_sup (f := fun V => ENNReal.ofReal (traceDefect (cubeSet V) (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω) (Annealed.sigmaBar M n))) hV

/-- The entire extended history is the finite real history, without a
`toReal` conversion that could discard infinity. -/
theorem parent_boundary_band_max_trace_history (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    parentBoundaryBandMaxTraceHistory M n height U t ω =
      ENNReal.ofReal (oldSignedMaxTraceHistory U (parentBoundaryBandFrameField M n height t ω)) := by
  have hEll := (responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet (originCube 2 n)) M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1 (pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t ω))).mono
      (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  unfold parentBoundaryBandMaxTraceHistory oldSignedMaxTraceHistory
  simp_rw [parent_boundary_band_max_trace_depth M n height r U hU t ω,
    ←ENNReal.ofReal_mul (pow_nonneg inverse_history_discount_range.1.le _)]
  rw [←ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg
    (pow_nonneg inverse_history_discount_range.1.le j)
    (old_signed_max_trace_depth_bounds U (parentBoundaryBandFrameField M n height t ω) hEll j).1)
    (old_signed_max_trace_series_summable U (parentBoundaryBandFrameField M n height t ω) hEll),
    ←ENNReal.ofReal_mul (sub_nonneg.mpr inverse_history_discount_range.2.le)]

/-- Actual maximum histories are nonnegative before taking their laws. -/
theorem parent_boundary_band_max_trace_history_nonneg (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ oldSignedMaxTraceHistory U (parentBoundaryBandFrameField M n height t ω) := by
  have hEll := (responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet (originCube 2 n)) M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1 (pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t ω))).mono
      (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  exact mul_nonneg (sub_nonneg.mpr inverse_history_discount_range.2.le)
    (tsum_nonneg (fun j => mul_nonneg (pow_nonneg inverse_history_discount_range.1.le j)
      (old_signed_max_trace_depth_bounds U _ hEll j).1))

/-- Conversion to the real carrier is exact, pointwise in every sample. -/
theorem parent_boundary_band_max_trace_history_toReal (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    (parentBoundaryBandMaxTraceHistory M n height U t ω).toReal =
      oldSignedMaxTraceHistory U (parentBoundaryBandFrameField M n height t ω) := by
  rw [parent_boundary_band_max_trace_history M n height r U hU t ω,
    ENNReal.toReal_ofReal (parent_boundary_band_max_trace_history_nonneg M n height r U hU t ω)]

end
end ASDExplicitGamma.Native
