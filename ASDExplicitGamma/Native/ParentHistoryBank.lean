module

public import ASDExplicitGamma.Native.ParentHistoryFrames
public import ASDExplicitGamma.Native.ParentHistoryNorms

/-! Actual protected inverse bank and honest physical-history finiteness. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Triadic Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Both extended histories are finite at every actual sample by
qualitative ellipticity, before any real conversion is used. -/
theorem parent_history_sample_finite
    (M : ABKModel 2) (P : TriadicCube 2) (n : ℤ) (height : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    parentBoundaryBandMaxTraceHistory M n height P t ω < ⊤ ∧
      parentBoundaryCommonCenteredMaxHistory M P n height t ω < ⊤ := by
  rw [parent_history_physical_history,parent_history_centered_history]
  exact ⟨ENNReal.ofReal_lt_top,ENNReal.ofReal_lt_top⟩

/-- The actual physical history has an honest L20 real representative,
without any current-label induction-state hypothesis. -/
theorem parent_history_physical_memLp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (P : TriadicCube 2) (n : ℤ) (r : ℕ) (hP : P.scale=n-(r:ℤ))
    (height : ℕ) (hpast : ∀ k<n,nativeInductionState M h k) (t : ℝ) (ht1 : t ≤ 1) :
    MemLp (fun ω => (parentBoundaryBandMaxTraceHistory M n height P t ω).toReal) 20
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  rw [memLp_iff,parent_history_toReal_norm _ _
    (ae_of_all _ (fun ω => (parent_history_sample_finite M P n height t ω).1.ne))]
  exact (parent_boundary_band_max_trace_L20 M h hM hg n height r P hP hpast t ht1).trans_lt ENNReal.ofReal_lt_top

end
end ASDExplicitGamma.Native
