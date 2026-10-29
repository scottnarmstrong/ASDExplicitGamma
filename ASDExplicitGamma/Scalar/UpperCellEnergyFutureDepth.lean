module

public import ASDExplicitGamma.Native.ParentBoundaryBandFull64
public import ASDExplicitGamma.Inverse.AssemblyTraceMeasurable
public import ASDExplicitGamma.Inverse.StoppedSelectedMaximum

/-! Actual full-response descendant maxima for the UPPER RESET history.
The order-64 bank is retained, with its exact ninth-power population payment. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Section3 Native Inverse
open scoped ENNReal
noncomputable section

/-- Complete terminal response, maximized over the depth-j cells of the
physical depth-fourteen observation cube in the old scalar frame. -/
def upperCellFutureDepthMax (M : ABKModel 2) (n : ℤ) (height j : ℕ)
    (weights : ℤ → ℝ) : Cutoff.CutoffSample 2 → ℝ≥0∞ :=
  historyFiniteMax (descendantsAtDepth (originCube 2 (n-14)) j)
    (fun Q ω => ENNReal.ofReal
      (nativeSourceFullResponseTrace M Q n (n+(height:ℤ)) weights ω))

/-- The actual descendant maximum is measurable. -/
theorem upper_cell_future_depth_max_measurable
    (M : ABKModel 2) (n : ℤ) (height j : ℕ) (weights : ℤ → ℝ) :
    Measurable (upperCellFutureDepthMax M n height j weights) :=
  history_finite_max_measurable _ _ (fun Q =>
    (root_trace_observable_measurable M Q n (n+(height:ℤ)) n weights).ennreal_ofReal)

/-- Every finite-depth full-response maximum is finite on every sample. -/
theorem upper_cell_future_depth_max_ne_top
    (M : ABKModel 2) (n : ℤ) (height j : ℕ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) : upperCellFutureDepthMax M n height j weights ω ≠ ⊤ := by
  apply ne_of_lt
  apply (Finset.sup_lt_iff (by simp : (⊥ : ℝ≥0∞) < ⊤)).mpr
  intro Q _
  exact ENNReal.ofReal_lt_top

/-- The actual order-64 full-response bank controls every depth maximum.
The maximum is taken before the norm; no cross-cell independence is used. -/
theorem upper_cell_future_depth_max_L64
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ k < n, nativeInductionState M h k)
    (height j : ℕ) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc n (n+(height:ℤ)), 0 ≤ weights k ∧ weights k ≤ 1) :
    eLpNorm (upperCellFutureDepthMax M n height j weights) 64
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ((9:ℝ≥0∞)^j)^((1:ℝ)/64)*
      ENNReal.ofReal (4*((1009309/500000:ℝ)+M.gamma*
        (16684*((height:ℝ)+(14+j:ℕ)+1)+5899542))*
          (3:ℝ)^((2*(height:ℝ)+4*(14+j:ℕ)+4)*M.gamma)) := by
  let s := descendantsAtDepth (originCube 2 (n-14)) j
  let f := fun Q : TriadicCube 2 => fun ω => ENNReal.ofReal
    (nativeSourceFullResponseTrace M Q n (n+(height:ℤ)) weights ω)
  have hf (Q) : Measurable (f Q) :=
    (root_trace_observable_measurable M Q n (n+(height:ℤ)) n weights).ennreal_ofReal
  have hb (Q) (hQ : Q ∈ s) := parent_boundary_band_cell_response_L64
    M h hM hg n height (14+j) Q (by
      have hs := scale_eq_sub_of_mem_descendantsAtDepth hQ
      change Q.scale = (n-14)-(j:ℤ) at hs
      omega) hpast weights hw
  have hn (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) :
      0 ≤ nativeSourceFullResponseTrace M Q n (n+(height:ℤ)) weights ω :=
    root_trace_observable_nonneg M Q n (n+(height:ℤ)) n (by omega) weights ω
  have hnorm (Q) (hQ : Q ∈ s) := hb Q hQ
  have hmax := finite_maximum_Lp (Cutoff.cutoffSampleLaw M).toMeasure s f hf
    64 (by norm_num) _ (fun Q hQ => by
      change eLpNorm (ENNReal.ofReal ∘ nativeSourceFullResponseTrace M Q n
        (n+(height:ℤ)) weights) _ _ ≤ _
      rw [eLpNorm_ofReal _ (Filter.Eventually.of_forall (hn Q))]
      exact hnorm Q hQ)
  have hcard : (s.card:ℝ≥0∞) = (9:ℝ≥0∞)^j := by
    simp only [s,descendantsAtDepth_card]
    norm_num
  rw [hcard] at hmax
  simpa only [ENNReal.ofReal_ofNat, upperCellFutureDepthMax, s, f] using hmax

end
end ASDExplicitGamma.Scalar
