module

public import ASDExplicitGamma.Native.ParentBoundaryCommonProtectedFullBank
public import ASDExplicitGamma.Native.ParentBoundaryObserverBandTrace
public import ASDExplicitGamma.Native.GenericSourceActualInverse
public import ASDExplicitGamma.Native.ParentBoundaryMeanObserverBank

/-! The exact physical observer bank for source mean heat, anchored in the starting frame. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Algsuperdiff.Section3
noncomputable section

/-- The actual full uncentered mean generator uses the SAME protected
singleton bank in the starting frame, with no source-offset frame loss. -/
theorem parent_boundary_mean_protected_source_bank
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (q m n : ℤ) (hqm : q=m-5) (hmn : m ≤ n) (height : ℕ)
    (hpast : ∀ k<n,nativeInductionState M h k) (t : ℝ) (ht : t ≤ 1) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      let a := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
        (pureFluxOpenResponseRestriction q (parentBoundaryObserverBandScalar q n height t ω))
      max (lemmaVTileHistory (originCube 2 q) 0 a) (pureFluxSourceTileHistory (originCube 2 q) 0 a) ≤
        ((Annealed.sigmaBar M n:ℝ)/(Annealed.sigmaBar M m:ℝ))*
          parentBoundaryCommonSingletonHistory M (originCube 2 q) m n height t ω := by
  have hq : (originCube 2 q).scale ≤ m := by change q ≤ m; omega
  have hgap : m-(originCube 2 q).scale ≤ 5 := by change m-q ≤ 5; omega
  filter_upwards [parent_boundary_common_singleton_physical_source M h hM hg (originCube 2 q)
    m n hq hgap hmn height hpast t ht] with ω hω
  dsimp only at hω ⊢
  rw [parent_boundary_mean_observer_coefficient_eq] at hω
  exact hω

/-- The physical observer inverse trace is bounded by twice the same
starting-frame singleton bank, with its full coarse matrix identified. -/
theorem parent_boundary_mean_protected_inverse_bank
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (q m n : ℤ) (hqm : q=m-5) (hmn : m ≤ n) (height : ℕ)
    (hpast : ∀ k<n,nativeInductionState M h k) (t : ℝ) (ht : t ≤ 1) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      bankInverseTraceObservable q M.nu (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1
        (parentBoundaryObserverBandScalar q n height t ω) ≤
          2*((Annealed.sigmaBar M n:ℝ)/(Annealed.sigmaBar M m:ℝ))*
          parentBoundaryCommonSingletonHistory M (originCube 2 q) m n height t ω := by
  have hq : (originCube 2 q).scale ≤ m := by change q ≤ m; omega
  have hgap : m-(originCube 2 q).scale ≤ 5 := by change m-q ≤ 5; omega
  filter_upwards [parent_boundary_common_protected_inverse_bank M h hM hg (originCube 2 q)
    m n hq hgap hmn height hpast t ht] with ω hω
  have hself : originCube 2 q ∈ descendantsAtDepth (originCube 2 q) 0 := by simp
  have hk : parentBoundaryCellCoefficient hself (parentBoundaryCommonCubeBand (originCube 2 q) n height t ω)=
      ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet (originCube 2 q))) ℝ ℝ
        (parentBoundaryObserverBandScalar q n height t ω) := by
    ext x
    rfl
  have hm := parent_boundary_common_cell_physical_coarse M hself n height t ω
  rw [hk] at hm
  rw [native_source_model_inverse_trace_eq_frame_trace,hm]
  exact hω

end
end ASDExplicitGamma.Native
