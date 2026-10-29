module

public import ASDExplicitGamma.Native.GenericSourceBandMoments
public import ASDExplicitGamma.Gaussian.PolynomialTests
public import ASDExplicitGamma.Variational.AdapterMu

/-! Genuine finite moments of source-cell variational energies on the
simultaneous band, before any annealed estimate is asserted. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Response Scalar Gaussian Main Triadic Variational Inverse
open scoped ENNReal
noncomputable section

local instance parentBoundaryCellMomentCompact (Q : TriadicCube 2) :
    CompactSpace (closure (cubeSet Q)) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet Q).isCompact_closure

/-- Inclusion of the actual closed descendant square in its closed parent. -/
def parentBoundaryCellClosedInclusion {Q U : TriadicCube 2} {depth : ℕ}
    (hU : U∈descendantsAtDepth Q depth) : C(closure (cubeSet U),closure (cubeSet Q)) :=
  ⟨fun x => ⟨x.1,closure_mono (cubeSet_subset_of_mem_descendantsAtDepth hU) x.2⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- Literal restriction of the continuous parent scalar to a child
response coefficient; the map is linear and contracts the actual sup norm. -/
def parentBoundaryCellCoefficient {Q U : TriadicCube 2} {depth : ℕ}
    (hU : U∈descendantsAtDepth Q depth) :
    C(closure (cubeSet Q),ℝ) →L[ℝ] ResponseCoefficient (cubeSet U) :=
  (BoundedContinuousFunction.compContinuousCLM ℝ ℝ (parentBoundaryCellClosedInclusion hU)).comp
    (ContinuousMap.linearIsometryBoundedOfCompact
      (closure (cubeSet Q)) ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap

/-- Restriction preserves the literal physical scalar on the child cube. -/
theorem parent_boundary_cell_coefficient_value {Q U : TriadicCube 2} {depth : ℕ}
    (hU : U∈descendantsAtDepth Q depth) (f : C(closure (cubeSet Q),ℝ))
    {x : Vec 2} (hx : x∈cubeSet U) :
    responseCoefficientExtension (parentBoundaryCellCoefficient hU f) x=
      f ⟨x,subset_closure ((cubeSet_subset_of_mem_descendantsAtDepth hU) hx)⟩ := by
  rw [responseCoefficientExtension_eq _ hx]
  simp [parentBoundaryCellCoefficient,parentBoundaryCellClosedInclusion,
    BoundedContinuousFunction.compContinuousCLM_apply,
    ContinuousMap.linearIsometryBoundedOfCompact_apply_apply]

/-- The source-cell coefficient map has contraction constant one. -/
theorem parent_boundary_cell_coefficient_norm {Q U : TriadicCube 2} {depth : ℕ}
    (hU : U∈descendantsAtDepth Q depth) (f : C(closure (cubeSet Q),ℝ)) :
    ‖parentBoundaryCellCoefficient hU f‖≤‖f‖ := by
  have hh := BoundedContinuousFunction.norm_compContinuous_le
    ((ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet Q)) ℝ ℝ) f)
    (parentBoundaryCellClosedInclusion hU)
  have heq : parentBoundaryCellCoefficient hU f=
      ((ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet Q)) ℝ ℝ) f).compContinuous
        (parentBoundaryCellClosedInclusion hU) := by
    simp only [parentBoundaryCellCoefficient,ContinuousLinearMap.comp_apply,
      BoundedContinuousFunction.compContinuousCLM_apply]
    rfl
  rw [heq]
  exact hh.trans_eq ((ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet Q)) ℝ ℝ).norm_map f)

/-- Actual variational energies on every translated descendant cell have
all finite Gaussian moments in the SAME true starting frame. -/
theorem parent_boundary_band_cell_energy_memLp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (hheight : 1≤height) (depth : ℕ)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 n) depth)
    (P : BlockVec 2) (t p : ℝ) (hp : 2≤p) :
    MemLp (fun omega : Cutoff.CutoffSample 2 =>
      responseFrameEnergyObservable (measurableSet_cubeSet U) (volume_cubeSet_toReal_pos U)
        M.nu (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1 P
        (parentBoundaryCellCoefficient hU (nativeSourceBandScalar n height t omega)))
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure := by
  let E := responseFrameEnergyObservable (measurableSet_cubeSet U) (volume_cubeSet_toReal_pos U)
    M.nu (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1 P
  have hE := responseFrameEnergyObservable_hasPolynomiallyBoundedC2Derivatives
    (measurableSet_cubeSet U) (volume_cubeSet_toReal_pos U) M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1 P
  have hc := c2_polynomial_comp_contraction (parentBoundaryCellCoefficient hU)
    (parent_boundary_cell_coefficient_norm hU) hE
  have hg : HasPolynomialGrowth (fun f => E (parentBoundaryCellCoefficient hU f)) := by
    obtain ⟨_,C,hC,d,hv,_,_⟩ := hc
    exact ⟨C,hC,d,hv⟩
  exact native_source_band_test_memLp M h hM n height hheight _ hc.1.continuous.measurable hg t p hp

end
end ASDExplicitGamma.Native
