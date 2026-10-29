module

public import ASDExplicitGamma.Native.HeatRefinedObserverShear
public import ASDExplicitGamma.Native.ParentBoundaryHistoryGauge

/-! Complete refined-observer histories paid by the original parent population. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Triadic
open Algsuperdiff.Section3
noncomputable section

/-- Restricting the literal band to its observer preserves every complete
inverse history on every further descendant. Both sides keep sigma_n. -/
theorem heat_refined_observer_history_eq_parent
    (M : ABKModel 2) (q n : ℤ) (r : ℕ)
    (hq : originCube 2 q ∈ descendantsAtDepth (originCube 2 n) r)
    (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (U : TriadicCube 2) (j : ℕ) (hU : U ∈ descendantsAtDepth (originCube 2 q) j) (a : ℝ) :
    lemmaVInverseHistory U
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
        (pureFluxOpenResponseRestriction q (parentBoundaryObserverBandScalar q n height t ω))) a =
    lemmaVInverseHistory U
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
        (pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t ω))) a := by
  have hUn : U ∈ descendantsAtDepth (originCube 2 n) (r+j) := by
    simpa only [Nat.add_comm] using mem_descendantsAtDepth_add hq hU
  have hEllQ := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet (originCube 2 q)) M.nu (Annealed.sigmaBar M n) M.nu_pos
    (Annealed.sigmaBar_characterization M n).1
    (pureFluxOpenResponseRestriction q (parentBoundaryObserverBandScalar q n height t ω))
  have hEllN := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet (originCube 2 n)) M.nu (Annealed.sigmaBar M n) M.nu_pos
    (Annealed.sigmaBar_characterization M n).1
    (pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t ω))
  apply parent_boundary_inverse_history_congr_blocks U _ _ _ _ _ _
    (hEllQ.mono (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU))
    (hEllN.mono (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hUn))
  intro d W hW
  have hWq : W ∈ descendantsAtDepth (originCube 2 q) (j+d) := by
    simpa only [Nat.add_comm] using mem_descendantsAtDepth_add hU hW
  have hWn : W ∈ descendantsAtDepth (originCube 2 n) (r+(j+d)) := by
    simpa only [Nat.add_comm] using mem_descendantsAtDepth_add hq hWq
  rw [parent_boundary_observer_band_coarse_matrix_frame M q n height t ω hWq,
    native_source_band_coarse_matrix_frame M n height t ω hWn]

/-- One original bank event controls every auxiliary shear and every refined
source mesh within the original five-level population. The source r=1 and
mesh 3-shellIndex obey this condition without enlarging that population. -/
theorem heat_refined_observer_tile_history_ae_le
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (q n : ℤ) (r : ℕ)
    (hq : originCube 2 q ∈ descendantsAtDepth (originCube 2 n) r)
    (height : ℕ) (hpast : ∀ l<n,nativeInductionState M h l) (t : ℝ) (ht : t ≤ 1) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,∀ g : ℝ,∀ j : ℕ,r+j ≤ 5 →
      lemmaVTileHistory (originCube 2 q) j
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
          (pureFluxOpenResponseRestriction q (heatRefinedObserverShear q n height t ω g))) ≤
      (3683/2500:ℝ)+nativeSourceBandRemainder M n height t ω := by
  have hb := native_source_band_history_rare_split M h hM hg n height hpast t ht
  filter_upwards [hb.1,hb.2.2.2.2] with ω hfinite hrare
  intro g j hj
  let Q := originCube 2 q
  let k := pureFluxOpenResponseRestriction q (heatRefinedObserverShear q n height t ω g)
  let af := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n) k
  have hsource := pureFlux_source_tile_history_le Q j af
    ((3683/2500:ℝ)+nativeSourceBandRemainder M n height t ω)
    (fun U hU => by
      change lemmaVInverseHistory U
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
          (pureFluxOpenResponseRestriction q (parentBoundaryObserverBandScalar q n height t ω+
            ContinuousMap.const _ g))) ((3:ℝ)^(1/4:ℝ)) ≤ _
      rw [parent_boundary_inverse_history_gauge q M.nu (Annealed.sigmaBar M n)
        M.nu_pos (Annealed.sigmaBar_characterization M n).1 _ g U j hU,
        heat_refined_observer_history_eq_parent M q n r hq height t ω U j hU]
      have hUn : U ∈ descendantsAtDepth (originCube 2 n) (r+j) := by
        simpa only [Nat.add_comm] using mem_descendantsAtDepth_add hq hU
      exact (native_source_band_mesh_history_le M n height t ω (r+j) hj hfinite.ne hUn).trans hrare)
  exact (tile_history_le_source_history Q j M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1 k).trans hsource

end
end ASDExplicitGamma.Native
