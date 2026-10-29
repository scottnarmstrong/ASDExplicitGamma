module

public import ASDExplicitGamma.Native.GenericSourceChildBandFrame
public import ASDExplicitGamma.Native.GenericSourceChildBandBank
public import ASDExplicitGamma.Inverse.SourceFramedHistory

/-! Complete source-tile history domination on the simultaneous heat band. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic ASDExplicitGamma.Response
open ASDExplicitGamma.Variational
open scoped ENNReal
noncomputable section

/-- Every source mesh tile is dominated by the actual complete local history
of the simultaneous band, on its genuine finiteness event. -/
theorem native_source_child_band_mesh_history_le
    (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (m : ℕ) (hm : m ≤ 4)
    (hfinite : nativeSourceChildBandHistory M n height t ω ≠ ⊤)
    {U : TriadicCube 2} (hU : U ∈ descendantsAtDepth (originCube 2 (n-1)) m) :
    lemmaVInverseHistory U
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n:ℝ)
        (pureFluxOpenResponseRestriction (n-1) (nativeSourceChildBandScalar n height t ω)))
      ((3:ℝ)^(1/4:ℝ)) ≤ (nativeSourceChildBandHistory M n height t ω).toReal := by
  let P := originCube 2 (n-1)
  let H := pureFluxOpenResponseRestriction (n-1) (nativeSourceChildBandScalar n height t ω)
  let σ : ℝ := Annealed.sigmaBar M n
  let af := responseFramePlanarCoefficientField M.nu σ H
  let q := (3:ℝ)^(1/4:ℝ)
  have hσ := (Annealed.sigmaBar_characterization M n).1
  have hq : 1 < q := Real.one_lt_rpow (by norm_num) (by norm_num)
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet P)
    M.nu σ M.nu_pos hσ H
  have hEllU := hEll.mono (measurableSet_openCubeSet U)
    (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  have hMatrix (V : TriadicCube 2) (j : ℕ) (hV : V ∈ descendantsAtDepth U j) :
      coarseBlockMatrix (cubeSet V) af = frameMatrix σ
        (coarseBlockMatrix (cubeSet V)
          (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω)) := by
    have hVP : V ∈ descendantsAtDepth P (m+j) := by
      simpa only [Nat.add_comm] using mem_descendantsAtDepth_add hU hV
    exact native_source_child_band_coarse_matrix_frame M n height t ω hVP
  have hHistory := source_bank_history_eq_of_framed_matrices U M n (n+(height:ℤ))
    (fun _ => Real.sqrt t) ω af hEllU hMatrix
  have hRoot : U ∈ bankLocalRoots P 4 := by
    rw [bankLocalRoots,Finset.mem_insert]
    right
    rw [Finset.mem_biUnion]
    exact ⟨m,Finset.mem_range.mpr (by omega),hU⟩
  have hmax := bank_member_history_le M (bankLocalRoots P 4) U hRoot n (n+(height:ℤ))
    (fun _ => Real.sqrt t) ω
  have hReal := ENNReal.toReal_mono hfinite hmax
  rw [hHistory,ENNReal.toReal_ofReal (lemmaVInverseHistory_nonneg U af hq)] at hReal
  exact hReal

/-- The actual mixed and pure-source mesh histories have one local-bank
majorant for every shell in the simultaneously inserted band. -/
theorem native_source_child_band_source_history_ae_le
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ j < n, nativeInductionState M h j) (i : ℕ)
    (t : ℝ) (ht1 : t ≤ 1) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      let Q := originCube 2 (n-1)
      let af := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n:ℝ)
        (pureFluxOpenResponseRestriction (n-1) (nativeSourceChildBandScalar n height t ω))
      max (lemmaVTileHistory Q (pureFluxBankSourceDepth (i+2)) af)
        (pureFluxSourceTileHistory Q (pureFluxBankSourceDepth (i+2)) af) ≤
          (nativeSourceChildBandHistory M n height t ω).toReal := by
  let Q := originCube 2 (n-1)
  let σ : ℝ := Annealed.sigmaBar M n
  have hb := native_source_child_band_local_bank M h hM hg n height hpast t ht1
  have hd := pureFlux_bank_source_depth_le_four (i+2) (by omega)
  filter_upwards [hb.history_finite] with ω hfinite
  let H := pureFluxOpenResponseRestriction (n-1) (nativeSourceChildBandScalar n height t ω)
  let af := responseFramePlanarCoefficientField M.nu σ H
  have hsource (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q (pureFluxBankSourceDepth (i+2))) :
      lemmaVInverseHistory U af ((3:ℝ)^(1/4:ℝ)) ≤
        (nativeSourceChildBandHistory M n height t ω).toReal :=
    native_source_child_band_mesh_history_le M n height t ω (pureFluxBankSourceDepth (i+2))
      (by omega) hfinite.ne hU
  have hr := pureFlux_source_tile_history_le Q (pureFluxBankSourceDepth (i+2)) af _ hsource
  have hm := tile_history_le_source_history Q (pureFluxBankSourceDepth (i+2)) M.nu σ
    M.nu_pos (Annealed.sigmaBar_characterization M n).1 H
  exact max_le (hm.trans hr) hr

end
end ASDExplicitGamma.Native
