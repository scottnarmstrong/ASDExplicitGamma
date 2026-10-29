module

public import ASDExplicitGamma.Native.HeatVHEATDriftSourceBank

/-! Exact history representation and measurability of the ACTUAL refined
source drift bank. Auxiliary gauges do not change its physical histories. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Triadic Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Every actual normalized source inverse history is exactly its finite
extended physical bank representation, before conversion to real. -/
theorem heatVHEATDrift_inverse_history_eq_bank
    (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (r : ℕ) (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 n) r) :
    lemmaVInverseHistory U (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
      (pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t ω))) ((3:ℝ)^(1/4:ℝ)) =
      (bankRootInverseHistory U M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω).toReal := by
  let P := originCube 2 n
  let H := pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t ω)
  let af := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n) H
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet P)
    M.nu (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1 H
  have hMatrix (V : TriadicCube 2) (j : ℕ) (hV : V∈descendantsAtDepth U j) :
      coarseBlockMatrix (cubeSet V) af=frameMatrix (Annealed.sigmaBar M n)
        (coarseBlockMatrix (cubeSet V) (attenuatedCoefficient M n (n+(height:ℤ))
          (fun _ => Real.sqrt t) ω)) :=
    native_source_band_coarse_matrix_frame M n height t ω (mem_descendantsAtDepth_add hU hV)
  have hh := source_bank_history_eq_of_framed_matrices U M n (n+(height:ℤ))
    (fun _ => Real.sqrt t) ω af
    (hEll.mono (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU)) hMatrix
  rw [hh,ENNReal.toReal_ofReal (lemmaVInverseHistory_nonneg U af
    (Real.one_lt_rpow (by norm_num) (by norm_num)))]

/-- The max of the mixed and pure-source banks is the literal complete
physical inverse-history maximum over the refined source mesh. -/
theorem heatVHEATDrift_bank_eq_root_max
    (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (g : ℝ) (d : Fin 9) :
    heatVHEATDriftBank M n height t ω g d=
      Book.Ch02.finsetSupReal (descendantsAtDepth (originCube 2 (n-1)) (pureFluxBankSourceDepth (d.val+2)))
        (fun U => (bankRootInverseHistory U M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω).toReal) := by
  let Q := originCube 2 (n-1)
  let j := pureFluxBankSourceDepth (d.val+2)
  let k := pureFluxOpenResponseRestriction (n-1) (heatRefinedObserverShear (n-1) n height t ω g)
  have hq : Q∈descendantsAtDepth (originCube 2 n) 1 := by
    simpa only [Nat.cast_one] using originCube_mem_descendantsAtDepth' 2 n 1
  have hm := tile_history_le_source_history Q j M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1 k
  change max _ _=_
  rw [max_eq_right hm]
  apply Book.Ch02.finsetSupReal_congr
  intro U hU
  change lemmaVInverseHistory U (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
    (pureFluxOpenResponseRestriction (n-1)
      (parentBoundaryObserverBandScalar (n-1) n height t ω+ContinuousMap.const _ g))) _=_
  rw [parent_boundary_inverse_history_gauge (n-1) M.nu (Annealed.sigmaBar M n) M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 _ g U j hU,
    heat_refined_observer_history_eq_parent M (n-1) n 1 hq height t ω U j hU]
  exact heatVHEATDrift_inverse_history_eq_bank M n height t ω (1+j) U (mem_descendantsAtDepth_add hq hU)

/-- Every auxiliary shear gives the same bank, on EVERY sample. -/
theorem heatVHEATDrift_bank_gauge
    (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (g : ℝ) (d : Fin 9) :
    heatVHEATDriftBank M n height t ω g d=heatVHEATDriftBank M n height t ω 0 d := by
  rw [heatVHEATDrift_bank_eq_root_max,heatVHEATDrift_bank_eq_root_max]

end
end ASDExplicitGamma.Native
