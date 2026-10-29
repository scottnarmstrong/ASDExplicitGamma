module

public import ASDExplicitGamma.Inverse.FullResponseActiveReferenceFrame
public import ASDExplicitGamma.Inverse.FullResponseIdentityShear

/-! Exact sheared identity-cell payment in the root reference frame. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider Algsuperdiff.Section3.Provider.Whitney
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic ASDExplicitGamma.Response
open ASDExplicitGamma.Variational
open scoped ENNReal

noncomputable section

/-- An identity slope leaves the full four-load trace exactly unchanged. -/
theorem hybrid_full_trace_cell_load_sum_one_eq (σ : ℝ) (A : BlockMat 2)
    (hσ : 0 < σ) :
    (∑ j : Fin 2 × Bool, hybridFullTraceCellLoadEnergy σ A 1 j) =
      Matrix.trace (toFullBlockMat (frameMatrix σ A)) := by
  rw [hybrid_full_trace_cell_load_sum_eq σ A 1 hσ, planar_flux_matrix_one]
  simp only [Matrix.conjTranspose_one, one_mul, mul_one]
  simp [Matrix.trace, toFullBlockMat, frameMatrix, Fintype.sum_sum_type,
    Fin.sum_univ_two, Matrix.diag_apply]
  ring

/-- Every actual untouched cube pays its exactly sheared clipped old matrix
in the root reference frame. The attenuation starts in the protected past. -/
theorem full_response_identity_reference_cell_le
    (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (hH : 377 ≤ H)
    (ω : Cutoff.CutoffSample 2) (J : ℤ) (hJ : Q.scale-1 ≤ J)
    (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc (Q.scale-342) J, 0 ≤ weights k ∧ weights k ≤ 1)
    (i : HybridIdentityCell Q H (rootBadWhitneyCells M Q H (rootTau .full)
      (waveGateEta .full) ω)) :
    let P := i.val.2.val
    let n := P.scale+40
    let R := assemblyPhysicalShearMatrix M n P.scale J
      (((P.index 0:ℝ)-1/2)*(3:ℝ)^P.scale)
      (((P.index 1:ℝ)-1/2)*(3:ℝ)^P.scale) (sourceBandWeights (Q.scale-342) weights) ω
    ENNReal.ofReal (Matrix.trace (toFullBlockMat (frameMatrix
      (Annealed.sigmaBar M (Q.scale-1) : ℝ)
      (coarseBlockMatrix (cubeSet P) (attenuatedCoefficient M (Q.scale-342) J weights ω))))/4) ≤
      ENNReal.ofReal (rootEdelta .full*rootAssemblyClock M.gamma H i.val.1) *
        ENNReal.ofReal (Matrix.trace (R.transpose*clippedCellMatrix M n P (rootTau .full) ω*R)/4) := by
  classical
  dsimp only
  let P := i.val.2.val
  let n := P.scale+40
  let A := coarseBlockMatrix (cubeSet P) (attenuatedCoefficient M (Q.scale-342) J weights ω)
  let G := rootAssemblyClock M.gamma H i.val.1
  have hnpos := root_whitney_layer_pos Q H i.val.1 i.val.2.property
  have hH0 : heightEntrance 0 ≤ H := by
    simpa only [heightEntrance, mul_zero, add_zero] using hH
  have hn : n ≤ Q.scale-342 := by
    have hh := layer_old_cutoff_le_protected Q.scale 0 H i.val.1 hH0 hnpos
    rw [root_whitney_old_cutoff_eq Q H i.val.1 i.val.2.property] at hh
    simpa only [n, P, protectedOldLabel, Nat.cast_zero, mul_zero, sub_zero] using hh
  have hgood := hybrid_identity_parent_good M Q H (rootTau .full)
    (waveGateEta .full) ω i
  have hlocal := good_cell_physical_shear_trace M P .full
    (Q.scale-342) J hn (by omega) weights hw ω hgood
  have hframe := full_response_cell_load_sum_reference_frame_le M Q H hH ω J
    (by omega) weights (fun _ => 1) (.inl i)
  dsimp only [hybridParent, hybridDomain, Book.Ch02.cubeDomain] at hframe
  rw [hybrid_full_trace_cell_load_sum_one_eq _ _
      (Annealed.sigmaBar_characterization M (Q.scale-1)).1,
    hybrid_full_trace_cell_load_sum_one_eq _ _
      (Annealed.sigmaBar_characterization M n).1] at hframe
  rw [← coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube P] at hframe
  have hnorm (t : ℝ) : ENNReal.ofReal (t/4) =
      ENNReal.ofReal (1/4:ℝ)*ENNReal.ofReal t := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/4)]
    congr 1
    ring
  have hframeN : ENNReal.ofReal (Matrix.trace (toFullBlockMat
      (frameMatrix (Annealed.sigmaBar M (Q.scale-1) : ℝ) A))/4) ≤
      ENNReal.ofReal G * ENNReal.ofReal (Matrix.trace (toFullBlockMat
        (frameMatrix (Annealed.sigmaBar M n : ℝ) A))/4) := by
    calc
      _ = ENNReal.ofReal (1/4:ℝ)*ENNReal.ofReal (Matrix.trace (toFullBlockMat
          (frameMatrix (Annealed.sigmaBar M (Q.scale-1) : ℝ) A))) := hnorm _
      _ ≤ ENNReal.ofReal (1/4:ℝ)*(ENNReal.ofReal G * ENNReal.ofReal
          (Matrix.trace (toFullBlockMat (frameMatrix (Annealed.sigmaBar M n : ℝ) A)))) :=
        mul_le_mul_of_nonneg_left hframe bot_le
      _ = _ := by
        rw [hnorm (Matrix.trace (toFullBlockMat (frameMatrix (Annealed.sigmaBar M n : ℝ) A)))]
        ac_rfl
  have hE : 0 ≤ rootEdelta .full := (Real.exp_pos _).le
  apply hframeN.trans
  have hs := mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hlocal)
    (show 0 ≤ ENNReal.ofReal G from bot_le)
  apply hs.trans_eq
  rw [ENNReal.ofReal_mul hE, ENNReal.ofReal_mul hE]
  dsimp only [G, P, n]
  ac_rfl

end
end ASDExplicitGamma.Inverse
