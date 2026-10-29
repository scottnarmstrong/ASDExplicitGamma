module

public import ASDExplicitGamma.Inverse.AssemblyIdentityTrace
public import ASDExplicitGamma.Inverse.AssemblyReferenceEnergy

/-! Exact source-root frame conversion for the actual full trace. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Multiscale
open ASDExplicitGamma.Triadic ASDExplicitGamma.Response ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian
noncomputable section

/-- Positivity of the genuine attenuated coarse response on every contained domain. -/
theorem assembly_attenuated_domain_quadratic_nonneg (M : ABKModel 2) (Q : TriadicCube 2)
    (n m N : ℤ) (hn : n ≤ m) (hm : m ≤ N) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2)
    (T : Book.Ch02.Domain 2) (hT : (T:Set (Vec 2)) ⊆ openCubeSet Q) (P : BlockVec 2) :
    0 ≤ blockVecDot P (blockMatVecMul (coarseBlockMatrix (T:Set (Vec 2))
      (attenuatedCoefficient M m N weights ω)) P) := by
  let aQ := sensitivityBookCoeffOn Q M.nu M.nu_pos
    (oldResponseCoefficient Q n ω+laterResponseCoefficient Q n N (sourceBandWeights m weights) ω)
  let aT := restrictCoeffOn aQ hT
  have he : Book.Ch02.coarseBlockMatrix T aT = coarseBlockMatrix (T:Set (Vec 2))
      (attenuatedCoefficient M m N weights ω) :=
    attenuated_domain_matrix_eq M Q n m N hn hm weights ω T hT
  rw [← he]
  by_cases hP : P=0
  · rw [hP]
    simp [blockVecDot,blockMatVecMul,vecDot,matVecMul]
  · exact (Book.Ch02.blockCoarseMatrixTheory T aT).block_matrix_posDef P hP |>.le

/-- Nonnegative paired energies supply the two trace signs needed for a
full-trace scalar-frame conversion. -/
theorem assembly_trace_frame_growth (A : BlockMat 2) (σold σ G : ℝ)
    (hσold : 0 < σold) (hσ : σold ≤ σ) (hG : 1 ≤ G) (hratio : σ/σold ≤ G)
    (hquad : ∀ P : BlockVec 2, 0 ≤ blockVecDot P (blockMatVecMul A P)) :
    Matrix.trace (toFullBlockMat (frameMatrix σ A))/4 ≤
      G*(Matrix.trace (toFullBlockMat (frameMatrix σold A))/4) := by
  have hULdiag (j : Fin 2) : 0 ≤ A.upperLeft j j := by
    have hh := hquad (Pi.single j 1,0)
    simpa [blockVecDot,blockMatVecMul,vecDot,matVecMul,Matrix.mulVec,Fin.sum_univ_two,Pi.single_apply] using hh
  have hLRdiag (j : Fin 2) : 0 ≤ A.lowerRight j j := by
    have hh := hquad (0,Pi.single j 1)
    simpa [blockVecDot,blockMatVecMul,vecDot,matVecMul,Matrix.mulVec,Fin.sum_univ_two,Pi.single_apply] using hh
  have hUL : 0 ≤ Matrix.trace A.upperLeft := Finset.sum_nonneg fun j _ => hULdiag j
  have hLR : 0 ≤ Matrix.trace A.lowerRight := Finset.sum_nonneg fun j _ => hLRdiag j
  have hh := full_response_framed_trace_le_of_scalar_frame_growth A σold σ G
    hσold hσ hG hratio hUL hLR
  exact (div_le_div_of_nonneg_right hh (by norm_num : (0:ℝ) ≤ 4)).trans_eq (by ring)

/-- Every actual old layer frame lies below the source-root frame, with
exactly the root-relative layer clock as its ratio upper bound. -/
theorem assembly_layer_to_root_frames (M : ABKModel 2) (l : ℤ)
    (k H n : ℕ) (hH : heightEntrance k ≤ H) (hn : 1 ≤ n) :
    let σold := (Annealed.sigmaBar M (layerOldCutoff l H n):ℝ)
    let σ := (Annealed.sigmaBar M (l-1):ℝ)
    let G := rootAssemblyClock M.gamma H n
    σold ≤ σ ∧ 1 ≤ G ∧ σ/σold ≤ G := by
  dsimp only
  have hcut := layer_old_cutoff_le_protected l k H n hH hn
  have hle : layerOldCutoff l H n ≤ l-1 := by unfold protectedOldLabel at hcut; omega
  have hcont := ASDExplicitGamma.Scalar.sigmaBar_structural_continuity M
    (layerOldCutoff l H n) (l-1-layerOldCutoff l H n) (by omega)
  rw [show layerOldCutoff l H n+(l-1-layerOldCutoff l H n)=l-1 by omega] at hcont
  have hold := (Annealed.sigmaBar_characterization M (layerOldCutoff l H n)).1
  have hratio := assembly_layer_root_frame_ratio M l k H n hH hn
  refine ⟨?_,hcont.1.trans hratio,hratio⟩
  have hh := (le_div_iff₀ hold).mp hcont.1
  simpa only [one_mul] using hh

/-- A good layer cell pays its actual sheared clipped trace in the source
root frame, retaining the exact normalized trace coefficient. -/
theorem assembly_good_layer_cell_trace_root_frame (M : ABKModel 2)
    (Q : TriadicCube 2) (k H n : ℕ) (hH : heightEntrance k ≤ H)
    {P : TriadicCube 2} (hP : P ∈ whitneyRootLayer Q H n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ j ∈ Finset.Ioc (protectedOldLabel Q.scale k) N, 0 ≤ weights j ∧ weights j ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M resetAllOrderTau (waveGateEta .allOrder) P) :
    let old := P.scale+40
    let R := assemblyPhysicalShearMatrix M old P.scale N
      (((P.index 0:ℝ)-1/2)*(3:ℝ)^P.scale) (((P.index 1:ℝ)-1/2)*(3:ℝ)^P.scale)
      (sourceBandWeights (protectedOldLabel Q.scale k) weights) ω
    rootTraceObservable M P (protectedOldLabel Q.scale k) N (Q.scale-1) weights ω/4 ≤
      rootAssemblyClock M.gamma H n*rootAssemblySensitivity*
        (Matrix.trace (R.transpose*clippedCellMatrix M old P resetAllOrderTau ω*R)/4) := by
  have hn := root_whitney_layer_pos Q H n hP
  have hlabel := root_whitney_old_cutoff_eq Q H n hP
  have hcut := layer_old_cutoff_le_protected Q.scale k H n hH hn
  have hold : P.scale+40 ≤ protectedOldLabel Q.scale k := by rwa [hlabel] at hcut
  have hmN : protectedOldLabel Q.scale k ≤ N := by unfold protectedOldLabel; omega
  have hquad := assembly_attenuated_domain_quadratic_nonneg M P
    (P.scale+40) (protectedOldLabel Q.scale k) N hold hmN weights ω
    (Book.Ch02.cubeDomain P) Set.Subset.rfl
  have hquad' : ∀ X : BlockVec 2, 0 ≤ blockVecDot X (blockMatVecMul
      (coarseBlockMatrix (cubeSet P) (attenuatedCoefficient M (protectedOldLabel Q.scale k) N weights ω)) X) := by
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube]
    exact hquad
  obtain ⟨hσ,hG,hratio⟩ := assembly_layer_to_root_frames M Q.scale k H n hH hn
  rw [hlabel] at hσ hratio
  have hframe := assembly_trace_frame_growth _ _ _ _
    (Annealed.sigmaBar_characterization M (P.scale+40)).1 hσ hG hratio hquad'
  have hlocal := assembly_good_cell_physical_shear_trace M P (protectedOldLabel Q.scale k)
    N hold hmN weights hw ω hgood
  apply hframe.trans
  exact (mul_le_mul_of_nonneg_left hlocal (root_assembly_clock_pos M.gamma H n).le).trans_eq (by ring)

end
end ASDExplicitGamma.Inverse
