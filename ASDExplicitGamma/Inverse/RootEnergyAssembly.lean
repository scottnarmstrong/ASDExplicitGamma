module

public import ASDExplicitGamma.Inverse.HybridAssembly
public import ASDExplicitGamma.Inverse.HybridLocalResponses
public import ASDExplicitGamma.Inverse.HybridCells
public import ASDExplicitGamma.Inverse.HybridFrameComparison
public import ASDExplicitGamma.Inverse.GoodCellClippedResponse
public import ASDExplicitGamma.Inverse.ClippedMatrixPositiveSums
public import ASDExplicitGamma.Inverse.HybridVariationalComparison

/-! The exact true-frame clock for every Whitney layer. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open ASDExplicitGamma.Response

noncomputable section

/-- A physical root Whitney cell has the actual source layer old cutoff. -/
theorem root_whitney_old_cutoff_eq (Q : TriadicCube 2) (H i : ℕ)
    {P : TriadicCube 2} (hP : P ∈ whitneyRootLayer Q H i) :
    layerOldCutoff Q.scale H i = P.scale+40 := by
  obtain ⟨R,hR,hRP⟩ := Finset.mem_image.mp hP
  have hs := whitney_layer_cell_scale Q.scale H i hR
  have hscale : P.scale=R.scale := by
    rw [← hRP]
    exact root_translate_cube_scale Q R
  unfold layerOldCutoff
  rw [← hs]
  rw [hscale]

/-- An untouched identity cube pays its actual clipped matrix in its
own old true frame. -/
theorem reset_hybrid_identity_response_bound (M : ABKModel 2)
    (Q : TriadicCube 2) (k H : ℕ) (hH : heightEntrance k ≤ H)
    (ω : Cutoff.CutoffSample 2)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc (protectedOldLabel Q.scale k) N,
      0 ≤ weights n ∧ weights n ≤ 1)
    (i : HybridIdentityCell Q H
      (rootBadWhitneyCells M Q H resetAllOrderTau (waveGateEta .allOrder) ω))
    (q : Vec 2) :
    (Annealed.sigmaBar M (i.val.2.val.scale+40):ℝ) * dotProduct q
      ((coarseBlockMatrix (hybridDomain (.inl i):Set (Vec 2))
        (attenuatedCoefficient M (protectedOldLabel Q.scale k) N weights ω)).lowerRight.mulVec q) ≤
      rootAssemblySensitivity * fullMatrixQuadratic (toFullBlockVec (0,q))
        (clippedCellMatrix M (i.val.2.val.scale+40) i.val.2.val resetAllOrderTau ω) := by
  have hgood := hybrid_identity_parent_good M Q H resetAllOrderTau
    (waveGateEta .allOrder) ω i
  have hraw := good_cell_raw_history M i.val.2.val resetAllOrderTau
    (waveGateEta .allOrder) ω hgood
  have hclip := clipped_good_pure_flux_eq M i.val.2.val
    (i.val.2.val.scale+40) resetAllOrderTau ω hraw q
  have hP : i.val.2.val ∈ whitneyRootLayer Q H i.val.1 := i.val.2.property
  have hnpos : 1 ≤ i.val.1 := root_whitney_layer_pos Q H i.val.1 hP
  have hlabel : layerOldCutoff Q.scale H i.val.1 = i.val.2.val.scale+40 :=
    root_whitney_old_cutoff_eq Q H i.val.1 hP
  have hOldLe := layer_old_cutoff_le_protected Q.scale k H i.val.1 hH hnpos
  have hn : i.val.2.val.scale+40 ≤ protectedOldLabel Q.scale k := by
    rw [← hlabel]
    exact hOldLe
  have hmN : protectedOldLabel Q.scale k ≤ N := by
    have hs : protectedOldLabel Q.scale k ≤ Q.scale-1 := by
      dsimp [protectedOldLabel]
      omega
    omega
  have hresponse := reset_good_cell_pure_flux_response M i.val.2.val
    (protectedOldLabel Q.scale k) N hn hmN weights hw ω hgood q
  have hσold : 0 < (Annealed.sigmaBar M (i.val.2.val.scale+40):ℝ) :=
    (Annealed.sigmaBar_characterization M _).1
  have hbound :
      (Annealed.sigmaBar M (i.val.2.val.scale+40):ℝ) * dotProduct q
        ((coarseBlockMatrix (cubeSet i.val.2.val)
          (attenuatedCoefficient M (protectedOldLabel Q.scale k) N weights ω)).lowerRight.mulVec q) ≤
      rootAssemblySensitivity * fullMatrixQuadratic (toFullBlockVec (0,q))
        (clippedCellMatrix M (i.val.2.val.scale+40) i.val.2.val resetAllOrderTau ω) := by
    calc
      _ ≤ (Annealed.sigmaBar M (i.val.2.val.scale+40):ℝ) *
          (rootAssemblySensitivity * dotProduct q
            ((coarseBlockMatrix (cubeSet i.val.2.val)
              (Cutoff.coefficientCutoff M.nu (i.val.2.val.scale+40) ω).toFun).lowerRight.mulVec q)) :=
        mul_le_mul_of_nonneg_left hresponse hσold.le
      _ = rootAssemblySensitivity * fullMatrixQuadratic (toFullBlockVec (0,q))
          (clippedCellMatrix M (i.val.2.val.scale+40) i.val.2.val resetAllOrderTau ω) := by
        calc
          _ = rootAssemblySensitivity *
              ((Annealed.sigmaBar M (i.val.2.val.scale+40):ℝ) *
                dotProduct q ((coarseBlockMatrix (cubeSet i.val.2.val)
                  (Cutoff.coefficientCutoff M.nu (i.val.2.val.scale+40) ω).toFun).lowerRight.mulVec q)) := by
            ring
          _ = _ := by rw [← hclip]
  rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube] at hbound
  exact hbound

/-- Every actual active simplex obeys the local `g(6 tau)` cap. A bad
parent has zero slope; a good parent uses the complete physical triangle sum. -/
theorem reset_hybrid_active_response_bound (M : ABKModel 2)
    (Q : TriadicCube 2) (k H : ℕ) (hH : heightEntrance k ≤ H)
    (ω : Cutoff.CutoffSample 2) (N : ℤ) (hN : Q.scale-1 ≤ N)
    (weights : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc (protectedOldLabel Q.scale k) N,
      0 ≤ weights n ∧ weights n ≤ 1)
    (C : HybridCell Q H
      (rootBadWhitneyCells M Q H resetAllOrderTau (waveGateEta .allOrder) ω) → Mat 2)
    (hCb : ∀ i, (hybridParent i).2.val ∈
      rootBadWhitneyCells M Q H resetAllOrderTau (waveGateEta .allOrder) ω → C i=0)
    (i : HybridActiveCell Q H
      (rootBadWhitneyCells M Q H resetAllOrderTau (waveGateEta .allOrder) ω))
    (q : Vec 2) :
    let m := protectedOldLabel Q.scale k
    let v := matVecMul (planarFluxMatrix (C (.inr i))) q
    (Annealed.sigmaBar M (i.1.val.2.val.scale+40):ℝ) * dotProduct v
      ((coarseBlockMatrix (hybridDomain (.inr i):Set (Vec 2))
        (attenuatedCoefficient M m N weights ω)).lowerRight.mulVec v) ≤
      rootAssemblySensitivity *
        rootResponseEnvelope (6*resetAllOrderTau) * dotProduct v v := by
  classical
  let m := protectedOldLabel Q.scale k
  let P := i.1.val.2.val
  let n := i.1.val.1
  let old := layerOldCutoff Q.scale H n
  have hP : P ∈ whitneyRootLayer Q H n := i.1.val.2.property
  have hnpos : 1 ≤ n := root_whitney_layer_pos Q H n hP
  have hlabel : old=P.scale+40 := root_whitney_old_cutoff_eq Q H n hP
  have hOldLe : old ≤ m := layer_old_cutoff_le_protected Q.scale k H n hH hnpos
  have hn : P.scale+40 ≤ m := by rw [← hlabel]; exact hOldLe
  have hmN : m ≤ N := by dsimp [m,protectedOldLabel]; omega
  by_cases hb : P ∈ rootBadWhitneyCells M Q H resetAllOrderTau
      (waveGateEta .allOrder) ω
  · dsimp only
    rw [hCb (.inr i) hb, planar_flux_matrix_zero]
    simp [matVecMul]
  · have hg := hybrid_parent_good_of_not_bad M Q H resetAllOrderTau
      (waveGateEta .allOrder) ω (.inr i) hb
    obtain ⟨a,ha,hTa⟩ := final_kuhn_support_depth_le_two
      Q H n hP i.2.property
    have hlocal := reset_good_parent_active_triangle_response M hTa ha i.2.val.order
      m N hn hmN weights hw ω hg (matVecMul (planarFluxMatrix (C (.inr i))) q)
    change (Annealed.sigmaBar M (i.1.val.2.val.scale+40):ℝ) *
      dotProduct (matVecMul (planarFluxMatrix (C (.inr i))) q)
        ((coarseBlockMatrix (i.2.val.openCarrier)
          (attenuatedCoefficient M m N weights ω)).lowerRight.mulVec
            (matVecMul (planarFluxMatrix (C (.inr i))) q)) ≤ _
    exact hlocal

end
end ASDExplicitGamma.Inverse
