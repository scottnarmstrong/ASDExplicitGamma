module

public import ASDExplicitGamma.Inverse.RootEnergyAssembly

/-! The hybrid inverse energy in the root scale-minus-one true frame. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider Algsuperdiff.Section3.Provider.Whitney
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Response
noncomputable section

/-- The root scale-minus-one frame has exactly the root-relative layer clock. -/
theorem assembly_layer_root_frame_ratio (M : ABKModel 2) (l : ℤ)
    (k H i : ℕ) (hH : heightEntrance k ≤ H) (hi : 1 ≤ i) :
    (Annealed.sigmaBar M (l-1):ℝ)/(Annealed.sigmaBar M (layerOldCutoff l H i):ℝ) ≤
      rootAssemblyClock M.gamma H i := by
  have hs := layer_old_cutoff_eq_source_offset l H i
    (by unfold heightEntrance at hH; omega) hi
  have hr := true_frame_ratio_le M (l-1) (layerOldCutoff l H i)
  have he : l-1-layerOldCutoff l H i = (layerRelativeOffset H i:ℤ) := by
    rw [hs]
    omega
  rw [he,Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg _)] at hr
  exact hr

/-- An untouched identity cube pays its actual local clipped matrix after
conversion to the root scale-minus-one frame. -/
theorem assembly_identity_root_framed_response (M : ABKModel 2)
    (Q : TriadicCube 2) (k H : ℕ) (hH : heightEntrance k ≤ H)
    (ω : Cutoff.CutoffSample 2) (N : ℤ) (hN : Q.scale-1 ≤ N)
    (weights : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc (protectedOldLabel Q.scale k) N,
      0 ≤ weights n ∧ weights n ≤ 1)
    (i : HybridIdentityCell Q H
      (rootBadWhitneyCells M Q H resetAllOrderTau (waveGateEta .allOrder) ω))
    (q : Vec 2) :
    let m := protectedOldLabel Q.scale k
    let w := rootAssemblyClock M.gamma H i.val.1
    ((Annealed.sigmaBar M (Q.scale-1):ℝ) *
      (volume (cubeSet i.val.2.val)).toReal/(volume (cubeSet Q)).toReal) *
        dotProduct q ((coarseBlockMatrix (cubeSet i.val.2.val)
          (attenuatedCoefficient M m N weights ω)).lowerRight.mulVec q) ≤
      rootAssemblySensitivity *
        (w * (volume (cubeSet i.val.2.val)).toReal/(volume (cubeSet Q)).toReal *
          fullMatrixQuadratic (toFullBlockVec (0,q))
            (clippedCellMatrix M (i.val.2.val.scale+40) i.val.2.val
              resetAllOrderTau ω)) := by
  let m := protectedOldLabel Q.scale k
  let P := i.val.2.val
  let n := i.val.1
  let old := layerOldCutoff Q.scale H n
  have hP : P ∈ whitneyRootLayer Q H n := i.val.2.property
  have hnpos : 1 ≤ n := root_whitney_layer_pos Q H n hP
  have hlabel : old=P.scale+40 := root_whitney_old_cutoff_eq Q H n hP
  have hOldLe : old ≤ m := layer_old_cutoff_le_protected Q.scale k H n hH hnpos
  have hn : P.scale+40 ≤ m := by rw [← hlabel]; exact hOldLe
  have hmN : m ≤ N := by dsimp [m,protectedOldLabel]; omega
  have hlocal := reset_hybrid_identity_response_bound M Q k H hH ω N hN weights hw i q
  have hratio := assembly_layer_root_frame_ratio M Q.scale k H n hH hnpos
  have hlabel' := root_whitney_old_cutoff_eq Q H n hP
  have hσ : 0 ≤ (Annealed.sigmaBar M (Q.scale-1):ℝ) :=
    (Annealed.sigmaBar_characterization M (Q.scale-1)).1.le
  have hσold : 0 < (Annealed.sigmaBar M (P.scale+40):ℝ) :=
    (Annealed.sigmaBar_characterization M _).1
  have hratio' := hratio
  rw [hlabel'] at hratio'
  have hB : 0 ≤ rootAssemblySensitivity * fullMatrixQuadratic
      (toFullBlockVec (0,q)) (clippedCellMatrix M (P.scale+40) P resetAllOrderTau ω) :=
    mul_nonneg root_assembly_sensitivity_pos.le
      (clipped_cell_matrix_quadratic_nonneg M (P.scale+40) P resetAllOrderTau ω _)
  have hframe := convert_local_frame_energy hσ hσold
    hlocal hB hratio'
  have hvol : 0 ≤ (volume (cubeSet P)).toReal/(volume (cubeSet Q)).toReal :=
    div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hf := mul_le_mul_of_nonneg_left hframe hvol
  dsimp only [m,n,P] at hf
  dsimp only [m,n,P]
  rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube]
  simp only [hybridDomain, Book.Ch02.cubeDomain_coe] at hf
  convert hf using 1 <;> ring_nf

/-- The active response in the root scale-minus-one true frame. -/
theorem assembly_active_root_framed_response (M : ABKModel 2)
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
    let w := rootAssemblyClock M.gamma H i.1.val.1
    (Annealed.sigmaBar M (Q.scale-1):ℝ) *
      (volume (hybridDomain (.inr i):Set (Vec 2))).toReal /
        (volume (cubeSet Q)).toReal *
          dotProduct v ((coarseBlockMatrix (hybridDomain (.inr i):Set (Vec 2))
            (attenuatedCoefficient M m N weights ω)).lowerRight.mulVec v) ≤
      rootAssemblySensitivity * rootResponseEnvelope (6*resetAllOrderTau) *
        (w * (volume (hybridDomain (.inr i):Set (Vec 2))).toReal /
          (volume (cubeSet Q)).toReal * dotProduct v v) := by
  classical
  let m := protectedOldLabel Q.scale k
  let P := i.1.val.2.val
  let n := i.1.val.1
  let v := matVecMul (planarFluxMatrix (C (.inr i))) q
  have hP : P ∈ whitneyRootLayer Q H n := i.1.val.2.property
  have hnpos : 1 ≤ n := root_whitney_layer_pos Q H n hP
  have hlabel := root_whitney_old_cutoff_eq Q H n hP
  have hratio := assembly_layer_root_frame_ratio M Q.scale k H n hH hnpos
  rw [root_whitney_old_cutoff_eq Q H n hP] at hratio
  have hσ : 0 ≤ (Annealed.sigmaBar M (Q.scale-1):ℝ) :=
    (Annealed.sigmaBar_characterization M (Q.scale-1)).1.le
  have hσold : 0 < (Annealed.sigmaBar M (P.scale+40):ℝ) :=
    (Annealed.sigmaBar_characterization M _).1
  have hτ : 0 ≤ resetAllOrderTau := by
    norm_num [resetAllOrderTau, Numerics.Wave.allOrderTau]
  have hv : 0 ≤ dotProduct v v :=
    Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
  have henv : 0 ≤ rootResponseEnvelope (6*resetAllOrderTau) := by
    unfold rootResponseEnvelope
    positivity
  have hB : 0 ≤ rootAssemblySensitivity *
      rootResponseEnvelope (6*resetAllOrderTau) * dotProduct v v :=
    mul_nonneg (mul_nonneg root_assembly_sensitivity_pos.le henv) hv
  have hlocal := reset_hybrid_active_response_bound M Q k H hH ω N hN weights hw C hCb i q
  have hframe := convert_local_frame_energy hσ hσold hlocal hB hratio
  have hvol : 0 ≤ (volume (hybridDomain (.inr i):Set (Vec 2))).toReal /
      (volume (cubeSet Q)).toReal :=
    div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hf := mul_le_mul_of_nonneg_left hframe hvol
  dsimp only [m,n,P,v] at hf
  dsimp only [m,n,P,v]
  convert hf using 1 <;> ring_nf

/-- The whole hybrid family has a single common slope map and pays the
actual clipped identity matrices and active flux energies in the root scale-minus-one
frame. -/
theorem assembly_hybrid_root_framed_split (M : ABKModel 2)
    (Q : TriadicCube 2) (k H : ℕ) (hH : heightEntrance k ≤ H)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ j, H ≤ j → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-j) resetAllOrderTau (waveGateEta .allOrder))
      j (rootBlockStart Q j))
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc (protectedOldLabel Q.scale k) N,
      0 ≤ weights n ∧ weights n ≤ 1) :
    let S := rootBadWhitneyCells M Q H resetAllOrderTau (waveGateEta .allOrder) ω
    let w := fun n : ℕ => rootAssemblyClock M.gamma H n
    ∃ C : HybridCell Q H S → Mat 2,
      (∀ i : HybridIdentityCell Q H S, C (.inl i)=1) ∧
      (∀ i, (hybridParent i).2.val ∈ S → C i=0) ∧
      (∀ i, ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
        x ∈ (hybridDomain i:Set (Vec 2)) →
          stoppedKuhnGradient M Q H
            (show 333 ≤ H by
              have hk : 377 + 12*k ≤ heightEntrance k := by
                unfold heightEntrance
                omega
              omega)
            resetAllOrderTau (waveGateEta .allOrder) ω hgood S
            (fun _ h => h.1) (fun _ h => h.2) x = C i) ∧
      (∀ q : Vec 2,
        ENNReal.ofReal ((Annealed.sigmaBar M (Q.scale-1):ℝ) *
          dotProduct q ((coarseBlockMatrix (cubeSet Q)
            (attenuatedCoefficient M (protectedOldLabel Q.scale k) N weights ω)).lowerRight.mulVec q)) ≤
        ENNReal.ofReal rootAssemblySensitivity *
          ((∑' i : HybridIdentityCell Q H S,
              ENNReal.ofReal (w i.val.1*(volume (cubeSet i.val.2.val)).toReal/
                (volume (cubeSet Q)).toReal * fullMatrixQuadratic (toFullBlockVec (0,q))
                  (clippedCellMatrix M (i.val.2.val.scale+40) i.val.2.val resetAllOrderTau ω))) +
            ENNReal.ofReal (rootResponseEnvelope (6*resetAllOrderTau)) *
              ∑' i : HybridActiveCell Q H S,
                ENNReal.ofReal (w i.1.val.1*(volume (hybridDomain (.inr i):Set (Vec 2))).toReal/
                  (volume (cubeSet Q)).toReal *
                  dotProduct (matVecMul (planarFluxMatrix (C (.inr i))) q)
                    (matVecMul (planarFluxMatrix (C (.inr i))) q)))) := by
  classical
  dsimp only
  let τ := resetAllOrderTau
  let η := waveGateEta .allOrder
  let S := rootBadWhitneyCells M Q H τ η ω
  let w := fun n : ℕ => rootAssemblyClock M.gamma H n
  have h333 : 333 ≤ H := by
    have hk : 377 + 12*k ≤ heightEntrance k := by
      unfold heightEntrance
      omega
    omega
  have hS : S ⊆ whitneyRootPartition Q H := fun _ h => h.1
  have hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V := fun _ h => h.2
  obtain ⟨C,hCi,hCb,hCa,hvar⟩ :=
    actual_hybrid_variational_comparison M Q H h333 τ η ω hgood S hS hbad
      (protectedOldLabel Q.scale k) N (by
        have hprot : protectedOldLabel Q.scale k ≤ Q.scale-1 := by
          dsimp [protectedOldLabel]
          omega
        omega) weights
  refine ⟨C,hCi,hCb,hCa,?_⟩
  intro q
  let σ := (Annealed.sigmaBar M (Q.scale-1):ℝ)
  let b := fun i : HybridCell Q H S => matVecMul (planarFluxMatrix (C i)) q
  let F := fun i : HybridCell Q H S => σ*(volume (hybridDomain i:Set (Vec 2))).toReal/
    (volume (cubeSet Q)).toReal*dotProduct (b i)
      ((coarseBlockMatrix (hybridDomain i:Set (Vec 2))
        (attenuatedCoefficient M (protectedOldLabel Q.scale k) N weights ω)).lowerRight.mulVec (b i))
  let fi := fun i : HybridIdentityCell Q H S => w i.val.1*
    (volume (cubeSet i.val.2.val)).toReal/(volume (cubeSet Q)).toReal*
      fullMatrixQuadratic (toFullBlockVec (0,q))
        (clippedCellMatrix M (i.val.2.val.scale+40) i.val.2.val τ ω)
  let fa := fun i : HybridActiveCell Q H S => w i.1.val.1*
    (volume (hybridDomain (.inr i):Set (Vec 2))).toReal/(volume (cubeSet Q)).toReal*
      dotProduct (b (.inr i)) (b (.inr i))
  have hσ : 0 ≤ σ := (Annealed.sigmaBar_characterization M _).1.le
  have hGE : 0 ≤ rootAssemblySensitivity := root_assembly_sensitivity_pos.le
  have hτ : 0 ≤ τ := by norm_num [τ, resetAllOrderTau, Numerics.Wave.allOrderTau]
  have hg : 0 ≤ rootResponseEnvelope (6*τ) := by
    unfold rootResponseEnvelope
    positivity
  have hroot : ENNReal.ofReal (σ*dotProduct q ((coarseBlockMatrix (cubeSet Q)
      (attenuatedCoefficient M (protectedOldLabel Q.scale k) N weights ω)).lowerRight.mulVec q)) ≤
        ∑' i : HybridCell Q H S, ENNReal.ofReal (F i) := by
    have hh := mul_le_mul_right (hvar q) (ENNReal.ofReal σ)
    rw [← ENNReal.ofReal_mul hσ, ← ENNReal.tsum_mul_left] at hh
    apply hh.trans_eq
    apply tsum_congr
    intro i
    rw [← ENNReal.ofReal_mul hσ]
    have he : volume (openCubeSet Q)=volume (cubeSet Q) :=
      (measure_congr (cubeSet_ae_eq_openCubeSet Q)).symm
    rw [he]
    congr 1
    dsimp only [F,b]
    ring
  let R : HybridCell Q H S → ENNReal := Sum.elim
    (fun i => ENNReal.ofReal rootAssemblySensitivity * ENNReal.ofReal (fi i))
    (fun i => ENNReal.ofReal (rootAssemblySensitivity *
      rootResponseEnvelope (6*τ)) * ENNReal.ofReal (fa i))
  have hterm (i : HybridCell Q H S) : ENNReal.ofReal (F i) ≤ R i := by
    cases i with
    | inl i =>
      change ENNReal.ofReal (F (.inl i)) ≤
        ENNReal.ofReal rootAssemblySensitivity * ENNReal.ofReal (fi i)
      rw [← ENNReal.ofReal_mul hGE]
      apply ENNReal.ofReal_le_ofReal
      have hh := assembly_identity_root_framed_response M Q k H hH ω N hN weights hw i q
      have hOne : matVecMul (1:Mat 2) q=q := by ext j; simp [matVecMul,Matrix.one_apply]
      have he : volume (hybridDomain (.inl i):Set (Vec 2))=volume (cubeSet i.val.2.val) :=
        (measure_congr (cubeSet_ae_eq_openCubeSet i.val.2.val)).symm
      dsimp only at hh
      rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube] at hh
      dsimp only [F,b,w,fi,σ,τ]
      rw [hCi i,planar_flux_matrix_one,hOne,he]
      simpa only [hybridDomain, Book.Ch02.cubeDomain_coe] using hh
    | inr i =>
      change ENNReal.ofReal (F (.inr i)) ≤
        ENNReal.ofReal (rootAssemblySensitivity *
          rootResponseEnvelope (6*τ)) * ENNReal.ofReal (fa i)
      rw [← ENNReal.ofReal_mul (mul_nonneg hGE hg)]
      exact ENNReal.ofReal_le_ofReal
        (assembly_active_root_framed_response M Q k H hH ω N hN weights hw C hCb i q)
  have hsum := hroot.trans (ENNReal.tsum_le_tsum hterm)
  apply hsum.trans_eq
  change (∑' i : HybridIdentityCell Q H S ⊕ HybridActiveCell Q H S, R i)=_
  rw [ENNReal.summable.tsum_sum ENNReal.summable]
  change (∑' i : HybridIdentityCell Q H S,
      ENNReal.ofReal rootAssemblySensitivity * ENNReal.ofReal (fi i)) +
    (∑' i : HybridActiveCell Q H S,
      ENNReal.ofReal (rootAssemblySensitivity * rootResponseEnvelope (6*τ)) *
        ENNReal.ofReal (fa i)) = _
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
    ENNReal.ofReal_mul hGE, mul_add, mul_assoc]

end
end ASDExplicitGamma.Inverse
