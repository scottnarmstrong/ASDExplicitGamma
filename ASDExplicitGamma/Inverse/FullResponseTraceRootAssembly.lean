module

public import ASDExplicitGamma.Inverse.FullResponseHybridReferenceTrace
public import ASDExplicitGamma.Inverse.FullResponseIdentityReferenceSum
public import ASDExplicitGamma.Inverse.FullResponseActiveParentLayers
public import ASDExplicitGamma.Inverse.AssemblyTraceMajorant

/-! Actual full-response trace assembly using the common four-load hybrid map. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Variational
open scoped ENNReal
noncomputable section

/-- Complete positive full-row majorant on a deterministic successful height. -/
def fullResponseTraceLayerMajorant (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (N : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) : ℝ≥0∞ :=
  ENNReal.ofReal (rootEdelta .full)*
    (∑' n : ℕ, ENNReal.ofReal (rootAssemblyClock M.gamma H n*
      fullResponseShearedLayerTrace M Q H n N (sourceBandWeights (Q.scale-342) weights) ω))+
  ENNReal.ofReal (rootEdelta .full*(planarGradientCharge 40+1))*
    ∑' n : ℕ, ENNReal.ofReal (rootAssemblyClock M.gamma H n*
      fullResponseActiveLayerDensity M Q H n N weights ω)

/-- The actual normalized full trace is paid by the exact sheared identity
layers and the sharp c0/c1 active parent-density layers. -/
theorem full_response_actual_trace_le_layer_majorant
    (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (hH : 377 ≤ H)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) (rootTau .full) (waveGateEta .full)) k (rootBlockStart Q k))
    (hfinite : ∀ j ≤ Q.scale-(H:ℤ), ∀ z, diameterField
      (q3PlanarMarks M j (rootTau .full) (waveGateEta .full)) ω z ≠ ∞)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ j ∈ Finset.Ioc (Q.scale-342) N, 0 ≤ weights j ∧ weights j ≤ 1) :
    ENNReal.ofReal (rootTraceObservable M Q (Q.scale-342) N (Q.scale-1) weights ω/4) ≤
      fullResponseTraceLayerMajorant M Q H N weights ω := by
  classical
  let S := rootBadWhitneyCells M Q H (rootTau .full) (waveGateEta .full) ω
  let σ := (Annealed.sigmaBar M (Q.scale-1):ℝ)
  have hmN : Q.scale-342 ≤ N := by omega
  obtain ⟨C,hCi,hCb,hCa,hroot⟩ := full_response_actual_trace_le_hybrid M Q H hH ω
    hgood (Q.scale-342) N (Q.scale-1) hmN weights
  let v := fun i : HybridCell Q H S =>
    (volume (hybridDomain i:Set (Vec 2))).toReal/(volume (cubeSet Q)).toReal
  let E := fun (i : HybridCell Q H S) (j : Fin 2 × Bool) =>
    hybridFullTraceCellLoadEnergy σ
      (coarseBlockMatrix (hybridDomain i:Set (Vec 2))
        (attenuatedCoefficient M (Q.scale-342) N weights ω)) (C i) j
  have hsplit : (∑ j : Fin 2 × Bool, ∑' i : HybridCell Q H S,
      ENNReal.ofReal (v i*E i j))*ENNReal.ofReal (1/4:ℝ) =
      (∑ j : Fin 2 × Bool, ∑' i : HybridIdentityCell Q H S,
        ENNReal.ofReal (v (.inl i)*E (.inl i) j))*ENNReal.ofReal (1/4:ℝ)+
      (∑ j : Fin 2 × Bool, ∑' i : HybridActiveCell Q H S,
        ENNReal.ofReal (v (.inr i)*E (.inr i) j))*ENNReal.ofReal (1/4:ℝ) := by
    have hsub (j : Fin 2 × Bool) :
        (∑' i : HybridCell Q H S, ENNReal.ofReal (v i*E i j)) =
          (∑' i : HybridIdentityCell Q H S, ENNReal.ofReal (v (.inl i)*E (.inl i) j))+
          (∑' i : HybridActiveCell Q H S, ENNReal.ofReal (v (.inr i)*E (.inr i) j)) :=
      ENNReal.summable.tsum_sum ENNReal.summable
    simp_rw [hsub]
    rw [Finset.sum_add_distrib,add_mul]
  have hEi (i : HybridIdentityCell Q H S) (j : Fin 2 × Bool) : 0 ≤ E (.inl i) j :=
    attenuated_domain_full_trace_cell_load_nonneg M Q (hybridDomain (.inl i))
      (hybrid_domain_subset_root (.inl i)) (Q.scale-342) N hmN weights ω σ (C (.inl i)) j
  have hnorm := assembly_four_load_normalization
    (fun i : HybridIdentityCell Q H S => v (.inl i))
    (fun i j => E (.inl i) j)
    (fun i => div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) hEi
  have hid := full_response_identity_reference_sum_le_layers M Q H hH ω N hN weights hw
  have hidentity : (∑ j : Fin 2 × Bool, ∑' i : HybridIdentityCell Q H S,
      ENNReal.ofReal (v (.inl i)*E (.inl i) j))*ENNReal.ofReal (1/4:ℝ) ≤
      ENNReal.ofReal (rootEdelta .full)*∑' n : ℕ, ENNReal.ofReal
        (rootAssemblyClock M.gamma H n*fullResponseShearedLayerTrace M Q H n N
          (sourceBandWeights (Q.scale-342) weights) ω) := by
    rw [hnorm]
    apply le_trans (b := _) _ hid
    apply le_of_eq
    apply tsum_congr
    intro i
    have hvol : volume (hybridDomain (.inl i):Set (Vec 2))=volume (cubeSet i.val.2.val) :=
      (measure_congr (cubeSet_ae_eq_openCubeSet i.val.2.val)).symm
    dsimp only [E]
    rw [hCi i,hybrid_full_trace_cell_load_sum_one_eq σ _ (Annealed.sigmaBar_characterization M _).1]
    dsimp only [v]
    rw [hvol,coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube]
    simp only [hybridDomain,Book.Ch02.cubeDomain_coe,σ]
    congr 1
    ring
  have hactive := full_response_active_reference_trace_le_parent_density_sum M Q H
    (by simpa only [rootH0] using hH) ω hgood N hN weights hw hfinite C hCb hCa
  rw [full_response_active_parent_sum_eq_layers] at hactive
  exact hroot.trans ((le_of_eq hsplit).trans (add_le_add hidentity hactive))

end
end ASDExplicitGamma.Inverse
