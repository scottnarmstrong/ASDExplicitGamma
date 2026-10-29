module

public import ASDExplicitGamma.Inverse.AssemblyTraceMajorant
public import ASDExplicitGamma.Inverse.AssemblyLayerSums

/-! Complete pathwise trace assembly on the actual common hybrid map. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider Algsuperdiff.Section3.Provider.Whitney
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Variational
open scoped ENNReal
noncomputable section

/-- The actual full trace is paid by complete positive deterministic sheared
matrix and spatial density layers, retaining one common four-load map. -/
theorem assembly_actual_trace_le_layer_majorant (M : ABKModel 2) (Q : TriadicCube 2)
    (k H : ℕ) (hH : heightEntrance k ≤ H) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ j, H ≤ j → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-j) resetAllOrderTau (waveGateEta .allOrder)) j (rootBlockStart Q j))
    (hfinite : ∀ j ≤ Q.scale-(H:ℤ), ∀ z, diameterField
      (q3PlanarMarks M j resetAllOrderTau (waveGateEta .allOrder)) ω z ≠ ∞)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc (protectedOldLabel Q.scale k) N, 0 ≤ weights n ∧ weights n ≤ 1) :
    ENNReal.ofReal (rootTraceObservable M Q (protectedOldLabel Q.scale k) N (Q.scale-1) weights ω/4) ≤
      assemblyTraceLayerMajorant M Q k H N weights ω := by
  classical
  let S := rootBadWhitneyCells M Q H resetAllOrderTau (waveGateEta .allOrder) ω
  let m := protectedOldLabel Q.scale k
  let a := sourceBandWeights m weights
  let σ := (Annealed.sigmaBar M (Q.scale-1):ℝ)
  let w := fun n : ℕ => rootAssemblyClock M.gamma H n
  have hmN : m ≤ N := by dsimp only [m,protectedOldLabel]; omega
  obtain ⟨C,hCi,hCb,hCa,hglobal⟩ := assembly_actual_full_trace_le_hybrid
    M Q H k hH ω hgood m N (Q.scale-1) hmN weights
  let v := fun i : HybridCell Q H S =>
    (volume (hybridDomain i:Set (Vec 2))).toReal/(volume (cubeSet Q)).toReal
  let E := fun (i : HybridCell Q H S) (j : Fin 2 × Bool) =>
    hybridFullTraceCellLoadEnergy σ (coarseBlockMatrix (hybridDomain i:Set (Vec 2))
      (attenuatedCoefficient M m N weights ω)) (C i) j
  let R := fun P : TriadicCube 2 => assemblyPhysicalShearMatrix M (P.scale+40) P.scale N
    (((P.index 0:ℝ)-1/2)*(3:ℝ)^P.scale) (((P.index 1:ℝ)-1/2)*(3:ℝ)^P.scale) a ω
  let t := fun P : TriadicCube 2 => Matrix.trace ((R P).transpose*
    clippedCellMatrix M (P.scale+40) P resetAllOrderTau ω*R P)/4
  let FI := fun i : HybridIdentityCell Q H S => w i.val.1*
    (volume (cubeSet i.val.2.val)).toReal/(volume (cubeSet Q)).toReal*t i.val.2.val
  let FA := fun i : HybridActiveCell Q H S => w i.1.val.1*
    (volume (hybridDomain (.inr i):Set (Vec 2))).toReal/(volume (cubeSet Q)).toReal*
      (‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (C (.inr i))‖^2*
        assemblyActiveParentMeanPayment M Q k H S N weights ω i)
  let K := 4*rootAssemblySensitivity*(1+2*Real.sqrt 3*resetAllOrderTau)
  have hv (i : HybridCell Q H S) : 0 ≤ v i := div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hE (i : HybridCell Q H S) (j : Fin 2 × Bool) : 0 ≤ E i j :=
    assembly_hybrid_trace_cell_load_nonneg M Q k H hH ω N (Q.scale-1) hmN weights S C i j
  have hnormal := assembly_four_load_normalization v E hv hE
  have hroot : ENNReal.ofReal (rootTraceObservable M Q m N (Q.scale-1) weights ω/4) ≤
      ∑' i : HybridCell Q H S, ENNReal.ofReal (v i*(∑ j : Fin 2 × Bool, E i j)/4) :=
    hglobal.trans_eq hnormal
  let B : HybridCell Q H S → ℝ≥0∞ := Sum.elim
    (fun i => ENNReal.ofReal rootAssemblySensitivity*ENNReal.ofReal (FI i))
    (fun i => ENNReal.ofReal K*ENNReal.ofReal (FA i))
  have hcell (i : HybridCell Q H S) : ENNReal.ofReal (v i*(∑ j : Fin 2 × Bool, E i j)/4) ≤ B i := by
    cases i with
    | inl i =>
      have hP : i.val.2.val ∈ whitneyRootLayer Q H i.val.1 := i.val.2.property
      have hparent := hybrid_identity_parent_good M Q H resetAllOrderTau (waveGateEta .allOrder) ω i
      have hlocal := assembly_good_layer_cell_trace_root_frame M Q k H i.val.1 hH hP
        N hN weights hw ω hparent
      have hvol : 0 ≤ (volume (cubeSet i.val.2.val)).toReal/(volume (cubeSet Q)).toReal :=
        div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      have hh := mul_le_mul_of_nonneg_left hlocal hvol
      have heVol : volume (hybridDomain (.inl i):Set (Vec 2))=volume (cubeSet i.val.2.val) :=
        (measure_congr (cubeSet_ae_eq_openCubeSet i.val.2.val)).symm
      change _ ≤ ENNReal.ofReal rootAssemblySensitivity*ENNReal.ofReal (FI i)
      rw [← ENNReal.ofReal_mul root_assembly_sensitivity_pos.le]
      apply ENNReal.ofReal_le_ofReal
      dsimp only [E]
      rw [hCi i,assembly_identity_load_sum σ (Annealed.sigmaBar_characterization M _).1]
      dsimp only [rootTraceObservable] at hh
      rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube] at hh
      dsimp only [v,FI,t,R,w,a,m,σ]
      rw [heVol]
      simpa only [hybridDomain,Book.Ch02.cubeDomain_coe,mul_assoc,mul_left_comm,mul_comm,div_eq_mul_inv] using hh
    | inr i =>
      simpa only [B,Sum.elim_inr,FA,K,w,v,E,σ,m,S,mul_assoc,div_eq_mul_inv] using
        assembly_active_cell_trace_payment M Q k H hH ω N hmN weights hw C hCb i
  have hsum := hroot.trans (ENNReal.tsum_le_tsum hcell)
  have hsum' : ENNReal.ofReal (rootTraceObservable M Q m N (Q.scale-1) weights ω/4) ≤
      ENNReal.ofReal rootAssemblySensitivity*(∑' i : HybridIdentityCell Q H S, ENNReal.ofReal (FI i))+
        ENNReal.ofReal K*(∑' i : HybridActiveCell Q H S, ENNReal.ofReal (FA i)) := by
    apply hsum.trans_eq
    change (∑' i : HybridIdentityCell Q H S ⊕ HybridActiveCell Q H S, B i)=_
    rw [ENNReal.summable.tsum_sum ENNReal.summable]
    simp only [Sum.elim_inl,Sum.elim_inr,ENNReal.tsum_mul_left]
  have hi := assembly_identity_trace_sum_le_layers M Q H S N a ω w
    (fun n => (root_assembly_clock_pos M.gamma H n).le)
  have ha := assembly_active_parent_mean_charge M Q k H hH ω hgood hfinite N weights hw C hCb hCa w
    (fun n => (root_assembly_clock_pos M.gamma H n).le)
  exact hsum'.trans (add_le_add (mul_le_mul_of_nonneg_left hi bot_le)
    (mul_le_mul_of_nonneg_left ha bot_le))

/-- Actual-law positive full-trace assembly: all successful-height and
finite-geometry inputs are derived from the source protected native past. -/
theorem assembly_q3_positive_trace_assembly (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p)
    (hpast : ∀ n : ℤ, n ≤ Q.scale-342-12*orderBand p → nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc (protectedOldLabel Q.scale (orderBand p)) N,
      0 ≤ weights n ∧ weights n ≤ 1) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ENNReal.ofReal (rootTraceObservable M Q (protectedOldLabel Q.scale (orderBand p))
        N (Q.scale-1) weights ω/4) ≤
          assemblyTraceLayerMajorant M Q (orderBand p)
            (resetQ3StoppedHeight M Q (orderBand p) ω) N weights ω := by
  let H0 := heightEntrance (orderBand p)+5
  have hH0 : 333 ≤ H0 := by unfold H0 heightEntrance; omega
  have hτ : 0 < resetAllOrderTau := by
    norm_num [resetAllOrderTau, Numerics.Wave.allOrderTau]
  have hq0 : 0 ≤ (allOrderDensity:ℝ) :=
    ((Real.exp_pos _).trans all_order_density_floor).le
  have hprotected : ∀ n ≤ Q.scale-(H0:ℤ)+40, nativeInductionState M h n := by
    intro n hn
    apply hpast n
    unfold H0 heightEntrance at hn
    omega
  have hgeometry := reset_q3_planar_geometry M h hM hγ Q p hp hpast
  have hgood := q3_stopped_height_ae_good M h hM hγ Q H0 hH0
    resetAllOrderTau hτ .allOrder (allOrderDensity:ℝ) hq0
    all_order_density_small all_order_density_covers_raw hprotected
  have hfin := q3_past_diameter_ae_ne_top M h hM hγ (Q.scale-(H0:ℤ))
    resetAllOrderTau hτ .allOrder (allOrderDensity:ℝ) hq0
    all_order_density_small all_order_density_covers_raw
    (fun n hn => hprotected n (by omega))
  filter_upwards [hgood,hfin] with ω hωg hωf
  let H := resetQ3StoppedHeight M Q (orderBand p) ω
  have hHH0 : H0 ≤ H := hgeometry.2.1 ω
  have hH : heightEntrance (orderBand p) ≤ H := by
    dsimp only [H0] at hHH0
    omega
  have hsuccess : ∀ j, H ≤ j → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-j) resetAllOrderTau (waveGateEta .allOrder))
      j (rootBlockStart Q j) := hωg
  have hfinite : ∀ j ≤ Q.scale-(H:ℤ), ∀ z, diameterField
      (q3PlanarMarks M j resetAllOrderTau (waveGateEta .allOrder)) ω z ≠ ∞ := by
    intro j hj z
    exact hωf j (by omega) z
  exact assembly_actual_trace_le_layer_majorant M Q (orderBand p) H hH ω
    hsuccess hfinite N hN weights hw

end
end ASDExplicitGamma.Inverse
