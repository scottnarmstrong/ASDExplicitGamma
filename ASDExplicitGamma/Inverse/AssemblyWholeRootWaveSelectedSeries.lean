module

public import ASDExplicitGamma.Inverse.AssemblyWholeRootWaveSelected
public import ASDExplicitGamma.Inverse.AssemblyWaveSeries
public import ASDExplicitGamma.Inverse.StoppedSelectedFamilyIdentity
public import ASDExplicitGamma.Triadic.PoincareCell

/-! Sharp all-order whole-root wave moments at the actual selected height. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- A selected layer pays twelve deterministic candidates and the exact
first-height and constant moments of the complete tail. -/
theorem assembly_trace_wave_selected_layer_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p)
    (hpast : ∀ n : ℤ,
      n ≤ Q.scale-342-12*orderBand p → nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc
      (protectedOldLabel Q.scale (orderBand p)) N,
      0 ≤ weights n ∧ weights n ≤ 1) (i : ℕ) :
    let H0 := heightEntrance (orderBand p)
    eLpNorm (assemblyTraceWaveLayer M Q (orderBand p) p N weights i)
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (assemblyWholeRootWaveSelectedLayerBudget M.gamma p
        ((N-Q.scale+1:ℤ):ℝ) H0 i) := by
  let k := orderBand p
  let H0 := heightEntrance k
  let D : ℝ := ((N-Q.scale+1:ℤ):ℝ)
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let H := q3SelectedHeight M Q k
  let f := fun n : ℕ => assemblyTraceWaveAtHeight M Q k (n+5) N weights i
  let fTail := fun n : ℕ => f (H0+12+n)
  have hH0 : 333 ≤ H0 := by dsimp only [H0,k]; unfold heightEntrance; omega
  have hD : 0 ≤ D := by dsimp only [D]; exact_mod_cast (by omega : 0 ≤ N-Q.scale+1)
  have hge (ω : Cutoff.CutoffSample 2) : H0 ≤ H ω := by
    exact q3_selected_height_ge M Q k ω
  have hH : Measurable H := selected_height_measurable M Q k
  have hf (n : ℕ) : Measurable (f n) := by
    change Measurable (fun ω =>
      rootAssemblyClock M.gamma (n+5) (i+1)*Real.sqrt (bankLayerWeight i)*
        physicalMissingWave M (layerOldCutoff Q.scale (n+5) (i+1)) Q.scale N
          (cubeCorner Q 0) (cubeCorner Q 1)
          (sourceBandWeights (protectedOldLabel Q.scale k) weights) ω)
    have hm := physical_missing_wave_measurable M
      (layerOldCutoff Q.scale (n+5) (i+1)) Q.scale N
      (cubeCorner Q 0) (cubeCorner Q 1)
      (sourceBandWeights (protectedOldLabel Q.scale k) weights)
    have hm' : Measurable (fun ω => Real.sqrt (bankLayerWeight i)*
        physicalMissingWave M (layerOldCutoff Q.scale (n+5) (i+1)) Q.scale N
          (cubeCorner Q 0) (cubeCorner Q 1)
          (sourceBandWeights (protectedOldLabel Q.scale k) weights) ω) :=
      measurable_const.mul hm
    have hm'' : Measurable (fun ω => rootAssemblyClock M.gamma (n+5) (i+1)*
        (Real.sqrt (bankLayerWeight i)*
          physicalMissingWave M (layerOldCutoff Q.scale (n+5) (i+1)) Q.scale N
            (cubeCorner Q 0) (cubeCorner Q 1)
            (sourceBandWeights (protectedOldLabel Q.scale k) weights) ω)) :=
      measurable_const.mul hm'
    convert hm'' using 1
    funext ω
    ring
  have hfTail (n : ℕ) : Measurable (fTail n) := hf _
  have hprob (n : ℕ) : μ {ω | H ω=H0+12+n} ≤
      ENNReal.ofReal (selectedTailProbability H0 n) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    dsimp only [H0,k,H]
    exact ENNReal.ofReal_le_ofReal (selected_height_atom M h hM hγ Q p hp hpast n)
  have hγ0 : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hCand0 : 0 ≤ assemblyWholeRootWaveCandidateBound M.gamma p D H0 i := by
    have hz : 0 ≤ selectedFirstClock H0 := by
      unfold selectedFirstClock
      have hh : (333:ℝ) ≤ H0 := by exact_mod_cast hH0
      linarith
    unfold assemblyWholeRootWaveCandidateBound
    have hp0 : 0 ≤ p := by linarith only [hp]
    positivity
  have hA : 0 ≤ assemblyWholeRootWaveTailScale M.gamma D i := by
    unfold assemblyWholeRootWaveTailScale
    positivity
  have hTailFactor : 0 ≤ localizationProfileDepth (i+1)+6+2*p*(D+1) := by
    have hp0 : 0 ≤ p := by linarith only [hp]
    have hD1 : 0 ≤ D+1 := by linarith
    positivity
  have hB : 0 ≤ assemblyWholeRootWaveTailScale M.gamma D i*
      (localizationProfileDepth (i+1)+6+2*p*(D+1)) :=
    mul_nonneg hA hTailFactor
  have hfinite := selected_twelve_candidate_Lp μ H hH H0 f hf p
    (by linarith only [hp]) (ENNReal.ofReal
      (assemblyWholeRootWaveCandidateBound M.gamma p D H0 i)) (by
        intro t ht
        have ht' := (selected_candidate_mem H0 t).mp ht
        exact assembly_trace_wave_candidate_height_Lp M h hM Q k p hp hpast
          N hN weights hw i t ht'.1 ht'.2)
  have hroot : (12:ℝ≥0∞)^(1/p:ℝ) = ENNReal.ofReal ((12:ℝ)^(1/p:ℝ)) := by
    simpa only [ENNReal.ofReal_ofNat] using
      ENNReal.ofReal_rpow_of_pos (p := (1/p:ℝ)) (by norm_num : (0:ℝ)<12)
  have hfinite' : eLpNorm
      (selectedBoundedFamily H (selectedCandidateHeights H0) f)
      (ENNReal.ofReal p) μ ≤ ENNReal.ofReal
        ((12:ℝ)^(1/p:ℝ)*assemblyWholeRootWaveCandidateBound M.gamma p D H0 i) := by
    calc
      _ ≤ (12:ℝ≥0∞)^(1/p:ℝ)*ENNReal.ofReal
          (assemblyWholeRootWaveCandidateBound M.gamma p D H0 i) := hfinite
      _ = _ := by
        rw [hroot,← ENNReal.ofReal_mul (by positivity : 0 ≤ (12:ℝ)^(1/p:ℝ))]
  have htail := selected_tail_Lp_of_affine_moments μ H hH H0 hH0
    M.gamma p hp (assemblyWholeRootWaveTailScale M.gamma D i) _ hA hB fTail hfTail hprob
    (fun n => by
      have hAtom := assembly_trace_wave_tail_atom_Lp M h hM Q k p hp hpast
        N hN weights hw i n
      have hFn : fTail n = assemblyTraceWaveAtHeight M Q k (H0+17+n)
          N weights i := by
        dsimp only [fTail,f]
        congr 1
        omega
      rw [hFn]
      change eLpNorm (assemblyTraceWaveAtHeight M Q k (H0+17+n)
        N weights i) (ENNReal.ofReal (2*p)) μ ≤ _
      change eLpNorm (assemblyTraceWaveAtHeight M Q k (H0+17+n)
        N weights i) (ENNReal.ofReal (2*p)) μ ≤ _ at hAtom
      exact hAtom)
  have hsplit := selected_real_family_eq H H0 hge f
  have hsum : eLpNorm
      (selectedBoundedFamily H (selectedCandidateHeights H0) f+
        (fun ω => ∑' n : ℕ,
          ({ω | H ω=H0+12+n} : Set (Cutoff.CutoffSample 2)).indicator
            (f (H0+12+n)) ω)) (ENNReal.ofReal p) μ ≤
      eLpNorm (selectedBoundedFamily H (selectedCandidateHeights H0) f)
        (ENNReal.ofReal p) μ+
      eLpNorm (fun ω => ∑' n : ℕ,
        ({ω | H ω=H0+12+n} : Set (Cutoff.CutoffSample 2)).indicator
          (f (H0+12+n)) ω) (ENNReal.ofReal p) μ :=
    eLpNorm_add_le (ENNReal.one_le_ofReal.mpr (by linarith only [hp]))
  have htail0 : 0 ≤ assemblyWholeRootWaveTailScale M.gamma D i*
      selectedWaveExactTail M.gamma p H0 (1:Fin 2)+
      (assemblyWholeRootWaveTailScale M.gamma D i*
        (localizationProfileDepth (i+1)+6+2*p*(D+1)))*
          selectedWaveExactTail M.gamma p H0 (0:Fin 2) := by
    have ht0 : 0 ≤ selectedWaveExactTail M.gamma p H0 (0:Fin 2) := by
      unfold selectedWaveExactTail
      apply tsum_nonneg
      intro n
      simp only [Fin.val_zero,pow_zero,one_mul]
      unfold selectedTailProbability
      positivity
    have ht1 : 0 ≤ selectedWaveExactTail M.gamma p H0 (1:Fin 2) := by
      unfold selectedWaveExactTail
      apply tsum_nonneg
      intro n
      simp only [Fin.val_one,pow_one]
      have hz : 0 ≤ selectedFirstClock H0+(n:ℝ) := by
        unfold selectedFirstClock
        have hh : (333:ℝ) ≤ (H0:ℝ) := by exact_mod_cast hH0
        have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        linarith
      unfold selectedTailProbability
      positivity
    positivity
  have hfiniteBudget : 0 ≤ (12:ℝ)^(1/p:ℝ)*
      assemblyWholeRootWaveCandidateBound M.gamma p D H0 i := by positivity
  have hbudget := add_le_add hfinite' htail.2
  have hfull (ω : Cutoff.CutoffSample 2) :
      resetQ3StoppedHeight M Q k ω=H ω+5 := by
    have hh := hge ω
    unfold H q3SelectedHeight at hh ⊢
    omega
  have heq : assemblyTraceWaveLayer M Q k p N weights i =
      fun ω => f (H ω) ω := by
    funext ω
    dsimp only [assemblyTraceWaveLayer,f,assemblyTraceWaveAtHeight]
    rw [hfull ω]
  change eLpNorm (assemblyTraceWaveLayer M Q k p N weights i)
      (ENNReal.ofReal p) μ ≤ _
  rw [heq]
  rw [hsplit]
  exact hsum.trans (hbudget.trans_eq (by
    rw [← ENNReal.ofReal_add hfiniteBudget htail0]
    congr 1
    dsimp only [assemblyWholeRootWaveSelectedLayerBudget]
    ring))

end
end ASDExplicitGamma.Inverse
