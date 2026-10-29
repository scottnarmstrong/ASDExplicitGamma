module

public import ASDExplicitGamma.Inverse.AssemblyWaveReconstruction
public import ASDExplicitGamma.Inverse.PhysicalGaussianWholeRoot
public import ASDExplicitGamma.Triadic.PoincareCell

/-! The sharp deterministic-height wave payment from the all-order whole-root estimate. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- Padding the terminal label by a zero attenuation leaves the physical
missing wave unchanged. This is the endpoint `N=n-1` convention. -/
theorem physical_missing_wave_pad_zero_terminal
    (M : ABKModel 2) (j n : ℤ) (hjn : j ≤ n-1) (a c : ℝ)
    (weights : ℤ → ℝ) :
    physicalMissingWave M j n (n-1) a c weights =
      physicalMissingWave M j n n a c (fun k => if k=n then 0 else weights k) := by
  let wpad : ℤ → ℝ := fun k => if k=n then 0 else weights k
  let K := closedRectangle a (a+(3:ℝ)^n) c (c+(3:ℝ)^n)
  have hinterval : insert n (Finset.Ioc j (n-1)) = Finset.Ioc j n := by
    simpa using (Finset.insert_Ioc_right_eq_Ioc_add_one (a := j) (b := n-1) hjn)
  have hnot : n ∉ Finset.Ioc j (n-1) := by
    simp only [Finset.mem_Ioc]
    omega
  have hsum (ω : Cutoff.CutoffSample 2) (x : K) :
      (∑ k ∈ Finset.Ioc j n, wpad k * (shellFieldScalarRestriction K (ω.1 k)) x) =
        ∑ k ∈ Finset.Ioc j (n-1), weights k * (shellFieldScalarRestriction K (ω.1 k)) x := by
    rw [← hinterval, Finset.sum_insert hnot]
    simp [wpad]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≠ n := by
      intro heq
      subst k
      simp only [Finset.mem_Ioc] at hk
      omega
    simp [hkn]
  have hband (ω : Cutoff.CutoffSample 2) :
      wholeRootModelBand (a := a) (b := a+(3:ℝ)^n) (c := c) (d := c+(3:ℝ)^n)
          j n wpad ω =
        wholeRootModelBand (a := a) (b := a+(3:ℝ)^n) (c := c) (d := c+(3:ℝ)^n)
          j (n-1) weights ω := by
    ext x
    simp only [wholeRootModelBand, modelWeightedBand, wholeRootWeights,
      ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
    rw [wholeRootShellLabel_sum_Ioc j n
          (fun k => wpad k * (shellFieldScalarRestriction K (ω.1 k)) x),
        wholeRootShellLabel_sum_Ioc j (n-1)
          (fun k => weights k * (shellFieldScalarRestriction K (ω.1 k)) x)]
    exact hsum ω x
  unfold physicalMissingWave
  funext ω
  rw [hband]

/-- The whole-root estimate includes the `D=0` endpoint: append the zero
terminal shell, and retain the source's one-unit allowances in both costs. -/
theorem physical_whole_root_wave_Lp_allow_zero_depth
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (j n N : ℤ) (hjn : j ≤ n-1) (hnN : n-1 ≤ N)
    (hstate : nativeInductionState M h j) (a c : ℝ) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc j N, 0 ≤ weights k ∧ weights k ≤ 1)
    (q : ℝ) (hq : 2 ≤ q) :
    eLpNorm (physicalMissingWave M j n N a c weights) (ENNReal.ofReal q)
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (160*M.gamma*((n-j:ℝ)+q*((N-n:ℝ)+2))*
        (3:ℝ)^(2*M.gamma*((N-j:ℝ)+1))) := by
  by_cases hnN' : n ≤ N
  · have hbase := physical_whole_root_wave_Lp M h hM j n N
      (by omega) hnN' hstate a c weights hw q hq
    have hcoeff : (n-j:ℝ)+q*((N-n:ℝ)+1) ≤
        (n-j:ℝ)+q*((N-n:ℝ)+2) := by nlinarith only [hq]
    have hexp : 2*M.gamma*(N-j:ℝ) ≤ 2*M.gamma*((N-j:ℝ)+1) := by
      have hγ : 0 < M.gamma := M.shellPrefix.gamma_pos
      nlinarith only [hγ]
    have hpow := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ)≤3) hexp
    have hγ0 : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
    have hnj0 : (0:ℝ) ≤ (n-j:ℝ) := by
      exact_mod_cast (show 0 ≤ n-j by omega)
    have hNn0 : (0:ℝ) ≤ (N-n:ℝ) := by
      exact_mod_cast (show 0 ≤ N-n by omega)
    have hq0 : 0 ≤ q := by linarith only [hq]
    have hB0 : 0 ≤ (n-j:ℝ)+q*((N-n:ℝ)+2) :=
      add_nonneg hnj0 (mul_nonneg hq0 (by linarith only [hNn0]))
    have hfac0 : 0 ≤ 160*M.gamma*((n-j:ℝ)+q*((N-n:ℝ)+2)) := by positivity
    have hlarge :
        160*M.gamma*((n-j:ℝ)+q*((N-n:ℝ)+1))*(3:ℝ)^(2*M.gamma*(N-j:ℝ)) ≤
          160*M.gamma*((n-j:ℝ)+q*((N-n:ℝ)+2))*
            (3:ℝ)^(2*M.gamma*((N-j:ℝ)+1)) := by
      calc
        _ ≤ 160*M.gamma*((n-j:ℝ)+q*((N-n:ℝ)+2))*(3:ℝ)^(2*M.gamma*(N-j:ℝ)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcoeff (by positivity)) (by positivity)
        _ ≤ _ := by
          exact mul_le_mul_of_nonneg_left hpow hfac0
    exact hbase.trans (ENNReal.ofReal_le_ofReal hlarge)
  · have hN : N=n-1 := by omega
    subst N
    let wpad : ℤ → ℝ := fun k => if k=n then 0 else weights k
    have hwpad : ∀ k ∈ Finset.Ioc j n, 0 ≤ wpad k ∧ wpad k ≤ 1 := by
      intro k hk
      by_cases hkn : k=n
      · subst k
        simp [wpad]
      · have hkold : k ∈ Finset.Ioc j (n-1) := by
          simp only [Finset.mem_Ioc] at hk ⊢
          exact ⟨hk.1, by omega⟩
        have h := hw k hkold
        simp [wpad,hkn,h]
    rw [physical_missing_wave_pad_zero_terminal M j n (by omega) a c weights]
    have hbase := physical_whole_root_wave_Lp M h hM j n n
      (by omega) le_rfl hstate a c wpad hwpad q hq
    convert hbase using 1
    push_cast
    ring_nf

/-- The actual clocked whole-root wave at a deterministic full stopping
height. This carrier is used to select the height only after applying the
all-order whole-root Gaussian estimate. -/
def assemblyTraceWaveAtHeight (M : ABKModel 2) (Q : TriadicCube 2)
    (k : ℕ) (H : ℕ) (N : ℤ) (weights : ℤ → ℝ) (i : ℕ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  rootAssemblyClock M.gamma H (i+1)*Real.sqrt (bankLayerWeight i)*
    physicalMissingWave M (layerOldCutoff Q.scale H (i+1)) Q.scale N
      (cubeCorner Q 0) (cubeCorner Q 1)
      (sourceBandWeights (protectedOldLabel Q.scale k) weights) ω

/-- At a fixed stopped height, the root wave costs its actual old-to-root
 gap plus the order times the root-to-terminal gap. The zero-depth endpoint is
 included with the source's one-unit allowance. -/
theorem assembly_trace_wave_at_height_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (Q : TriadicCube 2) (k H : ℕ)
    (hH : heightEntrance k+5 ≤ H)
    (hpast : ∀ n : ℤ, n ≤ Q.scale-342-12*k → nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc (protectedOldLabel Q.scale k) N,
      0 ≤ weights n ∧ weights n ≤ 1)
    (i : ℕ) (q : ℝ) (hq : 2 ≤ q) :
    eLpNorm (assemblyTraceWaveAtHeight M Q k H N weights i)
      (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (160*M.gamma*Real.sqrt (bankLayerWeight i)*
        ((localizationResetAbscissa (heightEntrance k+5-38)
            (H-(heightEntrance k+5)) i:ℝ)+1+
          q*(((N-Q.scale+1:ℤ):ℝ)+1))*
        (3:ℝ)^(2*M.gamma*((N-Q.scale+1:ℤ):ℝ)+
          4*M.gamma*(localizationResetAbscissa (heightEntrance k+5-38)
            (H-(heightEntrance k+5)) i:ℝ)+2*M.gamma)) := by
  let H0 := heightEntrance k+5
  let x := localizationResetAbscissa (H0-38) (H-H0) i
  let D : ℝ := ((N-Q.scale+1:ℤ):ℝ)
  let j := layerOldCutoff Q.scale H (i+1)
  let C := rootAssemblyClock M.gamma H (i+1)*Real.sqrt (bankLayerWeight i)
  let w := sourceBandWeights (protectedOldLabel Q.scale k) weights
  have hH0 : 377 ≤ H0 := by unfold H0 heightEntrance; omega
  have hHnat : H0 ≤ H := by change heightEntrance k+5≤H; exact hH
  have hHent : heightEntrance k ≤ H := by omega
  have hjprotect : j ≤ protectedOldLabel Q.scale k := by
    dsimp only [j]
    exact layer_old_cutoff_le_protected Q.scale k H (i+1) hHent (by omega)
  have hjstate : nativeInductionState M h j := by
    apply hpast j
    change j ≤ Q.scale-342-12*k at hjprotect
    exact hjprotect
  have hjroot : j ≤ Q.scale := by
    dsimp only [j]
    unfold layerOldCutoff layerDepth layerProfile
    omega
  have hjrootPrev : j ≤ Q.scale-1 := by
    dsimp only [j]
    unfold layerOldCutoff layerDepth layerProfile
    omega
  have hjN : j ≤ N := hjrootPrev.trans hN
  have hwj : ∀ n ∈ Finset.Ioc j N, 0 ≤ w n ∧ w n ≤ 1 := by
    intro n hn
    dsimp only [w]
    exact source_band_weights_bounds j (protectedOldLabel Q.scale k) N weights
      hw n hn
  have hxrootInt : Q.scale-j=(x:ℤ)+1 := by
    dsimp only [j,x,H0]
    unfold layerOldCutoff layerDepth layerProfile
      localizationResetAbscissa localizationProfileDepth
    omega
  have hxroot : (Q.scale:ℝ)-(j:ℝ)=x+1 := by exact_mod_cast hxrootInt
  have hD : D=(N:ℝ)-(Q.scale:ℝ)+1 := by
    dsimp only [D]
    push_cast
    ring
  have hDInt : ((N-Q.scale+1:ℤ):ℝ)=D := by rfl
  have hjreset : j=physicalResetOldLabel Q H0 (H-H0,i) := by
    dsimp only [j]
    have heq := assembly_old_label_eq_reset Q H0 hH0 (H-H0,i)
    have hsum : H0+(H-H0)=H := by omega
    rw [hsum] at heq
    exact heq
  have hgap : (N:ℝ)-(j:ℝ)=D+x := by
    rw [hjreset]
    have heq := physical_reset_gap_eq Q N H0 (H-H0,i)
    rw [hD, show (x:ℝ)=
      (localizationResetAbscissa (H0-38) (H-H0,i).1 (H-H0,i).2:ℝ) by rfl]
    exact heq
  have hD2 : (N:ℝ)-(Q.scale:ℝ)+2=D+1 := by rw [hD]; ring
  have hclockNat : layerRelativeOffset H (i+1)=x := by
    dsimp only [x,H0]
    unfold layerRelativeOffset layerProfile localizationResetAbscissa
      localizationProfileDepth
    omega
  have hclock : rootAssemblyClock M.gamma H (i+1)=(3:ℝ)^(2*M.gamma*x) := by
    unfold rootAssemblyClock
    rw [hclockNat]
  have hbase := physical_whole_root_wave_Lp_allow_zero_depth M h hM j Q.scale N
    hjrootPrev hN hjstate (cubeCorner Q 0) (cubeCorner Q 1) w hwj q hq
  rw [hD2,hgap] at hbase
  have hscale : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (by unfold rootAssemblyClock; positivity)
      (Real.sqrt_nonneg _)
  have hpow : (3:ℝ)^(2*M.gamma*(x:ℝ))*(3:ℝ)^(2*M.gamma*(D+x+1))=
      (3:ℝ)^(2*M.gamma*D+4*M.gamma*x+2*M.gamma) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<3)]
    congr 1
    ring
  have hnumeric :
      C*(160*M.gamma*((Q.scale-j:ℝ)+q*(D+1))*
          (3:ℝ)^(2*M.gamma*(D+x+1))) ≤
        160*M.gamma*Real.sqrt (bankLayerWeight i)*
          ((localizationResetAbscissa (heightEntrance k+5-38)
              (H-(heightEntrance k+5)) i:ℝ)+1+
            q*(((N-Q.scale+1:ℤ):ℝ)+1))*
          (3:ℝ)^(2*M.gamma*((N-Q.scale+1:ℤ):ℝ)+
            4*M.gamma*(localizationResetAbscissa (heightEntrance k+5-38)
              (H-(heightEntrance k+5)) i:ℝ)+2*M.gamma) := by
    apply le_of_eq
    calc
      C*(160*M.gamma*((Q.scale-j:ℝ)+q*(D+1))*
          (3:ℝ)^(2*M.gamma*(D+x+1))) =
        160*M.gamma*Real.sqrt (bankLayerWeight i)*(x+1+q*(D+1))*
          ((3:ℝ)^(2*M.gamma*(x:ℝ))*(3:ℝ)^(2*M.gamma*(D+x+1))) := by
        dsimp only [C]
        rw [hclock,hxroot]
        ring
      _ = _ := by rw [hDInt,hpow]
  have heq : assemblyTraceWaveAtHeight M Q k H N weights i=
      C • physicalMissingWave M j Q.scale N (cubeCorner Q 0) (cubeCorner Q 1) w := by
    funext ω
    rfl
  rw [heq,eLpNorm_const_smul,Real.enorm_eq_ofReal hscale]
  calc
    ENNReal.ofReal C * eLpNorm
        (physicalMissingWave M j Q.scale N (cubeCorner Q 0) (cubeCorner Q 1) w)
        (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure
        ≤ ENNReal.ofReal C * ENNReal.ofReal
          (160*M.gamma*((Q.scale-j:ℝ)+q*(D+1))*
            (3:ℝ)^(2*M.gamma*(D+x+1))) :=
      mul_le_mul_of_nonneg_left hbase (zero_le : (0:ℝ≥0∞)≤ENNReal.ofReal C)
    _ = ENNReal.ofReal (C*(160*M.gamma*((Q.scale-j:ℝ)+q*(D+1))*
          (3:ℝ)^(2*M.gamma*(D+x+1)))) := by rw [← ENNReal.ofReal_mul hscale]
    _ ≤ ENNReal.ofReal (160*M.gamma*Real.sqrt (bankLayerWeight i)*
        ((localizationResetAbscissa (heightEntrance k+5-38)
            (H-(heightEntrance k+5)) i:ℝ)+1+
          q*(((N-Q.scale+1:ℤ):ℝ)+1))*
        (3:ℝ)^(2*M.gamma*((N-Q.scale+1:ℤ):ℝ)+
          4*M.gamma*(localizationResetAbscissa (heightEntrance k+5-38)
            (H-(heightEntrance k+5)) i:ℝ)+2*M.gamma)) := by
      exact ENNReal.ofReal_le_ofReal hnumeric

end
end ASDExplicitGamma.Inverse
