module

public import ASDExplicitGamma.Inverse.AssemblyTraceLp
public import ASDExplicitGamma.Inverse.AssemblyTraceMeasurable
public import ASDExplicitGamma.Inverse.AssemblyErrorMoments
public import ASDExplicitGamma.Inverse.AssemblyWholeRootWaveSelectedSum

/-! The actual trace has its complete stopped all-order Lp budget. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- The positive trace budget with the sharp direct selected-height wave
series in its wave slot. -/
def assemblyTraceSeriesSelectedBudget (γ p D : ℝ) (k : ℕ) : ℝ :=
  let H0 := heightEntrance k+5
  assemblyTraceBaseline*rootLayerSum (2*γ)*
      assemblySelectedClockBudget γ p (heightEntrance k)+
    assemblyTraceWaveCoefficient*
      assemblyWholeRootWaveSelectedSeriesBudget γ p D (heightEntrance k)+
    assemblyTraceMatrixBudget γ p D H0+
    assemblyTraceDensityFactor*assemblyDensityBudget γ k H0+
    assemblyTraceCorrelationCoefficient*γ*(3:ℝ)^(2*γ*D)*
      (40*(2*p+2)*bandDensitySum4 k γ D (H0-38) 0+
        40*(2*p+2)*bandDensitySum4 k γ 0 (H0-38) 1)

/-- The complete actual trace in its source root frame is bounded in every
real order p≥2 by the summed positive trace budget. The wave terms use the
actual full stopped height, and matrix, density, and both common-noise
correlation terms are summed over all deterministic heights before selection. -/
theorem assembly_root_trace_Lp (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p)
    (hpast : ∀ n : ℤ,
      n ≤ Q.scale-342-12*orderBand p → nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc
      (protectedOldLabel Q.scale (orderBand p)) N,
      0 ≤ weights n ∧ weights n ≤ 1) :
    eLpNorm (rootTraceObservable M Q
      (protectedOldLabel Q.scale (orderBand p)) N (Q.scale-1) weights)
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (4*assemblyTraceSeriesSelectedBudget M.gamma p
          ((N-Q.scale+1:ℤ):ℝ) (orderBand p)) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let k := orderBand p
  let H0 := heightEntrance k+5
  let m := protectedOldLabel Q.scale k
  let H := fun ω => resetQ3StoppedHeight M Q k ω
  let D : ℝ := ((N-Q.scale+1:ℤ):ℝ)
  let a : ℝ := cubeCorner Q 0
  let c : ℝ := cubeCorner Q 1
  let w : ℤ → ℝ := sourceBandWeights m weights
  let wts : (ℕ×ℕ) → ℤ → ℝ := fun _ => w
  let Fw : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    ∑' i : ℕ, |assemblyTraceWaveLayer M Q k p N weights i ω|
  let Fm : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    ∑' hk : ℕ×ℕ, assemblyTraceMatrixTerm M Q H0 N w hk ω
  let Fd : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    ∑' hk : ℕ×ℕ, assemblyDensityTerm M Q H0 hk ω
  let Fc0 : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    ∑' hk : ℕ×ℕ,
      assemblyCorrelatedDensityAbsTerm M Q N p D a c wts (0:Fin 2) hk ω
  let Fc1 : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    ∑' hk : ℕ×ℕ,
      assemblyCorrelatedDensityAbsTerm M Q N p 0 a c wts (1:Fin 2) hk ω
  let B0 := assemblyTraceBaseline*rootLayerSum (2*M.gamma)
  let Cw := assemblyTraceWaveCoefficient
  let Cd := assemblyTraceDensityFactor
  let Cc := assemblyTraceCorrelationCoefficient*M.gamma*(3:ℝ)^(2*M.gamma*D)
  let clk : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    (3:ℝ)^(2*M.gamma*((H ω:ℝ)-38))
  let Env : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    B0*clk ω+(Cw*Fw ω+(Fm ω+(Cd*Fd ω+Cc*(Fc0 ω+Fc1 ω))))
  have hp1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr (by linarith only [hp])
  have hH0 : 377 ≤ H0 := by dsimp only [H0,k]; unfold heightEntrance; omega
  have h38 : 38 ≤ H0 := by omega
  have hD : 0 ≤ D := by dsimp only [D]; exact_mod_cast (by omega : 0 ≤ N-Q.scale+1)
  have hγ0 : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hSens : 0 ≤ rootAssemblySensitivity := root_assembly_sensitivity_pos.le
  have hstop (ω : Cutoff.CutoffSample 2) : H0 ≤ H ω := by
    change heightEntrance k+5 ≤ resetQ3StoppedHeight M Q k ω
    have hh := q3_selected_height_ge M Q k ω
    unfold q3SelectedHeight at hh
    omega
  have hq0 : 0 ≤ (allOrderDensity:ℝ) := by norm_num [allOrderDensity]
  have hMoment2 := density_moment_budget_nonneg (allOrderDensity:ℝ) hq0 2 1324 (by norm_num)
  have hMoment4 := density_moment_budget_nonneg (allOrderDensity:ℝ) hq0 4 1324 (by norm_num)
  have hCharge : 0 ≤ planarGradientCharge 40+1 := by
    unfold planarGradientCharge
    positivity
  have hLayerSum : 0 ≤ rootLayerSum (2*M.gamma) := by
    unfold rootLayerSum
    apply tsum_nonneg
    intro i
    exact mul_nonneg (bankLayerWeight_nonneg i) (by positivity)
  have hBaseline : 0 ≤ assemblyTraceBaseline := by
    unfold assemblyTraceBaseline assemblyActiveConstant
    have hτ' : 0 ≤ resetAllOrderTau := by norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
    have hResponse : 0 ≤ rootResponseEnvelope (6*resetAllOrderTau) := by
      unfold rootResponseEnvelope
      positivity
    positivity
  have hB0 : 0 ≤ B0 := mul_nonneg hBaseline hLayerSum
  have hCw : 0 ≤ Cw := by
    dsimp only [Cw,assemblyTraceWaveCoefficient]
    have hτ' : 0 ≤ resetAllOrderTau := by norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
    positivity
  have hCd : 0 ≤ Cd := assembly_trace_density_factor_pos.le
  have hCorrCoeff : 0 ≤ assemblyTraceCorrelationCoefficient := by
    unfold assemblyTraceCorrelationCoefficient
    have hτ' : 0 ≤ resetAllOrderTau := by norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
    unfold planarGradientCharge
    positivity
  have hCc : 0 ≤ Cc := by
    dsimp only [Cc]
    exact mul_nonneg (mul_nonneg hCorrCoeff hγ0) (by positivity)
  have hTraceMatrixNonneg (hk : ℕ×ℕ) (ω : Cutoff.CutoffSample 2) :
      0 ≤ assemblyTraceMatrixTerm M Q H0 N w hk ω := by
    unfold assemblyTraceMatrixTerm assemblyTraceMatrixDeviation
    exact mul_nonneg (mul_nonneg hSens (root_assembly_clock_pos _ _ _).le)
      (norm_nonneg _)
  have hclockLp : eLpNorm clk (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (assemblySelectedClockBudget M.gamma p
        (heightEntrance k)) := by
    change eLpNorm (fun ω => (3:ℝ)^(2*M.gamma*
      ((resetQ3StoppedHeight M Q k ω:ℝ)-38))) (ENNReal.ofReal p) μ ≤ _
    exact assembly_q3_selected_clock_Lp M h hM hγ Q p hp hpast
  have hwave := assembly_trace_wave_selected_series_Lp M h hM hγ Q p hp hpast N hN weights hw
  have hmatrix := assembly_trace_matrix_series_Lp M h hM hγ Q p hp H0
    (by dsimp only [H0,k]; omega) hpast N hN weights hw
  have hdensity := assembly_density_series_Lp M h hM hγ Q p hp H0
    (by dsimp only [H0,k]; omega) hpast
  have hwreset (hk : ℕ×ℕ) : ∀ n ∈ Finset.Ioc
      (physicalResetOldLabel Q H0 hk) N, 0 ≤ wts hk n ∧ wts hk n ≤ 1 := by
    intro n hn
    have hOld : physicalResetOldLabel Q H0 hk ≤ m := by
      rw [← assembly_old_label_eq_reset Q H0 hH0 hk]
      exact layer_old_cutoff_le_protected Q.scale k (H0+hk.1) (hk.2+1)
        (by dsimp only [H0]; omega) (by omega)
    exact source_band_weights_bounds (physicalResetOldLabel Q H0 hk) m N weights hw n hn
  have hcorr0 := assembly_correlated_density_abs_series_Lp M h hM hγ Q p hp hpast
    N hN a c wts hwreset D hD (0:Fin 2)
  have hcorr1 := assembly_correlated_density_abs_series_Lp M h hM hγ Q p hp hpast
    N hN a c wts hwreset 0 (by norm_num) (1:Fin 2)
  have hFwnonneg (ω : Cutoff.CutoffSample 2) : 0 ≤ Fw ω :=
    tsum_nonneg fun i => abs_nonneg _
  have hFmnonneg (ω : Cutoff.CutoffSample 2) : 0 ≤ Fm ω :=
    tsum_nonneg fun hk => hTraceMatrixNonneg hk ω
  have hFdnonneg (ω : Cutoff.CutoffSample 2) : 0 ≤ Fd ω :=
    tsum_nonneg fun hk => assembly_density_term_nonneg M Q H0 hk ω
  have hFc0nonneg (ω : Cutoff.CutoffSample 2) : 0 ≤ Fc0 ω :=
    tsum_nonneg fun hk => abs_nonneg _
  have hFc1nonneg (ω : Cutoff.CutoffSample 2) : 0 ≤ Fc1 ω :=
    tsum_nonneg fun hk => abs_nonneg _
  have hEnvnonneg (ω : Cutoff.CutoffSample 2) : 0 ≤ Env ω := by
    exact add_nonneg (mul_nonneg hB0 (by positivity))
      (add_nonneg (mul_nonneg hCw (hFwnonneg ω))
        (add_nonneg (hFmnonneg ω)
          (add_nonneg (mul_nonneg hCd (hFdnonneg ω))
            (mul_nonneg hCc (add_nonneg (hFc0nonneg ω) (hFc1nonneg ω))))))
  have hbaseHasSum (Hn : ℕ) (hHn : 38 ≤ Hn) :
      HasSum (fun i : ℕ => (assemblyTraceBaseline*rootAssemblyClock M.gamma Hn (i+1))*
          bankLayerWeight i)
        (assemblyTraceBaseline*(3:ℝ)^(2*M.gamma*((Hn:ℝ)-38))*
          rootLayerSum (2*M.gamma)) := by
    have hs := (assembly_clocked_layer_weights_hasSum M.gamma hγ Hn hHn).mul_left
      assemblyTraceBaseline
    convert hs using 1 <;> ring_nf
  have hselectedSeries (ω : Cutoff.CutoffSample 2) :
      (∑' i : ℕ, ENNReal.ofReal
        (assemblyTraceScalarLayer M Q k H0 (H ω-H0,i) N weights ω)) ≤
      ENNReal.ofReal (B0*clk ω)+
        (ENNReal.ofReal Cw*(∑' i : ℕ, ENNReal.ofReal
          (|assemblyTraceWaveLayer M Q k p N weights i ω|))+
        ((∑' hk : ℕ×ℕ, ENNReal.ofReal (assemblyTraceMatrixTerm M Q H0 N w hk ω))+
        (ENNReal.ofReal Cd*(∑' hk : ℕ×ℕ,
          ENNReal.ofReal (assemblyDensityTerm M Q H0 hk ω))+
        ENNReal.ofReal Cc*((∑' hk : ℕ×ℕ, ENNReal.ofReal
          (assemblyCorrelatedDensityAbsTerm M Q N p D a c wts (0:Fin 2) hk ω))+
          (∑' hk : ℕ×ℕ, ENNReal.ofReal
          (assemblyCorrelatedDensityAbsTerm M Q N p 0 a c wts (1:Fin 2) hk ω)))))) := by
    let Hn := H ω
    have hHn : H0 ≤ Hn := hstop ω
    have hterm (i : ℕ) :
        ENNReal.ofReal (assemblyTraceScalarLayer M Q k H0 (Hn-H0,i) N weights ω) ≤
          ENNReal.ofReal (assemblyTraceBaseline*rootAssemblyClock M.gamma Hn (i+1)*bankLayerWeight i)+
          ENNReal.ofReal (Cw*|assemblyTraceWaveLayer M Q k p N weights i ω|)+
          ENNReal.ofReal (assemblyTraceMatrixTerm M Q H0 N w (Hn-H0,i) ω)+
          ENNReal.ofReal (Cd*assemblyDensityTerm M Q H0 (Hn-H0,i) ω)+
          ENNReal.ofReal (Cc*(assemblyCorrelatedDensityAbsTerm M Q N p D a c wts
            (0:Fin 2) (Hn-H0,i) ω+assemblyCorrelatedDensityAbsTerm M Q N p 0 a c wts
            (1:Fin 2) (Hn-H0,i) ω)) := by
      have hreal := assembly_selected_trace_scalar_layer_bound M Q p N hN weights hw ω i hHn
      have hB : 0 ≤ assemblyTraceBaseline*rootAssemblyClock M.gamma Hn (i+1)*bankLayerWeight i :=
        mul_nonneg
          (mul_nonneg hBaseline (root_assembly_clock_pos _ _ _).le)
          (bankLayerWeight_nonneg i)
      have hW : 0 ≤ Cw*|assemblyTraceWaveLayer M Q k p N weights i ω| :=
        mul_nonneg hCw (abs_nonneg _)
      have hM : 0 ≤ assemblyTraceMatrixTerm M Q H0 N w (Hn-H0,i) ω :=
        hTraceMatrixNonneg (Hn-H0,i) ω
      have hD' : 0 ≤ Cd*assemblyDensityTerm M Q H0 (Hn-H0,i) ω :=
        mul_nonneg hCd (assembly_density_term_nonneg M Q H0 (Hn-H0,i) ω)
      have hC' : 0 ≤ Cc*(assemblyCorrelatedDensityAbsTerm M Q N p D a c wts
          (0:Fin 2) (Hn-H0,i) ω+assemblyCorrelatedDensityAbsTerm M Q N p 0 a c wts
          (1:Fin 2) (Hn-H0,i) ω) :=
        mul_nonneg hCc (add_nonneg (abs_nonneg _) (abs_nonneg _))
      have hreal' :
          assemblyTraceScalarLayer M Q k H0 (Hn-H0,i) N weights ω ≤
            assemblyTraceBaseline*rootAssemblyClock M.gamma Hn (i+1)*bankLayerWeight i+
            Cw*|assemblyTraceWaveLayer M Q k p N weights i ω|+
            assemblyTraceMatrixTerm M Q H0 N w (Hn-H0,i) ω+
            Cd*assemblyDensityTerm M Q H0 (Hn-H0,i) ω+
            Cc*(assemblyCorrelatedDensityAbsTerm M Q N p D a c wts
              (0:Fin 2) (Hn-H0,i) ω+assemblyCorrelatedDensityAbsTerm M Q N p 0 a c wts
              (1:Fin 2) (Hn-H0,i) ω) := by
        simpa only [Cw,Cd,Cc,D,a,c,wts,assemblyTraceMatrixTerm,
          assemblyDensityTerm,assemblyCorrelatedDensityAbsTerm] using hreal
      have hsumENN : ENNReal.ofReal
          (assemblyTraceBaseline*rootAssemblyClock M.gamma Hn (i+1)*bankLayerWeight i+
            (Cw*|assemblyTraceWaveLayer M Q k p N weights i ω|+
              (assemblyTraceMatrixTerm M Q H0 N w (Hn-H0,i) ω+
                (Cd*assemblyDensityTerm M Q H0 (Hn-H0,i) ω+
                  Cc*(assemblyCorrelatedDensityAbsTerm M Q N p D a c wts
                    (0:Fin 2) (Hn-H0,i) ω+assemblyCorrelatedDensityAbsTerm M Q N p 0 a c wts
                    (1:Fin 2) (Hn-H0,i) ω))))) =
          ENNReal.ofReal (assemblyTraceBaseline*rootAssemblyClock M.gamma Hn (i+1)*bankLayerWeight i)+
            (ENNReal.ofReal (Cw*|assemblyTraceWaveLayer M Q k p N weights i ω|)+
              (ENNReal.ofReal (assemblyTraceMatrixTerm M Q H0 N w (Hn-H0,i) ω)+
                (ENNReal.ofReal (Cd*assemblyDensityTerm M Q H0 (Hn-H0,i) ω)+
                  ENNReal.ofReal (Cc*(assemblyCorrelatedDensityAbsTerm M Q N p D a c wts
                    (0:Fin 2) (Hn-H0,i) ω+assemblyCorrelatedDensityAbsTerm M Q N p 0 a c wts
                    (1:Fin 2) (Hn-H0,i) ω))))) := by
        rw [ENNReal.ofReal_add hB (add_nonneg hW (add_nonneg hM (add_nonneg hD' hC'))),
          ENNReal.ofReal_add hW (add_nonneg hM (add_nonneg hD' hC')),
          ENNReal.ofReal_add hM (add_nonneg hD' hC'),
          ENNReal.ofReal_add hD' hC']
      calc
        _ ≤ ENNReal.ofReal
            (assemblyTraceBaseline*rootAssemblyClock M.gamma Hn (i+1)*bankLayerWeight i+
              (Cw*|assemblyTraceWaveLayer M Q k p N weights i ω|+
                (assemblyTraceMatrixTerm M Q H0 N w (Hn-H0,i) ω+
                  (Cd*assemblyDensityTerm M Q H0 (Hn-H0,i) ω+
                    Cc*(assemblyCorrelatedDensityAbsTerm M Q N p D a c wts
                      (0:Fin 2) (Hn-H0,i) ω+assemblyCorrelatedDensityAbsTerm M Q N p 0 a c wts
                      (1:Fin 2) (Hn-H0,i) ω))))) :=
              ENNReal.ofReal_le_ofReal (by simpa only [add_assoc] using hreal')
        _ = _ := by simpa only [add_assoc] using hsumENN
    calc
      _ ≤ ∑' i : ℕ,
          (ENNReal.ofReal (assemblyTraceBaseline*rootAssemblyClock M.gamma Hn (i+1)*bankLayerWeight i)+
          ENNReal.ofReal (Cw*|assemblyTraceWaveLayer M Q k p N weights i ω|)+
          ENNReal.ofReal (assemblyTraceMatrixTerm M Q H0 N w (Hn-H0,i) ω)+
          ENNReal.ofReal (Cd*assemblyDensityTerm M Q H0 (Hn-H0,i) ω)+
          ENNReal.ofReal (Cc*(assemblyCorrelatedDensityAbsTerm M Q N p D a c wts
            (0:Fin 2) (Hn-H0,i) ω+assemblyCorrelatedDensityAbsTerm M Q N p 0 a c wts
            (1:Fin 2) (Hn-H0,i) ω))) := ENNReal.tsum_le_tsum hterm
      _ ≤ _ := by
        simp only [ENNReal.tsum_add, add_assoc]
        have hb := hbaseHasSum Hn (by omega)
        have hbENN : (∑' i : ℕ, ENNReal.ofReal
            (assemblyTraceBaseline*rootAssemblyClock M.gamma Hn (i+1)*bankLayerWeight i)) =
            ENNReal.ofReal (B0*(3:ℝ)^(2*M.gamma*((Hn:ℝ)-38))) := by
          calc
            _ = ENNReal.ofReal (assemblyTraceBaseline*(3:ℝ)^(2*M.gamma*((Hn:ℝ)-38))*
                rootLayerSum (2*M.gamma)) := by
              rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg
            (mul_nonneg hBaseline (root_assembly_clock_pos _ _ _).le)
            (bankLayerWeight_nonneg i))
                hb.summable, hb.tsum_eq]
            _ = _ := by congr 1; dsimp only [B0]; ring
        rw [hbENN]
        have hi : Function.Injective (fun i : ℕ => (Hn-H0,i)) := by
          intro i j he
          exact congrArg Prod.snd he
        have hmatSel := ENNReal.tsum_comp_le_tsum_of_injective hi
          (fun hk => ENNReal.ofReal (assemblyTraceMatrixTerm M Q H0 N w hk ω))
        have hdenSel := ENNReal.tsum_comp_le_tsum_of_injective hi
          (fun hk => ENNReal.ofReal (assemblyDensityTerm M Q H0 hk ω))
        have hcorr0Sel := ENNReal.tsum_comp_le_tsum_of_injective hi
          (fun hk => ENNReal.ofReal (assemblyCorrelatedDensityAbsTerm M Q N p D a c wts
            (0:Fin 2) hk ω))
        have hcorr1Sel := ENNReal.tsum_comp_le_tsum_of_injective hi
          (fun hk => ENNReal.ofReal (assemblyCorrelatedDensityAbsTerm M Q N p 0 a c wts
            (1:Fin 2) hk ω))
        have hWaveEq : (∑' i : ℕ, ENNReal.ofReal
            (Cw*|assemblyTraceWaveLayer M Q k p N weights i ω|)) =
            ENNReal.ofReal Cw*(∑' i : ℕ, ENNReal.ofReal
              (|assemblyTraceWaveLayer M Q k p N weights i ω|)) := by
          calc
            _ = ∑' i : ℕ, ENNReal.ofReal Cw*ENNReal.ofReal
                (|assemblyTraceWaveLayer M Q k p N weights i ω|) := by
              apply tsum_congr
              intro i
              exact ENNReal.ofReal_mul hCw
            _ = _ := ENNReal.tsum_mul_left
        have hMatSel : (∑' i : ℕ, ENNReal.ofReal
              (assemblyTraceMatrixTerm M Q H0 N w (Hn-H0,i) ω)) ≤
            ∑' hk : ℕ×ℕ, ENNReal.ofReal
              (assemblyTraceMatrixTerm M Q H0 N w hk ω) := hmatSel
        have hDenEq : (∑' i : ℕ, ENNReal.ofReal
            (Cd*assemblyDensityTerm M Q H0 (Hn-H0,i) ω)) =
            ENNReal.ofReal Cd*(∑' i : ℕ, ENNReal.ofReal
              (assemblyDensityTerm M Q H0 (Hn-H0,i) ω)) := by
          calc
            _ = ∑' i : ℕ, ENNReal.ofReal Cd*ENNReal.ofReal
                (assemblyDensityTerm M Q H0 (Hn-H0,i) ω) := by
              apply tsum_congr
              intro i
              exact ENNReal.ofReal_mul hCd
            _ = _ := ENNReal.tsum_mul_left
        have hDenSel : (∑' i : ℕ, ENNReal.ofReal
            (assemblyDensityTerm M Q H0 (Hn-H0,i) ω)) ≤
            ∑' hk : ℕ×ℕ, ENNReal.ofReal (assemblyDensityTerm M Q H0 hk ω) := hdenSel
        have hCorrEq :
            (∑' i : ℕ, ENNReal.ofReal (Cc*(
              assemblyCorrelatedDensityAbsTerm M Q N p D a c wts
                (0:Fin 2) (Hn-H0,i) ω+
              assemblyCorrelatedDensityAbsTerm M Q N p 0 a c wts
                (1:Fin 2) (Hn-H0,i) ω))) =
            ENNReal.ofReal Cc*((∑' i : ℕ, ENNReal.ofReal
              (assemblyCorrelatedDensityAbsTerm M Q N p D a c wts
                (0:Fin 2) (Hn-H0,i) ω))+(∑' i : ℕ, ENNReal.ofReal
              (assemblyCorrelatedDensityAbsTerm M Q N p 0 a c wts
                (1:Fin 2) (Hn-H0,i) ω))) := by
          have hA0 (i : ℕ) : 0 ≤ assemblyCorrelatedDensityAbsTerm M Q N p D a c wts
              (0:Fin 2) (Hn-H0,i) ω := by
            unfold assemblyCorrelatedDensityAbsTerm
            exact abs_nonneg _
          have hA1 (i : ℕ) : 0 ≤ assemblyCorrelatedDensityAbsTerm M Q N p 0 a c wts
              (1:Fin 2) (Hn-H0,i) ω := by
            unfold assemblyCorrelatedDensityAbsTerm
            exact abs_nonneg _
          calc
            _ = ∑' i : ℕ, ENNReal.ofReal Cc*(ENNReal.ofReal
                (assemblyCorrelatedDensityAbsTerm M Q N p D a c wts
                  (0:Fin 2) (Hn-H0,i) ω)+ENNReal.ofReal
                (assemblyCorrelatedDensityAbsTerm M Q N p 0 a c wts
                  (1:Fin 2) (Hn-H0,i) ω)) := by
              apply tsum_congr
              intro i
              calc
                _ = ENNReal.ofReal Cc*ENNReal.ofReal
                    (assemblyCorrelatedDensityAbsTerm M Q N p D a c wts
                      (0:Fin 2) (Hn-H0,i) ω+
                      assemblyCorrelatedDensityAbsTerm M Q N p 0 a c wts
                      (1:Fin 2) (Hn-H0,i) ω) := ENNReal.ofReal_mul hCc
                _ = _ := congrArg (fun x : ℝ≥0∞ => ENNReal.ofReal Cc*x)
                  (ENNReal.ofReal_add (hA0 i) (hA1 i))
            _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
        have hCorrSel :
            (∑' i : ℕ, ENNReal.ofReal
              (assemblyCorrelatedDensityAbsTerm M Q N p D a c wts
                (0:Fin 2) (Hn-H0,i) ω))+
            (∑' i : ℕ, ENNReal.ofReal
              (assemblyCorrelatedDensityAbsTerm M Q N p 0 a c wts
                (1:Fin 2) (Hn-H0,i) ω)) ≤
            (∑' hk : ℕ×ℕ, ENNReal.ofReal
              (assemblyCorrelatedDensityAbsTerm M Q N p D a c wts
                (0:Fin 2) hk ω))+
            (∑' hk : ℕ×ℕ, ENNReal.ofReal
              (assemblyCorrelatedDensityAbsTerm M Q N p 0 a c wts
                (1:Fin 2) hk ω)) :=
          add_le_add hcorr0Sel hcorr1Sel
        calc
          _ = _ := by
            rw [hWaveEq,hDenEq,hCorrEq]
          _ ≤ _ := by
            apply add_le_add le_rfl
            apply add_le_add le_rfl
            apply add_le_add hMatSel
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hDenSel (by positivity)
            · exact mul_le_mul_of_nonneg_left hCorrSel (by positivity)
  have hscalarAE : ∀ᵐ ω ∂μ,
      ENNReal.ofReal (rootTraceObservable M Q m N (Q.scale-1) weights ω/4) ≤
        ENNReal.ofReal (Env ω) := by
    have hassembly := assembly_q3_positive_trace_assembly M h hM hγ Q p hp hpast
      N hN weights hw
    have hmatAE := hmatrix.1
    have hdenAE := hdensity.1
    have hcorr0AE := hcorr0.1
    have hcorr1AE := hcorr1.1
    have hwaveAE := hwave.1
    filter_upwards [hassembly,hmatAE,hdenAE,hcorr0AE,hcorr1AE,hwaveAE] with ω hω hm hd hc0 hc1 hwv
    have hmajor := assembly_trace_majorant_le_scalar_series M h hγ Q k H0 (H ω)
      (by dsimp only [H0,k]; unfold heightEntrance; omega) (hstop ω) hpast N weights ω
    have hsel := hselectedSeries ω
    have hmEq : (∑' hk : ℕ×ℕ, ENNReal.ofReal
        (assemblyTraceMatrixTerm M Q H0 N w hk ω)) = ENNReal.ofReal (Fm ω) := by
      exact (ENNReal.ofReal_tsum_of_nonneg
        (fun hk => hTraceMatrixNonneg hk ω) (Summable.of_norm hm)).symm
    have hdEq : (∑' hk : ℕ×ℕ, ENNReal.ofReal
        (assemblyDensityTerm M Q H0 hk ω)) = ENNReal.ofReal (Fd ω) := by
      exact (ENNReal.ofReal_tsum_of_nonneg
        (fun hk => assembly_density_term_nonneg M Q H0 hk ω) (Summable.of_norm hd)).symm
    have hc0Eq : (∑' hk : ℕ×ℕ, ENNReal.ofReal
        (assemblyCorrelatedDensityAbsTerm M Q N p D a c wts (0:Fin 2) hk ω)) =
        ENNReal.ofReal (Fc0 ω) := by
      exact (ENNReal.ofReal_tsum_of_nonneg (fun hk => abs_nonneg
        (assemblyCorrelatedDensityTerm M Q N p D a c wts (0:Fin 2) hk ω))
        (Summable.of_norm hc0)).symm
    have hc1Eq : (∑' hk : ℕ×ℕ, ENNReal.ofReal
        (assemblyCorrelatedDensityAbsTerm M Q N p 0 a c wts (1:Fin 2) hk ω)) =
        ENNReal.ofReal (Fc1 ω) := by
      exact (ENNReal.ofReal_tsum_of_nonneg (fun hk => abs_nonneg
        (assemblyCorrelatedDensityTerm M Q N p 0 a c wts (1:Fin 2) hk ω))
        (Summable.of_norm hc1)).symm
    have hwEq : (∑' i : ℕ, ENNReal.ofReal
        (|assemblyTraceWaveLayer M Q k p N weights i ω|)) = ENNReal.ofReal (Fw ω) := by
      exact (ENNReal.ofReal_tsum_of_nonneg (fun i => abs_nonneg
        (assemblyTraceWaveLayer M Q k p N weights i ω))
        (by simpa only [Real.norm_eq_abs] using hwv)).symm
    rw [hmEq,hdEq,hc0Eq,hc1Eq,hwEq] at hsel
    have hsum := hω.trans (hmajor.trans hsel)
    have ha : 0 ≤ B0*clk ω := mul_nonneg hB0 (by positivity)
    have hb : 0 ≤ Cw*Fw ω := mul_nonneg hCw (hFwnonneg ω)
    have hc : 0 ≤ Fm ω := hFmnonneg ω
    have hd : 0 ≤ Cd*Fd ω := mul_nonneg hCd (hFdnonneg ω)
    have he : 0 ≤ Cc*(Fc0 ω+Fc1 ω) :=
      mul_nonneg hCc (add_nonneg (hFc0nonneg ω) (hFc1nonneg ω))
    have hparts : ENNReal.ofReal (B0*clk ω)+
        (ENNReal.ofReal Cw*ENNReal.ofReal (Fw ω)+
          (ENNReal.ofReal (Fm ω)+
            (ENNReal.ofReal Cd*ENNReal.ofReal (Fd ω)+
              ENNReal.ofReal Cc*(ENNReal.ofReal (Fc0 ω)+ENNReal.ofReal (Fc1 ω))))) =
        ENNReal.ofReal (Env ω) := by
      dsimp only [Env]
      rw [ENNReal.ofReal_add ha (add_nonneg hb (add_nonneg hc (add_nonneg hd he))),
        ENNReal.ofReal_add hb (add_nonneg hc (add_nonneg hd he)),
        ENNReal.ofReal_add hc (add_nonneg hd he), ENNReal.ofReal_add hd he]
      rw [← ENNReal.ofReal_mul hCw, ← ENNReal.ofReal_mul hCd,
        ← ENNReal.ofReal_add (hFc0nonneg ω) (hFc1nonneg ω),
        ← ENNReal.ofReal_mul hCc]
    simpa only [add_assoc] using hsum.trans_eq hparts
  have hEnvLp : eLpNorm Env (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (assemblyTraceSeriesSelectedBudget M.gamma p D k) := by
    have hbaseLp : eLpNorm (fun ω => B0*clk ω) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (B0*assemblySelectedClockBudget M.gamma p (heightEntrance k)) := by
      rw [show (fun ω => B0*clk ω) = B0 • clk by funext ω; simp [smul_eq_mul]]
      rw [eLpNorm_const_smul,Real.enorm_eq_ofReal hB0]
      calc
        ENNReal.ofReal B0*eLpNorm clk (ENNReal.ofReal p) μ ≤
            ENNReal.ofReal B0*ENNReal.ofReal
              (assemblySelectedClockBudget M.gamma p (heightEntrance k)) :=
          mul_le_mul_of_nonneg_left hclockLp (by positivity)
        _ = ENNReal.ofReal (B0*assemblySelectedClockBudget M.gamma p
              (heightEntrance k)) := by rw [← ENNReal.ofReal_mul hB0]
    have hwLp : eLpNorm (fun ω => Cw*Fw ω) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (Cw*assemblyWholeRootWaveSelectedSeriesBudget M.gamma p D
          (heightEntrance k)) := by
      rw [show (fun ω => Cw*Fw ω) = Cw • Fw by funext ω; simp [smul_eq_mul]]
      rw [eLpNorm_const_smul,Real.enorm_eq_ofReal hCw]
      calc
        ENNReal.ofReal Cw*eLpNorm Fw (ENNReal.ofReal p) μ ≤
            ENNReal.ofReal Cw*ENNReal.ofReal
              (assemblyWholeRootWaveSelectedSeriesBudget M.gamma p D (heightEntrance k)) :=
          mul_le_mul_of_nonneg_left hwave.2 (by positivity)
        _ = ENNReal.ofReal (Cw*assemblyWholeRootWaveSelectedSeriesBudget M.gamma p D
              (heightEntrance k)) :=
          by rw [← ENNReal.ofReal_mul hCw]
    have hmLp := hmatrix.2
    have hdLp : eLpNorm (fun ω => Cd*Fd ω) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (Cd*assemblyDensityBudget M.gamma k H0) := by
      rw [show (fun ω => Cd*Fd ω) = Cd • Fd by funext ω; simp [smul_eq_mul]]
      rw [eLpNorm_const_smul,Real.enorm_eq_ofReal hCd]
      calc
        ENNReal.ofReal Cd*eLpNorm Fd (ENNReal.ofReal p) μ ≤
            ENNReal.ofReal Cd*ENNReal.ofReal (assemblyDensityBudget M.gamma k H0) :=
          mul_le_mul_of_nonneg_left hdensity.2 (by positivity)
        _ = ENNReal.ofReal (Cd*assemblyDensityBudget M.gamma k H0) :=
          by rw [← ENNReal.ofReal_mul hCd]
    have hcorrBand0 : 0 ≤ bandDensitySum4 k M.gamma D (H0-38) (0:Fin 2) := by
      rw [← (band_density_budget4_hasSum k M.gamma D hγ (H0-38) (0:Fin 2)).tsum_eq]
      exact tsum_nonneg fun hk => band_density_budget4_nonneg k M.gamma D hD
        (H0-38) (0:Fin 2) hk
    have hcorrBand1 : 0 ≤ bandDensitySum4 k M.gamma 0 (H0-38) (1:Fin 2) := by
      rw [← (band_density_budget4_hasSum k M.gamma 0 hγ (H0-38) (1:Fin 2)).tsum_eq]
      exact tsum_nonneg fun hk => band_density_budget4_nonneg k M.gamma 0 (by norm_num)
        (H0-38) (1:Fin 2) hk
    have hcLp : eLpNorm (fun ω => Cc*(Fc0 ω+Fc1 ω)) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (Cc*(40*(2*p+2)*bandDensitySum4 k M.gamma D (H0-38) 0+
          40*(2*p+2)*bandDensitySum4 k M.gamma 0 (H0-38) 1)) := by
      have hsum0 : 0 ≤ 40*(2*p+2)*bandDensitySum4 k M.gamma D (H0-38) 0 :=
        mul_nonneg (by linarith [hp]) hcorrBand0
      have hsum1 : 0 ≤ 40*(2*p+2)*bandDensitySum4 k M.gamma 0 (H0-38) 1 :=
        mul_nonneg (by linarith [hp]) hcorrBand1
      have hadd : eLpNorm (fun ω => Fc0 ω+Fc1 ω) (ENNReal.ofReal p) μ ≤
          eLpNorm Fc0 (ENNReal.ofReal p) μ+eLpNorm Fc1 (ENNReal.ofReal p) μ :=
        eLpNorm_add_le hp1
      rw [show (fun ω => Cc*(Fc0 ω+Fc1 ω)) = Cc • (fun ω => Fc0 ω+Fc1 ω)
        by funext ω; simp [smul_eq_mul]]
      rw [eLpNorm_const_smul,Real.enorm_eq_ofReal hCc]
      calc
        ENNReal.ofReal Cc*eLpNorm (fun ω => Fc0 ω+Fc1 ω) (ENNReal.ofReal p) μ ≤
            ENNReal.ofReal Cc*(eLpNorm Fc0 (ENNReal.ofReal p) μ+
              eLpNorm Fc1 (ENNReal.ofReal p) μ) :=
            mul_le_mul_of_nonneg_left hadd (by positivity)
        _ ≤ ENNReal.ofReal Cc*(ENNReal.ofReal
              (40*(2*p+2)*bandDensitySum4 k M.gamma D (H0-38) 0)+
              ENNReal.ofReal
              (40*(2*p+2)*bandDensitySum4 k M.gamma 0 (H0-38) 1)) :=
          mul_le_mul_of_nonneg_left (add_le_add hcorr0.2 hcorr1.2) (by positivity)
        _ = ENNReal.ofReal (Cc*(40*(2*p+2)*bandDensitySum4 k M.gamma D (H0-38) 0+
              40*(2*p+2)*bandDensitySum4 k M.gamma 0 (H0-38) 1)) := by
          rw [← ENNReal.ofReal_add hsum0 hsum1, ← ENNReal.ofReal_mul hCc]
    have hadd1 := (eLpNorm_add_le hp1).trans (add_le_add hbaseLp hwLp)
    have hadd2 := (eLpNorm_add_le hp1).trans (add_le_add hadd1 hmLp)
    have hadd3 := (eLpNorm_add_le hp1).trans (add_le_add hadd2 hdLp)
    have hadd4 := (eLpNorm_add_le hp1).trans (add_le_add hadd3 hcLp)
    change eLpNorm (fun ω => B0*clk ω+(Cw*Fw ω+(Fm ω+(Cd*Fd ω+Cc*(Fc0 ω+Fc1 ω)))))
      (ENNReal.ofReal p) μ ≤ _
    have hclockBudget : 0 ≤ assemblySelectedClockBudget M.gamma p
        (heightEntrance k) := by
      have htail : 0 ≤ selectedWaveExactTail (M.gamma/2) (p/2)
          (heightEntrance k) (0:Fin 2) := by
        unfold selectedWaveExactTail
        apply tsum_nonneg
        intro n
        simp only [Fin.val_zero, pow_zero, one_mul]
        unfold selectedTailProbability
        positivity
      have hentrance : 27 ≤ (heightEntrance k:ℝ) := by
        exact_mod_cast (by unfold heightEntrance; omega : 27 ≤ heightEntrance k)
      unfold assemblySelectedClockBudget
      positivity
    have hwaveBudget : 0 ≤ assemblyWholeRootWaveSelectedSeriesBudget M.gamma p D
        (heightEntrance k) :=
      assembly_whole_root_wave_selected_series_budget_nonneg M.gamma p D hγ hγ0 hp
        (heightEntrance k) (by unfold heightEntrance; omega) hD
    have hmatrixBudget : 0 ≤ assemblyTraceMatrixBudget M.gamma p D H0 := by
      rw [← (assembly_trace_matrix_budget_hasSum M.gamma p D hγ H0).tsum_eq]
      exact tsum_nonneg fun hk => assembly_trace_matrix_budget_term_nonneg
        M.gamma p D hγ0 (by linarith [hp]) hD H0 hk
    have hdensityBudget : 0 ≤ assemblyDensityBudget M.gamma k H0 := by
      rw [← (assembly_density_budget_hasSum M.gamma hγ k H0).tsum_eq]
      exact tsum_nonneg fun hk => assembly_density_budget_term_nonneg M.gamma k H0 hk
    have hbasePart : 0 ≤ B0*assemblySelectedClockBudget M.gamma p (heightEntrance k) :=
      mul_nonneg hB0 hclockBudget
    have hwavePart : 0 ≤ Cw*assemblyWholeRootWaveSelectedSeriesBudget M.gamma p D
        (heightEntrance k) :=
      mul_nonneg hCw hwaveBudget
    have hmatrixPart : 0 ≤ assemblyTraceMatrixBudget M.gamma p D H0 := hmatrixBudget
    have hdensityPart : 0 ≤ Cd*assemblyDensityBudget M.gamma k H0 :=
      mul_nonneg hCd hdensityBudget
    have hcorrPart : 0 ≤ Cc*(40*(2*p+2)*bandDensitySum4 k M.gamma D
          (H0-38) 0+40*(2*p+2)*bandDensitySum4 k M.gamma 0 (H0-38) 1) := by
      apply mul_nonneg hCc
      apply add_nonneg <;> positivity
    have hbudgetParts : ENNReal.ofReal (assemblyTraceSeriesSelectedBudget M.gamma p D k) =
        ENNReal.ofReal (B0*assemblySelectedClockBudget M.gamma p (heightEntrance k))+
          (ENNReal.ofReal (Cw*assemblyWholeRootWaveSelectedSeriesBudget M.gamma p D
            (heightEntrance k))+
            (ENNReal.ofReal (assemblyTraceMatrixBudget M.gamma p D H0)+
              (ENNReal.ofReal (Cd*assemblyDensityBudget M.gamma k H0)+
                ENNReal.ofReal (Cc*(40*(2*p+2)*bandDensitySum4 k M.gamma D
                  (H0-38) 0+40*(2*p+2)*bandDensitySum4 k M.gamma 0 (H0-38) 1))))) := by
      dsimp only [assemblyTraceSeriesSelectedBudget,B0,Cw,Cd,Cc]
      simp only [add_assoc]
      rw [ENNReal.ofReal_add hbasePart
          (add_nonneg hwavePart (add_nonneg hmatrixPart (add_nonneg hdensityPart hcorrPart))),
        ENNReal.ofReal_add hwavePart (add_nonneg hmatrixPart (add_nonneg hdensityPart hcorrPart)),
        ENNReal.ofReal_add hmatrixPart (add_nonneg hdensityPart hcorrPart),
        ENNReal.ofReal_add hdensityPart hcorrPart]
    have hEnvFun :
        (fun ω => B0*clk ω+(Cw*Fw ω+(Fm ω+(Cd*Fd ω+Cc*(Fc0 ω+Fc1 ω))))) =
        (fun ω => B0*clk ω)+(fun ω => Cw*Fw ω)+
          (fun ω => Fm ω)+(fun ω => Cd*Fd ω)+
            (fun ω => Cc*(Fc0 ω+Fc1 ω)) := by
      funext ω
      simp only [Pi.add_apply]
      ring_nf
    have hadd4' : eLpNorm
        ((fun ω => B0*clk ω)+(fun ω => Cw*Fw ω)+
          (fun ω => Fm ω)+(fun ω => Cd*Fd ω)+
            (fun ω => Cc*(Fc0 ω+Fc1 ω))) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (B0*assemblySelectedClockBudget M.gamma p (heightEntrance k))+
          (ENNReal.ofReal (Cw*assemblyWholeRootWaveSelectedSeriesBudget M.gamma p D
            (heightEntrance k))+
            (ENNReal.ofReal (assemblyTraceMatrixBudget M.gamma p D H0)+
              (ENNReal.ofReal (Cd*assemblyDensityBudget M.gamma k H0)+
                ENNReal.ofReal (Cc*(40*(2*p+2)*bandDensitySum4 k M.gamma D
                  (H0-38) 0+40*(2*p+2)*bandDensitySum4 k M.gamma 0 (H0-38) 1))))) := by
      simpa only [add_assoc] using hadd4
    rw [hEnvFun]
    exact hadd4'.trans_eq hbudgetParts.symm
  have hpoint : ∀ᵐ ω ∂μ,
      ‖(rootTraceObservable M Q m N (Q.scale-1) weights ω)/4‖ ≤ ‖Env ω‖ := by
    filter_upwards [hscalarAE] with ω hω
    have hq : 0 ≤ rootTraceObservable M Q m N (Q.scale-1) weights ω :=
      root_trace_observable_nonneg M Q m N (Q.scale-1) (by dsimp only [m]; unfold protectedOldLabel; omega)
        weights ω
    have hh : (rootTraceObservable M Q m N (Q.scale-1) weights ω)/4 ≤ Env ω :=
      (ENNReal.ofReal_le_ofReal_iff (hEnvnonneg ω)).mp hω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤
      (rootTraceObservable M Q m N (Q.scale-1) weights ω)/4),
      Real.norm_eq_abs, abs_of_nonneg (hEnvnonneg ω)]
    exact hh
  have htraceMeas := root_trace_observable_measurable M Q m N (Q.scale-1) weights
  have hquarterMeas : Measurable
      (fun ω => rootTraceObservable M Q m N (Q.scale-1) weights ω/4) :=
    htraceMeas.div_const 4
  have hmono := eLpNorm_mono_ae_real (μ := μ) (p := ENNReal.ofReal p)
    hquarterMeas.aestronglyMeasurable hpoint
  have hEnvNorm : (fun ω => ‖Env ω‖) = Env := by
    funext ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hEnvnonneg ω)]
  rw [hEnvNorm] at hmono
  have hquarter : eLpNorm (fun ω => rootTraceObservable M Q m N (Q.scale-1) weights ω/4)
      (ENNReal.ofReal p) μ ≤ ENNReal.ofReal
        (assemblyTraceSeriesSelectedBudget M.gamma p D k) := by
    exact hmono.trans hEnvLp
  have hmul : eLpNorm (fun ω => (4:ℝ)*
      (rootTraceObservable M Q m N (Q.scale-1) weights ω/4))
      (ENNReal.ofReal p) μ ≤ ENNReal.ofReal
        (4*assemblyTraceSeriesSelectedBudget M.gamma p D k) := by
    rw [show (fun ω => (4:ℝ)*
        (rootTraceObservable M Q m N (Q.scale-1) weights ω/4)) =
        (4:ℝ) • (fun ω => rootTraceObservable M Q m N (Q.scale-1) weights ω/4)
        by funext ω; simp [smul_eq_mul]]
    rw [eLpNorm_const_smul,Real.enorm_eq_ofReal (by norm_num : (0:ℝ)≤4)]
    calc
      ENNReal.ofReal 4*eLpNorm
          (fun ω => rootTraceObservable M Q m N (Q.scale-1) weights ω/4)
          (ENNReal.ofReal p) μ ≤ ENNReal.ofReal 4*ENNReal.ofReal
          (assemblyTraceSeriesSelectedBudget M.gamma p D k) :=
        mul_le_mul_of_nonneg_left hquarter (by positivity)
      _ = ENNReal.ofReal (4*assemblyTraceSeriesSelectedBudget M.gamma p D k) :=
        by rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤4)]
  have hEq : (fun ω => (4:ℝ)*
      (rootTraceObservable M Q m N (Q.scale-1) weights ω/4)) =
      rootTraceObservable M Q m N (Q.scale-1) weights := by
    funext ω
    ring
  rw [hEq] at hmul
  simpa only [μ,D,k] using hmul

end
end ASDExplicitGamma.Inverse
