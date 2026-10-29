module

public import ASDExplicitGamma.Inverse.AssemblyTraceMeasurable
public import ASDExplicitGamma.Inverse.AssemblyWaveSeries
public import ASDExplicitGamma.Inverse.AssemblyCorrelatedAbsSeries
public import ASDExplicitGamma.Inverse.AssemblyDensitySeries
public import ASDExplicitGamma.Inverse.AssemblyTraceMatrixSeries
public import ASDExplicitGamma.Inverse.AssemblySelectedClock
public import ASDExplicitGamma.Inverse.AssemblyTraceScalarSeries

/-! The actual full-stop trace moment from its positive layer expansion. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- Coefficient of the complete wave-density cross payment in the scalar
positive trace layer. -/
def assemblyTraceCorrelationCoefficient : ℝ :=
  4*rootAssemblySensitivity*(1+2*Real.sqrt 3*resetAllOrderTau)*
    (planarGradientCharge 40+1)

/-- Relative coefficient converting the actual D2 density series to the
larger spatial-density payment in the trace envelope. -/
def assemblyTraceDensityFactor : ℝ :=
  (4*(1+2*Real.sqrt 3*resetAllOrderTau)*assemblyActiveConstant)/
    rootResponseEnvelope (6*resetAllOrderTau)

theorem assembly_trace_density_factor_pos : 0 < assemblyTraceDensityFactor := by
  unfold assemblyTraceDensityFactor assemblyActiveConstant rootResponseEnvelope
  have hτ : 0 ≤ resetAllOrderTau := by
    norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
  positivity

/-- The trace's literal active spatial-density coefficient is exactly the
relative factor times the complete D2 density summand. -/
theorem assembly_trace_density_layer_eq (M : ABKModel 2) (Q : TriadicCube 2)
    (H0 : ℕ) (hH0 : 38 ≤ H0) (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) :
    rootAssemblyClock M.gamma (H0+hk.1) (hk.2+1)*
      (assemblyTraceCorrelationCoefficient*assemblyActiveConstant*
        ∑ e : Fin 3, resetDensityExcess M Q H0 resetAllOrderTau
          (waveGateEta .allOrder) (allOrderDensity:ℝ) 1324 2 hk e ω) =
    assemblyTraceDensityFactor*assemblyDensityTerm M Q H0 hk ω := by
  rw [assembly_clock_eq_reset M.gamma H0 hH0 hk]
  unfold assemblyTraceCorrelationCoefficient assemblyTraceDensityFactor
    assemblyDensityTerm resetDensityTerm2
  have hτ : 0 ≤ resetAllOrderTau := by
    norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
  have hden : 0 < rootResponseEnvelope (6*resetAllOrderTau) := by
    unfold rootResponseEnvelope
    positivity
  have hresponse : rootResponseEnvelope (6*resetAllOrderTau) =
      rootResponseEnvelope (resetAllOrderTau*6) := by
    congr 1
    ring
  have hden' : 0 < rootResponseEnvelope (resetAllOrderTau*6) := by
    simpa only [mul_comm] using hden
  rw [hresponse]
  field_simp [ne_of_gt hden']

/-- One actual stopped scalar trace layer is controlled by positive component
payments. The wave-density term uses the exact reconstruction at the selected
full stopping height and keeps both depth moments. -/
theorem assembly_selected_trace_scalar_layer_bound
    (M : ABKModel 2) (Q : TriadicCube 2) (p : ℝ)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc (protectedOldLabel Q.scale (orderBand p)) N,
      0 ≤ weights n ∧ weights n ≤ 1)
    (ω : Cutoff.CutoffSample 2) (i : ℕ)
    (hstop : heightEntrance (orderBand p)+5 ≤
      resetQ3StoppedHeight M Q (orderBand p) ω) :
    let H0 := heightEntrance (orderBand p)+5
    let H := resetQ3StoppedHeight M Q (orderBand p) ω
    let hk := (H-H0,i)
    let D := ((N-Q.scale+1:ℤ):ℝ)
    let a := cubeCorner Q 0
    let c := cubeCorner Q 1
    let wts : (ℕ×ℕ)→ℤ→ℝ := fun _ =>
      sourceBandWeights (protectedOldLabel Q.scale (orderBand p)) weights
    assemblyTraceScalarLayer M Q (orderBand p) H0 hk N weights ω ≤
      assemblyTraceBaseline*rootAssemblyClock M.gamma H (i+1)*bankLayerWeight i+
      assemblyTraceWaveCoefficient*
        |assemblyTraceWaveLayer M Q (orderBand p) p N weights i ω|+
      assemblyTraceMatrixTerm M Q H0 N
        (sourceBandWeights (protectedOldLabel Q.scale (orderBand p)) weights) hk ω+
      assemblyTraceDensityFactor*assemblyDensityTerm M Q H0 hk ω+
      assemblyTraceCorrelationCoefficient*M.gamma*(3:ℝ)^(2*M.gamma*D)*
        (assemblyCorrelatedDensityAbsTerm M Q N p D a c wts (0:Fin 2) hk ω+
          assemblyCorrelatedDensityAbsTerm M Q N p 0 a c wts (1:Fin 2) hk ω) := by
  dsimp only
  let H0 := heightEntrance (orderBand p)+5
  let H := resetQ3StoppedHeight M Q (orderBand p) ω
  let hk : ℕ×ℕ := (H-H0,i)
  let D : ℝ := ((N-Q.scale+1:ℤ):ℝ)
  let a := cubeCorner Q 0
  let c := cubeCorner Q 1
  let w := sourceBandWeights (protectedOldLabel Q.scale (orderBand p)) weights
  let wts : (ℕ×ℕ)→ℤ→ℝ := fun _ => w
  let W := physicalMissingWave M
    (layerOldCutoff Q.scale (H0+hk.1) (hk.2+1)) Q.scale N a c w ω
  let Y := fun m e => resetDensityExcess M Q H0 resetAllOrderTau
    (waveGateEta .allOrder) (allOrderDensity:ℝ) 1324 m hk e ω
  let R := physicalResetWave M Q N H0 a c wts hk ω
  let x := (localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ)
  have hH0 : 377 ≤ H0 := by unfold H0 heightEntrance; omega
  have hH0' : 38 ≤ H0 := by omega
  have hD : 0 ≤ D := by dsimp only [D]; exact_mod_cast (by omega : 0 ≤ N-Q.scale+1)
  have hx : 0 ≤ x := Nat.cast_nonneg _
  have hsumY : 0 ≤ ∑ e : Fin 3, Real.sqrt (Y 4 e) :=
    Finset.sum_nonneg fun e _ => Real.sqrt_nonneg _
  have hreset0 := assembly_reset_wave_reconstruction M Q N hN H0 hH0
    a c wts hk ω
  have hadd : H0+(H-H0)=H := by have hh := hstop; omega
  rw [hadd] at hreset0
  have hreset :
      (M.gamma*(D+x)*(3:ℝ)^(2*M.gamma*D))*R =
        rootAssemblyClock M.gamma H (i+1)*W := by
    simpa [D,x,R,W,hk,wts,hadd] using hreset0
  have hweight (hk' : ℕ×ℕ) : ∀ n ∈ Finset.Ioc
      (physicalResetOldLabel Q H0 hk') N, 0 ≤ wts hk' n ∧ wts hk' n ≤ 1 := by
    intro n hn
    exact source_band_weights_bounds (physicalResetOldLabel Q H0 hk')
      (protectedOldLabel Q.scale (orderBand p)) N weights hw n hn
  have hcorrsum :
      (∑ e : Fin 3, R * Real.sqrt (Y 4 e))=
        R * (∑ e : Fin 3, Real.sqrt (Y 4 e)) := by
    rw [← Finset.mul_sum]
  have hcorr0 :
      assemblyCorrelatedDensityAbsTerm M Q N p D a c wts (0:Fin 2) hk ω =
      (D+1) * |R| * (∑ e : Fin 3, Real.sqrt (Y 4 e)) := by
    unfold assemblyCorrelatedDensityAbsTerm assemblyCorrelatedDensityTerm
    dsimp only [H0]
    simp only [Fin.val_zero, pow_zero, mul_one]
    rw [hcorrsum, abs_mul, abs_mul,
      abs_of_nonneg (add_nonneg hD (by norm_num)),
      abs_of_nonneg hsumY]
    ring
  have hcorr1 :
      assemblyCorrelatedDensityAbsTerm M Q N p 0 a c wts (1:Fin 2) hk ω =
      x * |R| * (∑ e : Fin 3, Real.sqrt (Y 4 e)) := by
    unfold assemblyCorrelatedDensityAbsTerm assemblyCorrelatedDensityTerm
    dsimp only [H0]
    simp only [Fin.val_one, pow_one, zero_add, one_mul]
    rw [hcorrsum, abs_mul, abs_mul, abs_of_nonneg hx,
      abs_of_nonneg hsumY]
    ring
  have hcross :
      (D+x) * R * (∑ e : Fin 3, Real.sqrt (Y 4 e)) ≤
        assemblyCorrelatedDensityAbsTerm M Q N p D a c wts (0:Fin 2) hk ω+
          assemblyCorrelatedDensityAbsTerm M Q N p 0 a c wts (1:Fin 2) hk ω := by
    calc
      (D+x) * R * (∑ e : Fin 3, Real.sqrt (Y 4 e)) ≤
          (D+x) * |R| * (∑ e : Fin 3, Real.sqrt (Y 4 e)) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (le_abs_self R) (add_nonneg hD hx)) hsumY
      _ ≤ (D+1+x) * |R| * (∑ e : Fin 3, Real.sqrt (Y 4 e)) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg R)
        · exact hsumY
      _ = _ := by rw [hcorr0,hcorr1]; ring
  have hK : 0 ≤ assemblyTraceCorrelationCoefficient := by
    unfold assemblyTraceCorrelationCoefficient
    have hτ : 0 ≤ resetAllOrderTau := by
      norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
    have hsens := root_assembly_sensitivity_pos.le
    unfold planarGradientCharge
    positivity
  have hgam : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hcoef : 0 ≤ assemblyTraceCorrelationCoefficient*M.gamma*(3:ℝ)^(2*M.gamma*D) :=
    mul_nonneg (mul_nonneg hK hgam) (by positivity)
  have hcorr :
      assemblyTraceCorrelationCoefficient*M.gamma*(3:ℝ)^(2*M.gamma*D)*
        ((D+x)*R*(∑ e : Fin 3, Real.sqrt (Y 4 e))) ≤
      assemblyTraceCorrelationCoefficient*M.gamma*(3:ℝ)^(2*M.gamma*D)*
        (assemblyCorrelatedDensityAbsTerm M Q N p D a c wts (0:Fin 2) hk ω+
          assemblyCorrelatedDensityAbsTerm M Q N p 0 a c wts (1:Fin 2) hk ω) :=
    mul_le_mul_of_nonneg_left hcross hcoef
  have hwave : assemblyTraceWaveLayer M Q (orderBand p) p N weights i ω =
      rootAssemblyClock M.gamma H (i+1)*Real.sqrt (bankLayerWeight i)*W := by
    dsimp only [assemblyTraceWaveLayer,H,H0,W,hk]
    rw [hadd]
  have hwaveabs : |assemblyTraceWaveLayer M Q (orderBand p) p N weights i ω| =
      rootAssemblyClock M.gamma H (i+1)*Real.sqrt (bankLayerWeight i) * |W| := by
    rw [hwave]
    calc
      |rootAssemblyClock M.gamma H (i+1)*Real.sqrt (bankLayerWeight i)*W| =
          |rootAssemblyClock M.gamma H (i+1)| *
            |Real.sqrt (bankLayerWeight i)| * |W| := by rw [abs_mul,abs_mul]
      _ = rootAssemblyClock M.gamma H (i+1)*Real.sqrt (bankLayerWeight i)*|W| := by
        rw [abs_of_nonneg (root_assembly_clock_pos _ _ _).le,
          abs_of_nonneg (Real.sqrt_nonneg _)]
  have hW : W ≤ |W| := le_abs_self W
  have hwavecoef : 0 ≤ assemblyTraceWaveCoefficient := by
    unfold assemblyTraceWaveCoefficient
    have hτ : 0 ≤ resetAllOrderTau := by
      norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
    have hsens := root_assembly_sensitivity_pos.le
    unfold planarGradientCharge
    positivity
  have hdensity := assembly_trace_density_layer_eq M Q H0 hH0' hk ω
  have hmatrix : rootAssemblyClock M.gamma (H0+hk.1) (hk.2+1)*
      (rootAssemblySensitivity*assemblyTraceMatrixDeviation M Q (H0+hk.1)
        (hk.2+1) N w ω) =
      assemblyTraceMatrixTerm M Q H0 N w hk ω := by
    unfold assemblyTraceMatrixTerm
    ring
  have hcrossEq :
      rootAssemblyClock M.gamma H (i+1) *
        (assemblyTraceCorrelationCoefficient * W *
          (∑ e : Fin 3, Real.sqrt (Y 4 e))) =
      assemblyTraceCorrelationCoefficient*M.gamma*(3:ℝ)^(2*M.gamma*D)*
        ((D+x)*R*(∑ e : Fin 3, Real.sqrt (Y 4 e))) := by
    calc
      rootAssemblyClock M.gamma H (i+1) *
          (assemblyTraceCorrelationCoefficient * W *
            (∑ e : Fin 3, Real.sqrt (Y 4 e))) =
          assemblyTraceCorrelationCoefficient *
            (rootAssemblyClock M.gamma H (i+1) * W) *
            (∑ e : Fin 3, Real.sqrt (Y 4 e)) := by ring
      _ = assemblyTraceCorrelationCoefficient *
            (M.gamma*(D+x)*(3:ℝ)^(2*M.gamma*D)*R) *
            (∑ e : Fin 3, Real.sqrt (Y 4 e)) := by rw [← hreset]
      _ = _ := by ring
  have hscalarExpand :
      assemblyTraceScalarLayer M Q (orderBand p) H0 hk N weights ω =
        assemblyTraceBaseline * rootAssemblyClock M.gamma (H0+hk.1) (hk.2+1) *
            bankLayerWeight hk.2+
          assemblyTraceWaveCoefficient * rootAssemblyClock M.gamma (H0+hk.1) (hk.2+1) *
            Real.sqrt (bankLayerWeight hk.2) * W+
          rootAssemblyClock M.gamma (H0+hk.1) (hk.2+1) *
            (rootAssemblySensitivity * assemblyTraceMatrixDeviation M Q (H0+hk.1)
              (hk.2+1) N w ω)+
          rootAssemblyClock M.gamma (H0+hk.1) (hk.2+1) *
            (assemblyTraceCorrelationCoefficient * assemblyActiveConstant *
              (∑ e : Fin 3, Y 2 e))+
          rootAssemblyClock M.gamma (H0+hk.1) (hk.2+1) *
            (assemblyTraceCorrelationCoefficient * W *
              (∑ e : Fin 3, Real.sqrt (Y 4 e))) := by
    dsimp only [assemblyTraceScalarLayer, assemblyTraceBaseline,
      assemblyTraceWaveCoefficient, assemblyTraceMatrixDeviation,
      assemblyActiveConstant, assemblyTraceCorrelationCoefficient,
      H0, hk, w, W, Y]
    ring
  rw [hscalarExpand]
  dsimp only [H0,H,hk,D,a,c,w,wts,W,Y,R,x] at *
  rw [hadd] at hmatrix hdensity hcrossEq
  rw [hadd]
  rw [hmatrix, hdensity, hcrossEq]
  have hwave' : assemblyTraceWaveCoefficient*
      rootAssemblyClock M.gamma H (i+1)*Real.sqrt (bankLayerWeight i)*W ≤
      assemblyTraceWaveCoefficient *
        |assemblyTraceWaveLayer M Q (orderBand p) p N weights i ω| := by
    rw [hwaveabs]
    calc
      assemblyTraceWaveCoefficient * rootAssemblyClock M.gamma H (i+1) *
          Real.sqrt (bankLayerWeight i) * W =
          assemblyTraceWaveCoefficient *
            (rootAssemblyClock M.gamma H (i+1) *
              (Real.sqrt (bankLayerWeight i) * W)) := by ring
      _ ≤ assemblyTraceWaveCoefficient *
            (rootAssemblyClock M.gamma H (i+1) *
              (Real.sqrt (bankLayerWeight i) * |W|)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hW (Real.sqrt_nonneg _))
            (root_assembly_clock_pos _ _ _).le)
          hwavecoef
      _ = assemblyTraceWaveCoefficient *
            (rootAssemblyClock M.gamma H (i+1) *
              Real.sqrt (bankLayerWeight i) * |W|) := by ring
  have hcorr' := hcorr
  have hwave'' : assemblyTraceWaveCoefficient *
      rootAssemblyClock M.gamma H (i+1)*Real.sqrt (bankLayerWeight i) *
        physicalMissingWave M (layerOldCutoff Q.scale H (i+1)) Q.scale N
          (cubeCorner Q 0) (cubeCorner Q 1)
          (sourceBandWeights (protectedOldLabel Q.scale (orderBand p)) weights) ω ≤
      assemblyTraceWaveCoefficient *
        |assemblyTraceWaveLayer M Q (orderBand p) p N weights i ω| := by
    have htemp := hwave'
    dsimp only [W,hk] at htemp
    rw [hadd] at htemp
    exact htemp
  have hsumle := add_le_add hwave'' hcorr'
  linarith [hsumle]

end
end ASDExplicitGamma.Inverse
