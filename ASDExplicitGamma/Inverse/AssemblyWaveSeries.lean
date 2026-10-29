module

public import ASDExplicitGamma.Inverse.AssemblyWaveLayerLp
public import ASDExplicitGamma.Inverse.StoppedSeriesLp

/-! The actual full-stop physical-wave layer series. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Triadic
open ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- Geometric ratio after combining the layer-volume square root with the
two-dimensional localization depth. -/
def assemblyWaveDecayRatio (γ : ℝ) : ℝ := (3:ℝ)^(8*γ-1/2)

def assemblyWaveGeom0 (γ : ℝ) : ℝ :=
  assemblyWaveDecayRatio γ/(1-assemblyWaveDecayRatio γ)

def assemblyWaveGeom1 (γ : ℝ) : ℝ :=
  assemblyWaveDecayRatio γ/(1-assemblyWaveDecayRatio γ)^2

theorem assembly_wave_decay_ratio_pos (γ : ℝ) :
    0 < assemblyWaveDecayRatio γ := by
  unfold assemblyWaveDecayRatio
  exact Real.rpow_pos_of_pos (by norm_num) _

theorem assembly_wave_decay_ratio_lt_one (γ : ℝ) (hγ : γ ≤ gammaZero) :
    assemblyWaveDecayRatio γ < 1 := by
  have hg : γ ≤ 17/50000 := hγ
  unfold assemblyWaveDecayRatio
  apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1:ℝ)<3)
  nlinarith only [hg]

theorem assembly_wave_geometric_sums (γ : ℝ) (hγ : γ ≤ gammaZero) :
    HasSum (fun i : ℕ => assemblyWaveDecayRatio γ^(i+1)) (assemblyWaveGeom0 γ) ∧
    HasSum (fun i : ℕ => ((i+1:ℕ):ℝ)*assemblyWaveDecayRatio γ^(i+1))
      (assemblyWaveGeom1 γ) := by
  let q := assemblyWaveDecayRatio γ
  have hq0 : 0 ≤ q := (assembly_wave_decay_ratio_pos γ).le
  have hq1 : q < 1 := assembly_wave_decay_ratio_lt_one γ hγ
  have hg := hasSum_geometric_of_lt_one hq0 hq1
  have hm := hasSum_coe_mul_geometric_of_norm_lt_one
    (r := q) (by rw [Real.norm_of_nonneg hq0]; exact hq1)
  have h0 : HasSum (fun i : ℕ => q^(i+1)) (q/(1-q)) := by
    convert hg.mul_left q using 1
    · funext i
      rw [pow_succ]
      ring
    · field_simp
  have h1 : HasSum (fun i : ℕ => ((i+1:ℕ):ℝ)*q^(i+1)) (q/(1-q)^2) := by
    have hh := (hg.add hm).mul_left q
    convert hh using 1
    · funext i
      rw [pow_succ]
      push_cast
      ring
    · field_simp
      ring
  constructor
  · simpa only [q,assemblyWaveGeom0] using h0
  · simpa only [q,assemblyWaveGeom1] using h1

theorem assembly_trace_wave_layer_measurable
    (M : ABKModel 2) (Q : TriadicCube 2) (k : ℕ) (p : ℝ)
    (N : ℤ) (weights : ℤ → ℝ) (i : ℕ) :
    Measurable (assemblyTraceWaveLayer M Q k p N weights i) := by
  let H0 := heightEntrance k+5
  let H := resetQ3StoppedHeight M Q k
  let w := sourceBandWeights (protectedOldLabel Q.scale (orderBand p)) weights
  let F : ℕ × Cutoff.CutoffSample 2 → ℝ := fun z =>
    physicalMissingWave M (layerOldCutoff Q.scale z.1 (i+1)) Q.scale N
      (cubeCorner Q 0) (cubeCorner Q 1) w z.2
  have hH : Measurable H :=
    q3_stopped_height_measurable M Q H0 resetAllOrderTau (waveGateEta .allOrder)
  have hclock : Measurable (fun ω => rootAssemblyClock M.gamma (H ω) (i+1)) :=
    (measurable_of_countable (fun n : ℕ => rootAssemblyClock M.gamma n (i+1))).comp hH
  have hprod : Measurable F := by
    apply measurable_from_prod_countable_right
    intro n
    dsimp only [F]
    exact physical_missing_wave_measurable M
      (layerOldCutoff Q.scale n (i+1)) Q.scale N (cubeCorner Q 0) (cubeCorner Q 1) w
  have hmiss : Measurable (fun ω =>
      physicalMissingWave M (layerOldCutoff Q.scale (H ω) (i+1)) Q.scale N
        (cubeCorner Q 0) (cubeCorner Q 1) w ω) := by
    change Measurable (F ∘ fun ω => (H ω,ω))
    exact hprod.comp (Measurable.prodMk hH measurable_id)
  change Measurable (fun ω => rootAssemblyClock M.gamma (H ω) (i+1)*
    Real.sqrt (bankLayerWeight i)*F (H ω,ω))
  exact (hclock.mul_const (Real.sqrt (bankLayerWeight i))).mul hmiss

end
end ASDExplicitGamma.Inverse
