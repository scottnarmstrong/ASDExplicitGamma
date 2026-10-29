module

public import ASDExplicitGamma.Inverse.InitialSensitivityLambda
public import ASDExplicitGamma.Inverse.GoodCellDerivative
public import ASDExplicitGamma.Inverse.RootDefinitions

/-! Actual source sensitivity smallness, discharged from the same old
history and the full later derivative gates on the actual good cell. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic ASDExplicitGamma.Response
noncomputable section

/-- The actual good-cell event supplies its actual old-history event. -/
theorem good_cell_raw_history (M : ABKModel 2) (Q : TriadicCube 2) (τ η : ℝ)
    (ω : Cutoff.CutoffSample 2) (hgood : ω ∉ cellFailure M τ η Q) :
    ω ∈ clippedCellGoodEvent M (Q.scale+40) Q τ := by
  change clippedCellRawHistory M (Q.scale+40) Q ω ≤ ENNReal.ofReal τ
  by_contra hn
  exact hgood (Or.inl (lt_of_not_ge hn))

/-- The actual Dsharp times the genuine initial inverse lambda has the
source size bound, with no smallness, lambda, derivative or response premise. -/
theorem good_cell_sensitivity_size_bound (M : ABKModel 2) (Q : TriadicCube 2)
    (τ η : ℝ) (hτ : 0 ≤ τ) (hη : 0 ≤ η) (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M τ η Q) (J : ℤ) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc (Q.scale+40) J, 0 ≤ weights k ∧ weights k ≤ 1) :
    sensitivityDsharp Q (laterBandW2 Q (Q.scale+40) J weights ω)*
      sensitivityPathLambdaInverse M.nu M.nu_pos (oldResponseCoefficient Q (Q.scale+40) ω)
        (laterResponseCoefficient Q (Q.scale+40) J weights ω) (1/4) 0 ≤ 2*(1+τ)*(10*η) := by
  have hD := good_cell_later_band_Dsharp M Q τ η hη ω hgood J weights hw
  have hL := good_initial_sensitivity_lambda_bound M Q (Q.scale+40) J weights τ hτ ω
    (good_cell_raw_history M Q τ η ω hgood)
  have hL0 := sensitivityPathLambdaInverse_nonneg M.nu M.nu_pos
    (oldResponseCoefficient Q (Q.scale+40) ω) (laterResponseCoefficient Q (Q.scale+40) J weights ω)
    (by norm_num : (0:ℝ) < 1/4) 0
  have h1 := mul_le_mul_of_nonneg_right hD hL0
  have h2 := mul_le_mul_of_nonneg_left hL (show 0 ≤ 10*η by positivity)
  nlinarith only [h1,h2]

/-- Both fixed source tuples actually have x<=1/4, inside the stated
Cloc=1.1106 gate. The tuples retain their own tau and eta. -/
theorem root_sensitivity_gate_quarter (r : RootRow) :
    2*(1+rootTau r)*(10*waveGateEta (rootWaveTuple r)) ≤ (1/4:ℝ) := by
  cases r <;> norm_num [rootTau,rootWaveTuple,waveGateEta,
    Numerics.Wave.fullEta,Numerics.Wave.fullTau,Numerics.Wave.inverseEta,Numerics.Wave.inverseTau]

/-- Both ODE smallness hypotheses follow from the actual good-cell event. -/
theorem good_cell_sensitivity_ode_gate (M : ABKModel 2) (Q : TriadicCube 2) (r : RootRow)
    (ω : Cutoff.CutoffSample 2) (hgood : ω ∉ cellFailure M (rootTau r) (waveGateEta (rootWaveTuple r)) Q)
    (J : ℤ) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc (Q.scale+40) J, 0 ≤ weights k ∧ weights k ≤ 1) :
    let x := sensitivityDsharp Q (laterBandW2 Q (Q.scale+40) J weights ω)*
      sensitivityPathLambdaInverse M.nu M.nu_pos (oldResponseCoefficient Q (Q.scale+40) ω)
        (laterResponseCoefficient Q (Q.scale+40) J weights ω) (1/4) 0
    sensitivityB2*x < 1 ∧ x ≤ sensitivityCloc := by
  have ht : 0 ≤ rootTau r := by cases r <;> norm_num [rootTau]
  have hη := (wave_gate_eta_pos (rootWaveTuple r)).le
  have hx := (good_cell_sensitivity_size_bound M Q _ _ ht hη ω hgood J weights hw).trans
    (root_sensitivity_gate_quarter r)
  dsimp only
  constructor
  · have hB0 : 0 ≤ sensitivityB2 := by unfold sensitivityB2; positivity
    have hh := mul_le_mul_of_nonneg_left hx hB0
    have hB := sensitivityB2_lt_45016
    nlinarith only [hh,hB]
  · exact hx.trans (by norm_num [sensitivityCloc])

end
end ASDExplicitGamma.Inverse
