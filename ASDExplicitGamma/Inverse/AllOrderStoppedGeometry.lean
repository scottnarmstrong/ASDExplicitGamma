module

public import ASDExplicitGamma.Inverse.RestrictionReset
public import ASDExplicitGamma.Inverse.CompatibleEnergyGluing
public import ASDExplicitGamma.Inverse.StoppedDiameterLp
public import ASDExplicitGamma.Inverse.StoppedQ3Height
public import ASDExplicitGamma.Numerics.Wave.Gates
public import ASDExplicitGamma.Numerics.Inverse.RealBounds
import Mathlib.Tactic.NormNum

/-! Root-relative Whitney depths and the all-order stopped geometry adapters. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal

/-- The layer depth is the common DIAG mesh depth used by the Whitney
partition and the loading-independent compatible interpolant. -/
theorem layer_depth_eq_compatible_mesh (H i : ℕ) :
    layerDepth H i = compatibleWhitneyMeshDepth H i := by
  unfold layerDepth layerProfile compatibleWhitneyMeshDepth whitneyProfile
  omega

/-- A cell of layer `i` has the source root-relative side `l-r_i`. -/
theorem whitney_layer_cell_scale (l : ℤ) (H i : ℕ) {Q : TriadicCube 2}
    (hQ : Q ∈ bankWhitneyLayer l H i) :
    Q.scale = l - (layerDepth H i : ℤ) := by
  rw [layer_depth_eq_compatible_mesh]
  exact whitney_layer_mesh_scale l H i hQ

/-- The root-relative source offset `x_{i,h}=f_i+h-38`. -/
def layerRelativeOffset (h i : ℕ) : ℕ := layerProfile i + h - 38

/-- The fine-layer old cutoff has exactly the source `l-1-x_{i,h}` form. -/
theorem layer_old_cutoff_eq_source_offset (l : ℤ) (h i : ℕ)
    (hh : 377 ≤ h) (hi : 1 ≤ i) :
    layerOldCutoff l h i =
      l - 1 - (layerRelativeOffset h i : ℤ) := by
  unfold layerOldCutoff layerDepth layerRelativeOffset layerProfile
  push_cast
  omega

/-- The three contained-cube resolutions retain the source all-order label
margin `r_i-40-e ≥ 340+12k`. -/
theorem layer_buffer_margin_at_order (k h i e : ℕ)
    (hh : heightEntrance k ≤ h) (hi : 1 ≤ i) (he : e ≤ 2) :
    340 + 12 * k ≤ layerDepth h i - 40 - e := by
  have hprofile : 2 ≤ layerProfile i := by
    unfold layerProfile
    omega
  unfold heightEntrance layerDepth at *
  omega

/- The source tail starts at layer depth `H+5`: the first Whitney profile is
`f₁=2`, and `r₁,H=H+5`.  The generic stopped-height theorem counts the full
`3^(2(H+5))` starting population, so this shift is already covered by its
source union bound. -/

def resetAllOrderTau : ℝ := (Numerics.Wave.allOrderTau : ℝ)

def allOrderDensity : ℚ := 65 / 10^135

theorem all_order_density_covers_raw :
    (364 * 3^80 : ℝ) * (3 * (61 / 10 : ℝ) / resetAllOrderTau)^12 ≤
      (allOrderDensity : ℝ) := by
  norm_num [allOrderDensity, resetAllOrderTau, Numerics.Wave.allOrderTau]

theorem all_order_density_floor :
    Real.exp (-6000) < (allOrderDensity : ℝ) := by
  apply Numerics.Inverse.inv_density_floor
  norm_num [allOrderDensity]

theorem all_order_density_small :
    (allOrderDensity : ℝ) ≤ 1 / 10000000000 := by
  norm_num [allOrderDensity]

theorem q3_mark_control_at_order (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (p : ℝ) (_hp : 2 ≤ p)
    (hpast : ∀ n : ℤ,
      n ≤ Q.scale - 342 - 12 * orderBand p → nativeInductionState M h n)
    (m : ℕ) (hm : heightEntrance (orderBand p) + 5 ≤ m) :
    PlanarMarkControl (Cutoff.cutoffSampleLaw M).toMeasure
      (q3PlanarMarks M (Q.scale - (m : ℤ)) resetAllOrderTau
        (waveGateEta .allOrder)) (allOrderDensity : ℝ) := by
  have hτ : 0 < resetAllOrderTau := by
    norm_num [resetAllOrderTau, Numerics.Wave.allOrderTau]
  have hm' : 382 + 12 * orderBand p ≤ m := by
    unfold heightEntrance at hm
    omega
  have hmZ : (382 : ℤ) + 12 * (orderBand p : ℤ) ≤ (m : ℤ) := by
    exact_mod_cast hm'
  have hlabel : Q.scale - (m : ℤ) + 40 ≤
      Q.scale - 342 - 12 * orderBand p := by
    omega
  have hpast' : ∀ n : ℤ, n ≤ (Q.scale - (m : ℤ)) + 40 →
      nativeInductionState M h n := by
    intro n hn
    exact hpast n (hn.trans hlabel)
  exact q3_mark_control M h hM hγ (Q.scale - (m : ℤ)) resetAllOrderTau hτ
    .allOrder (allOrderDensity : ℝ) all_order_density_covers_raw hpast'

def q3PlanarMarkFamily (M : ABKModel 2) (Q : TriadicCube 2) (m : ℕ) :
    PlanarMarks (Cutoff.CutoffSample 2) :=
  q3PlanarMarks M (Q.scale - (m : ℤ)) resetAllOrderTau (waveGateEta .allOrder)

/-- The all-order selected stopping index counts the complete fine grid at
depth `H+5`, matching the first layer's actual old label `l-H-5+40`. -/
noncomputable def resetQ3StoppedHeight (M : ABKModel 2) (Q : TriadicCube 2) (k : ℕ) :
    Cutoff.CutoffSample 2 → ℕ :=
  planarStoppedHeight (heightEntrance k + 5)
    (q3PlanarMarkFamily M Q) (rootBlockStart Q)

/-- The selected layer height is the fine-grid stopping index with its
five fixed first-layer generations removed. -/
noncomputable def q3SelectedHeight (M : ABKModel 2) (Q : TriadicCube 2) (k : ℕ) :
    Cutoff.CutoffSample 2 → ℕ :=
  fun ω => resetQ3StoppedHeight M Q k ω - 5

theorem q3_selected_height_ge (M : ABKModel 2) (Q : TriadicCube 2)
    (k : ℕ) (ω : Cutoff.CutoffSample 2) :
    heightEntrance k ≤ q3SelectedHeight M Q k ω := by
  have hs := planar_stopped_height_ge (heightEntrance k + 5)
    (q3PlanarMarkFamily M Q) (rootBlockStart Q) ω
  unfold q3SelectedHeight resetQ3StoppedHeight at *
  omega

theorem q3_selected_height_tail_at_order (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p)
    (hpast : ∀ n : ℤ,
      n ≤ Q.scale - 342 - 12 * orderBand p → nativeInductionState M h n)
      (H : ℕ) (hH : heightEntrance (orderBand p) ≤ H) :
    (Cutoff.cutoffSampleLaw M).toMeasure.real
      {ω | H < q3SelectedHeight M Q (orderBand p) ω} ≤
        Real.exp (-heightExponent H / 32) := by
  let B := q3PlanarMarkFamily M Q
  have hB : ∀ m, heightEntrance (orderBand p) + 5 ≤ m →
      PlanarMarkControl (Cutoff.cutoffSampleLaw M).toMeasure (B m)
        (allOrderDensity : ℝ) := by
    intro m hm
    exact q3_mark_control_at_order M h hM hγ Q p hp hpast m hm
  have htail := planar_stopped_height_tail
    (Cutoff.cutoffSampleLaw M).toMeasure (heightEntrance (orderBand p) + 5)
    (by unfold heightEntrance; omega) B (allOrderDensity : ℝ)
    (by norm_num [allOrderDensity]) all_order_density_small hB (rootBlockStart Q)
    (H + 5) (by
      have hH' : 377 + 12 * orderBand p ≤ H := by simpa [heightEntrance] using hH
      omega)
  have hevent : {ω | H < q3SelectedHeight M Q (orderBand p) ω} =
      {ω | H + 5 < resetQ3StoppedHeight M Q (orderBand p) ω} := by
    ext ω
    have hs := planar_stopped_height_ge
      (heightEntrance (orderBand p) + 5) B (rootBlockStart Q) ω
    change (H < planarStoppedHeight (heightEntrance (orderBand p) + 5)
      B (rootBlockStart Q) ω - 5) ↔
      H + 5 < planarStoppedHeight (heightEntrance (orderBand p) + 5)
        B (rootBlockStart Q) ω
    omega
  have hpow : heightExponent H ≤ heightExponent (H + 5) := by
    rw [height_exponent_add]
    have hg := Numerics.Inverse.inv_quarter_growth.le
    have hfactor : 1 ≤ ((3 : ℝ)^(1/4:ℝ))^5 := by
      have hroot : 0 ≤ (3 : ℝ)^(1/4:ℝ) := by positivity
      exact one_le_pow₀ (by nlinarith [hg])
    have hnonneg : 0 ≤ heightExponent H := by
      unfold heightExponent
      positivity
    nlinarith
  have harg : -heightExponent (H + 5) / 32 ≤
      -heightExponent H / 32 := by
    linarith
  rw [hevent]
  exact htail.trans (Real.exp_le_exp.mpr harg)

end ASDExplicitGamma.Inverse
