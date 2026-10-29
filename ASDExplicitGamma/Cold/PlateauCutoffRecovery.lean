module

public import ASDExplicitGamma.Cold.ColdRecoveryFamily
public import ASDExplicitGamma.Cold.PlateauRecoveryAlgebra

/-! # CO-PLATEAU-P4: actual cutoff recovery under integrated-energy stationarity -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- Stationarity is used only for the actual integrated own-cell energies, via their exact
trace identity. It is never asserted for energy density inside a cell. -/
theorem expected_own_cell_cutoff_lower {Q : TriadicCube 2} {r : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {ℙ : Measure Ω} (F : ColdRecoveryFamily Q r Ω)
    (hInt : ColdRecoveryIntegrable F ℙ) (hr : r = 4) {μ : ℝ}
    (hstationary : ∀ R, ∫ ω, F.cellTrace R ω ∂ℙ = μ) :
    2*(7/8)*μ ≤ ∫ ω, squareCellMean Q r (fun R => F.cellCutoffEnergy R ω) ∂ℙ := by
  have hcell (R : SquareCells Q r) :
      2*(cubeAverage R.val (plateauOnSquare Q)-(1/8 : ℝ))*μ ≤ ∫ ω, F.cellCutoffEnergy R ω ∂ℙ := by
    have h := integral_mono_ae ((hInt.cellTrace R).const_mul
      (2*(cubeAverage R.val (plateauOnSquare Q)-(1/8 : ℝ)))) (hInt.cellCutoffEnergy R)
      (Filter.Eventually.of_forall (F.cellCutoffEnergy_lower hr R))
    rw [integral_const_mul,hstationary R] at h
    exact h
  have h := squareCellMean_mono Q r hcell
  rw [integral_squareCellMean Q r hInt.cellCutoffEnergy]
  have heq : squareCellMean Q r (fun R => 2*(cubeAverage R.val (plateauOnSquare Q)-(1/8 : ℝ))*μ) =
      2*(7/8)*μ := by
    have hh : (fun R : SquareCells Q r => 2*(cubeAverage R.val (plateauOnSquare Q)-(1/8 : ℝ))*μ) =
        (fun R => (2*μ)*(cubeAverage R.val (plateauOnSquare Q)-(1/8 : ℝ))) := by funext R; ring
    rw [hh,squareCellMean_mul,squareCellMean_plateau_comparison_weights]
    ring
  rw [heq] at h
  exact h

/-- Expectation of the genuine pathwise optimizer comparison, using only ordinary integrated
source quantities and source stationarity of the cell trace defects. -/
theorem expected_partition_cutoff_recovery {Q : TriadicCube 2} {r : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {ℙ : Measure Ω} (F : ColdRecoveryFamily Q r Ω)
    (hInt : ColdRecoveryIntegrable F ℙ) {c μ : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (hstationary : ∀ R, ∫ ω, F.cellTrace R ω ∂ℙ = μ) :
    (1-c)*(∫ ω, squareCellMean Q r (fun R => F.cellCutoffEnergy R ω) ∂ℙ) -
      (1/c-1)*(12/7)*(2*(μ-∫ ω, F.parentTrace ω ∂ℙ)) ≤
      ∫ ω, F.parentCutoffEnergy ω ∂ℙ := by
  have hW := integrable_squareCellMean Q r hInt.cellCutoffEnergy
  have hT := integrable_squareCellMean Q r hInt.cellTrace
  have hdiff : Integrable (fun ω => squareCellMean Q r (fun R => F.cellTrace R ω)-F.parentTrace ω) ℙ :=
    hT.sub hInt.parentTrace
  have hpoint (ω : Ω) := square_matched_partition_cutoff_recovery Q (F.elliptic ω) hc hc1 (F.parent ω) (F.cells ω)
  have h := integral_mono_ae ((hW.const_mul (1-c)).sub (hdiff.const_mul ((1/c-1)*(12/7)*2)))
    hInt.parentCutoffEnergy (Filter.Eventually.of_forall (fun ω => by
      change (1-c)*squareCellMean Q r (fun R => F.cellCutoffEnergy R ω) -
        ((1/c-1)*(12/7)*2)*(squareCellMean Q r (fun R => F.cellTrace R ω)-F.parentTrace ω) ≤
        F.parentCutoffEnergy ω
      dsimp only [ColdRecoveryFamily.cellTrace,ColdRecoveryFamily.parentTrace,
        ColdRecoveryFamily.cellCutoffEnergy,ColdRecoveryFamily.parentCutoffEnergy]
      convert hpoint ω using 1
      ring))
  change (∫ ω, (1-c)*squareCellMean Q r (fun R => F.cellCutoffEnergy R ω) -
    ((1/c-1)*(12/7)*2)*(squareCellMean Q r (fun R => F.cellTrace R ω)-F.parentTrace ω) ∂ℙ) ≤ _ at h
  rw [integral_sub (hW.const_mul _) (hdiff.const_mul _),integral_const_mul,integral_const_mul,
    integral_sub hT hInt.parentTrace,integral_squareCellMean Q r hInt.cellTrace] at h
  simp_rw [hstationary] at h
  rw [squareCellMean_const] at h
  convert h using 1
  ring

/-- CO-PLATEAU-P4. The displayed main mean is the actual terminal
ordinary trace mean. Only source stationarity of integrated own-cell traces is assumed;
all projection-gap and cutoff inequalities have been proved from actual optimizers. -/
theorem plateau_cutoff_recovery {Q : TriadicCube 2} {r : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {ℙ : Measure Ω} (F : ColdRecoveryFamily Q r Ω)
    (hInt : ColdRecoveryIntegrable F ℙ) (hr : r = 4) {c μsmall : ℝ}
    (hc : 0 < c) (hc1 : c < 1)
    (hstationary : ∀ R, ∫ ω, F.cellTrace R ω ∂ℙ = μsmall) :
    2*(1-c)*(7/8)*(∫ ω, F.parentTrace ω ∂ℙ) -
      2*((1/c-1)*(12/7)-(1-c)*(7/8))*(μsmall-∫ ω, F.parentTrace ω ∂ℙ) ≤
      ∫ ω, F.parentCutoffEnergy ω ∂ℙ := by
  have hlower := expected_own_cell_cutoff_lower F hInt hr hstationary
  have hpath := expected_partition_cutoff_recovery F hInt hc hc1 hstationary
  have hm := mul_le_mul_of_nonneg_left hlower (by linarith : 0 ≤ 1-c)
  apply plateau_recovery_lower_bound
  linarith only [hm,hpath]

/-- The consequent source constants are exactly `C_T=4/[7(1-c)]`, `C_D=96/(49c)-1`. -/
theorem plateau_cutoff_recovery_constants {Q : TriadicCube 2} {r : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {ℙ : Measure Ω} (F : ColdRecoveryFamily Q r Ω)
    (hInt : ColdRecoveryIntegrable F ℙ) (hr : r = 4) {c μsmall : ℝ}
    (hc : 0 < c) (hc1 : c < 1)
    (hstationary : ∀ R, ∫ ω, F.cellTrace R ω ∂ℙ = μsmall) :
    (∫ ω, F.parentTrace ω ∂ℙ) ≤
      (4/(7*(1-c)))*(∫ ω, F.parentCutoffEnergy ω ∂ℙ) +
      (96/(49*c)-1)*(μsmall-∫ ω, F.parentTrace ω ∂ℙ) :=
  plateau_recovery_constants hc hc1 (plateau_cutoff_recovery F hInt hr hc hc1 hstationary)

end ASDExplicitGamma.Cold
