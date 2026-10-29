module

public import ASDExplicitGamma.Cold.ColdPlateauFamily
public import ASDExplicitGamma.Cold.PlateauMatchedTransport
public import ASDExplicitGamma.Cold.NonnegativeSeriesExpectation
public import ASDExplicitGamma.Cold.PlateauSeriesEnvelope

/-! # Expectation of the actual four-load plateau transport series -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
namespace ASDExplicitGamma.Cold

/-- The actual weighted graph series is integrable and commutes with expectation.
Only measurability and the source all-depth history bounds are assumed. -/
theorem ColdPlateauFamily.weightedGraph_expectation {Q : TriadicCube 2} {Ω : Type*}
    [MeasurableSpace Ω] {ℙ : Measure Ω} [IsFiniteMeasure ℙ]
    (F : ColdPlateauFamily Q Ω) {D : Ω → ℝ}
    (hD : Measurable D) (hDn : ∀ᵐ ω ∂ℙ, 0 ≤ D ω)
    (h20 : Integrable (fun ω => D ω^20) ℙ)
    (hV : ∀ k, AEStronglyMeasurable (F.projectedGraph (2*(k+1))) ℙ)
    (hroot : ∀ᵐ ω ∂ℙ, (F.atDepth 0).parentTrace ω ≤ D ω)
    (hmax : ∀ᵐ ω ∂ℙ, ∀ r, ∀ R, (F.atDepth r).cellTrace R ω ≤ (3:ℝ)^((r:ℝ)/4)*D ω) :
    Integrable (fun ω => ∑' k : ℕ, plateauEvenWeight k*F.projectedGraph (2*(k+1)) ω) ℙ ∧
      Summable (fun k => plateauEvenWeight k*(∫ ω, F.projectedGraph (2*(k+1)) ω ∂ℙ)) ∧
      (∫ ω, ∑' k : ℕ, plateauEvenWeight k*F.projectedGraph (2*(k+1)) ω ∂ℙ) =
        ∑' k : ℕ, plateauEvenWeight k*(∫ ω, F.projectedGraph (2*(k+1)) ω ∂ℙ) := by
  have hM : Integrable (fun ω => 1+D ω^2) ℙ :=
    (integrable_const 1).add (integrable_history_square hD hDn h20)
  have h := dominated_nonnegative_series_expectation
    (fun k => (hV k).const_mul (plateauEvenWeight k)) hM
    (b := fun k => plateauEvenWeight k*(8+6*(3:ℝ)^(((2*(k+1):ℕ):ℝ)/4)))
    (fun k => mul_nonneg (plateauEvenWeight_nonneg k) (by positivity))
    summable_plateau_history_envelope
    (Filter.Eventually.of_forall (fun ω k => mul_nonneg (plateauEvenWeight_nonneg k)
      (F.projectedGraph_nonneg _ ω)))
    (show ∀ᵐ ω ∂ℙ, ∀ k, plateauEvenWeight k*F.projectedGraph (2*(k+1)) ω ≤
      (plateauEvenWeight k*(8+6*(3:ℝ)^(((2*(k+1):ℕ):ℝ)/4)))*(1+D ω^2) from by
      filter_upwards [hDn,hroot,hmax] with ω hn hr hm k
      have hb := mul_le_mul_of_nonneg_left
        (F.projectedGraph_history_bound (2*(k+1)) ω hn hr (hm _)) (plateauEvenWeight_nonneg k)
      simpa only [mul_assoc] using hb)
  simpa only [integral_const_mul] using h

/-- The proved pathwise transport estimate passes to the actual cold expectation. -/
theorem expected_plateau_matched_energy_le {Q : TriadicCube 2} {Ω : Type*}
    [MeasurableSpace Ω] {ℙ : Measure Ω} [IsFiniteMeasure ℙ]
    (F : ColdPlateauFamily Q Ω) {D : Ω → ℝ}
    (hD : Measurable D) (hDn : ∀ᵐ ω ∂ℙ, 0 ≤ D ω)
    (h20 : Integrable (fun ω => D ω^20) ℙ)
    (hV : ∀ k, AEStronglyMeasurable (F.projectedGraph (2*(k+1))) ℙ)
    (hroot : ∀ᵐ ω ∂ℙ, (F.atDepth 0).parentTrace ω ≤ D ω)
    (hmax : ∀ᵐ ω ∂ℙ, ∀ r, ∀ R, (F.atDepth r).cellTrace R ω ≤ (3:ℝ)^((r:ℝ)/4)*D ω) :
    (∫ ω, (F.atDepth 0).parentCutoffEnergy ω ∂ℙ) ≤
      ∑' k : ℕ, plateauEvenWeight k*(∫ ω, F.projectedGraph (2*(k+1)) ω ∂ℙ) := by
  obtain ⟨hInt,_,heq⟩ := F.weightedGraph_expectation hD hDn h20 hV hroot hmax
  rw [← heq]
  have hn : ∀ᵐ ω ∂ℙ, 0 ≤ (F.atDepth 0).parentCutoffEnergy ω := by
    exact Filter.Eventually.of_forall (fun ω => by
      change 0 ≤ volumeAverage (openCubeSet Q) (fun x => plateauOnSquare Q x*squareMatchedDensity Q (F.parent ω) x)
      unfold volumeAverage
      apply mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
      exact mul_nonneg (plateauOnSquare_nonneg Q x)
        (squareMatchedDensity_nonneg Q (F.elliptic ω) (F.parent ω) hx))
  exact integral_mono_of_nonneg hn hInt
    (Filter.Eventually.of_forall (fun ω => plateau_matched_energy_le Q (F.elliptic ω) (F.parent ω)))

end ASDExplicitGamma.Cold
