module

public import ASDExplicitGamma.Inverse.SelectedWave

/-! Complete selected tails on the actual layer height. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- Removing the five fixed fine-grid generations preserves measurability. -/
theorem selected_height_measurable (M : ABKModel 2) (Q : TriadicCube 2) (k : ℕ) :
    Measurable (q3SelectedHeight M Q k) := by
  exact (q3_stopped_height_measurable M Q (heightEntrance k+5)
    resetAllOrderTau (waveGateEta .allOrder)).sub_const 5

/-- Every atom in the complete selected tail pays the probability at h-1. -/
theorem selected_height_atom (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p)
    (hpast : ∀ n : ℤ,
      n ≤ Q.scale-342-12*orderBand p → nativeInductionState M h n) (n : ℕ) :
    (Cutoff.cutoffSampleLaw M).toMeasure.real
      {ω | q3SelectedHeight M Q (orderBand p) ω =
        heightEntrance (orderBand p)+12+n} ≤
      selectedTailProbability (heightEntrance (orderBand p)) n := by
  let H0 := heightEntrance (orderBand p)
  have hsub : {ω | q3SelectedHeight M Q (orderBand p) ω=H0+12+n} ⊆
      {ω | H0+11+n < q3SelectedHeight M Q (orderBand p) ω} := by
    intro ω hω
    change q3SelectedHeight M Q (orderBand p) ω=H0+12+n at hω
    change H0+11+n < q3SelectedHeight M Q (orderBand p) ω
    omega
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    (q3_selected_height_tail_at_order M h hM hγ Q p hp hpast _ (by omega))

/-- A complete tail bound from its actual height atoms and ordinary moments.
No independence between the selected height and the observable is used. -/
theorem selected_tail_Lp_of_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H : Ω → ℕ) (hH : Measurable H)
    (H0 : ℕ) (hH0 : 333 ≤ H0) (γ r : ℝ) (hr : 2 ≤ r) (j : Fin 2)
    (f : ℕ → Ω → ℝ) (hf : ∀ n, Measurable (f n))
    (hprob : ∀ n, μ {ω | H ω=H0+12+n} ≤ ENNReal.ofReal (selectedTailProbability H0 n))
    (hw : ∀ n, eLpNorm (f n) (ENNReal.ofReal (2*r)) μ ≤
      ENNReal.ofReal (40*(4*r+2)*(selectedFirstClock H0+(n:ℝ))^j.val*
        (3:ℝ)^(4*γ*(selectedFirstClock H0+(n:ℝ))))) :
    let F := fun n => ({ω | H ω=H0+12+n} : Set Ω).indicator (f n)
    (∀ᵐ ω ∂μ, Summable (fun n => ‖F n ω‖)) ∧
      eLpNorm (fun ω => ∑' n, F n ω) (ENNReal.ofReal r) μ ≤
        ENNReal.ofReal (40*(4*r+2)*selectedWaveExactTail γ r H0 j) := by
  let F := fun n => ({ω | H ω=H0+12+n} : Set Ω).indicator (f n)
  let b := fun n : ℕ => (selectedFirstClock H0+(n:ℝ))^j.val*
    (3:ℝ)^(4*γ*(selectedFirstClock H0+(n:ℝ)))*
      (selectedTailProbability H0 n)^(1/(2*r):ℝ)
  let C := 40*(4*r+2)
  have hr0 : 0 < r := by linarith only [hr]
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hz (n : ℕ) : 0 ≤ selectedFirstClock H0+(n:ℝ) := by
    have hh : (333:ℝ) ≤ H0 := by exact_mod_cast hH0
    unfold selectedFirstClock
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith only [hh,hn]
  have hb0 (n : ℕ) : 0 ≤ b n := by
    have hzn := hz n
    have hprob0 : 0 ≤ selectedTailProbability H0 n := by
      unfold selectedTailProbability
      positivity
    dsimp only [b]
    positivity
  have hE (n : ℕ) : MeasurableSet {ω | H ω=H0+12+n} :=
    hH (measurableSet_singleton _)
  have hF (n : ℕ) : Measurable (F n) := (hf n).indicator (hE n)
  have hbound (n : ℕ) : eLpNorm (F n) (ENNReal.ofReal r) μ ≤ ENNReal.ofReal (C*b n) := by
    have hzn := hz n
    have hh := indicator_holder μ (f n) (hf n).aestronglyMeasurable
      {ω | H ω=H0+12+n} (hE n) r hr0
    have hpow := ENNReal.rpow_le_rpow (hprob n) (by positivity : (0:ℝ) ≤ 1/(2*r))
    rw [ENNReal.ofReal_rpow_of_pos (by unfold selectedTailProbability; positivity)] at hpow
    apply (hh.trans (mul_le_mul (hw n) hpow
      (zero_le : (0:ℝ≥0∞) ≤ _) (zero_le : (0:ℝ≥0∞) ≤ _))).trans_eq
    rw [← ENNReal.ofReal_mul (show 0 ≤ 40*(4*r+2)*(selectedFirstClock H0+(n:ℝ))^j.val*
      (3:ℝ)^(4*γ*(selectedFirstClock H0+(n:ℝ))) by positivity)]
    congr 1
    dsimp only [C,b]
    ring
  have hseries := physical_selected_exact_tail_summable γ r H0 hr0 hH0 j
  have hs : HasSum (fun n => C*b n) (C*∑' n, b n) := hseries.hasSum.mul_left C
  exact countable_density_series_Lp μ (ENNReal.ofReal r)
    (ENNReal.one_le_ofReal.mpr (by linarith only [hr])) F hF (fun n => C*b n)
    (fun n => mul_nonneg hC (hb0 n)) _ hs hbound

end
end ASDExplicitGamma.Inverse
