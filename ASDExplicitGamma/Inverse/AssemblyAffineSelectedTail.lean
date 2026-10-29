module

public import ASDExplicitGamma.Inverse.AssemblyWholeRootWaveSeries

/-! Selected tail sums with a linear height moment and a separate constant payment. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- Height-tail selection preserves separate coefficients of the first
height moment and the order/terminal-depth payment. -/
theorem selected_tail_Lp_of_affine_moments
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : Ω → ℕ) (hH : Measurable H) (H0 : ℕ) (hH0 : 333 ≤ H0)
    (γ r : ℝ) (hr : 2 ≤ r) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (f : ℕ → Ω → ℝ) (hf : ∀ n, Measurable (f n))
    (hprob : ∀ n, μ {ω | H ω=H0+12+n} ≤
      ENNReal.ofReal (selectedTailProbability H0 n))
    (hw : ∀ n, eLpNorm (f n) (ENNReal.ofReal (2*r)) μ ≤
      ENNReal.ofReal ((A*(selectedFirstClock H0+(n:ℝ))+B)*
        (3:ℝ)^(4*γ*(selectedFirstClock H0+(n:ℝ))))) :
    let F := fun n => ({ω | H ω=H0+12+n} : Set Ω).indicator (f n)
    (∀ᵐ ω ∂μ, Summable (fun n => ‖F n ω‖)) ∧
      eLpNorm (fun ω => ∑' n, F n ω) (ENNReal.ofReal r) μ ≤
        ENNReal.ofReal (A*selectedWaveExactTail γ r H0 (1:Fin 2)+
          B*selectedWaveExactTail γ r H0 (0:Fin 2)) := by
  let F := fun n => ({ω | H ω=H0+12+n} : Set Ω).indicator (f n)
  let b0 := fun n : ℕ => (3:ℝ)^(4*γ*(selectedFirstClock H0+(n:ℝ)))*
    (selectedTailProbability H0 n)^(1/(2*r):ℝ)
  let b1 := fun n : ℕ => (selectedFirstClock H0+(n:ℝ))*b0 n
  let b := fun n : ℕ =>
    (A*(selectedFirstClock H0+(n:ℝ))+B)*
      (3:ℝ)^(4*γ*(selectedFirstClock H0+(n:ℝ)))*
        (selectedTailProbability H0 n)^(1/(2*r):ℝ)
  have hr0 : 0 < r := by linarith only [hr]
  have hz (n : ℕ) : 0 ≤ selectedFirstClock H0+(n:ℝ) := by
    have hh : (333:ℝ) ≤ H0 := by exact_mod_cast hH0
    unfold selectedFirstClock
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith only [hh,hn]
  have hp0 (n : ℕ) : 0 ≤ selectedTailProbability H0 n := by
    unfold selectedTailProbability
    exact (Real.exp_pos _).le
  have hb0 (n : ℕ) : 0 ≤ b0 n := by
    have hn := hz n
    have hp := hp0 n
    dsimp only [b0]
    positivity
  have hb1 (n : ℕ) : 0 ≤ b1 n := by
    dsimp only [b1]
    exact mul_nonneg (hz n) (hb0 n)
  have hb (n : ℕ) : 0 ≤ b n := by
    have hn := hz n
    have hp := hp0 n
    dsimp only [b]
    positivity
  have hE (n : ℕ) : MeasurableSet {ω | H ω=H0+12+n} :=
    hH (measurableSet_singleton _)
  have hF (n : ℕ) : Measurable (F n) := (hf n).indicator (hE n)
  have hbound (n : ℕ) : eLpNorm (F n) (ENNReal.ofReal r) μ ≤
      ENNReal.ofReal (b n) := by
    have hzn := hz n
    have hh := indicator_holder μ (f n) (hf n).aestronglyMeasurable
      {ω | H ω=H0+12+n} (hE n) r (by linarith only [hr])
    have hpow := ENNReal.rpow_le_rpow (hprob n)
      (by positivity : (0:ℝ) ≤ 1/(2*r))
    rw [ENNReal.ofReal_rpow_of_pos
      (by unfold selectedTailProbability; positivity)] at hpow
    apply (hh.trans (mul_le_mul (hw n) hpow
      (zero_le : (0:ℝ≥0∞)≤_) (zero_le : (0:ℝ≥0∞)≤_))).trans_eq
    rw [← ENNReal.ofReal_mul
      (show 0 ≤ (A*(selectedFirstClock H0+(n:ℝ))+B)*
        (3:ℝ)^(4*γ*(selectedFirstClock H0+(n:ℝ))) by positivity)]
  have hseries0 := physical_selected_exact_tail_summable γ r H0 hr0 hH0 (0:Fin 2)
  have hseries1 := physical_selected_exact_tail_summable γ r H0 hr0 hH0 (1:Fin 2)
  have hs0 : HasSum b0 (selectedWaveExactTail γ r H0 (0:Fin 2)) := by
    simpa only [b0,selectedWaveExactTail,Fin.val_zero,pow_zero,one_mul] using
      hseries0.hasSum
  have hs1 : HasSum b1 (selectedWaveExactTail γ r H0 (1:Fin 2)) := by
    simpa only [b1,b0,selectedWaveExactTail,Fin.val_one,pow_one,mul_assoc] using
      hseries1.hasSum
  have hs : HasSum b
      (A*selectedWaveExactTail γ r H0 (1:Fin 2)+
        B*selectedWaveExactTail γ r H0 (0:Fin 2)) := by
    convert (hs1.mul_left A).add (hs0.mul_left B) using 1
    funext n
    dsimp only [b,b0,b1]
    ring
  exact countable_density_series_Lp μ (ENNReal.ofReal r)
    (ENNReal.one_le_ofReal.mpr (by linarith only [hr])) F hF b hb _ hs hbound

end
end ASDExplicitGamma.Inverse
