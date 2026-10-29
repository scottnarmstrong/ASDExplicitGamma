module

public import ASDExplicitGamma.Inverse.SelectedTail

/-! Complete physical W₀/W₁ bounds at the exact selected layer height. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- The complete infinite tail of the actual selected physical wave.
The order r may be p, 2p, or 4p without changing the protected past or height. -/
theorem selected_physical_tail_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p)
    (hpast : ∀ n : ℤ,
      n ≤ Q.scale-342-12*orderBand p → nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (a c : ℝ)
    (weights : (ℕ × ℕ) → ℤ → ℝ)
    (hw : ∀ hk, ∀ k ∈ Finset.Ioc
      (physicalResetOldLabel Q (heightEntrance (orderBand p)) hk) N,
      0 ≤ weights hk k ∧ weights hk k ≤ 1)
    (layer : ℕ) (j : Fin 2) (r : ℝ) (hr : 2 ≤ r) :
    let H0 := heightEntrance (orderBand p)
    let H := q3SelectedHeight M Q (orderBand p)
    let F := fun n => ({ω | H ω=H0+12+n} : Set (Cutoff.CutoffSample 2)).indicator
      (physicalHeightWeightedWave M Q N H0 a c weights layer j (H0+12+n))
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, Summable (fun n => ‖F n ω‖)) ∧
      eLpNorm (fun ω => ∑' n, F n ω) (ENNReal.ofReal r)
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (40*(4*r+2)*selectedWaveExactTail M.gamma r H0 j) := by
  let H0 := heightEntrance (orderBand p)
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hH0 : 333 ≤ H0 := by unfold H0 heightEntrance; omega
  have hpast' : ∀ n ≤ Q.scale-(H0:ℤ)+35, nativeInductionState M h n := by
    intro n hn
    apply hpast n
    unfold H0 heightEntrance at hn
    omega
  have hprob (n : ℕ) : μ {ω | q3SelectedHeight M Q (orderBand p) ω=H0+12+n} ≤
      ENNReal.ofReal (selectedTailProbability H0 n) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    exact ENNReal.ofReal_le_ofReal (selected_height_atom M h hM hγ Q p hp hpast n)
  have hOrdinary (n : ℕ) :
      eLpNorm (physicalHeightWeightedWave M Q N H0 a c weights layer j (H0+12+n))
        (ENNReal.ofReal (2*r)) μ ≤
      ENNReal.ofReal (40*(4*r+2)*(selectedFirstClock H0+(n:ℝ))^j.val*
        (3:ℝ)^(4*M.gamma*(selectedFirstClock H0+(n:ℝ)))) := by
    have hh := physical_height_weighted_wave_Lp M h hM Q N hN H0 hH0 hpast'
      a c weights hw layer j (H0+12+n) (by omega) (2*r) (by linarith only [hr])
    have hclock : ((H0+12+n:ℕ):ℝ)-38 = selectedFirstClock H0+(n:ℝ) := by
      unfold selectedFirstClock
      push_cast
      ring
    rw [hclock] at hh
    have hz : 0 ≤ selectedFirstClock H0+(n:ℝ) := by
      have hreal : (333:ℝ) ≤ H0 := by exact_mod_cast hH0
      unfold selectedFirstClock
      have hn := Nat.cast_nonneg (α := ℝ) n
      linarith only [hreal,hn]
    exact hh.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (show 40*(2*r+2) ≤ 40*(4*r+2) by linarith only [hr])
          (pow_nonneg hz _)) (by positivity)))
  exact selected_tail_Lp_of_moments μ _
    (selected_height_measurable M Q (orderBand p)) H0 hH0 M.gamma r hr j
    (fun n => physicalHeightWeightedWave M Q N H0 a c weights layer j (H0+12+n))
    (fun n => physical_height_weighted_wave_measurable M Q N H0 a c weights layer j _)
    hprob hOrdinary

/-- Both the twelve candidates and every later atom are retained for the
actual selected layer height, at all finite orders on the same band. -/
theorem selected_physical_wave_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p)
    (hpast : ∀ n : ℤ,
      n ≤ Q.scale-342-12*orderBand p → nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (a c : ℝ)
    (weights : (ℕ × ℕ) → ℤ → ℝ)
    (hw : ∀ hk, ∀ k ∈ Finset.Ioc
      (physicalResetOldLabel Q (heightEntrance (orderBand p)) hk) N,
      0 ≤ weights hk k ∧ weights hk k ≤ 1)
    (layer : ℕ) (j : Fin 2) (r : ℝ) (hr : 2 ≤ r) :
    let H0 := heightEntrance (orderBand p)
    let H := q3SelectedHeight M Q (orderBand p)
    eLpNorm (fun ω => physicalHeightWeightedWave M Q N H0 a c weights layer j (H ω) ω)
      (ENNReal.ofReal r) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (physicalSelectedWaveExactBudget M.gamma r H0 j) := by
  let H0 := heightEntrance (orderBand p)
  let H := q3SelectedHeight M Q (orderBand p)
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let f := physicalHeightWeightedWave M Q N H0 a c weights layer j
  let B := 40*(2*r+2)*((H0:ℝ)-27)^j.val*(3:ℝ)^(4*M.gamma*((H0:ℝ)-27))
  have hH0 : 333 ≤ H0 := by unfold H0 heightEntrance; omega
  have hreal : (333:ℝ) ≤ H0 := by exact_mod_cast hH0
  have hz : (0:ℝ) ≤ (H0:ℝ)-27 := by linarith only [hreal]
  have hpast' : ∀ n ≤ Q.scale-(H0:ℤ)+35, nativeInductionState M h n := by
    intro n hn
    apply hpast n
    unfold H0 heightEntrance at hn
    omega
  have hfinite := selected_twelve_candidate_Lp μ H
    (selected_height_measurable M Q (orderBand p)) H0 f
    (fun H => physical_height_weighted_wave_measurable M Q N H0 a c weights layer j H)
    r (by linarith only [hr]) (ENNReal.ofReal B)
    (fun t ht => physical_height_wave_candidate_Lp M h hM Q N hN H0 hH0
      hpast' a c weights hw layer j t ht r hr)
  have hfinite' : eLpNorm (selectedBoundedFamily H (selectedCandidateHeights H0) f)
      (ENNReal.ofReal r) μ ≤ ENNReal.ofReal (physicalSelectedWaveFiniteBudget M.gamma r H0 j) := by
    apply hfinite.trans_eq
    have hroot : (12:ℝ≥0∞)^(1/r:ℝ) = ENNReal.ofReal ((12:ℝ)^(1/r:ℝ)) := by
      simpa only [ENNReal.ofReal_ofNat] using
        ENNReal.ofReal_rpow_of_pos (p := (1/r:ℝ)) (by norm_num : (0:ℝ) < 12)
    rw [hroot, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (12:ℝ)^(1/r:ℝ))]
    congr 1
    unfold physicalSelectedWaveFiniteBudget
    dsimp only [B]
    ring
  have htail := (selected_physical_tail_Lp M h hM hγ Q p hp hpast N hN
    a c weights hw layer j r hr).2
  have he := selected_real_family_eq H H0 (q3_selected_height_ge M Q _) f
  change eLpNorm (fun ω => f (H ω) ω) (ENNReal.ofReal r) μ ≤
    ENNReal.ofReal (physicalSelectedWaveExactBudget M.gamma r H0 j)
  rw [he]
  apply (eLpNorm_add_le (ENNReal.one_le_ofReal.mpr (by linarith only [hr]))).trans
  apply (add_le_add hfinite' htail).trans_eq
  have hfinite0 : 0 ≤ physicalSelectedWaveFiniteBudget M.gamma r H0 j := by
    unfold physicalSelectedWaveFiniteBudget
    positivity
  have htail0 : 0 ≤ 40*(4*r+2)*selectedWaveExactTail M.gamma r H0 j := by
    apply mul_nonneg (by positivity)
    unfold selectedWaveExactTail
    apply tsum_nonneg
    intro n
    have hclock : 0 ≤ selectedFirstClock H0+(n:ℝ) := by
      unfold selectedFirstClock
      have hn := Nat.cast_nonneg (α := ℝ) n
      linarith only [hreal,hn]
    have hprob : 0 ≤ selectedTailProbability H0 n := by
      unfold selectedTailProbability
      positivity
    positivity
  exact (ENNReal.ofReal_add hfinite0 htail0).symm

end
end ASDExplicitGamma.Inverse
