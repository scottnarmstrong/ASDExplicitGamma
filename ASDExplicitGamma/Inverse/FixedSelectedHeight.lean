module

public import ASDExplicitGamma.Inverse.RootDefinitions

/-! One fixed-row interface for the actual selected-height source estimates.
Every height, atom and complete tail is the actual q3 construction. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal
noncomputable section

/-- The actual source selected height used by every fixed row. -/
def rootSelectedHeight (M : ABKModel 2) (Q : TriadicCube 2) (r : RootRow) :
    Cutoff.CutoffSample 2 → ℕ :=
  q3StoppedHeight M Q (rootH0 r) (rootTau r) (waveGateEta (rootWaveTuple r))

/-- Exact fixed-height output: twelve bounded heights, every source tail
atom, J_p, the literal full root-tail moment and the global/local tiny cap. -/
def FixedSelectedHeightConclusion (M : ABKModel 2) (Q : TriadicCube 2) (r : RootRow) : Prop :=
  let H0 := rootH0 r
  let H := rootSelectedHeight M Q r
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  Measurable H ∧ (∀ ω, H0 ≤ H ω) ∧ (selectedCandidateHeights H0).card=12 ∧
    (∀ n : ℕ, μ.real {ω | H ω=H0+12+n} ≤ selectedTailProbability H0 n) ∧
    ∀ p : ℝ, 2 ≤ p → p ≤ 256 →
      eLpNorm (selectedHeightClock M.gamma H) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (selectedJp M.gamma p H0) ∧
      eLpNorm (selectedRootClockTail M.gamma H0 H) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (selectedRootTiny H0) ∧
      (∫⁻ ω, (selectedRootClockTail M.gamma H0 H ω)^p ∂μ) ≤
        ENNReal.ofReal (selectedRootExactMoment M.gamma p H0)

private theorem inverse_density_inputs :
    0 ≤ (Numerics.Inverse.invInverseQ:ℝ) ∧ (Numerics.Inverse.invInverseQ:ℝ) ≤ 1/10000000000 ∧
      (364*3^80:ℝ)*(3*(61/10:ℝ)/10000000000)^12 ≤ (Numerics.Inverse.invInverseQ:ℝ) := by
  have hq0 := ((Real.exp_pos (-6000)).trans Numerics.Inverse.inv_inverse_density_floor).le
  have hcap := (Rat.cast_lt (K := ℝ)).mpr Numerics.Inverse.invInverse_density.2.2
  norm_num only [Rat.cast_div,Rat.cast_pow,Rat.cast_one,Rat.cast_ofNat] at hcap
  have hraw := (Rat.cast_le (K := ℝ)).mpr Numerics.Inverse.invInverse_density.1
  dsimp only [Numerics.Inverse.invInverseQraw,Numerics.Inverse.invInverseTau] at hraw
  push_cast at hraw
  exact ⟨hq0,hcap.le,hraw⟩

private theorem full_density_inputs :
    0 ≤ (Numerics.Inverse.invFullQ:ℝ) ∧ (Numerics.Inverse.invFullQ:ℝ) ≤ 1/10000000000 ∧
      (364*3^80:ℝ)*(3*(61/10:ℝ)/5000000000000000)^12 ≤ (Numerics.Inverse.invFullQ:ℝ) := by
  have hq0 := ((Real.exp_pos (-6000)).trans Numerics.Inverse.inv_full_density_floor).le
  have hcap := (Rat.cast_lt (K := ℝ)).mpr Numerics.Inverse.invFull_density.2.2
  norm_num only [Rat.cast_div,Rat.cast_pow,Rat.cast_one,Rat.cast_ofNat] at hcap
  have hraw := (Rat.cast_le (K := ℝ)).mpr Numerics.Inverse.invFull_density.1
  dsimp only [Numerics.Inverse.invFullQraw,Numerics.Inverse.invFullTau] at hraw
  push_cast at hraw
  exact ⟨hq0,hcap.le,hraw⟩

theorem root_row_density_inputs (r : RootRow) :
    0 ≤ rootQ r ∧ rootQ r ≤ 1/10000000000 ∧
      (364*3^80:ℝ)*(3*(61/10:ℝ)/rootTau r)^12 ≤ rootQ r := by
  cases r with
  | globalInverse => exact inverse_density_inputs
  | localInverse => exact inverse_density_inputs
  | firstLocal => exact inverse_density_inputs
  | full => exact full_density_inputs

/-- The fixed-row root-clock interface. Actual W₀/W₁
estimates are supplied separately by physical_selected_wave_Lp. No height,
wave or density independence premise is used. -/
theorem q3_fixed_selected_height
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (r : RootRow)
    (hpast : ∀ k ≤ Q.scale-(rootH0 r:ℤ)+40, nativeInductionState M h k) :
    FixedSelectedHeightConclusion M Q r := by
  have hH : rootH0 r=333 ∨ rootH0 r=377 := by cases r <;> decide
  have hH0 : 333 ≤ rootH0 r := by omega
  have hτ : 0 < rootTau r := by cases r <;> norm_num [rootTau]
  obtain ⟨hq0,hq,hraw⟩ := root_row_density_inputs r
  refine ⟨q3_stopped_height_measurable M Q _ _ _,
    q3_stopped_height_ge M Q _ _ _,selected_candidate_heights_card _,?_,?_⟩
  · intro n
    exact q3_selected_height_atom M h hM hg Q _ hH0 _ hτ _ (rootQ r) hq0 hq hraw hpast n
  · intro p hp hp256
    have hp0 : 0 < p := by linarith only [hp]
    exact ⟨q3_selected_clock_Lp M h hM hg Q _ hH0 _ hτ _ (rootQ r) hq0 hq hraw hpast p hp0 hp256,
      q3_selected_root_tail_tiny M h hM hg Q _ hH _ hτ _ (rootQ r) hq0 hq hraw hpast p hp256,
      q3_selected_root_tail_exact_moment M h hM hg Q _ hH0 _ hτ _ (rootQ r) hq0 hq hraw hpast p hp0 hp256⟩

end
end ASDExplicitGamma.Inverse
