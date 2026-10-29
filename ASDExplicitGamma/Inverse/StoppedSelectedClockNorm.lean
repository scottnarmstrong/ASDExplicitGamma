module

public import ASDExplicitGamma.Inverse.StoppedSelectedRootExactMoment

/-! The exact selected-height Jp clock norm, including its bounded part and full tail. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- The physical root clock at the actual selected height. -/
def selectedHeightClock {Ω : Type*} (γ : ℝ) (H : Ω → ℕ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal ((3:ℝ)^(2*γ*((H ω:ℝ)-38)))

/-- The exact source Jp expression, retaining the complete selected tail. -/
def selectedJp (γ p : ℝ) (H0 : ℕ) : ℝ :=
  ((3:ℝ)^(2*p*γ*((H0:ℝ)-27))+selectedRootExactMoment γ p H0)^(1/p:ℝ)

/-- The tail's index convention agrees exactly with the physical height clock. -/
theorem selected_root_clock_tail_eq {Ω : Type*} (γ : ℝ) (H0 : ℕ) (H : Ω → ℕ) (ω : Ω) :
    selectedRootClockTail γ H0 H ω = if H0+11 < H ω then selectedHeightClock γ H ω else 0 := by
  by_cases hω : H0+11 < H ω
  · have hn : H0+12 ≤ H ω := by omega
    have he : selectedFirstClock H0+((H ω-(H0+12):ℕ):ℝ) = (H ω:ℝ)-38 := by
      rw [Nat.cast_sub hn]
      unfold selectedFirstClock
      push_cast
      ring
    simp only [selectedRootClockTail,hω,ite_true,he,selectedHeightClock]
  · simp only [selectedRootClockTail,hω,ite_false]

/-- Pointwise moment split of the physical selected clock. The bounded part
is paid at Hs; the tail retains the actual selected height. -/
theorem selected_clock_moment_split {Ω : Type*} (γ p : ℝ) (hg : 0 ≤ γ)
    (hp : 0 < p) (H0 : ℕ) (H : Ω → ℕ) (ω : Ω) :
    (selectedHeightClock γ H ω)^p ≤
      ENNReal.ofReal ((3:ℝ)^(2*p*γ*((H0:ℝ)-27)))+(selectedRootClockTail γ H0 H ω)^p := by
  have hpow : (selectedHeightClock γ H ω)^p = ENNReal.ofReal ((3:ℝ)^(2*p*γ*((H ω:ℝ)-38))) := by
    unfold selectedHeightClock
    rw [ENNReal.ofReal_rpow_of_pos (by positivity),← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
    congr 1
    ring_nf
  by_cases hω : H0+11 < H ω
  · rw [selected_root_clock_tail_eq,ite_eq_left hω]
    exact le_add_left le_rfl
  · rw [selected_root_clock_tail_eq,ite_eq_right hω,ENNReal.zero_rpow_of_pos hp,add_zero,hpow]
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
    have hn : H ω ≤ H0+11 := by omega
    have hc : (H ω:ℝ) ≤ (H0:ℝ)+11 := by exact_mod_cast hn
    exact mul_le_mul_of_nonneg_left (by linarith only [hc]) (by positivity : 0 ≤ 2*p*γ)

/-- The actual q3 selected physical root clock obeys the exact full Jp norm
bound. No independence between selection, density, or waves is used. -/
theorem q3_selected_clock_Lp (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h)
    (hg : A.gamma ≤ gammaZero) (Q : TriadicCube 2) (H0 : ℕ) (hH : 333 ≤ H0)
    (τ : ℝ) (hτ : 0 < τ) (t : WaveGateTuple) (q : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (hraw : (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 ≤ q)
    (hpast : ∀ k ≤ Q.scale-(H0:ℤ)+40, nativeInductionState A h k)
    (p : ℝ) (hp : 0 < p) (hp256 : p ≤ 256) :
    eLpNorm (selectedHeightClock A.gamma (q3StoppedHeight A Q H0 τ (waveGateEta t)))
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw A).toMeasure ≤ ENNReal.ofReal (selectedJp A.gamma p H0) := by
  let μ := (Cutoff.cutoffSampleLaw A).toMeasure
  let H := q3StoppedHeight A Q H0 τ (waveGateEta t)
  let C := ENNReal.ofReal ((3:ℝ)^(2*p*A.gamma*((H0:ℝ)-27)))
  have hmH : Measurable H := q3_stopped_height_measurable A Q H0 τ (waveGateEta t)
  have hm : Measurable (selectedHeightClock A.gamma H) :=
    (measurable_of_countable (fun k : ℕ => ENNReal.ofReal ((3:ℝ)^(2*A.gamma*((k:ℝ)-38))))).comp hmH
  have htail := q3_selected_root_tail_exact_moment A h hA hg Q H0 hH τ hτ t q hq0 hq hraw hpast p hp hp256
  have ht0 : 0 ≤ selectedRootExactMoment A.gamma p H0 := by
    unfold selectedRootExactMoment
    apply tsum_nonneg
    intro n
    unfold selectedTailProbability
    positivity
  have hmoment : (∫⁻ ω, (selectedHeightClock A.gamma H ω)^p ∂μ) ≤
      ENNReal.ofReal ((3:ℝ)^(2*p*A.gamma*((H0:ℝ)-27))+selectedRootExactMoment A.gamma p H0) := by
    have hh := lintegral_mono (μ := μ) (selected_clock_moment_split A.gamma p A.shellPrefix.gamma_pos.le hp H0 H)
    change (∫⁻ ω, (selectedHeightClock A.gamma H ω)^p ∂μ) ≤
      ∫⁻ ω, C+(selectedRootClockTail A.gamma H0 H ω)^p ∂μ at hh
    rw [lintegral_add_left measurable_const,lintegral_const,measure_univ,mul_one] at hh
    apply (hh.trans (add_le_add le_rfl htail)).trans_eq
    exact (ENNReal.ofReal_add (by positivity : 0 ≤ (3:ℝ)^(2*p*A.gamma*((H0:ℝ)-27))) ht0).symm
  rw [nonnegative_Lp_moment_formula μ _ hm p hp]
  apply (ENNReal.rpow_le_rpow hmoment (by positivity : (0:ℝ) ≤ 1/p)).trans_eq
  exact ENNReal.ofReal_rpow_of_nonneg
    (add_nonneg (by positivity) ht0) (by positivity)

end
end ASDExplicitGamma.Inverse
