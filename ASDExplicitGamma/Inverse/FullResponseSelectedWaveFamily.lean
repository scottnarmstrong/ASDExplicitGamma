module

public import ASDExplicitGamma.Inverse.PhysicalGaussianSelectedWave

/-! Reusable correlated height selection for the full-response scalar families. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- The existing twelve-candidate and complete-tail arguments apply to any
actual wave family with the source ordinary moments. Selection need not be
independent of the family. -/
theorem full_response_selected_wave_family_Lp
    (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h)
    (hg : A.gamma ≤ gammaZero) (Q : TriadicCube 2) (H0 : ℕ) (hH : 333 ≤ H0)
    (τ : ℝ) (hτ : 0 < τ) (t : WaveGateTuple) (q : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (hraw : (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 ≤ q)
    (hpast : ∀ k ≤ Q.scale-(H0:ℤ)+40, nativeInductionState A h k)
    (j : Fin 2) (f : ℕ → Cutoff.CutoffSample 2 → ℝ) (hf : ∀ H, Measurable (f H))
    (hmom : ∀ H, H0 ≤ H → ∀ r : ℝ, 2 ≤ r →
      eLpNorm (f H) (ENNReal.ofReal r) (Cutoff.cutoffSampleLaw A).toMeasure ≤
        ENNReal.ofReal (40*(r+2)*((H:ℝ)-38)^j.val*(3:ℝ)^(4*A.gamma*((H:ℝ)-38))))
    (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256) :
    let H := q3StoppedHeight A Q H0 τ (waveGateEta t)
    eLpNorm (fun ω => f (H ω) ω) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw A).toMeasure ≤
      ENNReal.ofReal (physicalSelectedWaveBudget A.gamma p H0 j) := by
  let μ := (Cutoff.cutoffSampleLaw A).toMeasure
  let H := q3StoppedHeight A Q H0 τ (waveGateEta t)
  let B := 40*(2*p+2)*((H0:ℝ)-27)^j.val*(3:ℝ)^(4*A.gamma*((H0:ℝ)-27))
  have h0real : (333:ℝ) ≤ H0 := by exact_mod_cast hH
  have hz0 : (0:ℝ) ≤ (H0:ℝ)-27 := by linarith only [h0real]
  have hb (v : ℕ) (hv : v ∈ selectedCandidateHeights H0) :
      eLpNorm (f v) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal B := by
    have hv' := (selected_candidate_mem H0 v).mp hv
    have hvreal : (H0:ℝ) ≤ v := by exact_mod_cast hv'.1
    have hu : (v:ℝ) ≤ (H0:ℝ)+11 := by exact_mod_cast hv'.2
    have hz : (0:ℝ) ≤ (v:ℝ)-38 := by linarith only [hvreal,h0real]
    have hzz : (v:ℝ)-38 ≤ (H0:ℝ)-27 := by linarith only [hu]
    apply (hmom v hv'.1 p hp).trans
    apply ENNReal.ofReal_le_ofReal
    have hcoef : 40*(p+2) ≤ 40*(2*p+2) := by linarith only [hp]
    have hprod := mul_le_mul hcoef (pow_le_pow_left₀ hz hzz j.val)
      (pow_nonneg hz j.val) (by positivity : 0 ≤ 40*(2*p+2))
    exact mul_le_mul hprod
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
        (mul_le_mul_of_nonneg_left hzz (by have hg0 := A.shellPrefix.gamma_pos; positivity)))
      (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) _) (by positivity)
  have hfinite : eLpNorm (selectedBoundedFamily H (selectedCandidateHeights H0) f)
      (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (physicalSelectedWaveFiniteBudget A.gamma p H0 j) := by
    have hh := selected_twelve_candidate_Lp μ H
      (q3_stopped_height_measurable A Q H0 τ (waveGateEta t)) H0 f hf p
      (by linarith only [hp]) (ENNReal.ofReal B) hb
    apply hh.trans_eq
    have hroot : (12:ℝ≥0∞)^(1/p:ℝ) = ENNReal.ofReal ((12:ℝ)^(1/p:ℝ)) := by
      simpa only [ENNReal.ofReal_ofNat] using
        ENNReal.ofReal_rpow_of_pos (p := (1/p:ℝ)) (by norm_num : (0:ℝ) < 12)
    rw [hroot, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (12:ℝ)^(1/p:ℝ))]
    congr 1
    unfold physicalSelectedWaveFiniteBudget
    dsimp only [B]
    ring
  have hOrdinary (n : ℕ) :
      eLpNorm (f (H0+12+n)) (ENNReal.ofReal (2*p)) μ ≤
        ENNReal.ofReal (40*(4*p+2)*(selectedFirstClock H0+(n:ℝ))^j.val*
          (3:ℝ)^(4*A.gamma*(selectedFirstClock H0+(n:ℝ)))) := by
    have he : ((H0+12+n:ℕ):ℝ)-38 = selectedFirstClock H0+(n:ℝ) := by
      unfold selectedFirstClock
      push_cast
      ring
    have hh := hmom (H0+12+n) (by omega) (2*p) (by linarith only [hp])
    rw [he] at hh
    apply hh.trans
    apply ENNReal.ofReal_le_ofReal
    have hz : 0 ≤ selectedFirstClock H0+(n:ℝ) := by
      have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
      unfold selectedFirstClock
      linarith only [h0real,hn]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show 40*(2*p+2) ≤ 40*(4*p+2) by linarith only [hp])
        (pow_nonneg hz _)) (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) _)
  have htail := q3_selected_wave_exact_from_moments A h hA hg Q H0 hH τ hτ t q
    hq0 hq hraw hpast p hp hp256 j (fun n => f (H0+12+n)) (fun n => hf _) hOrdinary
  have he := selected_real_family_eq H H0
    (fun ω => q3_stopped_height_ge A Q H0 τ (waveGateEta t) ω) f
  have hfinite0 : 0 ≤ physicalSelectedWaveFiniteBudget A.gamma p H0 j := by
    unfold physicalSelectedWaveFiniteBudget
    positivity
  have htail0 : 0 ≤ 40*(4*p+2)*selectedWaveExactTail A.gamma p H0 j := by
    apply mul_nonneg (by positivity)
    unfold selectedWaveExactTail
    apply tsum_nonneg
    intro n
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have hz : 0 ≤ selectedFirstClock H0+(n:ℝ) := by
      unfold selectedFirstClock
      linarith only [h0real,hn]
    have hP : 0 ≤ selectedTailProbability H0 n := by
      unfold selectedTailProbability
      positivity
    positivity
  have hnorm : eLpNorm (fun ω => f (H ω) ω) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (physicalSelectedWaveExactBudget A.gamma p H0 j) := by
    rw [he]
    apply (eLpNorm_add_le (ENNReal.one_le_ofReal.mpr (by linarith only [hp]))).trans
    apply (add_le_add hfinite htail.2).trans_eq
    exact (ENNReal.ofReal_add hfinite0 htail0).symm
  apply hnorm.trans
  apply ENNReal.ofReal_le_ofReal
  unfold physicalSelectedWaveExactBudget physicalSelectedWaveBudget
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (selected_wave_exact_tail_le A.gamma p hg (by linarith only [hp]) hp256 H0 hH j)
    (by positivity))

end
end ASDExplicitGamma.Inverse
