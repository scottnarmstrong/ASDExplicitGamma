module

public import ASDExplicitGamma.Main.ObsChronoError
public import ASDExplicitGamma.Main.ObsMainRangeNodes
public import ASDExplicitGamma.Main.ShellClock
public import ASDExplicitGamma.Main.AffineFlatBoundary
public import ASDExplicitGamma.Main.EnvelopeSigns
public import ASDExplicitGamma.Main.CalibratedError

/-! STEP-MA-CHRONOLOGY-V-MONOTONE: at `γ = γ₀` the generator inequality of the observer node at
the actual `v = (amp/σ̄_m)² ≤ v̄ = mainSourceClock γ₀` implies the same inequality at `v̄`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Inverse
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

theorem chrono_capQ_nonneg (d : ℕ) : 0 ≤ mainAffineFlatBoundaryCapQ d := by
  unfold mainAffineFlatBoundaryCapQ
  split_ifs <;> try (push_cast; positivity)
  have hl : (0 : ℝ) ≤ (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ) := by
    unfold ASDExplicitGamma.Numerics.Model.q3ModeLength; push_cast; positivity
  have hl1 : (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ) ≤ 1 := by
    unfold ASDExplicitGamma.Numerics.Model.q3ModeLength; push_cast
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  nlinarith

/-- The actual `v = (amp/σ̄_m)²` equals the shell clock. -/
theorem chrono_v_eq_shellClock (M : ABKModel 2) (h : ℝ) (m : ℤ) :
    (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2 = shellClock M h m := by
  unfold shellClock q3ModelAmplitude
  rw [div_pow, mul_pow]
  congr 2
  change (Real.rpow 3 (M.gamma * ((m + 1 : ℤ) : ℝ))) ^ 2 = _
  rw [show Real.rpow 3 (M.gamma * ((m + 1 : ℤ) : ℝ)) = (3 : ℝ) ^ (M.gamma * ((m + 1 : ℤ) : ℝ)) from rfl,
    ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  push_cast
  ring

/-- MA-SHELL-CLOCK for the actual `v`. -/
theorem chrono_v_le_clock (M : ABKModel 2) (h : ℝ) (m : ℤ) (hγ : 0 < M.gamma)
    (hm : nativeInductionState M h m) :
    (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2 ≤
      mainSourceClock M.gamma := by
  rw [chrono_v_eq_shellClock]
  exact shellClock_le M h m hγ hm

/-- Pointwise-in-`f` domination: the generator bound at `v` is dominated by the one at `w`. -/
theorem chrono_generator_pointwise {v w a0 H xi xi' f q t d : ℝ} (M : ABKModel 2) {b b' : ℝ}
    (hb : b ^ 2 = v) (hb' : b' ^ 2 = w) (hq : 0 ≤ q) (ht : 0 ≤ t) (hg0 : 0 ≤ M.gamma)
    (hg : M.gamma ≤ gammaZero) (hv : 0 ≤ v) (hvw : v ≤ w) (hH : 0 ≤ H)
    (hxi : xi ≤ xi')
    (hd : d ≤ v * q + mainAffineTerm M b q t + mainSourceError' v a0 f H xi q +
      mainInverseAbs v (mainInverseMuMinusSource v) t) :
    d ≤ w * q + mainAffineTerm M b' q t + mainSourceError' w a0 f H xi' q +
      mainInverseAbs w (mainInverseMuMinusSource w) t := by
  refine hd.trans ?_
  have h1 : v * q ≤ w * q := mul_le_mul_of_nonneg_right hvw hq
  have h2 := chrono_affine_mono M (b := b) (b' := b') (q := q) (t := t) hg0 hg hq ht
    (by rw [hb, hb']; exact hvw)
  have h3 := chrono_sourceError_mono (f := f) (a := a0) (a' := a0) hq hv hvw le_rfl hH
    le_rfl hxi
  have h4 := chrono_inverseAbs_mono hv hvw ht
  linarith

theorem ma_chronology_v_monotone_node
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ) (h1 : 1 ≤ hobs) (h40 : hobs ≤ 40)
    (hγ0 : M.gamma = gammaZero) :
    let b' := Real.sqrt (mainSourceClock M.gamma)
    let q := mainAffineFlatBoundaryCapQ (hobs - 1)
    let u := modelTraceHeatAverage (m + (hobs : ℤ)) M m
    (∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ u s ∧
        u s ≤ min (inSourceMeanActual M m 5 s)
          (mainEnvelopeXi (b' ^ 2) M.gamma mainSourceInversePrefix (theta M) s / mainBetaOld)) ∧
      (∀ᵐ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
        deriv u s ≤ b' ^ 2 * q + mainAffineTerm M b' q s +
          mainSourceError' (b' ^ 2) (inSourceMeanActual M m 5 s) (u s)
            (mainEnvelopeH (theta M) M.gamma s)
            (mainEnvelopeXi (b' ^ 2) M.gamma mainSourceInversePrefix (theta M) s) q +
          mainInverseAbs (b' ^ 2) (mainInverseMuMinusSource (b' ^ 2)) s) := by
  intro b' q u
  have hnode := ma_generator_hypotheses_observer_node M h hM hγ N hpast m hm hobs h1 h40
  dsimp only at hnode
  have hgpos : 0 < M.gamma := by rw [hγ0]; norm_num [gammaZero]
  have hg0 : 0 ≤ M.gamma := hgpos.le
  have hvle := chrono_v_le_clock M h m hgpos (hpast m hm)
  have hclock : 0 ≤ mainSourceClock M.gamma := (mainSourceClock_pos hgpos).le
  have hb'2 : b' ^ 2 = mainSourceClock M.gamma := Real.sq_sqrt hclock
  set b := q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ) with hbdef
  have hvw : b ^ 2 ≤ b' ^ 2 := by rw [hb'2]; exact hvle
  have hv0 : 0 ≤ b ^ 2 := sq_nonneg b
  have hq : 0 ≤ q := chrono_capQ_nonneg _
  refine ⟨fun s hs => ?_, ?_⟩
  · obtain ⟨h0, hle⟩ := hnode.2.1 s hs
    refine ⟨h0, hle.trans ?_⟩
    have hx := chrono_envXi_mono (xiPre := mainSourceInversePrefix) (theta := theta M) (t := s)
      hg0 hγ hv0 hvw hs.1
    have hbo : 0 < mainBetaOld := by unfold mainBetaOld; norm_num
    exact min_le_min le_rfl (div_le_div_of_nonneg_right hx hbo.le)
  · filter_upwards [hnode.2.2.1] with s hs hs01
    have hd := hs hs01
    have hx := chrono_envXi_mono (xiPre := mainSourceInversePrefix) (theta := theta M) (t := s)
      hg0 hγ hv0 hvw hs01.1
    exact chrono_generator_pointwise M (hb := rfl) (hb' := rfl) hq hs01.1 hg0 hγ hv0 hvw
      (mainEnvelopeH_nonneg _ _ _) hx hd

/-- `v̄ = mainSourceClock γ₀` is the value `pV` of `Numerics/MainReturn'/Formula.lean`:
`(443/125)(17/50000) exp((2·17/50000) log 3)`. -/
theorem chrono_vbar_eq_pV :
    mainSourceClock gammaZero =
      (443 / 125 * (17 / 50000) : ℝ) * Real.exp ((2 * 17 / 50000 : ℝ) * Real.log 3) := by
  unfold mainSourceClock gammaZero
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  congr 2
  ring

/-- The `f`-domain at `v` is contained in the domain at `w ≥ v`. -/
theorem chrono_domain_subset {gamma a0 xiPre theta t v w : ℝ} (hg0 : 0 ≤ gamma)
    (hg : gamma ≤ gammaZero) (hv : 0 ≤ v) (hvw : v ≤ w) (ht : 0 ≤ t) :
    Set.Icc (0 : ℝ) (min a0 (mainEnvelopeXi v gamma xiPre theta t / mainBetaOld)) ⊆
      Set.Icc (0 : ℝ) (min a0 (mainEnvelopeXi w gamma xiPre theta t / mainBetaOld)) := by
  have hx := chrono_envXi_mono (xiPre := xiPre) (theta := theta) hg0 hg hv hvw ht
  have hbo : 0 < mainBetaOld := by unfold mainBetaOld; norm_num
  exact Set.Icc_subset_Icc le_rfl (min_le_min le_rfl (div_le_div_of_nonneg_right hx hbo.le))

end

end ASDExplicitGamma.Main
