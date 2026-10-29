module

public import ASDExplicitGamma.Main.ObsLowerFinal
public import ASDExplicitGamma.Main.ObsInverseDeficitFinal

/-! Node theorems for MA-TRACE-LOWER-GENERATOR, MA-INVERSE-DEFICIT and
MA-GENERATOR-HYPOTHESES at every main-range observer `1 ≤ hobs ≤ 40`, from the standing
assumptions only. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Inverse
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

theorem ma_trace_lower_observer_hA (M : ABKModel 2) (h : ℝ) (m : ℤ) (hobs : ℕ)
    (h40 : hobs ≤ 40) : ∀ s ∈ Set.Icc (0 : ℝ) 1, ObsInverseLowerGen M h m hobs s :=
  fun s hs => main_observer_q3_inverse_trace_lower_ae M h m hobs h40 s hs

theorem ma_inverse_deficit_observer_node
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ) (h1 : 1 ≤ hobs) (h40 : hobs ≤ 40) :
    let v := (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      -v * (mainInverseHeatAverage (m + (hobs : ℤ)) M m t - 2) ≤
        mainInverseAbs v (mainInverseMuMinusSource v) t) ∧
    AbsolutelyContinuousOnInterval (mainInverseHeatAverage (m + (hobs : ℤ)) M m) 0 1 ∧
      ∀ᵐ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
        -mainKappa (mainInverseMuMinusSource v) * mainInverseHeatAverage (m + (hobs : ℤ)) M m s -
            mainKappa (mainInverseMuMinusSource v) * mainRho ≤
          deriv (mainInverseHeatAverage (m + (hobs : ℤ)) M m) s := by
  intro v
  have hA := ma_trace_lower_observer_hA M h m hobs h40
  exact ⟨fun t ht => obs_inverse_deficit_absolute_branch M h hM hγ N hpast m hm hobs h40 hA t ht,
    obs_inverse_deficit_derivative M h hM hγ N hpast m hm hobs h40 hA⟩

theorem ma_generator_hypotheses_observer_node
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ) (h1 : 1 ≤ hobs) (h40 : hobs ≤ 40) :
    let b := q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)
    let q := mainAffineFlatBoundaryCapQ (hobs - 1)
    AbsolutelyContinuousOnInterval (modelTraceHeatAverage (m + (hobs : ℤ)) M m) 0 1 ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1,
        0 ≤ modelTraceHeatAverage (m + (hobs : ℤ)) M m s ∧
          modelTraceHeatAverage (m + (hobs : ℤ)) M m s ≤
            min (inSourceMeanActual M m 5 s)
              (mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) s /
                mainBetaOld)) ∧
      (∀ᵐ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
        deriv (modelTraceHeatAverage (m + (hobs : ℤ)) M m) s ≤
          b ^ 2 * q + mainAffineTerm M b q s +
            mainSourceError' (b ^ 2) (inSourceMeanActual M m 5 s)
              (modelTraceHeatAverage (m + (hobs : ℤ)) M m s) (mainEnvelopeH (theta M) M.gamma s)
              (mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) s) q +
            mainInverseAbs (b ^ 2) (mainInverseMuMinusSource (b ^ 2)) s) ∧
      (∀ᵐ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
        -mainKappa (mainInverseMuMinusSource (b ^ 2)) *
              mainInverseHeatAverage (m + (hobs : ℤ)) M m s -
            mainKappa (mainInverseMuMinusSource (b ^ 2)) * mainRho ≤
          deriv (mainInverseHeatAverage (m + (hobs : ℤ)) M m) s) :=
  main_generator_hypotheses_hot_full M h hM hγ N hpast m hm hobs h1 h40
    (ma_trace_lower_observer_hA M h m hobs h40)

end

end ASDExplicitGamma.Main
