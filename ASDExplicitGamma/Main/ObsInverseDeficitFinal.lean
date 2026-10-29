module

public import ASDExplicitGamma.Main.ObsInverseDeficit
public import ASDExplicitGamma.Main.HotGeneratorHypotheses
public import ASDExplicitGamma.Main.Q3HeatIdentity

/-! MA-GENERATOR-HYPOTHESES at observer roots with the source `I_abs`, depending only on the
pathwise observer lower generator (A) and the standing assumptions. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Inverse
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

theorem main_generator_hypotheses_hot_of_lowerGen
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ) (h1 : 1 ≤ hobs) (h40 : hobs ≤ 40)
    (hA : ∀ s ∈ Set.Icc (0 : ℝ) 1, ObsInverseLowerGen M h m hobs s) :
    let b := q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)
    let q := mainAffineFlatBoundaryCapQ (hobs - 1)
    AbsolutelyContinuousOnInterval (modelTraceHeatAverage (m + (hobs : ℤ)) M m) 0 1 ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1,
        0 ≤ modelTraceHeatAverage (m + (hobs : ℤ)) M m s ∧
          modelTraceHeatAverage (m + (hobs : ℤ)) M m s ≤
            min (inSourceMeanActual M m 5 s)
              (mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) s /
                mainBetaOld)) ∧
      ∀ᵐ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
        deriv (modelTraceHeatAverage (m + (hobs : ℤ)) M m) s ≤
          b ^ 2 * q + mainAffineTerm M b q s +
            mainSourceError' (b ^ 2) (inSourceMeanActual M m 5 s)
              (modelTraceHeatAverage (m + (hobs : ℤ)) M m s) (mainEnvelopeH (theta M) M.gamma s)
              (mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) s) q +
            mainInverseAbs (b ^ 2) (mainInverseMuMinusSource (b ^ 2)) s :=
  main_generator_hypotheses_hot' M h hM hγ N hpast m hm hobs h1 h40
    (fun s hs => obs_inverse_deficit_absolute_branch M h hM hγ N hpast m hm hobs h40 hA s hs)

/-- `u' ≥ -κ u - δ_inv` a.e. on `[0,1]` for the observer inverse heat average. -/
theorem obs_inverse_deficit_derivative
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ) (h40 : hobs ≤ 40)
    (hA : ∀ s ∈ Set.Icc (0 : ℝ) 1, ObsInverseLowerGen M h m hobs s) :
    let v := (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2
    AbsolutelyContinuousOnInterval (mainInverseHeatAverage (m + (hobs : ℤ)) M m) 0 1 ∧
      ∀ᵐ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
        -mainKappa (mainInverseMuMinusSource v) * mainInverseHeatAverage (m + (hobs : ℤ)) M m s -
            mainKappa (mainInverseMuMinusSource v) * mainRho ≤
          deriv (mainInverseHeatAverage (m + (hobs : ℤ)) M m) s := by
  intro v
  have hstate : ∀ j : ℕ, nativeInductionState M h (m - (j : ℤ)) := fun j =>
    hpast (m - (j : ℤ)) (by omega)
  have hHeat := (main_actual_q3_heat_identities (m + (hobs : ℤ)) M h hM m).2
  refine ⟨hHeat.1, ?_⟩
  filter_upwards [hHeat.2.1] with s hs hs01
  have hd := (hs hs01).deriv
  rw [hd]
  exact obs_inverse_generator_row M h hM hγ m hobs h40 s hs01 hstate (hA s hs01)

theorem main_generator_hypotheses_hot_full
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ) (h1 : 1 ≤ hobs) (h40 : hobs ≤ 40)
    (hA : ∀ s ∈ Set.Icc (0 : ℝ) 1, ObsInverseLowerGen M h m hobs s) :
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
          deriv (mainInverseHeatAverage (m + (hobs : ℤ)) M m) s) := by
  intro b q
  have h1' := main_generator_hypotheses_hot_of_lowerGen M h hM hγ N hpast m hm hobs h1
    h40 hA
  have h2 := obs_inverse_deficit_derivative M h hM hγ N hpast m hm hobs h40 hA
  exact ⟨h1'.1, h1'.2.1, h1'.2.2, h2.2⟩

end

end ASDExplicitGamma.Main
