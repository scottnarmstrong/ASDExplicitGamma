module

public import ASDExplicitGamma.Main.EnvelopeHTheta
public import ASDExplicitGamma.Main.ThetaGeneratorHotGeneratorIntegrated
public import ASDExplicitGamma.Main.ThetaGeneratorHotGeneratorHypotheses
public import ASDExplicitGamma.Main.ThetaGeneratorHotInverseIdent
public import ASDExplicitGamma.Main.ThetaGeneratorHotGeneratorAssembly
public import ASDExplicitGamma.Main.ObsMainRangeNodes

/-! MA-GENERATOR-HYPOTHESES at every observer, with `H := mainEnvelopeH35Theta (theta M) (b²) M.gamma`,
from the standing assumptions only (the pathwise observer lower generator is discharged by
`ma_trace_lower_observer_hA`). -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Inverse
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

/-- MA-GENERATOR-HYPOTHESES at an observer root with the source `I_abs`. The single named
hypothesis `hInv` is exactly the output form of the observer inverse-deficit adapter. -/
theorem main_generator_hypotheses_hot_Th
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ) (h1 : 1 ≤ hobs) (h40 : hobs ≤ 40)
    (hInv : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      -((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) *
          (mainInverseHeatAverage (m + (hobs : ℤ)) M m s - 2) ≤
        mainInverseAbs ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2)
          (mainInverseMuMinusSource
            ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2)) s) :
    let b := q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)
    let q := mainAffineFlatBoundaryCapQ (hobs - 1)
    AbsolutelyContinuousOnInterval (modelTraceHeatAverage (m + (hobs : ℤ)) M m) 0 1 ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1,
        0 ≤ modelTraceHeatAverage (m + (hobs : ℤ)) M m s ∧
          modelTraceHeatAverage (m + (hobs : ℤ)) M m s ≤
            min (inSourceMeanActual M m 5 s)
              (mainEnvelopeXi (b ^ 2) M.gamma (theta M * mainSourceInversePrefix) (theta M) s /
                mainBetaOld)) ∧
      ∀ᵐ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
        deriv (modelTraceHeatAverage (m + (hobs : ℤ)) M m) s ≤
          b ^ 2 * q + mainAffineTerm_Th M b q s +
            mainSourceError' (b ^ 2) (inSourceMeanActual M m 5 s)
              (modelTraceHeatAverage (m + (hobs : ℤ)) M m s) (mainEnvelopeH35Theta (theta M) (b ^ 2) M.gamma s)
              (mainEnvelopeXi (b ^ 2) M.gamma (theta M * mainSourceInversePrefix) (theta M) s) q +
            mainInverseAbs (b ^ 2) (mainInverseMuMinusSource (b ^ 2)) s := by
  intro b q
  have hmain := main_generator_hypotheses_hot_of_inverse_deficit_Th M h hM hγ N hpast m hm
    hobs h1 h40 (fun s => mainInverseAbs (b ^ 2) (mainInverseMuMinusSource (b ^ 2)) s)
    (fun s hs => by
      obtain ⟨hint, heq⟩ := hotInverseTrace_integral_Th M h hM m hobs s
      refine ⟨hint, ?_⟩
      rw [heq]
      exact hInv s hs)
  dsimp only at hmain
  exact ⟨hmain.1, fun s hs => main_generator_hot_domain_Th M h hM hγ N hpast m hm hobs h1 h40 s hs,
    hmain.2⟩


theorem ma_generator_hypotheses_observer_node_Th
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
              (mainEnvelopeXi (b ^ 2) M.gamma (theta M * mainSourceInversePrefix) (theta M) s /
                mainBetaOld)) ∧
      (∀ᵐ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
        deriv (modelTraceHeatAverage (m + (hobs : ℤ)) M m) s ≤
          b ^ 2 * q + mainAffineTerm_Th M b q s +
            mainSourceError' (b ^ 2) (inSourceMeanActual M m 5 s)
              (modelTraceHeatAverage (m + (hobs : ℤ)) M m s) (mainEnvelopeH35Theta (theta M) (b ^ 2) M.gamma s)
              (mainEnvelopeXi (b ^ 2) M.gamma (theta M * mainSourceInversePrefix) (theta M) s) q +
            mainInverseAbs (b ^ 2) (mainInverseMuMinusSource (b ^ 2)) s) ∧
      (∀ᵐ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
        -mainKappa (mainInverseMuMinusSource (b ^ 2)) *
              mainInverseHeatAverage (m + (hobs : ℤ)) M m s -
            mainKappa (mainInverseMuMinusSource (b ^ 2)) * mainRho ≤
          deriv (mainInverseHeatAverage (m + (hobs : ℤ)) M m) s) := by
  intro b q
  have hA := ma_trace_lower_observer_hA M h m hobs h40
  have h1' := main_generator_hypotheses_hot_Th M h hM hγ N hpast m hm hobs h1 h40
    (fun s hs => obs_inverse_deficit_absolute_branch M h hM hγ N hpast m hm hobs h40 hA s hs)
  have h2 := obs_inverse_deficit_derivative M h hM hγ N hpast m hm hobs h40 hA
  exact ⟨h1'.1, h1'.2.1, h1'.2.2, h2.2⟩

end

end ASDExplicitGamma.Main
