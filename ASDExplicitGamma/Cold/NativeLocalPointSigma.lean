module

public import ASDExplicitGamma.Cold.NativeGaussianRange
public import Algsuperdiff.Assumptions.ShellField.LIHLocalSigma

/-! # The sharp Gaussian point sigma algebra carries the actual local integral information -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Homogenization Algsuperdiff.Section3
open Algsuperdiff.Frozen.Assumptions
namespace ASDExplicitGamma.Cold

/-- The literal stream-point restriction sigma algebra on an arbitrary region. -/
@[instance_reducible] def coldStreamPointSigma (U : Set (Vec 2)) : MeasurableSpace (ShellField 2) :=
  MeasurableSpace.comap (fun j : ShellField 2 => fun x : U => j x.val 1 0) inferInstance

/-- Each observed stream point is measurable from its own region restriction. -/
theorem cold_streamPoint_measurable (U : Set (Vec 2)) (x : U) :
    @Measurable (ShellField 2) ℝ (coldStreamPointSigma U) (borel ℝ)
      (fun j => j x.val 1 0) := by
  have hres : @Measurable (ShellField 2) (U → ℝ) (coldStreamPointSigma U) inferInstance
      (fun j => fun y : U => j y.val 1 0) := Measurable.of_comap_le le_rfl
  exact (measurable_pi_apply x).comp hres

/-- Planar skew symmetry makes every matrix entry locally measurable from its scalar stream. -/
theorem cold_matrixPoint_measurable (U : Set (Vec 2)) (x : U) (i k : Fin 2) :
    @Measurable (ShellField 2) ℝ (coldStreamPointSigma U) (borel ℝ)
      (fun j => j x.val i k) := by
  have hs := cold_streamPoint_measurable U x
  fin_cases i <;> fin_cases k
  · change @Measurable (ShellField 2) ℝ (coldStreamPointSigma U) (borel ℝ) (fun j => j x.val 0 0)
    have he : (fun j : ShellField 2 => j x.val 0 0) = (fun _ => (0:ℝ)) := by
      funext j
      have h := ShellField.skew_entry j x.val 0 0
      linarith
    rw [he]
    exact measurable_const
  · change @Measurable (ShellField 2) ℝ (coldStreamPointSigma U) (borel ℝ) (fun j => j x.val 0 1)
    have he : (fun j : ShellField 2 => j x.val 0 1) = (fun j => -(j x.val 1 0)) := by
      funext j
      exact ShellField.skew_entry j x.val 0 1
    rw [he]
    exact hs.neg
  · exact hs
  · change @Measurable (ShellField 2) ℝ (coldStreamPointSigma U) (borel ℝ) (fun j => j x.val 1 1)
    have he : (fun j : ShellField 2 => j x.val 1 1) = (fun _ => (0:ℝ)) := by
      funext j
      have h := ShellField.skew_entry j x.val 1 1
      linarith
    rw [he]
    exact measurable_const

end ASDExplicitGamma.Cold
