module

public import ASDExplicitGamma.Main.InverseInsertion
public import ASDExplicitGamma.Main.HeatRegularity
public import ASDExplicitGamma.Gaussian.ModelHeatTrace

/-! The two actual OLD-frame tests under one fresh-shell covariance. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ProbabilityTheory Filter Set
open Algsuperdiff.Section3 ASDExplicitGamma.Gaussian

/-- The literal averaged inverse trace during insertion. -/
noncomputable def mainInverseHeatAverage (n : ℤ) (M : ABKModel 2) (m : ℤ) (t : ℝ) : ℝ :=
  ∫ omega, mainInsertionInverseTrace M m n t omega ∂(Cutoff.cutoffSampleLaw M).toMeasure

/-- Exact transport to the continuous-coefficient inverse test. -/
theorem mainInverseHeatAverage_eq (n : ℤ) (M : ABKModel 2) (m : ℤ) :
    mainInverseHeatAverage n M m =
      modelHeatAverage (closure (cubeSet (originCube 2 n))) M m
        (mainInverseObservable n M.nu (Annealed.sigmaBar M m : ℝ)) := by
  funext t
  apply integral_congr_ae
  exact Eventually.of_forall fun omega => (mainInverseObservable_inserted M m n t omega).symm

/-- The full insertion-panel conclusion, with the actual generator as `d`. -/
def mainHeatPanelIdentity (f d : ℝ → ℝ) : Prop :=
  AbsolutelyContinuousOnInterval f 0 1 ∧
    (∀ᵐ t : ℝ, t ∈ Icc 0 1 → HasDerivAt f (d t) t) ∧
    HasDerivWithinAt f (d 0) (Ici 0) 0

/-- The half-line heat theorem gives the a.e. identity on the closed panel. -/
theorem mainHeatPanelIdentity_of_C1 {f d : ℝ → ℝ}
    (hd : ContinuousOn d (Ici 0))
    (hpos : ∀ t ∈ Ioi 0, HasDerivAt f (d t) t)
    (hzero : HasDerivWithinAt f (d 0) (Ici 0) 0) : mainHeatPanelIdentity f d := by
  refine ⟨main_heat_absolutelyContinuous hd hpos hzero, ?_, hzero⟩
  filter_upwards [volume.ae_ne (0 : ℝ)] with t ht htI
  exact hpos t (lt_of_le_of_ne htI.1 (Ne.symm ht))

end ASDExplicitGamma.Main
