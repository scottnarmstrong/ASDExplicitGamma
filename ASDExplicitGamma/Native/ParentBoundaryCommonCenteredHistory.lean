module

public import ASDExplicitGamma.Native.ParentBoundaryCommonSharpExpectation
public import ASDExplicitGamma.Native.ParentBoundaryCommonMomentDerivative
public import ASDExplicitGamma.Inverse.RawMomentRoot
public import ASDExplicitGamma.Inverse.HistoryPopulation

/-! The actual complete descendant history with one shared source-square center. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

local instance parentCommonHistoryResponseMeasurable (Q : TriadicCube 2) :
    MeasurableSpace (ResponseCoefficient (openCubeSet Q)) := borel _
local instance parentCommonHistoryResponseBorel (Q : TriadicCube 2) :
    BorelSpace (ResponseCoefficient (openCubeSet Q)) := ⟨rfl⟩
local instance parentCommonHistoryCompact (P : TriadicCube 2) : CompactSpace (closure (cubeSet P)) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet P).isCompact_closure

/-- The actual centered descendant trace is measurable before taking any
finite maximum or complete history sum. -/
theorem parent_boundary_common_cube_trace_measurable
    (M : ABKModel 2) {P Q : TriadicCube 2} {d : ℕ} (hQ : Q ∈ descendantsAtDepth P d)
    (n : ℤ) (height : ℕ) (t : ℝ) :
    Measurable (fun ω => squareTrace Q M.nu (Annealed.sigmaBar M n)
      (parentBoundaryCommonCubeObserved hQ n height t ω)) := by
  let K := closure (cubeSet P)
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact K (isBounded_cubeSet P).isCompact_closure
  have hold := measurable_olderField K ell n hK
  have hfresh := (centeringMap (parentBoundaryCommonCubeCenter P)).continuous.measurable.comp
    (measurable_modelBand K (nativeSourceBandIndex n height))
  have hobs : Measurable (parentBoundaryCommonCubeObserved hQ n height t) :=
    (parentBoundaryCommonOpenCellCoefficient hQ).continuous.measurable.comp
      (hold.add (hfresh.const_smul (Real.sqrt t)))
  exact (parent_boundary_common_square_trace_polynomial Q M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1).1.continuous.measurable.comp hobs

/-- Literal finite maximum over the actual source descendants. The fresh
center is subtracted on P before the whole family is restricted. -/
def parentBoundaryCommonCenteredDepthMax (M : ABKModel 2) (P : TriadicCube 2)
    (n : ℤ) (height : ℕ) (t : ℝ) (j : ℕ) : Cutoff.CutoffSample 2 → ℝ≥0∞ :=
  historyFiniteMax Finset.univ (fun Q : SquareCells P j => fun ω => ENNReal.ofReal
    (squareTrace Q.val M.nu (Annealed.sigmaBar M n)
      (parentBoundaryCommonCubeObserved Q.property n height t ω)))

/-- The literal complete centered maximum history, with all depths and
all shared-center cross-square covariances retained. -/
def parentBoundaryCommonCenteredMaxHistory (M : ABKModel 2) (P : TriadicCube 2)
    (n : ℤ) (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ≥0∞ :=
  ENNReal.ofReal (1-inverseHistoryDiscount)*∑' j : ℕ,
    ENNReal.ofReal (inverseHistoryDiscount^j)*parentBoundaryCommonCenteredDepthMax M P n height t j ω

/-- Genuine measurability of each actual centered spatial maximum. -/
theorem parent_boundary_common_centered_depth_max_measurable
    (M : ABKModel 2) (P : TriadicCube 2) (n : ℤ) (height : ℕ) (t : ℝ) (j : ℕ) :
    Measurable (parentBoundaryCommonCenteredDepthMax M P n height t j) := by
  unfold parentBoundaryCommonCenteredDepthMax
  exact history_finite_max_measurable _ _ (fun Q =>
    (parent_boundary_common_cube_trace_measurable M Q.property n height t).ennreal_ofReal)

/-- The complete common-centered history is measurable before conversion
from extended reals, so no infinite value is silently discarded. -/
theorem parent_boundary_common_centered_history_measurable
    (M : ABKModel 2) (P : TriadicCube 2) (n : ℤ) (height : ℕ) (t : ℝ) :
    Measurable (parentBoundaryCommonCenteredMaxHistory M P n height t) := by
  unfold parentBoundaryCommonCenteredMaxHistory
  exact (Measurable.tsum (fun j =>
    (parent_boundary_common_centered_depth_max_measurable M P n height t j).const_mul _)).const_mul _

end
end ASDExplicitGamma.Native
