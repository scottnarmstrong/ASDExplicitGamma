module

public import Algsuperdiff.Section3.Provider.Affine.KuhnWeakGradient
public import Homogenization.Sobolev.Truncation.Basic

/-! The existing finite-Kuhn weak-gradient engine, on an arbitrary translated
root. This analytic helper retains the literal nodal interpolant and its
constant slope on every open simplex. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
open Algsuperdiff.Section3.Provider.Affine Algsuperdiff.Section3.Provider.Whitney
noncomputable section

local instance stoppedKuhnFiniteVolume (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- Canonical H1 realization of the actual finite piecewise-affine gluing.
Continuity and compact support are geometric obligations at this helper. -/
def finiteKuhnH1 (Q : TriadicCube 2) (cells : Finset (KuhnCell 2))
    (datum : Vec 2 → ℝ) {scale : ℤ}
    (hscale : ∀ T ∈ cells, T.supportCube.scale=scale)
    (hcontinuous : Continuous (zeroExtendedKuhnAffine cells datum))
    (hcompact : HasCompactSupport (zeroExtendedKuhnAffine cells datum)) :
    H1Function (openCubeSet Q) where
  toFun := zeroExtendedKuhnAffine cells datum
  grad := fun x i => zeroExtendedKuhnAffineCoordDeriv cells datum i x
  memL2 := (hcontinuous.memLp_of_hasCompactSupport hcompact).mono_measure Measure.restrict_le_self
  gradMemL2 := by
    intro i
    refine MemLp.of_bound
      (measurable_zeroExtendedKuhnAffineCoordDeriv cells datum hcontinuous i).aestronglyMeasurable
      (zeroExtendedKuhnAffineCoordBound cells datum i) ?_
    exact Filter.Eventually.of_forall fun x =>
      norm_zeroExtendedKuhnAffineCoordDeriv_le cells datum hscale hcontinuous i x
  hasWeakGradient := by
    intro i
    exact (hasWeakPartialDerivOn_univ_zeroExtendedKuhnAffine cells datum hscale hcontinuous i).restrict
      (isOpen_openCubeSet Q) (Set.subset_univ _)

/-- A compact geometric support inside the root supplies the actual zero
trace, independently of which affine simplex contains a point. -/
theorem finite_kuhn_h1_memH10 (Q : TriadicCube 2) (cells : Finset (KuhnCell 2))
    (datum : Vec 2 → ℝ) {scale : ℤ}
    (hscale : ∀ T ∈ cells, T.supportCube.scale=scale)
    (hcontinuous : Continuous (zeroExtendedKuhnAffine cells datum))
    (K : Set (Vec 2)) (hK : IsCompact K) (hKU : K ⊆ openCubeSet Q)
    (hzero : ∀ x, x ∉ K → zeroExtendedKuhnAffine cells datum x=0) :
    MemH10 (openCubeSet Q) (zeroExtendedKuhnAffine cells datum) := by
  let hc := HasCompactSupport.intro hK hzero
  exact memH10_of_compactSupport (isOpenBoundedConvexDomain_openCubeSet Q)
    (finiteKuhnH1 Q cells datum hscale hcontinuous hc) hK hKU hzero

end
end ASDExplicitGamma.Inverse
