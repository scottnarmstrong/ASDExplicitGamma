module

public import ASDExplicitGamma.Gaussian.Q3RealizationFourier
public import ASDExplicitGamma.Scalar.ResolventParityHilbert
public import Algsuperdiff.Section3.Provider.Corrector.ShellSumLayerFlip

/-! Sign symmetry for the actual fresh-shell Gaussian series, with an
independent OLD variable held fixed. -/
@[expose] public section

open MeasureTheory
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian

namespace ASDExplicitGamma.Scalar

open scoped Topology

/-- Restricting the scalar component of a shell commutes with the exact
negation action on the source shell field. -/
theorem shellFieldScalarRestriction_negate
    (K : Set (Homogenization.Vec 2)) [CompactSpace K]
    (j : ShellField 2) :
    shellFieldScalarRestriction K (ShellField.negate j) =
      -shellFieldScalarRestriction K j := by
  ext x
  simp [shellFieldScalarRestriction, planarShellScalarStream,
    planarShellMatrixEntry, ShellField.negate_apply]

/-- Flipping only the fresh coordinate preserves an independent product law;
the first coordinate, which represents the OLD environment, is unchanged. -/
theorem product_fresh_flip_preserves
    {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    (μ : Measure α) [SFinite μ] (ν : Measure Ω) [SFinite ν] (neg : Ω → Ω)
    (hneg : Measurable neg) (hmap : Measure.map neg ν = ν) :
    Measure.map (fun p : α × Ω => (p.1, neg p.2)) (μ.prod ν) =
      μ.prod ν := by
  calc
    Measure.map (fun p : α × Ω => (p.1, neg p.2)) (μ.prod ν) =
        (μ.map id).prod (ν.map neg) := by
          have hfun : (fun p : α × Ω => (p.1, neg p.2)) = Prod.map id neg := by
            funext p
            rfl
          rw [hfun]
          exact (Measure.map_prod_map μ ν measurable_id hneg).symm
    _ = μ.prod ν := by rw [Measure.map_id, hmap]

end ASDExplicitGamma.Scalar
