module

public import ASDExplicitGamma.Inverse.StoppedRootSpatialAverage
public import ASDExplicitGamma.Inverse.StoppedRealDiameter

/-! The actual spatial bad-density average and its exact centering identity. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
noncomputable section

/-- Actual root-volume-normalized spatial moment over a deterministic source
layer, using the globally indexed physical q3 block field. -/
def rootDiameterAverage {Ω : Type*} (B : PlanarMarks Ω) (Q : TriadicCube 2)
    (R : ℕ) (E : Set (Vec 2)) (m : ℕ) (ω : Ω) : ℝ :=
  (∫ p in E, (realDiameterField B (physicalBlockIndex (rootFineLabel Q R) p) ω)^m)/
    (volume (cubeSet Q)).toReal

/-- Exact finite partial-block representation of the actual spatial average. -/
theorem root_diameter_average_eq {Ω : Type*} (B : PlanarMarks Ω) (Q : TriadicCube 2)
    (R : ℕ) (E : Set (Vec 2)) (hE : MeasurableSet E) (hEQ : E ⊆ cubeSet Q) (m : ℕ) :
    rootDiameterAverage B Q R E m = fun ω => ∑ z : ↥(rootBlockPopulation Q R),
      localizationPartialWeight Q E (physicalBlockSet (rootFineLabel Q R) z.val)*
        (realDiameterField B z.val ω)^m := by
  funext ω
  exact root_spatial_average_eq Q R E hE hEQ
    (fun z : BlockSite => (realDiameterField B z ω)^m)

/-- The spatial average is a measurable sample observable because its physical
partition is finite and deterministic. -/
theorem root_diameter_average_measurable {Ω : Type*} [MeasurableSpace Ω]
    (B : PlanarMarks Ω) (hL : ∀ x, MeasurableSet (B.localMark x))
    (hP : ∀ n x, MeasurableSet (B.positiveMark n x))
    (Q : TriadicCube 2) (R : ℕ) (E : Set (Vec 2)) (hE : MeasurableSet E)
    (hEQ : E ⊆ cubeSet Q) (m : ℕ) : Measurable (rootDiameterAverage B Q R E m) := by
  rw [root_diameter_average_eq B Q R E hE hEQ m]
  apply Finset.measurable_sum
  intro z _
  exact measurable_const.mul ((real_diameter_measurable B hL hP z.val).pow_const m)

/-- Centering the actual spatial average is exactly the weighted sum of its
centered block moments; integrability is needed only for expectation linearity. -/
theorem root_diameter_average_centered_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (B : PlanarMarks Ω) (Q : TriadicCube 2) (R : ℕ)
    (E : Set (Vec 2)) (hE : MeasurableSet E) (hEQ : E ⊆ cubeSet Q) (m : ℕ)
    (hi : ∀ z : ↥(rootBlockPopulation Q R), Integrable (fun ω => (realDiameterField B z.val ω)^m) μ) :
    (fun ω => rootDiameterAverage B Q R E m ω-∫ ζ, rootDiameterAverage B Q R E m ζ ∂μ) =
      fun ω => ∑ z : ↥(rootBlockPopulation Q R),
        localizationPartialWeight Q E (physicalBlockSet (rootFineLabel Q R) z.val)*
          ((realDiameterField B z.val ω)^m-∫ ζ, (realDiameterField B z.val ζ)^m ∂μ) := by
  rw [root_diameter_average_eq B Q R E hE hEQ m]
  funext ω
  rw [integral_finsetSum _ (fun z _ => (hi z).const_mul _)]
  simp_rw [integral_const_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z _
  ring

end
end ASDExplicitGamma.Inverse
