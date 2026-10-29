module

public import ASDExplicitGamma.Scalar.UpperCellEnergyResetBandProjection
public import ASDExplicitGamma.Scalar.UpperCellEnergyResetVectorCoordinates
public import ASDExplicitGamma.Scalar.UpperCellEnergyResetPhysicalWeakGradient

/-! The literal physical full flux has the projected forcing derivatives
as weak-gradient rows; no regularity of that corrected flux is assumed. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Probability.Stationary Algsuperdiff.Section3.Provider.Corrector
noncomputable section

/-- Row i of the complete projected forcing derivatives. -/
def upperCellResetDerivativeRow {Ω : Type*} [MeasurableSpace Ω]
    [AddAction (Vec 2) Ω] {μ : Measure Ω}
    [MeasurableConstVAdd (Vec 2) Ω] [VAddInvariantMeasure (Vec 2) Ω μ]
    (D : Fin 2 → VectorL2 2 μ) (i : Fin 2) : VectorL2 2 μ :=
  ∑ j : Fin 2,upperCellResetCoordLift μ j
    (vectorL2Coord i (upperCellResetStationaryFlux (D j)))

/-- A strongly measurable physical version of the actual derivative row. -/
def upperCellResetDerivativeRowRepr {Ω : Type*} [MeasurableSpace Ω]
    [AddAction (Vec 2) Ω] {μ : Measure Ω}
    [MeasurableConstVAdd (Vec 2) Ω] [VAddInvariantMeasure (Vec 2) Ω μ]
    (D : Fin 2 → VectorL2 2 μ) (i : Fin 2) : Ω → HilbertVec 2 :=
  (Lp.aestronglyMeasurable (upperCellResetDerivativeRow D i)).mk _

section Rows
variable {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec 2) Ω] {μ : Measure Ω}
variable [MeasurableConstVAdd (Vec 2) Ω] [VAddInvariantMeasure (Vec 2) Ω μ]

theorem upper_cell_reset_derivative_row_coord
    (D : Fin 2 → VectorL2 2 μ) (i j : Fin 2) :
    vectorL2Coord j (upperCellResetDerivativeRow D i)=
      vectorL2Coord i (upperCellResetStationaryFlux (D j)) := by
  classical
  unfold upperCellResetDerivativeRow
  rw [map_sum]
  simp only [upper_cell_reset_coord_lift]
  simp

theorem upper_cell_reset_derivative_row_measurable
    (D : Fin 2 → VectorL2 2 μ) (i : Fin 2) :
    StronglyMeasurable (upperCellResetDerivativeRowRepr D i) :=
  (Lp.aestronglyMeasurable (upperCellResetDerivativeRow D i)).stronglyMeasurable_mk

theorem upper_cell_reset_derivative_row_memLp
    (D : Fin 2 → VectorL2 2 μ) (i : Fin 2) :
    MemLp (upperCellResetDerivativeRowRepr D i) 2 μ :=
  (Lp.memLp (upperCellResetDerivativeRow D i)).ae_eq
    (Lp.aestronglyMeasurable (upperCellResetDerivativeRow D i)).ae_eq_mk

theorem upper_cell_reset_derivative_row_toLp
    (D : Fin 2 → VectorL2 2 μ) (i : Fin 2) :
    (upper_cell_reset_derivative_row_memLp D i).toLp
      (upperCellResetDerivativeRowRepr D i)=upperCellResetDerivativeRow D i := by
  apply Lp.ext
  exact (upper_cell_reset_derivative_row_memLp D i).coeFn_toLp.trans
    (Lp.aestronglyMeasurable (upperCellResetDerivativeRow D i)).ae_eq_mk.symm
end Rows

/-- Actual full-band weak gradients in the true physical cube. The only
pending analytic input is the strong derivative of the uncorrected forcing;
the corrected flux and its spatial regularity are constructed in the proof. -/
theorem upper_cell_reset_band_physical_weak_gradient'
    (M : ABKModel 2) (n terminal : ℤ) (c : ℝ) (e : Vec 2) (Q : TriadicCube 2)
    (D : Fin 2 → VectorL2 2 (Cutoff.cutoffSampleLaw M).toMeasure)
    (hD : ∀ j,HasDerivAt (fun t : ℝ => koopman (t • basisVec j)
      (upperCellResetBandForcing M n terminal c e)) (D j) 0) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,∀ i : Fin 2,
      HasWeakGradientOn (openCubeSet Q)
        (fun x => (realize (cutoffBandFlux M n terminal c e) ω x).toVec i)
        (fun x => (realize (upperCellResetDerivativeRowRepr D i) ω x).toVec) := by
  have hXm := stronglyMeasurable_cutoffBandFlux M n terminal c e
  have hX := memLp_two_cutoffBandFlux M n terminal c e
  apply ae_all_iff.mpr
  intro i
  have hgrad : HasHorizontalGradient
      ((memLp_coordField hXm hX i).toLp (coordField (cutoffBandFlux M n terminal c e) i))
      ((upper_cell_reset_derivative_row_memLp D i).toLp
        (upperCellResetDerivativeRowRepr D i)) := by
    intro j
    rw [upper_cell_reset_derivative_row_toLp,upper_cell_reset_derivative_row_coord]
    have hd := upper_cell_reset_band_derivative M n terminal c e (basisVec j) (D j) (hD j)
    have hcoord := (vectorL2Coord (μ := (Cutoff.cutoffSampleLaw M).toMeasure) i).hasFDerivAt.comp_hasDerivAt 0 hd
    have hc : HasDerivAt (fun t : ℝ => koopman (t • basisVec j)
        (vectorL2Coord i (hX.toLp (cutoffBandFlux M n terminal c e))))
        (vectorL2Coord i (upperCellResetStationaryFlux (D j))) 0 := by
      simpa only [Function.comp_def,←koopman_vectorL2Coord] using hcoord
    rw [vectorL2Coord_toLp hXm hX i] at hc
    exact hc
  exact upper_cell_reset_horizontal_physical_weak_gradient Q
    (stronglyMeasurable_coordField hXm i) (memLp_coordField hXm hX i)
    (upper_cell_reset_derivative_row_measurable D i)
    (upper_cell_reset_derivative_row_memLp D i) hgrad

end
end ASDExplicitGamma.Scalar
