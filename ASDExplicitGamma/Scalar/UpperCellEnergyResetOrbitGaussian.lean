module

public import ASDExplicitGamma.Scalar.UpperCellEnergyResetInvariantProjection
public import ASDExplicitGamma.Scalar.UpperCellEnergyResetGaussianClosure
public import ASDExplicitGamma.Model.SpectralFirstChaos

/-! Gaussianity of the full stationary flux and its strong derivatives,
derived from the actual Gaussian translation orbit of its scalar forcing. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory ProbabilityTheory Filter
open Algsuperdiff.Probability.Stationary Algsuperdiff.Section3.Provider.Corrector
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped Topology
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec 2) Ω]
variable {μ : Measure Ω}
variable [MeasurableConstVAdd (Vec 2) Ω] [VAddInvariantMeasure (Vec 2) Ω μ]

/-- The complete stationary first-chaos span of the actual scalar band. -/
def upperCellResetOrbit (v : ScalarL2 μ) : Submodule ℝ (ScalarL2 μ) :=
  KoopmanOrbitSubspace (fun z : Vec 2 => koopman z) v

instance upperCellResetOrbitProjection (v : ScalarL2 μ) :
    (upperCellResetOrbit v).HasOrthogonalProjection := by
  unfold upperCellResetOrbit
  infer_instance

/-- The full scalar-band orbit projection commutes with translations. -/
theorem upper_cell_reset_orbit_projection_translate
    (v : ScalarL2 μ) (z : Vec 2) (f : ScalarL2 μ) :
    (upperCellResetOrbit v).starProjection (koopman z f)=
      koopman z ((upperCellResetOrbit v).starProjection f) := by
  apply koopmanOrbitProjection_commute
  · intro x y g
    rw [koopman_koopman,add_comm]
  · intro x g
    rw [koopman_koopman,neg_add_cancel,koopman_zero]

/-- The genuine full solenoidal projection preserves every coordinate of
the scalar band's complete Gaussian first-chaos span. -/
theorem upper_cell_reset_flux_orbit_mem
    (v : ScalarL2 μ) (F : VectorL2 2 μ)
    (hF : ∀ i,vectorL2Coord i F ∈ upperCellResetOrbit v) :
    ∀ i,vectorL2Coord i (upperCellResetStationaryFlux F) ∈ upperCellResetOrbit v :=
  upper_cell_reset_flux_coordinates_mem (upperCellResetOrbit v)
    (upper_cell_reset_orbit_projection_translate v) F hF

/-- The actual full-flux coordinates have centered Gaussian laws, derived
from the scalar forcing's joint orbit law and invariant closed-span membership. -/
theorem upper_cell_reset_flux_orbit_gaussian [IsProbabilityMeasure μ]
    (v : ScalarL2 μ)
    (hv : IsCenteredGaussianFamily μ (fun z : Vec 2 => fun ω => koopman z v ω))
    (F : VectorL2 2 μ) (hF : ∀ i,vectorL2Coord i F ∈ upperCellResetOrbit v)
    (i : Fin 2) :
    ∃ variance : NNReal, μ.map (vectorL2Coord i (upperCellResetStationaryFlux F))=
      gaussianReal 0 variance := by
  exact upper_cell_reset_gaussian_closed_span μ (fun z : Vec 2 => koopman z v) hv _
    (upper_cell_reset_flux_orbit_mem v F hF i)

/-- A strong derivative of a vector in the scalar band orbit remains in
the same COMPLETE orbit, before any stationary flux projection is applied. -/
theorem upper_cell_reset_orbit_derivative_mem
    (v : ScalarL2 μ) (b : Vec 2) (F D : VectorL2 2 μ)
    (hF : ∀ i,vectorL2Coord i F ∈ upperCellResetOrbit v)
    (hD : HasDerivAt (fun t : ℝ => koopman (t • b) F) D 0) :
    ∀ i,vectorL2Coord i D ∈ upperCellResetOrbit v := by
  intro i
  let K := upperCellResetOrbit v
  have hd := (vectorL2Coord (μ := μ) i).hasFDerivAt.comp_hasDerivAt 0 hD
  have hd' : HasDerivAt (fun t : ℝ => koopman (t • b) (vectorL2Coord i F)) (vectorL2Coord i D) 0 := by
    simpa only [Function.comp_def,←koopman_vectorL2Coord] using hd
  have hclosed : IsClosed (K : Set (ScalarL2 μ)) := Submodule.isClosed_topologicalClosure _
  have hstable (z : Vec 2) : koopman z (vectorL2Coord i F) ∈ K := by
    have hgroup (x y : Vec 2) (g : ScalarL2 μ) :
        koopman (x+y) g=koopman x (koopman y g) := by
      rw [koopman_koopman,add_comm]
    exact koopmanOrbitSubspace_stable (fun z : Vec 2 => koopman (μ := μ) z) v
      hgroup z (vectorL2Coord i F) (hF i)
  apply hclosed.mem_of_tendsto hd'.tendsto_slope
  apply Filter.Eventually.of_forall
  intro t
  rw [slope_def_module]
  exact K.smul_mem _ (K.sub_mem (hstable (t • b)) (hstable (0 • b)))

/-- Gaussianity of the actual projected derivative is a consequence of
forcing Gaussianity and strong differentiation, not an added assumption on it. -/
theorem upper_cell_reset_flux_derivative_gaussian [IsProbabilityMeasure μ]
    (v : ScalarL2 μ)
    (hv : IsCenteredGaussianFamily μ (fun z : Vec 2 => fun ω => koopman z v ω))
    (b : Vec 2) (F D : VectorL2 2 μ)
    (hF : ∀ i,vectorL2Coord i F ∈ upperCellResetOrbit v)
    (hD : HasDerivAt (fun t : ℝ => koopman (t • b) F) D 0) (i : Fin 2) :
    ∃ variance : NNReal, μ.map (vectorL2Coord i (upperCellResetStationaryFlux D))=
      gaussianReal 0 variance :=
  upper_cell_reset_flux_orbit_gaussian v hv D
    (upper_cell_reset_orbit_derivative_mem v b F D hF hD) i

end
end ASDExplicitGamma.Scalar
