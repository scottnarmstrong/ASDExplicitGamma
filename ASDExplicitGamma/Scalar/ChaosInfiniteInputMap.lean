module

public import ASDExplicitGamma.Gaussian.SeriesMoment
public import ASDExplicitGamma.Scalar.ChaosHilbertMoment

/-! Exact finite-coordinate pushforward of the existing countable Gaussian realization. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory

/-- The first n Gaussian coordinates in their Euclidean carrier. -/
def gaussianFirstCoordinates (n : ℕ) (omega : ℕ → ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => omega i)

/-- Finite coordinate restriction is measurable. -/
theorem gaussian_first_coordinates_measurable (n : ℕ) : Measurable (gaussianFirstCoordinates n) := by
  unfold gaussianFirstCoordinates
  fun_prop

/-- The finite index carrier is exactly the initial segment of the countable carrier. -/
def gaussianFinRangeEquiv (n : ℕ) : Fin n ≃ (Finset.range n) where
  toFun := fun i => ⟨i,Finset.mem_range.mpr i.isLt⟩
  invFun := fun i => ⟨i,Finset.mem_range.mp i.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The actual finite-dimensional marginals of the countable realization are standard Gaussians. -/
theorem map_gaussian_first_coordinates (n : ℕ) :
    Gaussian.standardGaussianInfinitePi.map (gaussianFirstCoordinates n)=
      stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  let I := Finset.range n
  let E := MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) (gaussianFinRangeEquiv n).symm
  have hE : (Measure.pi (fun _ : I => gaussianReal 0 1)).map E=
      Measure.pi (fun _ : Fin n => gaussianReal 0 1) :=
    Measure.pi_map_piCongrLeft (β := fun _ : Fin n => ℝ) (gaussianFinRangeEquiv n).symm
      (fun _ : Fin n => gaussianReal 0 1)
  have hfun : gaussianFirstCoordinates n=
      (WithLp.toLp 2) ∘ E ∘ I.restrict := by
    funext omega
    apply PiLp.ext
    intro i
    rfl
  rw [hfun,Gaussian.standardGaussianInfinitePi,← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map E.measurable (Finset.measurable_restrict I)]
  rw [Measure.infinitePi_map_restrict,hE,ProbabilityTheory.map_pi_eq_stdGaussian]

end ASDExplicitGamma.Scalar
