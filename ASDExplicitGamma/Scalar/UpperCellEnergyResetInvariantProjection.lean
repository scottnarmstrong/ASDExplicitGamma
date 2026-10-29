module

public import ASDExplicitGamma.Scalar.UpperCellEnergyResetVectorCoordinates

/-! Preservation of invariant scalar closed spans by the genuine stationary
Helmholtz splitting. This is the first-chaos reduction for the full band. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Probability.Stationary
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Apply the scalar orthogonal projection to each Euclidean coordinate. -/
def upperCellResetVectorProjection (K : Submodule ℝ (ScalarL2 μ)) [K.HasOrthogonalProjection] :
    VectorL2 2 μ →L[ℝ] VectorL2 2 μ :=
  ∑ i : Fin 2,(upperCellResetCoordLift μ i).comp
    (K.starProjection.comp (vectorL2Coord i))

theorem upper_cell_reset_vector_projection_coord
    (K : Submodule ℝ (ScalarL2 μ)) [K.HasOrthogonalProjection]
    (i : Fin 2) (F : VectorL2 2 μ) :
    vectorL2Coord i (upperCellResetVectorProjection K F)=K.starProjection (vectorL2Coord i F) := by
  classical
  change vectorL2Coord i (∑ j : Fin 2,upperCellResetCoordLift μ j
    (K.starProjection (vectorL2Coord j F)))=_
  rw [map_sum]
  simp only [upper_cell_reset_coord_lift]
  simp

theorem upper_cell_reset_vector_projection_symmetric
    (K : Submodule ℝ (ScalarL2 μ)) [K.HasOrthogonalProjection] :
    (upperCellResetVectorProjection K).toLinearMap.IsSymmetric := by
  intro F G
  change inner ℝ (upperCellResetVectorProjection K F) G=
    inner ℝ F (upperCellResetVectorProjection K G)
  rw [upper_cell_reset_vector_inner,upper_cell_reset_vector_inner]
  simp_rw [upper_cell_reset_vector_projection_coord]
  exact Finset.sum_congr rfl (fun i _ => K.starProjection_isSymmetric _ _)

variable [AddAction (Vec 2) Ω] [MeasurableConstVAdd (Vec 2) Ω]
variable [VAddInvariantMeasure (Vec 2) Ω μ]

/-- A scalar projection commuting with translations preserves the literal
strong horizontal gradient relation coordinatewise. -/
theorem upper_cell_reset_vector_projection_gradient
    (K : Submodule ℝ (ScalarL2 μ)) [K.HasOrthogonalProjection]
    (hcomm : ∀ (z : Vec 2) (f : ScalarL2 μ),K.starProjection (koopman z f)=koopman z (K.starProjection f))
    {phi : ScalarL2 μ} {F : VectorL2 2 μ} (hF : HasHorizontalGradient phi F) :
    HasHorizontalGradient (K.starProjection phi) (upperCellResetVectorProjection K F) := by
  intro i
  rw [upper_cell_reset_vector_projection_coord]
  have hh := K.starProjection.hasFDerivAt.comp_hasDerivAt 0 (hF i)
  simpa only [Function.comp_def,hcomm] using hh

/-- The componentwise projection preserves the complete stationary potential
space, because it preserves the full strong-gradient range before closure. -/
theorem upper_cell_reset_vector_projection_potential
    (K : Submodule ℝ (ScalarL2 μ)) [K.HasOrthogonalProjection]
    (hcomm : ∀ (z : Vec 2) (f : ScalarL2 μ),K.starProjection (koopman z f)=koopman z (K.starProjection f))
    {F : VectorL2 2 μ} (hF : F ∈ stationaryPotentialSubspace (μ := μ) (d := 2)) :
    upperCellResetVectorProjection K F ∈ stationaryPotentialSubspace (μ := μ) (d := 2) := by
  let S := stationaryPotentialSubspace (μ := μ) (d := 2)
  have hsub : horizontalGradientRange (μ := μ) (d := 2) ≤
      S.comap (upperCellResetVectorProjection K).toLinearMap := by
    rintro G ⟨phi,hphi⟩
    exact Submodule.le_topologicalClosure _
      ⟨K.starProjection phi,upper_cell_reset_vector_projection_gradient K hcomm hphi⟩
  have hclosed : IsClosed
      (S.comap (upperCellResetVectorProjection K).toLinearMap : Set (VectorL2 2 μ)) :=
    (Submodule.isClosed_topologicalClosure _).preimage
      (upperCellResetVectorProjection K).continuous
  exact Submodule.topologicalClosure_minimal _ hsub hclosed hF

/-- Symmetry gives preservation of the orthogonal stationary solenoidal
space as well, so the two actual projections commute. -/
theorem upper_cell_reset_vector_projection_commutes
    (K : Submodule ℝ (ScalarL2 μ)) [K.HasOrthogonalProjection]
    (hcomm : ∀ (z : Vec 2) (f : ScalarL2 μ),K.starProjection (koopman z f)=koopman z (K.starProjection f))
    (F : VectorL2 2 μ) :
    stationaryPotentialProjection (upperCellResetVectorProjection K F)=
      upperCellResetVectorProjection K (stationaryPotentialProjection F) := by
  have horth (G : VectorL2 2 μ) (hG : G ∈ stationarySolenoidalSubspace (μ := μ) (d := 2)) :
      upperCellResetVectorProjection K G ∈ stationarySolenoidalSubspace (μ := μ) (d := 2) := by
    intro H hH
    calc
      inner ℝ H (upperCellResetVectorProjection K G)=
        inner ℝ (upperCellResetVectorProjection K H) G :=
          (upper_cell_reset_vector_projection_symmetric K H G).symm
      _ = 0 := hG _ (upper_cell_reset_vector_projection_potential K hcomm hH)
  symm
  apply eq_stationaryPotentialProjection_of_mem_of_sub_mem_orthogonal
  · exact upper_cell_reset_vector_projection_potential K hcomm (stationaryPotentialProjection_mem F)
  · rw [←map_sub]
    exact horth _ (sub_stationaryPotentialProjection_mem_orthogonal F)

/-- If the actual forcing coordinates lie in an invariant closed scalar
span, every coordinate of its full corrected flux lies in that same span. -/
theorem upper_cell_reset_flux_coordinates_mem
    (K : Submodule ℝ (ScalarL2 μ)) [K.HasOrthogonalProjection]
    (hcomm : ∀ (z : Vec 2) (f : ScalarL2 μ),K.starProjection (koopman z f)=koopman z (K.starProjection f))
    (F : VectorL2 2 μ) (hF : ∀ i,vectorL2Coord i F ∈ K) :
    ∀ i,vectorL2Coord i (upperCellResetStationaryFlux F) ∈ K := by
  have hfix : upperCellResetVectorProjection K F=F := by
    apply upper_cell_reset_vector_ext μ
    intro i
    rw [upper_cell_reset_vector_projection_coord]
    exact K.starProjection_eq_self_iff.mpr (hF i)
  have hpfix : upperCellResetVectorProjection K (stationaryPotentialProjection F)=
      stationaryPotentialProjection F := by
    rw [←upper_cell_reset_vector_projection_commutes K hcomm F,hfix]
  intro i
  have hpot : vectorL2Coord i (stationaryPotentialProjection F) ∈ K := by
    rw [←hpfix,upper_cell_reset_vector_projection_coord]
    exact K.starProjection_apply_mem _
  change vectorL2Coord i (F-stationaryPotentialProjection F) ∈ K
  rw [map_sub]
  exact K.sub_mem (hF i) hpot

end
end ASDExplicitGamma.Scalar
