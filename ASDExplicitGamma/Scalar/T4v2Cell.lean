module

public import ASDExplicitGamma.Scalar.T4v2Energy
public import ASDExplicitGamma.Scalar.SmoothFeedbackNode

/-! T4 v2: the cell-local flux of `fwStar` agrees with the global flux; tiled energies. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Native MeasureTheory

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

theorem t4v2_cell_ext (Q R : TriadicCube 2) (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (k : ResponseCoefficient (openCubeSet Q)) {x : Vec 2} (hx : x ∈ openCubeSet R) :
    responseCoefficientExtension (oldSignedCellCoefficient Q R hRQ k) x =
      responseCoefficientExtension k x := by
  rw [responseCoefficientExtension_eq _ hx, responseCoefficientExtension_eq _ (hRQ hx)]
  rfl

theorem t4v2_cell_flux (ν σ : ℝ) (Q R : TriadicCube 2) (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (k : ResponseCoefficient (openCubeSet Q)) (Z : Vec 2 → BlockVec 2) {x : Vec 2}
    (hx : x ∈ openCubeSet R) :
    scalarCoefficientFlux (responseFramePlanarCoefficientField ν σ
      (oldSignedCellCoefficient Q R hRQ k)) Z x =
    scalarCoefficientFlux (responseFramePlanarCoefficientField ν σ k) Z x := by
  unfold scalarCoefficientFlux blockCoeffField
  rw [responseFramePlanarCoefficientField_apply, responseFramePlanarCoefficientField_apply,
    t4v2_cell_ext Q R hRQ k hx]

/-- The `fwStar` summand of one load is the sum of the two global tiled weak energies. -/
theorem t4v2_cell_average (ν σ : ℝ) (Q : TriadicCube 2)
    (k : ResponseCoefficient (openCubeSet Q)) (Z : Vec 2 → BlockVec 2) (w : Vec 2 → Vec 2) :
    oldSignedCellAverage Q 134 (fun U =>
      vectorWeakHaarEnergy U.val (fun x j => (Z x).1 j - w x j) +
        vectorWeakHaarEnergy U.val (fun x => (scalarCoefficientFlux
          (responseFramePlanarCoefficientField ν σ
            (oldSignedCellCoefficient Q U.val
              (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)) Z x).2)) =
    lemmaVTiledWeakEnergy Q 134 (fun x j => (Z x).1 j - w x j) +
      lemmaVTiledWeakEnergy Q 134
        (fun x => (scalarCoefficientFlux (responseFramePlanarCoefficientField ν σ k) Z x).2) := by
  have hpt : ∀ U : OldSignedCellIndex Q 134,
      vectorWeakHaarEnergy U.val (fun x j => (Z x).1 j - w x j) +
        vectorWeakHaarEnergy U.val (fun x => (scalarCoefficientFlux
          (responseFramePlanarCoefficientField ν σ
            (oldSignedCellCoefficient Q U.val
              (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)) Z x).2) =
      (fun R : TriadicCube 2 => vectorWeakHaarEnergy R (fun x j => (Z x).1 j - w x j) +
        vectorWeakHaarEnergy R (fun x => (scalarCoefficientFlux
          (responseFramePlanarCoefficientField ν σ k) Z x).2)) U.val := by
    intro U
    have hae : (fun x => (scalarCoefficientFlux (responseFramePlanarCoefficientField ν σ
        (oldSignedCellCoefficient Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)) Z x).2) =ᵐ[
        volumeMeasureOn (openCubeSet U.val)] fun x => (scalarCoefficientFlux
          (responseFramePlanarCoefficientField ν σ k) Z x).2 := by
      have hU : ∀ᵐ x ∂volumeMeasureOn (openCubeSet U.val), x ∈ openCubeSet U.val :=
        ae_restrict_of_forall_mem (measurableSet_openCubeSet U.val) (fun x hx => hx)
      filter_upwards [hU] with x hx
      rw [t4v2_cell_flux ν σ Q U.val _ k Z hx]
    simp only
    rw [smooth_feedback_vector_weak_energy_congr_ae U.val hae]
  rw [show (fun U : OldSignedCellIndex Q 134 => _) = _ from funext hpt]
  rw [old_signed_cell_average_eq_descendantsAverage Q 134
    (fun R => vectorWeakHaarEnergy R (fun x j => (Z x).1 j - w x j) +
        vectorWeakHaarEnergy R (fun x => (scalarCoefficientFlux
          (responseFramePlanarCoefficientField ν σ k) Z x).2))]
  unfold lemmaVTiledWeakEnergy descendantsAverage
  dsimp only
  rw [Finset.sum_add_distrib, mul_add]

end

end ASDExplicitGamma.Scalar
