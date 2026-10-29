module

public import ASDExplicitGamma.Native.ParentBoundaryModeRotation

/-! Complete common-noise covariance rotation, before estimating the fields. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main ASDExplicitGamma.Response
noncomputable section

/-- The complete plus and minus covariance matrices are related by the
same two quarter turns as their physical modes. No independence is used. -/
theorem parent_boundary_remainder_covariance_rotation (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    ∀ᵐ x ∂normalizedCubeMeasure Q,∀ i k : Fin 2,
      oldSignedRemainderCovarianceField Q b L true i x k =
        ∑ j : Fin 2,∑ l : Fin 2,responsePlanarJ k l *
          oldSignedRemainderCovarianceField Q b L false j x l * responsePlanarJ j i := by
  have hm : ∀ᵐ x ∂normalizedCubeMeasure Q,∀ n : whiteBasisIndex,∀ i k : Fin 2,
      matVecMul responsePlanarJ (fun l => oldSignedRemainderCoordinate Q b L true n (i,l) x) k =
        ∑ j : Fin 2,∑ l : Fin 2,responsePlanarJ k l *
          matVecMul responsePlanarJ (fun a => oldSignedRemainderCoordinate Q b L false n (j,a) x) l *
          responsePlanarJ j i := by
    rw [ae_all_iff]
    exact parent_boundary_remainder_mode_rotation Q b L
  have hp := fun i k => old_signed_remainder_vector_covariance_hasSum Q b L true i k
  have hn := fun i k => old_signed_remainder_vector_covariance_hasSum Q b L false i k
  simp_rw [←ae_all_iff] at hp hn
  filter_upwards [hm,hp,hn] with x hx hp hn
  intro i k
  have hs := hasSum_sum (s := Finset.univ) (fun j _ =>
    hasSum_sum (s := Finset.univ) (fun l _ =>
      ((hn j l).mul_left (responsePlanarJ k l)).mul_right (responsePlanarJ j i)))
  apply (hp i k).unique
  apply hs.congr_fun
  intro n
  rw [hx n i k]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Explicit signed permutation of the four complete covariance entries. -/
theorem parent_boundary_remainder_covariance_entries (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    (fun x => oldSignedRemainderCovarianceField Q b L true 0 x 0) =ᵐ[normalizedCubeMeasure Q]
      (fun x => -oldSignedRemainderCovarianceField Q b L false 1 x 1) ∧
    (fun x => oldSignedRemainderCovarianceField Q b L true 0 x 1) =ᵐ[normalizedCubeMeasure Q]
      (fun x => oldSignedRemainderCovarianceField Q b L false 1 x 0) ∧
    (fun x => oldSignedRemainderCovarianceField Q b L true 1 x 0) =ᵐ[normalizedCubeMeasure Q]
      (fun x => oldSignedRemainderCovarianceField Q b L false 0 x 1) ∧
    (fun x => oldSignedRemainderCovarianceField Q b L true 1 x 1) =ᵐ[normalizedCubeMeasure Q]
      (fun x => -oldSignedRemainderCovarianceField Q b L false 0 x 0) := by
  have hh := parent_boundary_remainder_covariance_rotation Q b L
  refine ⟨?_,?_,?_,?_⟩
  all_goals filter_upwards [hh] with x hx
  · simpa [Fin.sum_univ_two,responsePlanarJ] using hx 0 0
  · simpa [Fin.sum_univ_two,responsePlanarJ] using hx 0 1
  · simpa [Fin.sum_univ_two,responsePlanarJ] using hx 1 0
  · simpa [Fin.sum_univ_two,responsePlanarJ] using hx 1 1

end
end ASDExplicitGamma.Native
