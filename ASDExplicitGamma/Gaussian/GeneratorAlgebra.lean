module

public import ASDExplicitGamma.Gaussian.GaussCentering

/-! # Absolute center/mixed/remainder expansion of a covariance generator -/

@[expose] public section

open Filter Set
open scoped Topology

namespace ASDExplicitGamma.Gaussian

section
variable {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A bounded image of square-summable directions is square-summable. -/
theorem summable_sq_norm_map {H : ℕ → E} (hH : Summable (fun j => ‖H j‖ ^ 2))
    (A : E →L[ℝ] X) : Summable (fun j => ‖A (H j)‖ ^ 2) := by
  apply (hH.mul_left (‖A‖ ^ 2)).of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm (H j)) 2
  simpa only [mul_pow] using h

/-- Bilinear evaluations of two bounded images are absolutely summable. -/
theorem summable_bilinear_images {H : ℕ → E} (hH : Summable (fun j => ‖H j‖ ^ 2))
    (B : X →L[ℝ] Y →L[ℝ] ℝ) (A : E →L[ℝ] X) (D : E →L[ℝ] Y) :
    Summable (fun j => B (A (H j)) (D (H j))) := by
  apply (hH.mul_left (‖B‖ * ‖A‖ * ‖D‖)).of_norm_bounded
  intro j
  calc
    ‖B (A (H j)) (D (H j))‖ ≤ ‖B‖ * ‖A (H j)‖ * ‖D (H j)‖ := B.le_opNorm₂ _ _
    _ ≤ ‖B‖ * (‖A‖ * ‖H j‖) * (‖D‖ * ‖H j‖) := by
      gcongr
      · exact A.le_opNorm _
      · exact D.le_opNorm _
    _ = (‖B‖ * ‖A‖ * ‖D‖) * ‖H j‖ ^ 2 := by ring

/-- Exact covariance splitting for a symmetric bilinear Hessian. The mixed term is retained. -/
theorem bilinear_covariance_split {H : ℕ → E}
    (hH : Summable (fun j => ‖H j‖ ^ 2)) (B : X →L[ℝ] X →L[ℝ] ℝ)
    (hB : ∀ u w, B u w = B w u) (P C : E →L[ℝ] X) :
    (1 / 2 : ℝ) * (∑' j, B (P (H j)) (P (H j))) =
      (1 / 2 : ℝ) * (∑' j, B (C (H j)) (C (H j))) +
      (∑' j, B (C (H j)) ((P - C) (H j))) +
      (1 / 2 : ℝ) * (∑' j, B ((P - C) (H j)) ((P - C) (H j))) := by
  have hcc := summable_bilinear_images hH B C C
  have hcr := summable_bilinear_images hH B C (P - C)
  have hrr := summable_bilinear_images hH B (P - C) (P - C)
  have hpoint (j : ℕ) : B (P (H j)) (P (H j)) =
      B (C (H j)) (C (H j)) + 2 * B (C (H j)) ((P - C) (H j)) +
        B ((P - C) (H j)) ((P - C) (H j)) := by
    have hp : P (H j) = C (H j) + (P - C) (H j) := by
      simp only [sub_apply, add_sub_cancel]
    rw [hp]
    simp only [map_add, add_apply]
    rw [hB ((P - C) (H j)) (C (H j))]
    ring
  rw [tsum_congr hpoint, (hcc.add (hcr.mul_left 2)).tsum_add hrr,
    hcc.tsum_add (hcr.mul_left 2), tsum_mul_left]
  ring

end

section FiniteCenters
variable {n : ℕ} {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

private theorem map_coordinates (I : (Fin n → ℝ) →L[ℝ] X) (u : Fin n → ℝ) :
    I u = ∑ i, u i • I (Pi.single i 1) := by
  classical
  have hu : u = ∑ i, u i • Pi.single i (1 : ℝ) := by
    calc
      u = ∑ i, Pi.single i (u i) := (Finset.univ_sum_single u).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
  conv_lhs => rw [hu]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact I.map_smul _ _

/-- The physical center covariance, including every off-diagonal entry. -/
noncomputable def centerCovariance (H : ℕ → E) (L : E →L[ℝ] (Fin n → ℝ))
    (i l : Fin n) : ℝ := ∑' j, L (H j) i * L (H j) l

/-- The center generator written in the coordinates (8.17). -/
noncomputable def centerGenerator (H : ℕ → E) (L : E →L[ℝ] (Fin n → ℝ))
    (I : (Fin n → ℝ) →L[ℝ] X) (B : X →L[ℝ] X →L[ℝ] ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ l, centerCovariance H L i l * B (I (Pi.single i 1)) (I (Pi.single l 1))

/-- The mixed generator written with all actual center/remainder cross covariances. -/
noncomputable def mixedGenerator (H : ℕ → E) (L : E →L[ℝ] (Fin n → ℝ))
    (I : (Fin n → ℝ) →L[ℝ] X) (R : E →L[ℝ] X) (B : X →L[ℝ] X →L[ℝ] ℝ) : ℝ :=
  ∑' j, ∑ i, L (H j) i * B (I (Pi.single i 1)) (R (H j))

/-- Center matrix coefficients are absolutely summable. -/
theorem summable_center_covariance {H : ℕ → E}
    (hH : Summable (fun j => ‖H j‖ ^ 2)) (L : E →L[ℝ] (Fin n → ℝ)) (i l : Fin n) :
    Summable (fun j => L (H j) i * L (H j) l) := by
  let B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.proj l)
  exact summable_bilinear_images hH B L L

/-- The trace along constant center fields is the full center covariance matrix generator. -/
theorem center_generator_eq {H : ℕ → E} (hH : Summable (fun j => ‖H j‖ ^ 2))
    (L : E →L[ℝ] (Fin n → ℝ)) (I : (Fin n → ℝ) →L[ℝ] X)
    (B : X →L[ℝ] X →L[ℝ] ℝ) :
    (1 / 2 : ℝ) * (∑' j, B (I (L (H j))) (I (L (H j)))) =
      centerGenerator H L I B := by
  classical
  have hpoint (j : ℕ) : B (I (L (H j))) (I (L (H j))) =
      ∑ i, ∑ l, (L (H j) i * L (H j) l) * B (I (Pi.single i 1)) (I (Pi.single l 1)) := by
    rw [map_coordinates I (L (H j))]
    simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro l hl
    ring
  have hs (i l : Fin n) : Summable (fun j =>
      (L (H j) i * L (H j) l) * B (I (Pi.single i 1)) (I (Pi.single l 1))) :=
    (summable_center_covariance hH L i l).mul_right _
  rw [tsum_congr hpoint, Summable.tsum_finsetSum (fun i _ =>
    summable_sum fun l _ => hs i l)]
  simp_rw [Summable.tsum_finsetSum (fun l _ => hs _ l), tsum_mul_right]
  rfl

/-- The bilinear mixed trace equals the center-coordinate mixed trace. -/
theorem mixed_generator_eq (H : ℕ → E) (L : E →L[ℝ] (Fin n → ℝ))
    (I : (Fin n → ℝ) →L[ℝ] X) (R : E →L[ℝ] X) (B : X →L[ℝ] X →L[ℝ] ℝ) :
    (∑' j, B (I (L (H j))) (R (H j))) = mixedGenerator H L I R B := by
  apply tsum_congr
  intro j
  rw [map_coordinates I, map_sum]
  simp only [sum_apply, map_smul, smul_apply, smul_eq_mul]

/-- The generator identity, including the center matrix and the mixed center/remainder term. -/
theorem generator_split {H : ℕ → E} (hH : Summable (fun j => ‖H j‖ ^ 2))
    (P : E →L[ℝ] X) (L : E →L[ℝ] (Fin n → ℝ)) (I : (Fin n → ℝ) →L[ℝ] X)
    (B : X →L[ℝ] X →L[ℝ] ℝ) (hB : ∀ u w, B u w = B w u) :
    (1 / 2 : ℝ) * (∑' j, B (P (H j)) (P (H j))) =
      centerGenerator H L I B + mixedGenerator H L I (P - I.comp L) B +
        (1 / 2 : ℝ) * (∑' j, B ((P - I.comp L) (H j)) ((P - I.comp L) (H j))) := by
  rw [bilinear_covariance_split hH B hB P (I.comp L)]
  rw [show (fun j => B ((I.comp L) (H j)) ((I.comp L) (H j))) =
    (fun j => B (I (L (H j))) (I (L (H j)))) from rfl]
  rw [center_generator_eq hH L I B]
  rw [show (fun j => B ((I.comp L) (H j)) ((P - I.comp L) (H j))) =
    (fun j => B (I (L (H j))) ((P - I.comp L) (H j))) from rfl]
  rw [mixed_generator_eq H L I (P - I.comp L) B]

end FiniteCenters
end ASDExplicitGamma.Gaussian
