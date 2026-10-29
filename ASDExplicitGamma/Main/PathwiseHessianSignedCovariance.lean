module

public import ASDExplicitGamma.Native.OldSignedWhiteContraction

/-! Bilinear form of the actual signed whole-plane q3 covariance contraction. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native

/-- The actual OLD-frame signed white contraction against two deterministic
vectors is `-v/2` times their dot product.  The kernel is the whole-plane
projected q3 kernel and the series ranges over the complete white basis. -/
theorem main_q3_signed_projected_vector_covariance
    (b : ℝ) (L : {l : ℝ // 0 < l}) (x p q : Vec 2) :
    (∑' n : whiteBasisIndex,
      q3Convolution b L h3Zero (whiteBasis n) x *
        inner ℝ (whiteBasis n)
          (∑ i : Fin 2, ∑ j : Fin 2,
            (p i * q j) • oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j)) =
      -(b ^ 2 / 2) * (∑ i : Fin 2, p i * q i) := by
  let K : WhiteNoise :=
    ∑ i : Fin 2, ∑ j : Fin 2,
      (p i * q j) • oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j
  have hparseval := whiteBasis.tsum_inner_mul_inner
    (q3Section b L h3Zero x) K
  have hsum :
      (∑' n : whiteBasisIndex,
        q3Convolution b L h3Zero (whiteBasis n) x *
          inner ℝ (whiteBasis n) K) =
        inner ℝ (q3Section b L h3Zero x) K := by
    convert hparseval using 1
    apply tsum_congr
    intro n
    rw [q3Convolution, real_inner_comm (whiteBasis n)]
  have hx : L.1 • (L.1⁻¹ • x) = x := by
    rw [smul_smul, mul_inv_cancel₀ L.2.ne', one_smul]
  have hcov (i j : Fin 2) :
      inner ℝ (q3Section b L h3Zero x)
        (oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j) =
        -(b ^ 2 / 2) * (if i = j then 1 else 0) := by
    have h := old_signed_rotated_white_point_covariance b L (L.1⁻¹ • x) i j
    rw [hx] at h
    exact h
  calc
    (∑' n : whiteBasisIndex,
      q3Convolution b L h3Zero (whiteBasis n) x *
        inner ℝ (whiteBasis n)
          (∑ i : Fin 2, ∑ j : Fin 2,
            (p i * q j) • oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j)) =
        inner ℝ (q3Section b L h3Zero x) K := by
          simpa only [K] using hsum
    _ = -(b ^ 2 / 2) * (∑ i : Fin 2, p i * q i) := by
      simp only [K, inner_sum, real_inner_smul_right]
      simp_rw [hcov]
      simp [Fin.sum_univ_two]
      ring

/-- The same cancellation in the zero-padded natural-number indexing used by
the actual main-cube q3 response directions. -/
theorem main_q3_signed_projected_vector_covariance_enumerated
    (b : ℝ) (L : {l : ℝ // 0 < l}) (x p q : Vec 2) :
    (∑' n : ℕ,
      q3Convolution b L h3Zero
          (gaussEnumerated whiteBasis n) x *
        inner ℝ (gaussEnumerated whiteBasis n)
          (∑ i : Fin 2, ∑ j : Fin 2,
            (p i * q j) • oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j)) =
      -(b ^ 2 / 2) * (∑ i : Fin 2, p i * q i) := by
  let K : WhiteNoise :=
    ∑ i : Fin 2, ∑ j : Fin 2,
      (p i * q j) • oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i j
  let f : WhiteNoise → ℝ := fun w =>
    q3Convolution b L h3Zero w x * inner ℝ w K
  have hf : f 0 = 0 := by simp [f]
  rw [enumerated_tsum_apply whiteBasis f hf]
  simpa only [f, K] using
    main_q3_signed_projected_vector_covariance b L x p q

/-- Coordinate form of the signed projection cancellation for a frozen
input vector: the complete actual q3 mode sum is `-v/2` times that vector. -/
theorem main_q3_signed_projected_vector_apply_enumerated
    (b : ℝ) (L : {l : ℝ // 0 < l}) (x p : Vec 2) (k : Fin 2) :
    (∑' n : ℕ,
      q3Convolution b L h3Zero
          (gaussEnumerated whiteBasis n) x *
        inner ℝ (gaussEnumerated whiteBasis n)
          (∑ i : Fin 2,
            p i • oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) i k)) =
      -(b ^ 2 / 2) * p k := by
  simpa [basisVec, Pi.single_apply, Fin.sum_univ_two] using
    main_q3_signed_projected_vector_covariance_enumerated b L x p (basisVec k)

end ASDExplicitGamma.Main

end
