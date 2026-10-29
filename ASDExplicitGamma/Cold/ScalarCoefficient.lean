module

public import ASDExplicitGamma.Cold.NativeCellTrace

/-! # Positive amplitude scaling on the genuine coefficient carrier -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
namespace ASDExplicitGamma.Cold

/-- Multiplication by a deterministic scalar is measurable for the full regular-field sigma algebra. -/
theorem measurable_scalar_coefficient {d : ℕ} (c : ℝ) :
    Measurable (fun a : RegCoeffField d => c • a) := by
  apply measurable_of_entryTestR_transport
  · intro y i j
    simpa only [RegCoeffField.smul_apply,Matrix.smul_apply,smul_eq_mul] using
      (measurable_apply_entry y i j).const_mul c
  · intro i j φ hφ
    exact ⟨c,i,j,φ,hφ,fun a => entryTestR_smul i j c a⟩

/-- Positive scalar multiplication preserves the literal lower and inverse upper matrix bounds. -/
theorem cold_isEllipticMatrix_smul {d : ℕ} {lam Lam c : ℝ} {A : Mat d}
    (hc : 0 < c) (hA : IsEllipticMatrix lam Lam A) :
    IsEllipticMatrix (c*lam) (c*Lam) (c • A) := by
  rcases hA with ⟨hlam,hle,hlower,hupper⟩
  have hLam : 0 < Lam := hlam.trans_le hle
  have hdet : IsUnit A.det := isUnit_det_of_isEllipticMatrix ⟨hlam,hle,hlower,hupper⟩
  refine ⟨mul_pos hc hlam,mul_le_mul_of_nonneg_left hle hc.le,?_,?_⟩
  · intro ξ
    rw [smul_matVecMul,vecDot_smul_right]
    have h := mul_le_mul_of_nonneg_left (hlower ξ) hc.le
    convert h using 1; ring
  · intro ξ
    rw [nonsing_inv_smul c hc.ne' hdet,smul_matVecMul,vecDot_smul_right]
    have h := mul_le_mul_of_nonneg_left (hupper ξ) (inv_nonneg.mpr hc.le)
    simpa only [mul_inv_rev,mul_comm,mul_left_comm,mul_assoc] using h

/-- Positive scalar multiplication preserves actual field ellipticity on a domain. -/
theorem cold_isEllipticFieldOn_smul {d : ℕ} {lam Lam c : ℝ} {U : Set (Vec d)}
    {a : CoeffField d} (hc : 0 < c) (hEll : IsEllipticFieldOn lam Lam U a) :
    IsEllipticFieldOn (c*lam) (c*Lam) U (c • a) := by
  classical
  refine ⟨?_,fun x hx => cold_isEllipticMatrix_smul hc (hEll.2 x hx)⟩
  have hmeas := hEll.1.const_smul c
  convert hmeas using 1
  funext x i j
  by_cases hx : x ∈ U <;> simp [hx]

end ASDExplicitGamma.Cold
