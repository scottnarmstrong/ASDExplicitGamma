module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import ASDExplicitGamma.Scalar.AnalyticEigenvalueBound

/-! Trace reduction of the coarse-duality operator estimate. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Matrix

/-- Inverting a Hermitian matrix in its actual eigenbasis gives the reciprocal trace. -/
theorem hermitian_inverse_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hpos : A.PosDef) :
    A⁻¹.trace = ∑ i,(hpos.isHermitian.eigenvalues i)⁻¹ := by
  let hA := hpos.isHermitian
  let U := hA.eigenvectorUnitary
  let v : (ι → ℝ)ˣ :=
    { val := hA.eigenvalues
      inv := fun i => (hA.eigenvalues i)⁻¹
      val_inv := funext (fun i => mul_inv_cancel₀ (hpos.eigenvalues_pos i).ne')
      inv_val := funext (fun i => inv_mul_cancel₀ (hpos.eigenvalues_pos i).ne') }
  have hv : Ring.inverse hA.eigenvalues=(fun i => (hA.eigenvalues i)⁻¹) := by
    change Ring.inverse (v : ι → ℝ)=_
    rw [Ring.inverse_unit]
    rfl
  have hi : (U : Matrix ι ι ℝ)⁻¹=star (U : Matrix ι ι ℝ) :=
    Matrix.inv_eq_left_inv (Unitary.coe_star_mul_self U)
  have his : (star (U : Matrix ι ι ℝ))⁻¹=(U : Matrix ι ι ℝ) :=
    Matrix.inv_eq_left_inv (Unitary.coe_mul_star_self U)
  have hs : A=(U : Matrix ι ι ℝ)*Matrix.diagonal hA.eigenvalues*star (U : Matrix ι ι ℝ) := by
    simpa only [Unitary.conjStarAlgAut_apply,Function.comp_def,
      RCLike.ofReal_real_eq_id,id_eq] using hA.spectral_theorem
  conv_lhs => rw [hs,Matrix.mul_inv_rev,Matrix.mul_inv_rev,his,hi,Matrix.inv_diagonal]
  rw [← Matrix.mul_assoc,Matrix.trace_mul_cycle]
  simp only [Unitary.coe_star_mul_self,Matrix.one_mul,Matrix.trace_diagonal,hv]

/-- The Loewner coarse-duality inequality gives the inverse trace inequality. -/
theorem inverse_trace_le_trace_of_orthogonal_duality {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A R : Matrix ι ι ℝ) (hR : Rᵀ*R=1)
    (hdual : (A-R*A⁻¹*Rᵀ).PosSemidef) : A⁻¹.trace≤A.trace := by
  have ht := hdual.trace_nonneg
  rw [Matrix.trace_sub,Matrix.trace_mul_cycle,hR,Matrix.one_mul] at ht
  exact sub_nonneg.mp ht

/-- SC-ANALYTIC-BOUND-M at every actual eigenvalue of the positive coarse matrix. -/
theorem eigenvalues_le_of_coarse_duality {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A R : Matrix ι ι ℝ) (hA : A.PosDef) (hR : Rᵀ*R=1)
    (hdual : (A-R*A⁻¹*Rᵀ).PosSemidef) :
    let T := A.trace-(Fintype.card ι:ℝ)
    0≤T ∧ ∀ i,hA.isHermitian.eigenvalues i≤1+2*T+Real.sqrt (2*T) := by
  have ht := inverse_trace_le_trace_of_orthogonal_duality A R hR hdual
  rw [hermitian_inverse_trace A hA,hA.isHermitian.trace_eq_sum_eigenvalues] at ht
  simpa only [hA.isHermitian.trace_eq_sum_eigenvalues,RCLike.ofReal_real_eq_id,id_eq] using
    eigenvalue_bound_of_inverse_trace hA.isHermitian.eigenvalues hA.eigenvalues_pos ht

end ASDExplicitGamma.Scalar
