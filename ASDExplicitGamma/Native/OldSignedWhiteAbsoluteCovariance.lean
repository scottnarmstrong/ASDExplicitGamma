module

public import ASDExplicitGamma.Native.OldSignedCovarianceIntegral

/-! Absolute complete white covariance control by the product of the
actual Hilbert norms, allowing an L2 harmonic kernel and an L2 test field. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
noncomputable section

/-- Finite white cross-coefficients obey Cauchy--Schwarz without a
quadratic majorant that would demand an extra moment from either field. -/
theorem old_signed_white_absolute_sum_le {H I : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (e : HilbertBasis I ℝ H) (u v : H) (s : Finset I) :
    (∑ n ∈ s,|inner ℝ (e n) u*inner ℝ (e n) v|)≤‖u‖*‖v‖ := by
  have hu := e.orthonormal.sum_inner_products_le (s := s) (x := u)
  have hv := e.orthonormal.sum_inner_products_le (s := s) (x := v)
  simp only [Real.norm_eq_abs,sq_abs] at hu hv
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun n => |inner ℝ (e n) u|) (fun n => |inner ℝ (e n) v|)
  simp only [sq_abs,←abs_mul] at hcs
  have hm := mul_le_mul hu hv (Finset.sum_nonneg (fun n _ => sq_nonneg _)) (sq_nonneg ‖u‖)
  have hn : 0≤∑ n ∈ s,|inner ℝ (e n) u*inner ℝ (e n) v| :=
    Finset.sum_nonneg (fun n _ => abs_nonneg _)
  apply (sq_le_sq₀ hn (mul_nonneg (norm_nonneg u) (norm_nonneg v))).mp
  exact hcs.trans (hm.trans_eq (by ring))

/-- The absolute complete covariance series is summable and bounded by
the product of the actual two kernel norms. -/
theorem old_signed_white_absolute_tsum_le {H I : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (e : HilbertBasis I ℝ H) (u v : H) :
    Summable (fun n => |inner ℝ (e n) u*inner ℝ (e n) v|) ∧
      (∑' n,|inner ℝ (e n) u*inner ℝ (e n) v|)≤‖u‖*‖v‖ := by
  have hs := summable_of_sum_le (fun n => abs_nonneg (inner ℝ (e n) u*inner ℝ (e n) v))
    (old_signed_white_absolute_sum_le e u v)
  exact ⟨hs,hs.tsum_le_of_sum_le (old_signed_white_absolute_sum_le e u v)⟩

end
end ASDExplicitGamma.Native
