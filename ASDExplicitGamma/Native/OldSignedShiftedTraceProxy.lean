module

public import ASDExplicitGamma.Native.OldSignedTiledWeakProjection
public import ASDExplicitGamma.Inverse.RawWeakHistory

/-! Genuine convergence and comparison for the source-tiling weak history. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic Inverse
noncomputable section

/-- Shifting a convergent weighted series preserves its local geometric
weights, provided their base is nonzero. -/
theorem old_signed_summable_weighted_shift (w : ℝ) (hw : w ≠ 0)
    (f : ℕ → ℝ) (hs : Summable (fun j => w^j*f j)) (mesh : ℕ) :
    Summable (fun j => w^j*f (mesh+j)) := by
  have ht := (summable_nat_add_iff mesh).mpr hs
  have he : (fun j => w^(j+mesh)*f (j+mesh))=
      (fun j => w^mesh*(w^j*f (mesh+j))) := by
    funext j
    rw [pow_add,Nat.add_comm j mesh]
    ring
  rw [he] at ht
  exact (summable_mul_left_iff (pow_ne_zero _ hw)).mp ht

/-- The inverse-weighted trace tail at the physical mesh depth is finite. -/
theorem old_signed_shifted_weak_trace_proxy_summable
    (Q : TriadicCube 2) (mesh : ℕ) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    Summable (fun j : ℕ => inverseHistoryDiscount^(2*j)*lemmaVInverseDepthMax Q a (mesh+j)*
      descendantsAverage Q (mesh+j) (fun U => traceDefect (openCubeSet U) a 1)) := by
  have hs := old_signed_weak_trace_proxy_summable Q a hEll
  simp only [pow_mul,mul_assoc] at hs ⊢
  exact old_signed_summable_weighted_shift _
    (pow_ne_zero _ inverse_history_discount_range.1.ne') _ hs mesh

/-- A proved family of parent projection bounds controls the actual tiled
weak energy by the shifted inverse-weighted trace, without a mesh penalty. -/
theorem old_signed_tiled_weak_trace_bound {ι : Type*} [Fintype ι]
    (Q : TriadicCube 2) (mesh : ℕ) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (F : ι → Vec 2 → Vec 2)
    (hF : ∀ c i,MemLp (fun x => F c x i) 2 (normalizedCubeMeasure Q))
    (hdepth : ∀ j, (∑ c,∑ i,energy Q (cubeProjection Q j (fun x => F c x i))) ≤
      lemmaVInverseDepthMax Q a j*descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1)) :
    descendantsAverage Q mesh (fun U => ∑ c,vectorWeakHaarEnergy U (F c)) ≤
      rawWeakTraceProxy (fun j => lemmaVInverseDepthMax Q a (mesh+j))
        (fun j => descendantsAverage Q (mesh+j) (fun U => traceDefect (openCubeSet U) a 1)) := by
  have hr := old_signed_tiled_weak_projection_series Q mesh F hF
  have hs := old_signed_shifted_weak_trace_proxy_summable Q mesh a hEll
  have hα := inverse_history_discount_range
  have hc : 0 ≤ 1-inverseHistoryDiscount^2 :=
    sub_nonneg.mpr (pow_le_one₀ hα.1.le hα.2.le)
  rw [hr.2]
  apply mul_le_mul_of_nonneg_left _ hc
  apply hr.1.tsum_le_tsum _ hs
  intro j
  exact (mul_le_mul_of_nonneg_left (hdepth (mesh+j))
    (pow_nonneg hα.1.le (2*j))).trans_eq (by ring)

end
end ASDExplicitGamma.Native
