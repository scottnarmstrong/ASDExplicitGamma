module

public import ASDExplicitGamma.Native.OldSignedFullTraceProxy

/-! Complete projection representation of the doubled OLD weak norm. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic Inverse
noncomputable section

/-- Full-block depth projection energy in the physical product norm. -/
def oldSignedFullProjectionEnergy (Q : TriadicCube 2) (j : ℕ) (F : Vec 2 → BlockVec 2) : ℝ :=
  (∑ i,energy Q (cubeProjection Q j (fun x => (F x).1 i)))+
    (∑ i,energy Q (cubeProjection Q j (fun x => (F x).2 i)))

/-- The doubled weak norm squared is the sum of the two genuine energies. -/
theorem old_signed_block_weak_norm_sq (Q : TriadicCube 2) (F : Vec 2 → BlockVec 2) :
    (oldSignedBlockWeakNorm Q F)^2=vectorWeakHaarEnergy Q (fun x => (F x).1)+
      vectorWeakHaarEnergy Q (fun x => (F x).2) := by
  unfold oldSignedBlockWeakNorm
  rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
  simp only [vectorWeakHaarNorm,Real.sq_sqrt (vectorWeakHaarEnergy_nonneg Q _)]

/-- Full-block energy is invariant under the actual block exchange. -/
theorem old_signed_block_weak_norm_sq_swap (Q : TriadicCube 2) (F : Vec 2 → BlockVec 2) :
    (oldSignedBlockWeakNorm Q (fun x => (F x).swap))^2=(oldSignedBlockWeakNorm Q F)^2 := by
  simp only [old_signed_block_weak_norm_sq,Prod.swap]
  exact add_comm _ _

/-- Full-block complete projection series, with summability recorded first. -/
theorem old_signed_full_weak_projection_series (Q : TriadicCube 2)
    (F : Vec 2 → BlockVec 2) (hF : MemBlockL2 (openCubeSet Q) F) :
    Summable (fun j : ℕ => inverseHistoryDiscount^(2*j)*oldSignedFullProjectionEnergy Q j F) ∧
    (oldSignedBlockWeakNorm Q F)^2=(1-inverseHistoryDiscount^2)*
      ∑' j : ℕ,inverseHistoryDiscount^(2*j)*oldSignedFullProjectionEnergy Q j F := by
  have h1 := old_signed_vector_weak_projection_series Q (fun x => (F x).1)
    (fun i => memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hF) i))
  have h2 := old_signed_vector_weak_projection_series Q (fun x => (F x).2)
    (fun i => memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hF) i))
  constructor
  · simpa only [oldSignedFullProjectionEnergy,mul_add] using h1.1.add h2.1
  · rw [old_signed_block_weak_norm_sq,h1.2,h2.2]
    simp only [oldSignedFullProjectionEnergy,mul_add]
    rw [h1.1.tsum_add h2.1]
    ring

/-- A proved full-block depth budget sums to the physical trace proxy.
The constant is kept explicit for the sharp directional source payments. -/
theorem old_signed_full_weak_proxy_bound (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (F : Vec 2 → BlockVec 2) (hF : MemBlockL2 (openCubeSet Q) F) (c : ℝ)
    (hdepth : ∀ j,oldSignedFullProjectionEnergy Q j F ≤
      c*(fullResponseDepthMax Q a j*descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1))) :
    (oldSignedBlockWeakNorm Q F)^2 ≤ c*rawWeakTraceProxy (fullResponseDepthMax Q a)
      (fun j => descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1)) := by
  have hseries := old_signed_full_weak_projection_series Q F hF
  have hs := old_signed_full_trace_proxy_summable Q a hEll
  have hh := hseries.1.tsum_le_tsum (fun j =>
    (mul_le_mul_of_nonneg_left (hdepth j) (pow_nonneg inverse_history_discount_range.1.le (2*j))).trans_eq
      (show inverseHistoryDiscount^(2*j)*(c*(fullResponseDepthMax Q a j*
        descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1)))=
        c*(inverseHistoryDiscount^(2*j)*fullResponseDepthMax Q a j*
          descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1)) by ring)) (hs.mul_left c)
  rw [tsum_mul_left] at hh
  rw [hseries.2]
  have hc : 0 ≤ 1-inverseHistoryDiscount^2 :=
    sub_nonneg.mpr (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le)
  exact (mul_le_mul_of_nonneg_left hh hc).trans_eq (by unfold rawWeakTraceProxy; ring)

end
end ASDExplicitGamma.Native
