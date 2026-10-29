module

public import ASDExplicitGamma.Scalar.PhysicalResolventParity

/-! Lipschitz continuity of the pure-flux block inverse in its coefficient operator (public
copy of the private lemma). -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open scoped BigOperators InnerProductSpace

noncomputable section

section Generic

variable {Y X : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

theorem block_sub_eq_inserted {α : ℝ} (A A' : X →L[ℝ] Y) :
    pureFluxBlockOperator α A' - pureFluxBlockOperator α A =
      pureFluxBlockOperator 0 (A' - A) := by
  have hA : A' = A + (A' - A) := by abel
  have hM : pureFluxBlockOperator α A' =
      pureFluxBlockOperator α A + pureFluxBlockOperator 0 (A' - A) := by
    exact (congrArg (pureFluxBlockOperator α) hA).trans
      (pureFluxBlockOperator_add α A (A' - A)).symm
  rw [hM]
  abel

theorem blockInverse_resolvent {α : ℝ} (hα : 0 < α) (A A' : X →L[ℝ] Y) :
    pureFluxBlockInverse α hα A - pureFluxBlockInverse α hα A' =
      pureFluxBlockInverse α hα A *
        (pureFluxBlockOperator α A' - pureFluxBlockOperator α A) *
          pureFluxBlockInverse α hα A' := by
  let B := pureFluxBlockInverse α hα A
  let B' := pureFluxBlockInverse α hα A'
  let T := pureFluxBlockOperator α A
  let T' := pureFluxBlockOperator α A'
  have hBT : B * T = 1 := pureFluxBlockInverse_right α hα A
  have hT'B' : T' * B' = 1 := pureFluxBlockInverse_left α hα A'
  change B - B' = B * (T' - T) * B'
  calc
    B - B' = B * 1 - 1 * B' := by simp
    _ = B * (T' * B') - (B * T) * B' := by rw [hT'B', hBT]
    _ = (B * T') * B' - (B * T) * B' := by rw [← mul_assoc]
    _ = (B * T' - B * T) * B' := by rw [sub_mul]
    _ = B * (T' - T) * B' := by rw [← mul_sub]

theorem blockInverse_diff_norm_le {α : ℝ} (hα : 0 < α) (A A' : X →L[ℝ] Y) :
    ‖pureFluxBlockInverse α hα A - pureFluxBlockInverse α hα A'‖ ≤
      (α⁻¹) ^ 2 * ‖A - A'‖ := by
  rw [blockInverse_resolvent hα A A', block_sub_eq_inserted]
  have hB := pureFluxBlockInverse_opNorm_le hα A
  have hB' := pureFluxBlockInverse_opNorm_le hα A'
  have hC := pureFluxBlockInserted_opNorm_le (A' - A)
  let B := pureFluxBlockInverse α hα A
  let C := pureFluxBlockOperator 0 (A' - A)
  let B' := pureFluxBlockInverse α hα A'
  have hBC : ‖B * C‖ ≤ ‖B‖ * ‖C‖ := norm_mul_le B C
  have hBCB : ‖B * C * B'‖ ≤ (‖B‖ * ‖C‖) * ‖B'‖ := by
    calc
      ‖B * C * B'‖ ≤ ‖B * C‖ * ‖B'‖ := norm_mul_le (B * C) B'
      _ ≤ (‖B‖ * ‖C‖) * ‖B'‖ := mul_le_mul_of_nonneg_right hBC (norm_nonneg B')
  calc
    ‖B * C * B'‖ ≤ (‖B‖ * ‖C‖) * ‖B'‖ := hBCB
    _ ≤ (α⁻¹ * ‖A' - A‖) * α⁻¹ := by gcongr
    _ = (α⁻¹) ^ 2 * ‖A - A'‖ := by rw [norm_sub_rev]; ring

theorem blockInverse_continuous {α : ℝ} (hα : 0 < α) :
    Continuous (fun A : X →L[ℝ] Y => pureFluxBlockInverse α hα A) := by
  let c : NNReal := ⟨(α⁻¹) ^ 2, sq_nonneg _⟩
  have hc : (c : ℝ) = (α⁻¹) ^ 2 := rfl
  have hLip : LipschitzWith c (fun A : X →L[ℝ] Y => pureFluxBlockInverse α hα A) := by
    apply LipschitzWith.of_dist_le_mul
    intro A A'
    rw [dist_eq_norm, dist_eq_norm]
    simpa only [hc] using blockInverse_diff_norm_le hα A A'
  exact hLip.continuous

end Generic

end

end ASDExplicitGamma.Scalar
