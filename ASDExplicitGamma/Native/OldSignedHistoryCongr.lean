module

public import ASDExplicitGamma.Native.OldSignedAffineCorrector
public import ASDExplicitGamma.Scalar.InverseHistoryBlocks

/-! OLD histories depend only on the physical coefficient on the cell.
The arbitrary whole-plane display of a restricted coefficient changes none
of its contained-descendant data. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Variational
open scoped ENNReal
noncomputable section

/-- Actual coarse matrices agree at every contained descendant when the
physical coefficient classes agree on the parent. -/
theorem old_signed_descendant_coarse_congr (Q : TriadicCube 2) (depth : ℕ)
    (a b : CoeffField 2) (hab : a =ᵐ[volumeMeasureOn (openCubeSet Q)] b)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    coarseBlockMatrix (openCubeSet U) a=coarseBlockMatrix (openCubeSet U) b :=
  coarseBlockMatrix_congr_of_ae_eq (ae_restrict_of_ae_restrict_of_subset
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) hab)

/-- The full-response depth maximum is intrinsic to the actual cell data. -/
theorem old_signed_response_depth_congr (Q : TriadicCube 2) (depth : ℕ)
    (a b : CoeffField 2) (hab : a =ᵐ[volumeMeasureOn (openCubeSet Q)] b) :
    fullResponseDepthMax Q a depth=fullResponseDepthMax Q b depth := by
  unfold fullResponseDepthMax
  apply Book.Ch02.finsetSupReal_congr
  intro U hU
  unfold fullResponseOperatorNorm
  rw [cube_coarseMatrix_eq_open,cube_coarseMatrix_eq_open,
    old_signed_descendant_coarse_congr Q depth a b hab U hU]

/-- The inverse depth maximum is likewise intrinsic; actual ellipticity
identifies its canonical inverse with the true coarse lower-right block. -/
theorem old_signed_inverse_depth_congr (Q : TriadicCube 2) (depth : ℕ)
    (a b : CoeffField 2) {lamA LamA lamB LamB : ℝ}
    (ha : IsEllipticFieldOn lamA LamA (openCubeSet Q) a)
    (hb : IsEllipticFieldOn lamB LamB (openCubeSet Q) b)
    (hab : a =ᵐ[volumeMeasureOn (openCubeSet Q)] b) :
    lemmaVInverseDepthMax Q a depth=lemmaVInverseDepthMax Q b depth := by
  unfold lemmaVInverseDepthMax
  apply Book.Ch02.finsetSupReal_congr
  intro U hU
  have hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
  rw [inverse_history_lowerRight U a (ha.mono (measurableSet_openCubeSet U) hsub),
    inverse_history_lowerRight U b (hb.mono (measurableSet_openCubeSet U) hsub),
    cube_coarseMatrix_eq_open,cube_coarseMatrix_eq_open,
    old_signed_descendant_coarse_congr Q depth a b hab U hU]

/-- The complete real inverse history agrees, retaining every depth. -/
theorem old_signed_inverse_history_congr (Q : TriadicCube 2)
    (a b : CoeffField 2) {lamA LamA lamB LamB : ℝ}
    (ha : IsEllipticFieldOn lamA LamA (openCubeSet Q) a)
    (hb : IsEllipticFieldOn lamB LamB (openCubeSet Q) b)
    (hab : a =ᵐ[volumeMeasureOn (openCubeSet Q)] b) :
    oldSignedInverseHistory Q a=oldSignedInverseHistory Q b := by
  unfold oldSignedInverseHistory lemmaVInverseHistory
  congr 1
  apply tsum_congr
  intro j
  rw [old_signed_inverse_depth_congr Q j a b ha hb hab]

/-- The complete full-response history agrees as an ENNReal value,
including finiteness, before its real conversion is used. -/
theorem old_signed_response_history_ennreal_congr (Q : TriadicCube 2)
    (a b : CoeffField 2) (hab : a =ᵐ[volumeMeasureOn (openCubeSet Q)] b) :
    completeFullResponseHistory Q a=completeFullResponseHistory Q b := by
  unfold completeFullResponseHistory
  apply congrArg (fun t : ℝ≥0∞ => ENNReal.ofReal (1-inverseHistoryDiscount) * t)
  apply tsum_congr
  intro j
  rw [old_signed_response_depth_congr Q j a b hab]

/-- The complete discounted trace history is the same physical history. -/
theorem old_signed_trace_history_congr (Q : TriadicCube 2)
    (a b : CoeffField 2) (hab : a =ᵐ[volumeMeasureOn (openCubeSet Q)] b) :
    oldSignedTraceHistory Q a=oldSignedTraceHistory Q b := by
  unfold oldSignedTraceHistory
  apply congrArg (fun t : ℝ≥0∞ => ENNReal.ofReal (1-inverseHistoryDiscount) * t)
  apply tsum_congr
  intro j
  apply congrArg ENNReal.ofReal
  apply congrArg (fun t : ℝ => inverseHistoryDiscount ^ j * t)
  unfold descendantsAverage
  apply congrArg (fun t : ℝ => (((descendantsAtDepth Q j).card : ℝ)⁻¹)*t)
  apply Finset.sum_congr rfl
  intro U hU
  unfold traceDefect
  rw [old_signed_descendant_coarse_congr Q j a b hab U hU]

/-- All three actual local histories in AN (5.1) are unchanged by an
extension choice. There is no reset to a different old-medium law. -/
theorem old_signed_histories_congr (Q : TriadicCube 2)
    (a b : CoeffField 2) {lamA LamA lamB LamB : ℝ}
    (ha : IsEllipticFieldOn lamA LamA (openCubeSet Q) a)
    (hb : IsEllipticFieldOn lamB LamB (openCubeSet Q) b)
    (hab : a =ᵐ[volumeMeasureOn (openCubeSet Q)] b) :
    oldSignedInverseHistory Q a=oldSignedInverseHistory Q b ∧
      oldSignedResponseHistory Q a=oldSignedResponseHistory Q b ∧
      oldSignedCorrectorHistory Q a=oldSignedCorrectorHistory Q b := by
  have hm : oldSignedResponseHistory Q a=oldSignedResponseHistory Q b :=
    congrArg ENNReal.toReal (old_signed_response_history_ennreal_congr Q a b hab)
  refine ⟨old_signed_inverse_history_congr Q a b ha hb hab,hm,?_⟩
  unfold oldSignedCorrectorHistory
  rw [hm,old_signed_trace_history_congr Q a b hab]

end
end ASDExplicitGamma.Native
