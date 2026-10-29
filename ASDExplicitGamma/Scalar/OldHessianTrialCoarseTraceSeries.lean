module

public import ASDExplicitGamma.Scalar.OldHessianTrialCoarseColumnBudget
public import ASDExplicitGamma.Native.OldSignedCellHistories

/-! The genuine coarse-cell shifted trace is a complete series in the
original parent coefficient. Cell extensions do not change any term. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Inverse
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- A complete descendant trace average depends only on the cell medium. -/
theorem old_hessian_descendant_trace_congr (U : TriadicCube 2) (depth : ℕ)
    (a b : CoeffField 2) (hab : a =ᵐ[volumeMeasureOn (openCubeSet U)] b) :
    descendantsAverage U depth (fun V => traceDefect (openCubeSet V) a 1)=
      descendantsAverage U depth (fun V => traceDefect (openCubeSet V) b 1) := by
  unfold descendantsAverage
  dsimp only
  apply congrArg (fun t : ℝ => (((descendantsAtDepth U depth).card:ℝ)⁻¹)*t)
  apply Finset.sum_congr rfl
  intro V hV
  unfold traceDefect
  rw [old_signed_descendant_coarse_congr U depth a b hab V hV]

/-- The shifted inverse-weighted trace is intrinsic to the medium on its
root, including every inverse-depth maximum. -/
theorem old_hessian_shifted_proxy_congr (U : TriadicCube 2) (a b : CoeffField 2)
    {lamA LamA lamB LamB : ℝ}
    (ha : IsEllipticFieldOn lamA LamA (openCubeSet U) a)
    (hb : IsEllipticFieldOn lamB LamB (openCubeSet U) b)
    (hab : a =ᵐ[volumeMeasureOn (openCubeSet U)] b) :
    rawWeakTraceProxy (fun j => lemmaVInverseDepthMax U a (1+j))
      (fun j => descendantsAverage U (1+j) (fun V => traceDefect (openCubeSet V) a 1))=
    rawWeakTraceProxy (fun j => lemmaVInverseDepthMax U b (1+j))
      (fun j => descendantsAverage U (1+j) (fun V => traceDefect (openCubeSet V) b 1)) := by
  unfold rawWeakTraceProxy
  apply congrArg (fun t : ℝ => (1-inverseHistoryDiscount^2)*t)
  apply tsum_congr
  intro j
  dsimp only
  rw [old_signed_inverse_depth_congr U (1+j) a b ha hb hab,
    old_hessian_descendant_trace_congr U (1+j) a b hab]

/-- Actual joint coarse-cell inverse/trace term at shifted depth 1+j. -/
def oldHessianCoarseTraceTerm (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (k : ResponseCoefficient (openCubeSet Q)) (j : ℕ) : ℝ :=
  let a := responseFramePlanarCoefficientField nu sigma k
  oldSignedCellAverage Q coarse (fun D => lemmaVInverseDepthMax D.val a (1+j)*
    descendantsAverage D.val (1+j) (fun V => traceDefect (openCubeSet V) a 1))

/-- Exact complete coarse trace series in the original parent coefficient,
with convergence established before the finite-cell/infinite-depth interchange. -/
theorem old_hessian_coarse_shifted_trace_series (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    Summable (fun j => inverseHistoryDiscount^(2*j)*oldHessianCoarseTraceTerm Q coarse nu sigma k j) ∧
    oldHessianCoarseShiftedTrace Q coarse nu sigma k=
      (1-inverseHistoryDiscount^2)*∑' j,inverseHistoryDiscount^(2*j)*
        oldHessianCoarseTraceTerm Q coarse nu sigma k j := by
  let a := responseFramePlanarCoefficientField nu sigma k
  let T := fun (j : ℕ) (D : OldSignedCellIndex Q coarse) =>
    inverseHistoryDiscount^(2*j)*(lemmaVInverseDepthMax D.val a (1+j)*
      descendantsAverage D.val (1+j) (fun V => traceDefect (openCubeSet V) a 1))
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    nu sigma hnu hsigma k
  have hs (D : OldSignedCellIndex Q coarse) : Summable (fun j => T j D) := by
    have hD := hEll.mono (measurableSet_openCubeSet D.val)
      (openCubeSet_subset_of_mem_descendantsAtDepth D.property)
    have hh := parent_boundary_shifted_summable inverseHistoryDiscount inverse_history_discount_range.1.ne'
      (fun j => lemmaVInverseDepthMax D.val a j*
        descendantsAverage D.val j (fun V => traceDefect (openCubeSet V) a 1)) 1
      (by simpa only [mul_assoc] using old_signed_weak_trace_proxy_summable D.val a hD)
    exact hh
  have he := old_signed_cell_average_series Q coarse T hs
  have hterm (j : ℕ) : oldSignedCellAverage Q coarse (T j)=
      inverseHistoryDiscount^(2*j)*oldHessianCoarseTraceTerm Q coarse nu sigma k j :=
    old_signed_cell_average_mul Q coarse _ _
  simp_rw [hterm] at he
  refine ⟨he.1,?_⟩
  rw [he.2,←old_signed_cell_average_mul]
  unfold oldHessianCoarseShiftedTrace
  apply congrArg (oldSignedCellAverage Q coarse)
  funext D
  have hsub := openCubeSet_subset_of_mem_descendantsAtDepth D.property
  simpa only [rawWeakTraceProxy,T,mul_assoc] using old_hessian_shifted_proxy_congr D.val _ a
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet D.val)
      nu sigma hnu hsigma (oldSignedCellCoefficient Q D.val hsub k))
    (hEll.mono (measurableSet_openCubeSet D.val) hsub)
    (old_signed_cell_frame_coefficient_ae Q D.val hsub nu sigma k)

end
end ASDExplicitGamma.Scalar
