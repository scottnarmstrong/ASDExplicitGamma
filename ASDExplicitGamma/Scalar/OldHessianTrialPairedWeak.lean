module

public import ASDExplicitGamma.Scalar.OldHessianTrialPairedCoercivity
public import ASDExplicitGamma.Scalar.OldHessianTrialWeakShift
public import ASDExplicitGamma.Native.OldSignedWeakTraceProxySeries
public import ASDExplicitGamma.Native.ParentBoundaryCompatibleWeak

/-! Complete paired weak coercivity: first and reciprocal fields share one
quarter-history energy budget, as required for the principal half-payment. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Triadic Variational
noncomputable section

/-- Both complete weak energies of a genuine response field are controlled
by one actual inverse history and one physical energy. No component gets a
separate copy of that budget. -/
theorem old_hessian_paired_response_weak (Q : TriadicCube 2)
    {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (W : BlockState 2) (hW : BlockResponseSpace a (openCubeSet Q) W)
    (hmem : MemBlockL2 (openCubeSet Q) W.eval) :
    vectorWeakHaarEnergy Q W.potential+
      vectorWeakHaarEnergy Q (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2) ≤
        lemmaVInverseHistory Q a ((3:ℝ)^(1/4:ℝ))*
          blockPairingAverage (openCubeSet Q) a W W := by
  let G := fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2
  let E := blockPairingAverage (openCubeSet Q) a W W
  have hp := memVectorL2_fst_of_memBlockL2 hmem
  have hg : MemVectorL2 (openCubeSet Q) G :=
    blockResponse_lowerImage_memVectorL2_of_flux_memVectorL2_of_mem_responseSpace_of_isEllipticFieldOn
      hW (memVectorL2_snd_of_memBlockL2 hmem) hEll
  let F : Bool → Vec 2 → Vec 2 := fun c => if c then W.potential else G
  have hF (c : Bool) (i : Fin 2) : MemLp (fun x => F c x i) 2 (normalizedCubeMeasure Q) := by
    cases c
    · exact memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hg i)
    · exact memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hp i)
  have hr := old_signed_finite_weak_projection_series Q F hF
  have he : vectorWeakHaarEnergy Q W.potential+vectorWeakHaarEnergy Q G=
      ∑ c : Bool,vectorWeakHaarEnergy Q (F c) := by
    simp only [F,Fintype.sum_bool,Bool.false_eq_true,ite_false,ite_true]
  have hq : (1:ℝ)<Real.sqrt 3 := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num : (0:ℝ)≤1)
      (by norm_num : (1:ℝ)<3)
  have hs0 : Summable (fun j : ℕ => inverseHistoryDiscount^(2*j)*lemmaVInverseDepthMax Q a j) := by
    simpa only [old_hessian_discount_square,←pow_mul] using lemmaVInverseHistory_summable Q hEll hq
  have hs : Summable (fun j : ℕ => inverseHistoryDiscount^(2*j)*(lemmaVInverseDepthMax Q a j*E)) := by
    simpa only [mul_assoc] using hs0.mul_right E
  have hd (j : ℕ) : (∑ c : Bool,∑ i : Fin 2,energy Q
      (cubeProjection Q j (fun x => F c x i)))≤lemmaVInverseDepthMax Q a j*E := by
    simpa only [F,Fintype.sum_bool,Bool.false_eq_true,ite_false,ite_true,G,E] using
      old_hessian_paired_response_projection Q j hEll W hW hmem
  have hc : 0≤1-inverseHistoryDiscount^2 := sub_nonneg.mpr
    (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le)
  have hb : vectorWeakHaarEnergy Q W.potential+vectorWeakHaarEnergy Q G≤
      compatibleInverseHistory Q a*E := by
    rw [he,hr.2]
    have hh := mul_le_mul_of_nonneg_left (hr.1.tsum_le_tsum
      (fun j => mul_le_mul_of_nonneg_left (hd j) (pow_nonneg inverse_history_discount_range.1.le _)) hs) hc
    apply hh.trans_eq
    simp only [compatibleInverseHistory,lemmaVInverseHistory,old_hessian_discount_square,←pow_mul]
    rw [mul_assoc,←tsum_mul_right]
    apply congrArg (fun t : ℝ => (1-inverseHistoryDiscount^2)*t)
    exact tsum_congr (fun j => by ring)
  exact hb.trans (mul_le_mul_of_nonneg_right (parent_boundary_compatible_history_le Q hEll)
    (compatible_blockPairingAverage_nonneg hEll W))

end
end ASDExplicitGamma.Scalar
