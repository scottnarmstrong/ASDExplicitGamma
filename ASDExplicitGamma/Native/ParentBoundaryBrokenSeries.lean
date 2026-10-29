module

public import ASDExplicitGamma.Native.ParentBoundaryRestriction
public import ASDExplicitGamma.Native.OldSignedWeakTraceProxySeries

/-! Complete projection series for the broken weak norms of the SAME
physical parent fields on independent comparison cells. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Main Triadic Variational
noncomputable section

/-- A fixed finite shift preserves geometric weighted summability.
The factor is inverted only after its nonzero value is proved. -/
theorem parent_boundary_shifted_summable (alpha : ℝ) (ha : alpha≠0)
    (f : ℕ → ℝ) (depth : ℕ) (hs : Summable (fun j => alpha^(2*j)*f j)) :
    Summable (fun j => alpha^(2*j)*f (depth+j)) := by
  have ht : Summable (fun j : ℕ => alpha^(2*(depth+j))*f (depth+j)) :=
    hs.comp_injective (show Function.Injective (fun j : ℕ => depth+j) from
      fun _ _ hh => Nat.add_left_cancel hh)
  have hn : alpha^(2*depth)≠0 := pow_ne_zero _ ha
  apply (ht.mul_left ((alpha^(2*depth))⁻¹)).congr
  intro j
  calc
    _ = (alpha^(2*depth))⁻¹*alpha^(2*depth)*(alpha^(2*j)*f (depth+j)) := by
      rw [Nat.mul_add,pow_add]
      ring
    _ = _ := by rw [inv_mul_cancel₀ hn,one_mul]

private theorem discount_sq : (Real.sqrt 3)⁻¹=inverseHistoryDiscount^2 := by
  have hb : sourceHaarBase^2=Real.sqrt 3 := by
    rw [sourceHaarBase,Real.sqrt_eq_rpow,←Real.rpow_natCast,
      ←Real.rpow_mul (by norm_num : (0:ℝ)≤3)]
    congr 1
    norm_num
  have hh := congrArg (fun z : ℝ => z⁻¹) hb
  have hi : sourceHaarBase⁻¹=inverseHistoryDiscount := inverse_history_discount_eq.symm
  rw [←inv_pow,hi] at hh
  exact hh.symm

/-- Exact complete broken weak series for an arbitrary physical vector
field. No zero boundary trace or affine fine-cell condition is required. -/
theorem parent_boundary_broken_vector_series (Q : TriadicCube 2) (depth : ℕ)
    (F : Vec 2 → Vec 2)
    (hF : ∀ i,MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q)) :
    Summable (fun j : ℕ => inverseHistoryDiscount^(2*j)*
      ∑ i : Fin 2,energy Q (cubeProjection Q (depth+j) (fun x => F x i))) ∧
    descendantsAverage Q depth (fun U => vectorWeakHaarEnergy U F)=
      (1-inverseHistoryDiscount^2)*∑' j : ℕ,inverseHistoryDiscount^(2*j)*
        ∑ i : Fin 2,energy Q (cubeProjection Q (depth+j) (fun x => F x i)) := by
  have hq : (1:ℝ)<Real.sqrt 3 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg (3:ℝ)]
  have hs (i : Fin 2) : Summable (fun j : ℕ => inverseHistoryDiscount^(2*j)*
      energy Q (cubeProjection Q (depth+j) (fun x => F x i))) := by
    apply parent_boundary_shifted_summable _ inverse_history_discount_range.1.ne'
      (fun j => energy Q (cubeProjection Q j (fun x => F x i))) depth
    simpa only [discount_sq,←pow_mul] using summable_weighted_projections Q hq (hF i)
  have he (i : Fin 2) : descendantsAverage Q depth (fun U => dualEnergy U (Real.sqrt 3) (fun x => F x i))=
      (1-inverseHistoryDiscount^2)*∑' j : ℕ,inverseHistoryDiscount^(2*j)*
        energy Q (cubeProjection Q (depth+j) (fun x => F x i)) := by
    simpa only [discount_sq,←pow_mul] using parent_boundary_broken_weak_identity Q depth hq (hF i)
  constructor
  · simp_rw [Finset.mul_sum]
    exact summable_sum (fun i _ => hs i)
  · simp only [vectorWeakHaarEnergy,Homogenization.descendantsAverage_sum,he]
    rw [←Finset.mul_sum,←Summable.tsum_finsetSum (fun i _ => hs i)]
    apply congrArg (fun z : ℝ => (1-inverseHistoryDiscount^2)*z)
    exact tsum_congr (fun j => (Finset.mul_sum _ _ _).symm)

/-- Finite load aggregation of that exact complete broken series. -/
theorem parent_boundary_broken_finite_series {I : Type*} [Fintype I]
    (Q : TriadicCube 2) (depth : ℕ) (F : I → Vec 2 → Vec 2)
    (hF : ∀ c i,MemLp (fun x => F c x i) 2 (normalizedCubeMeasure Q)) :
    Summable (fun j : ℕ => inverseHistoryDiscount^(2*j)*
      ∑ c : I,∑ i : Fin 2,energy Q (cubeProjection Q (depth+j) (fun x => F c x i))) ∧
    descendantsAverage Q depth (fun U => ∑ c : I,vectorWeakHaarEnergy U (F c))=
      (1-inverseHistoryDiscount^2)*∑' j : ℕ,inverseHistoryDiscount^(2*j)*
        ∑ c : I,∑ i : Fin 2,energy Q (cubeProjection Q (depth+j) (fun x => F c x i)) := by
  classical
  have hs (c : I) := parent_boundary_broken_vector_series Q depth (F c) (hF c)
  constructor
  · simpa only [Finset.mul_sum] using summable_sum (fun c _ => (hs c).1)
  · calc
      _ = ∑ c : I,descendantsAverage Q depth (fun U => vectorWeakHaarEnergy U (F c)) :=
        Homogenization.descendantsAverage_sum Q depth Finset.univ
          (fun U c => vectorWeakHaarEnergy U (F c))
      _ = _ := by
        simp_rw [(fun c => (hs c).2)]
        rw [←Finset.mul_sum,←Summable.tsum_finsetSum (fun c _ => (hs c).1)]
        apply congrArg (fun z : ℝ => (1-inverseHistoryDiscount^2)*z)
        exact tsum_congr (fun j => (Finset.mul_sum _ _ _).symm)

end
end ASDExplicitGamma.Native
