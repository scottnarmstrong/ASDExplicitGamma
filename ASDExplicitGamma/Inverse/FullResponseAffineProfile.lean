module

public import ASDExplicitGamma.Inverse.FullResponseBudgetSigns

/-! The complete source endpoint rows equal the literal certified affine profiles. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Numerics.Inverse
noncomputable section

/-- Exact source (11.6) row identity at order 64, before the outer clock is enlarged. -/
theorem full_response_endpoint_sum64 (γ D : ℝ) :
    (∑ a : Fin 3, fullResponseLeadingRow64 γ D a)+
      (∑ b : Fin 4, fullResponseErrorRow64 γ D b) =
        (invFull64Bt:ℝ)+γ*(3:ℝ)^(2*γ*D)*((invFull64KD:ℝ)*D+(invFull64K0:ℝ)) := by
  simp only [fullResponseLeadingRow64,fullResponseErrorRow64,fullResponseLeadingEndpoint,
    fullResponseErrorEndpoint,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Finset.univ_eq_empty,Finset.sum_empty,add_zero]
  unfold invFull64Bt invFull64KD invFull64K0 invFull64mx invFull64de invFull64C
  push_cast
  unfold planarGradientCharge
  norm_num only [Nat.reduceMul]
  ring

/-- Exact source (11.6) row identity at order 128, before the outer clock is enlarged. -/
theorem full_response_endpoint_sum128 (γ D : ℝ) :
    (∑ a : Fin 3, fullResponseLeadingRow128 γ D a)+
      (∑ b : Fin 4, fullResponseErrorRow128 γ D b) =
        (invFull128Bt:ℝ)+γ*(3:ℝ)^(2*γ*D)*((invFull128KD:ℝ)*D+(invFull128K0:ℝ)) := by
  simp only [fullResponseLeadingRow128,fullResponseErrorRow128,fullResponseLeadingEndpoint,
    fullResponseErrorEndpoint,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Finset.univ_eq_empty,Finset.sum_empty,add_zero]
  unfold invFull128Bt invFull128KD invFull128K0 invFull128mx invFull128de invFull128C
  push_cast
  unfold planarGradientCharge
  norm_num only [Nat.reduceMul]
  ring

end
end ASDExplicitGamma.Inverse
