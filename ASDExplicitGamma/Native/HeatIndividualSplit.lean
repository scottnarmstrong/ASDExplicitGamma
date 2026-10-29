module

public import ASDExplicitGamma.Native.HeatConfiguredSourceComparison
public import ASDExplicitGamma.Native.HeatRemainderMoments

/-! Exact bounded-bank and rare decomposition of the individual source row. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native MeasureTheory
noncomputable section

/-- The full individual source bill after splitting the OLD bank into its
bounded part and its rare reserve. Both predecessor and current rare moments
are retained, in each of the first and second rare orders. -/
def heatIndividualSourceBill (k : ℕ) (e d κ c b T R : ℝ) : ℝ :=
  (k:ℝ)*e*((d*b+4*(2*κ*b+c*b^2))*T^(k-1)+(2*κ*b+c*b^2)*T^k+
    d*(R*T^(k-1))+(2*κ+2*b*c)*(4*(R*T^(k-1))+R*T^k)+
    c*(4*(R^2*T^(k-1))+R^2*T^k))

/-- Exact expansion at the split bank, before expectations or norm bounds. -/
theorem heat_individual_source_bill_eq (k : ℕ) (hk : 1 ≤ k)
    (e d κ c b T R : ℝ) :
    heatIndividualSourceBill k e d κ c b T R =
      (k:ℝ)*e*T^(k-1)*(d*(b+R)+2*κ*((b+R)*(T+4))+c*((b+R)^2*(T+4))) := by
  have hp : T^k = T^(k-1)*T := by
    rw [← pow_succ, Nat.sub_add_cancel hk]
  rw [heatIndividualSourceBill,hp]
  ring

/-- The physical inverse trace bound and the OLD rare split suffice for the
entire individual source row; no moment or configured-generator bound is
assumed here. -/
theorem heat_individual_source_le_bill (k : ℕ) (hk : 1 ≤ k)
    (e a κ c b T P D R : ℝ)
    (he : 0 ≤ e) (ha : 0 ≤ a) (hκ : 0 ≤ κ) (hc : 0 ≤ c)
    (hT : 0 ≤ T) (hP : 0 ≤ P) (hD : D ≤ 2*P) (hPR : P ≤ b+R) :
    (k:ℝ)*T^(k-1)*(e*(a*D+2*κ*(P*(T+4))+c*(P^2*(T+4)))) ≤
      heatIndividualSourceBill k e (2*a) κ c b T R := by
  rw [heat_individual_source_bill_eq k hk]
  have hBR : 0 ≤ b+R := hP.trans hPR
  have hP2 : P^2 ≤ (b+R)^2 := pow_le_pow_left₀ hP hPR 2
  have hTF : 0 ≤ T+4 := by positivity
  have hbank : a*D ≤ (2*a)*(b+R) := by
    calc
      _ ≤ a*(2*P) := mul_le_mul_of_nonneg_left hD ha
      _ = (2*a)*P := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hPR (by positivity)
  have hlin : 2*κ*(P*(T+4)) ≤ 2*κ*((b+R)*(T+4)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hPR hTF) (by positivity)
  have hquad : c*(P^2*(T+4)) ≤ c*((b+R)^2*(T+4)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hP2 hTF) hc
  have hsum := add_le_add (add_le_add hbank hlin) hquad
  calc
    _ = (k:ℝ)*e*T^(k-1)*(a*D+2*κ*(P*(T+4))+c*(P^2*(T+4))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

end
end ASDExplicitGamma.Native
