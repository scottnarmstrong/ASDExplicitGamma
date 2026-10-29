module

public import ASDExplicitGamma.Native.FullResponseRows
public import ASDExplicitGamma.Scalar.UpperCellEnergyEndpointProfiles

/-! Exact full64 population and depth arithmetic for the complete UPPER
future history. The population factor is included before summing the tail. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Native
noncomputable section

/-- The dimension-two p64 population factor is precisely 3^(j/32). -/
theorem upper_cell_population_factor (j : ℕ) :
    ((9:ℝ)^j)^((1:ℝ)/64) = (3:ℝ)^((j:ℝ)/32) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 9)]
  rw [show (9:ℝ) = (3:ℝ)^(2:ℝ) by norm_num,
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
  congr 1
  ring

/-- The discounted actual full64 depth budget is exactly four times the
native complete-future term, in the old frame at physical lag fourteen. -/
theorem upper_cell_future_term_identity (gamma height : ℝ) (j : ℕ) :
    (1-(3:ℝ)^(-(1/4:ℝ)))*((3:ℝ)^(-(1/4:ℝ)))^j*
      ((9:ℝ)^j)^((1:ℝ)/64)*
      (4*((1009309/500000:ℝ)+gamma*(16684*(height+(14+(j:ℝ))+1)+5899542))*
        (3:ℝ)^((2*height+4*(14+(j:ℝ))+4)*gamma)) =
      4*nativeFullResponse64FutureTerm gamma (height+15) 15 j := by
  rw [upper_cell_population_factor]
  have hp : ((3:ℝ)^(-(1/4:ℝ)))^j*(3:ℝ)^((j:ℝ)/32)*
      (3:ℝ)^((2*height+4*(14+(j:ℝ))+4)*gamma) =
      ((3:ℝ)^(-(7/32:ℝ)+4*gamma))^j*
        (3:ℝ)^(2*gamma*(height+15)+2*gamma*15) := by
    simp only [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3),
      ← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
    congr 1
    ring
  unfold nativeFullResponse64FutureTerm
  calc
    _ = 4*(1-(3:ℝ)^(-(1/4:ℝ)))*
        (1009309/500000+gamma*(16684*(height+(j:ℝ)+15)+5899542))*
        (((3:ℝ)^(-(1/4:ℝ)))^j*(3:ℝ)^((j:ℝ)/32)*
          (3:ℝ)^((2*height+4*(14+(j:ℝ))+4)*gamma)) := by ring
    _ = _ := by rw [hp]; ring

end
end ASDExplicitGamma.Scalar
