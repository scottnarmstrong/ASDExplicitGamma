module

public import ASDExplicitGamma.Inverse.RootDefinitions

/-! Complete source derivative-threshold series, without a finite scan or
an assumption of independence from the selected height. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

/-- The actual source ratio is strictly below 10/11. -/
theorem wave_gate_ratio_bounds : 0 ≤ (3:ℝ)^(-1/8:ℝ) ∧ (3:ℝ)^(-1/8:ℝ) < 10/11 := by
  have h0 : 0 ≤ (3:ℝ)^(-1/8:ℝ) := Real.rpow_nonneg (by norm_num) _
  refine ⟨h0,?_⟩
  have hp : ((3:ℝ)^(-1/8:ℝ))^8=1/3 := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 3)]
    norm_num
  by_contra hn
  have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 10/11) (le_of_not_gt hn) 8
  rw [hp] at hh
  norm_num at hh

/-- The complete positive-later-shell threshold sum, in its exact value. -/
theorem wave_gate_threshold_hasSum :
    HasSum (fun L : ℕ => (3:ℝ)^(-((L:ℝ)+1)/8))
      ((3:ℝ)^(-1/8:ℝ)/(1-(3:ℝ)^(-1/8:ℝ))) := by
  have ha := wave_gate_ratio_bounds
  have hh := (hasSum_geometric_of_lt_one ha.1 (ha.2.trans (by norm_num : (10/11:ℝ) < 1))).mul_left
    ((3:ℝ)^(-1/8:ℝ))
  convert hh using 1
  · funext L
    rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 3),← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
    congr 1
    ring
  · rw [div_eq_mul_inv]

/-- The source's safe absolute factor ten pays the entire later family. -/
theorem wave_gate_threshold_tsum_le_ten : (∑' L : ℕ, (3:ℝ)^(-((L:ℝ)+1)/8)) ≤ 10 := by
  rw [wave_gate_threshold_hasSum.tsum_eq]
  have ha := wave_gate_ratio_bounds
  have hd : 0 < 1-(3:ℝ)^(-1/8:ℝ) := by linarith only [ha.2]
  rw [div_le_iff₀ hd]
  linarith only [ha.2]

/-- Finite old-to-ultraviolet intervals are paid by the complete source
threshold sum, including the first positive shell. -/
theorem wave_gate_interval_threshold_sum_le_ten (n J : ℤ) :
    (∑ k ∈ Finset.Ioc n J, (3:ℝ)^(-((k-n:ℤ):ℝ)/8)) ≤ 10 := by
  let f : ℤ → ℕ := fun k => (k-n-1).toNat
  have hi : Set.InjOn f (Finset.Ioc n J) := by
    intro k hk l hl he
    have hk' := (Finset.mem_Ioc.mp hk).1
    have hl' := (Finset.mem_Ioc.mp hl).1
    dsimp only [f] at he
    omega
  have he (k : ℤ) (hk : k ∈ Finset.Ioc n J) :
      (3:ℝ)^(-((k-n:ℤ):ℝ)/8)=(3:ℝ)^(-((f k:ℝ)+1)/8) := by
    have hk' := (Finset.mem_Ioc.mp hk).1
    have hx : ((f k:ℕ):ℤ)+1=k-n := by dsimp only [f]; omega
    congr 1
    have hx' : (f k:ℝ)+1=((k-n:ℤ):ℝ) := by exact_mod_cast hx
    rw [hx']
  calc
    _ = ∑ L ∈ (Finset.Ioc n J).image f, (3:ℝ)^(-((L:ℝ)+1)/8) := by
      rw [Finset.sum_image hi]
      exact Finset.sum_congr rfl he
    _ ≤ ∑' L : ℕ, (3:ℝ)^(-((L:ℝ)+1)/8) :=
      wave_gate_threshold_hasSum.summable.sum_le_tsum _ (fun _ _ => by positivity)
    _ ≤ 10 := wave_gate_threshold_tsum_le_ten

end
end ASDExplicitGamma.Inverse
