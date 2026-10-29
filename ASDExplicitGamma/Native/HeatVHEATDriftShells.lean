module

public import ASDExplicitGamma.Native.HeatVHEATDriftRareIntegral

/-! Exact finite-shell bank expansion before any expectation. -/
@[expose] public section
namespace ASDExplicitGamma.Native
noncomputable section

/-- All shells of one child share its original local remainder. Expanding
that bank once gives precisely the constant, linear and quadratic VHEAT terms. -/
theorem heatVHEATDrift_shell_sum_le
    {D : Type*} (ds : Finset D) (v kap mu B : D → ℝ)
    (e b R : ℝ) (he : 0 ≤ e)
    (hv : ∀ d∈ds,0 ≤ v d ∧ v d ≤ e)
    (hkap : ∀ d∈ds,0 ≤ kap d) (hmu : ∀ d∈ds,0 ≤ mu d)
    (hB : ∀ d∈ds,0 ≤ B d ∧ B d ≤ b+R) :
    (∑ d∈ds,(2*v d*kap d*B d+v d*mu d*(B d)^2)) ≤
      e*((2*(∑ d∈ds,kap d)*b+(∑ d∈ds,mu d)*b^2)+
        (2*(∑ d∈ds,kap d)+2*b*(∑ d∈ds,mu d))*R+(∑ d∈ds,mu d)*R^2) := by
  have hs : (∑ d∈ds,(2*v d*kap d*B d+v d*mu d*(B d)^2)) ≤
      ∑ d∈ds,(2*e*kap d*(b+R)+e*mu d*(b+R)^2) := by
    apply Finset.sum_le_sum
    intro d hd
    have hlin := mul_le_mul
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hv d hd).2 (by norm_num : (0:ℝ)≤2))
        (hkap d hd)) (hB d hd).2 (hB d hd).1
      (mul_nonneg (mul_nonneg (by norm_num) he) (hkap d hd))
    have hquad := mul_le_mul (mul_le_mul_of_nonneg_right (hv d hd).2 (hmu d hd))
      (pow_le_pow_left₀ (hB d hd).1 (hB d hd).2 2) (sq_nonneg _)
      (mul_nonneg he (hmu d hd))
    exact add_le_add hlin hquad
  refine hs.trans_eq ?_
  rw [Finset.sum_add_distrib]
  simp only [←Finset.sum_mul,←Finset.mul_sum]
  ring

end
end ASDExplicitGamma.Native
