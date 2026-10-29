module

public import ASDExplicitGamma.Native.OldSignedFiniteMinkowski

/-! Finite shell contractions with one common physical theta factor. -/
@[expose] public section
namespace ASDExplicitGamma.Native
noncomputable section

/-- Two Euclidean shell budgets multiply without a shell-count loss. -/
theorem parent_row_pair_budget {I : Type*} [Fintype I]
    (f g : I → ℝ) (θ A B : ℝ) (hθ : 0≤θ) (hA : 0≤A)
    (hf : Real.sqrt (∑ i,f i^2)≤Real.sqrt θ*A)
    (hg : Real.sqrt (∑ i,g i^2)≤Real.sqrt θ*B) :
    (∑ i,f i*g i)≤θ*(A*B) := by
  have hh := (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ f g).trans
    (mul_le_mul hf hg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hA))
  exact hh.trans_eq (by rw [mul_mul_mul_comm,←pow_two,Real.sq_sqrt hθ])

/-- Squaring a root budget returns the exact quadratic shell payment. -/
theorem parent_row_energy_budget {I : Type*} [Fintype I]
    (f : I → ℝ) (θ A : ℝ) (hθ : 0≤θ)
    (hf : Real.sqrt (∑ i,f i^2)≤Real.sqrt θ*A) :
    (∑ i,f i^2)≤θ*A^2 := by
  have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) hf 2
  rwa [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),mul_pow,Real.sq_sqrt hθ] at hh

/-- Mixed square roots of the weak allowance and a shell variance simplify
without changing the sign of the physical amplitude. -/
theorem parent_row_weak_variance_root (X b : ℝ) (hX : 0≤X) :
    Real.sqrt X*Real.sqrt (X*b^2)=X*|b| := by
  rw [Real.sqrt_mul hX,Real.sqrt_sq_eq_abs,←mul_assoc,←pow_two,Real.sq_sqrt hX]

/-- The complete source quadratic/mixed sum is paid by its three Euclidean
budgets; the scalar weak allowance is common to all shells. -/
theorem parent_row_source_sum_budget {I : Type*} [Fintype I]
    (k b e : I → ℝ) (θ K V R X : ℝ) (hθ : 0≤θ) (hK : 0≤K) (hX : 0≤X)
    (he : ∀ i,0≤e i)
    (hk : Real.sqrt (∑ i,k i^2)≤Real.sqrt θ*K)
    (hb : Real.sqrt (∑ i,b i^2)≤Real.sqrt θ*V)
    (hr : Real.sqrt (∑ i,e i)≤Real.sqrt θ*R) :
    (∑ i,(k i^2*((3683/2500:ℝ)*X)+(2*k i)*(Real.sqrt X*Real.sqrt (X*b i^2))+
      (2*k i)*(Real.sqrt X*Real.sqrt (e i))))≤
      θ*(K^2*((3683/2500:ℝ)*X)+2*K*(X*V)+2*K*(Real.sqrt X*R)) := by
  have hsq := parent_row_energy_budget k θ K hθ hk
  have habs : Real.sqrt (∑ i,|b i|^2)≤Real.sqrt θ*V := by simpa only [sq_abs] using hb
  have hcross := parent_row_pair_budget k (fun i => |b i|) θ K V hθ hK hk habs
  have heRoot : Real.sqrt (∑ i,(Real.sqrt (e i))^2)≤Real.sqrt θ*R := by
    simpa only [Real.sq_sqrt (he _)] using hr
  have hrec := parent_row_pair_budget k (fun i => Real.sqrt (e i)) θ K R hθ hK hk heRoot
  simp_rw [parent_row_weak_variance_root X _ hX]
  have hrewrite : (∑ i,(k i^2*((3683/2500:ℝ)*X)+(2*k i)*(X*|b i|)+
      (2*k i)*(Real.sqrt X*Real.sqrt (e i))))=
      (∑ i,k i^2)*((3683/2500:ℝ)*X)+(2*X)*(∑ i,k i*|b i|)+
        (2*Real.sqrt X)*(∑ i,k i*Real.sqrt (e i)) := by
    simp only [Finset.mul_sum,Finset.sum_mul,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hrewrite]
  exact (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_right hsq (mul_nonneg (by norm_num) hX))
    (mul_le_mul_of_nonneg_left hcross (mul_nonneg (by norm_num) hX)))
    (mul_le_mul_of_nonneg_left hrec (mul_nonneg (by norm_num) (Real.sqrt_nonneg X)))).trans_eq (by ring)

end
end ASDExplicitGamma.Native
