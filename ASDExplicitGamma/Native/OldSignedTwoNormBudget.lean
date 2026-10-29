module

public import ASDExplicitGamma.Triadic.HaarNormTriangle

/-! The two disjoint load families are combined before Cauchy--Schwarz. -/
@[expose] public section
namespace ASDExplicitGamma.Native
noncomputable section

/-- Minkowski separates affine and oscillatory arrays while keeping the
top and bottom load supports in their Euclidean direct sum. -/
theorem old_signed_two_norm_budget (g₁ g₂ p₁ p₂ o₁ o₂ : ℝ)
    (hg₁ : 0≤g₁) (hg₂ : 0≤g₂)
    (h₁ : g₁≤p₁+o₁) (h₂ : g₂≤p₂+o₂) :
    Real.sqrt (g₁^2+g₂^2)≤Real.sqrt (p₁^2+p₂^2)+Real.sqrt (o₁^2+o₂^2) := by
  have hh := Triadic.sqrt_finset_sq_add_le Finset.univ
    (fun i : Fin 2 => if i=0 then p₁ else p₂)
    (fun i : Fin 2 => if i=0 then o₁ else o₂)
  simp only [Fin.sum_univ_two,ite_true,show (1:Fin 2)≠0 from by decide,ite_false] at hh
  exact (Real.sqrt_le_sqrt (add_le_add (pow_le_pow_left₀ hg₁ h₁ 2)
    (pow_le_pow_left₀ hg₂ h₂ 2))).trans hh

end
end ASDExplicitGamma.Native
