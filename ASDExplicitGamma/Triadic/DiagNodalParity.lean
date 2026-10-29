module

public import ASDExplicitGamma.Triadic.DiagNodalLattice
public import ASDExplicitGamma.Triadic.DiagStencilParity

/-! Parity of every centered bilinear coefficient under source face reflection. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

noncomputable section

/-- Parity signs of 1, t₀, t₁ and t₀t₁ under a grid reflection. -/
def diagNodalParitySigns (flipg fliph : Bool) (σ : ℝ) : Fin 4 → ℝ :=
  ![σ, if flipg then -σ else σ, if fliph then -σ else σ,
    if flipg then -(if fliph then -σ else σ) else (if fliph then -σ else σ)]

/-- The four coefficient parities follow from the actual U/V filter parities. -/
theorem diagNodalCoefficients_parity {G : Type*} [AddCommGroup G]
    (φ : (ℤ × ℤ) →+ G) (R : G →+ G) (b : G) (g h : ℤ × ℤ) (flipg fliph : Bool)
    (hg : R (φ g) = if flipg then -φ g else φ g)
    (hh : R (φ h) = if fliph then -φ h else φ h) (f : G → ℝ) (σ : ℝ)
    (hf : ∀ x, f (R x+b) = σ*f x) (a : Fin 4) (x : G) :
    diagNodalCoefficients φ g h f a (R x+b) =
      diagNodalParitySigns flipg fliph σ a * diagNodalCoefficients φ g h f a x := by
  have hu := diagStencilAction_U_parity φ R b h fliph hh f σ hf
  have hv := diagStencilAction_V_parity φ R b h fliph hh f σ hf
  have h00 := diagStencilAction_U_parity φ R b g flipg hg
    (diagStencilAction φ (diagStencilU h) f) σ hu x
  have h10 := diagStencilAction_V_parity φ R b g flipg hg
    (diagStencilAction φ (diagStencilU h) f) σ hu x
  have h01 := diagStencilAction_U_parity φ R b g flipg hg
    (diagStencilAction φ (diagStencilV h) f) (if fliph then -σ else σ) hv x
  have h11 := diagStencilAction_V_parity φ R b g flipg hg
    (diagStencilAction φ (diagStencilV h) f) (if fliph then -σ else σ) hv x
  fin_cases a
  · simpa [diagNodalCoefficients, diagNodalParitySigns, map_mul, Module.End.mul_apply] using h00
  · simpa [diagNodalCoefficients, diagNodalParitySigns, map_mul, Module.End.mul_apply] using h10
  · simpa [diagNodalCoefficients, diagNodalParitySigns, map_mul, Module.End.mul_apply] using h01
  · simpa [diagNodalCoefficients, diagNodalParitySigns, map_mul, Module.End.mul_apply] using h11

theorem diagNodalCoefficients_sq_parity {G : Type*} [AddCommGroup G]
    (φ : (ℤ × ℤ) →+ G) (R : G →+ G) (b : G) (g h : ℤ × ℤ) (flipg fliph : Bool)
    (hg : R (φ g) = if flipg then -φ g else φ g)
    (hh : R (φ h) = if fliph then -φ h else φ h) (f : G → ℝ) (σ : ℝ)
    (hσ : σ^2 = 1) (hf : ∀ x, f (R x+b) = σ*f x) (a : Fin 4) (x : G) :
    diagNodalCoefficients φ g h f a (R x+b)^2 = diagNodalCoefficients φ g h f a x^2 := by
  rw [diagNodalCoefficients_parity φ R b g h flipg fliph hg hh f σ hf, mul_pow]
  have hs : diagNodalParitySigns flipg fliph σ a ^ 2 = 1 := by
    cases flipg <;> cases fliph <;> fin_cases a <;> simp [diagNodalParitySigns, hσ]
  rw [hs, one_mul]

/-- The cell residual budget is reflection invariant for actual odd source arrays. -/
theorem diagNodalResidualBudget_parity {G : Type*} [AddCommGroup G]
    (φ : (ℤ × ℤ) →+ G) (R : G →+ G) (b : G) (g h : ℤ × ℤ) (flipg fliph : Bool)
    (hg : R (φ g) = if flipg then -φ g else φ g)
    (hh : R (φ h) = if fliph then -φ h else φ h) (f : G → ℝ)
    (hf : ∀ x, f (R x+b) = -f x) (x : G) :
    diagNodalResidualBudget φ g h f (R x+b) = diagNodalResidualBudget φ g h f x := by
  have hf' : ∀ x, f (R x+b) = (-1:ℝ)*f x := by simpa only [neg_one_mul] using hf
  have hs := diagNodalCoefficients_sq_parity φ R b g h flipg fliph hg hh f (-1)
    (by norm_num) hf'
  have h0 := diagNodalCoefficients_parity φ R b g h flipg fliph hg hh f (-1) hf' 0 x
  simp only [diagNodalParitySigns, Matrix.cons_val_zero, neg_one_mul] at h0
  simp only [diagNodalResidualBudget, hs, h0, hf]
  ring

/-- The positive-gradient budget is reflection invariant as well. -/
theorem diagNodalGradientBudget_parity {G : Type*} [AddCommGroup G]
    (φ : (ℤ × ℤ) →+ G) (R : G →+ G) (b : G) (g h : ℤ × ℤ) (flipg fliph : Bool)
    (hg : R (φ g) = if flipg then -φ g else φ g)
    (hh : R (φ h) = if fliph then -φ h else φ h) (f : G → ℝ)
    (hf : ∀ x, f (R x+b) = -f x) (x : G) :
    diagNodalGradientBudget φ g h f (R x+b) = diagNodalGradientBudget φ g h f x := by
  have hf' : ∀ x, f (R x+b) = (-1:ℝ)*f x := by simpa only [neg_one_mul] using hf
  have hs := diagNodalCoefficients_sq_parity φ R b g h flipg fliph hg hh f (-1)
    (by norm_num) hf'
  simp only [diagNodalGradientBudget, hs]

end

end ASDExplicitGamma.Triadic
