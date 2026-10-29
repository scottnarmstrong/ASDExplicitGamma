module

public import ASDExplicitGamma.Triadic.DiagStencilMoments

/-! Parity of the symmetric and antisymmetric nodal cell filters. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

noncomputable section

theorem diagStencilU_atoms (g : ℤ × ℤ) :
    diagStencilU g = (1/2:ℚ) • 1 + (1/4:ℚ) • diagStencilAtom g +
      (1/4:ℚ) • diagStencilAtom (-g) := by
  unfold diagStencilU diagStencilAverage
  simp only [map_smul, map_add, map_one, diagStencilAdjoint_atom,
    smul_mul_assoc, mul_smul_comm, smul_smul, mul_add, add_mul,
    one_mul, mul_one, diagStencilAtom_inverse, smul_add]
  module

theorem diagStencilAction_U {G : Type*} [AddCommGroup G]
    (φ : (ℤ × ℤ) →+ G) (g : ℤ × ℤ) (f : G → ℝ) (x : G) :
    diagStencilAction φ (diagStencilU g) f x =
      f x/2 + f (x+φ g)/4 + f (x-φ g)/4 := by
  rw [diagStencilU_atoms]
  simp [Rat.smul_def, sub_eq_add_neg]
  ring

theorem diagStencilAction_V {G : Type*} [AddCommGroup G]
    (φ : (ℤ × ℤ) →+ G) (g : ℤ × ℤ) (f : G → ℝ) (x : G) :
    diagStencilAction φ (diagStencilV g) f x = (f (x+φ g)-f (x-φ g))/2 := by
  rw [diagStencilV_atoms]
  simp [Rat.smul_def, sub_eq_add_neg]
  ring

/-- Reflection moves a shift to the sign-reversed shift when appropriate. -/
theorem diagStencil_reflected_value {G : Type*} [AddCommGroup G]
    (φ : (ℤ × ℤ) →+ G) (R : G →+ G) (b : G) (g : ℤ × ℤ) (flip : Bool)
    (hR : R (φ g) = if flip then -φ g else φ g) (f : G → ℝ) (σ : ℝ)
    (hf : ∀ x, f (R x+b) = σ*f x) (x : G) :
    f (R x+b+φ g) = σ*f (if flip then x-φ g else x+φ g) ∧
      f (R x+b-φ g) = σ*f (if flip then x+φ g else x-φ g) := by
  cases flip
  · simp only [Bool.false_eq_true, ↓reduceIte] at hR ⊢
    constructor
    · convert hf (x+φ g) using 1
      congr 1
      simp only [map_add, hR]
      abel
    · convert hf (x-φ g) using 1
      congr 1
      simp only [map_sub, hR]
      abel
  · simp only [↓reduceIte] at hR ⊢
    constructor
    · convert hf (x-φ g) using 1
      congr 1
      simp only [map_sub, hR]
      abel
    · convert hf (x+φ g) using 1
      congr 1
      simp only [map_add, hR]
      abel

/-- The symmetric filter preserves the source face parity. -/
theorem diagStencilAction_U_parity {G : Type*} [AddCommGroup G]
    (φ : (ℤ × ℤ) →+ G) (R : G →+ G) (b : G) (g : ℤ × ℤ) (flip : Bool)
    (hR : R (φ g) = if flip then -φ g else φ g) (f : G → ℝ) (σ : ℝ)
    (hf : ∀ x, f (R x+b) = σ*f x) (x : G) :
    diagStencilAction φ (diagStencilU g) f (R x+b) =
      σ*diagStencilAction φ (diagStencilU g) f x := by
  obtain ⟨hp, hm⟩ := diagStencil_reflected_value φ R b g flip hR f σ hf x
  rw [diagStencilAction_U, hf, hp, hm, diagStencilAction_U]
  cases flip <;> dsimp <;> ring

/-- A centered difference reverses the parity in the differentiated coordinate. -/
theorem diagStencilAction_V_parity {G : Type*} [AddCommGroup G]
    (φ : (ℤ × ℤ) →+ G) (R : G →+ G) (b : G) (g : ℤ × ℤ) (flip : Bool)
    (hR : R (φ g) = if flip then -φ g else φ g) (f : G → ℝ) (σ : ℝ)
    (hf : ∀ x, f (R x+b) = σ*f x) (x : G) :
    diagStencilAction φ (diagStencilV g) f (R x+b) =
      (if flip then -σ else σ)*diagStencilAction φ (diagStencilV g) f x := by
  obtain ⟨hp, hm⟩ := diagStencil_reflected_value φ R b g flip hR f σ hf x
  rw [diagStencilAction_V, hp, hm, diagStencilAction_V]
  cases flip <;> dsimp <;> ring

end

end ASDExplicitGamma.Triadic
