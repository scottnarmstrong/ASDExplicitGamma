module

public import ASDExplicitGamma.Triadic.DiagNodalLattice
public import ASDExplicitGamma.Triadic.DiagStencilParity

/-! Corner values of the centered nodal bilinear polynomial. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

noncomputable section

/-- Nodal averaging on the negative or positive face of a cell. -/
def diagStencilCorner (g : ℤ × ℤ) (b : Fin 2) : DiagStencil :=
  if b = 0 then diagStencilAdjoint (diagStencilAverage g) else diagStencilAverage g

theorem diagStencilCorner_centered (g : ℤ × ℤ) (b : Fin 2) :
    diagStencilCorner g b = diagStencilU g + ((b.val : ℚ)-1/2) • diagStencilV g := by
  rw [diagStencilU_atoms, diagStencilV_atoms]
  fin_cases b <;>
    simp [diagStencilCorner, diagStencilAverage, smul_add, smul_sub, smul_smul] <;> module

/-- A corner filter averages the two adjacent cell means. -/
theorem diagStencilAction_corner {G : Type*} [AddCommGroup G]
    (φ : (ℤ × ℤ) →+ G) (g : ℤ × ℤ) (f : G → ℝ) (x : G) (b : Fin 2) :
    diagStencilAction φ (diagStencilCorner g b) f x =
      let z := if b = 0 then x else x+φ g
      (f z + f (z-φ g))/2 := by
  unfold diagStencilCorner diagStencilAverage
  fin_cases b <;> simp [Rat.smul_def, sub_eq_add_neg] <;> ring

/-- Corner value in centered polynomial coefficients. -/
theorem diagNodalCoefficients_corner {G : Type*} [AddCommGroup G]
    (φ : (ℤ × ℤ) →+ G) (g h : ℤ × ℤ) (f : G → ℝ) (x : G) (b c : Fin 2) :
    let a := diagNodalCoefficients φ g h f
    a 0 x + ((b.val:ℝ)-1/2)*a 1 x + ((c.val:ℝ)-1/2)*a 2 x +
      ((b.val:ℝ)-1/2)*((c.val:ℝ)-1/2)*a 3 x =
        diagStencilAction φ (diagStencilCorner g b * diagStencilCorner h c) f x := by
  intro a
  rw [diagStencilCorner_centered, diagStencilCorner_centered]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply,
    Rat.smul_def, Rat.cast_sub, Rat.cast_natCast, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  dsimp [a, diagNodalCoefficients]
  ring

/-- The two corner filters give the exact four neighboring cell means. -/
theorem diagStencilAction_corner_pair {G : Type*} [AddCommGroup G]
    (φ : (ℤ × ℤ) →+ G) (g h : ℤ × ℤ) (f : G → ℝ) (x : G) (b c : Fin 2) :
    diagStencilAction φ (diagStencilCorner g b * diagStencilCorner h c) f x =
      let z := x + (if b = 0 then 0 else φ g) + (if c = 0 then 0 else φ h)
      (f z + f (z-φ g) + f (z-φ h) + f (z-φ g-φ h))/4 := by
  rw [map_mul, Module.End.mul_apply, diagStencilAction_corner]
  simp_rw [diagStencilAction_corner]
  have hcomm (y : G) : y + φ h - φ g = y - φ g + φ h := by abel
  fin_cases b <;> fin_cases c <;> norm_num
  all_goals
    simp (config := { failIfUnchanged := false }) only
      [add_sub_cancel_right, hcomm]
    ring

end

end ASDExplicitGamma.Triadic
