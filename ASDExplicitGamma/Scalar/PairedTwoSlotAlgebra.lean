module

public import ASDExplicitGamma.Scalar.PhysicalPureFluxMinimum

/-! Block algebra of the two-slot NEW inverse: the `J`-form, the pair energy, and
the exact splitting of the pair energy into its two pure-slot energies. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open scoped InnerProduct InnerProductSpace

noncomputable section

variable {Y X : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- The two equations of the block system `N s = (y, x)`. -/
theorem pair_inverse_equations {α : ℝ} (hα : 0 < α) (B : X →L[ℝ] Y)
    (s : pureFluxPair (Y := Y) (X := X)) :
    α • (pureFluxBlockInverse α hα B s).ofLp.1 + B (pureFluxBlockInverse α hα B s).ofLp.2
        = s.ofLp.1 ∧
      -(B.adjoint (pureFluxBlockInverse α hα B s).ofLp.1) +
        α • (pureFluxBlockInverse α hα B s).ofLp.2 = s.ofLp.2 := by
  have h := congrArg (fun T : _ →L[ℝ] _ => T s) (pureFluxBlockInverse_left α hα B)
  have h2 := congrArg (fun w : pureFluxPair (Y := Y) (X := X) => w.ofLp)
    (show pureFluxBlockOperator α B (pureFluxBlockInverse α hα B s) = s by
      simpa [ContinuousLinearMap.mul_def] using h)
  rw [pureFluxBlockOperator_apply] at h2
  exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

/-- The `J`-form of the inverse in terms of the two components. -/
theorem pair_J_form {α : ℝ} (hα : 0 < α) (B : X →L[ℝ] Y)
    (s : pureFluxPair (Y := Y) (X := X)) :
    ⟪pureFluxParity (Y := Y) (X := X) s, pureFluxBlockInverse α hα B s⟫_ℝ =
      ⟪s.ofLp.1, (pureFluxBlockInverse α hα B s).ofLp.1⟫_ℝ -
        ⟪s.ofLp.2, (pureFluxBlockInverse α hα B s).ofLp.2⟫_ℝ := by
  rw [WithLp.prod_inner_apply, pureFluxParity_apply]
  simp [inner_neg_left, sub_eq_add_neg]

/-- The symmetric pair energy of a solution `(y,x)`. -/
def pairEnergy' (α : ℝ) (y : Y) (x : X) : ℝ := α * (‖x‖ ^ 2 + ‖y‖ ^ 2)

/-- The pair form of the inverse is the pair energy of the solution. -/
theorem pair_form_eq_energy {α : ℝ} (hα : 0 < α) (B : X →L[ℝ] Y)
    (s : pureFluxPair (Y := Y) (X := X)) :
    ⟪s, pureFluxBlockInverse α hα B s⟫_ℝ =
      pairEnergy' α (pureFluxBlockInverse α hα B s).ofLp.1
        (pureFluxBlockInverse α hα B s).ofLp.2 := by
  obtain ⟨h1, h2⟩ := pair_inverse_equations hα B s
  set y := (pureFluxBlockInverse α hα B s).ofLp.1
  set x := (pureFluxBlockInverse α hα B s).ofLp.2
  rw [WithLp.prod_inner_apply]
  have e1 : ⟪s.ofLp.1, y⟫_ℝ = α * ‖y‖ ^ 2 + ⟪B x, y⟫_ℝ := by
    rw [← h1, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq]; simp
  have e2 : ⟪s.ofLp.2, x⟫_ℝ = α * ‖x‖ ^ 2 - ⟪B.adjoint y, x⟫_ℝ := by
    rw [← h2, inner_add_left, inner_neg_left, inner_smul_left, real_inner_self_eq_norm_sq]; simp; ring
  have e3 : ⟪B x, y⟫_ℝ = ⟪B.adjoint y, x⟫_ℝ := by
    rw [real_inner_comm, ← ContinuousLinearMap.adjoint_inner_left]
  unfold pairEnergy'
  change ⟪s.ofLp.1, y⟫_ℝ + ⟪s.ofLp.2, x⟫_ℝ = _
  rw [e1, e2, e3]
  ring

/-- The pair energy as the sum of the two slot pairings. -/
theorem pair_energy_eq_sum {α : ℝ} (hα : 0 < α) (B : X →L[ℝ] Y)
    (s : pureFluxPair (Y := Y) (X := X)) :
    pairEnergy' α (pureFluxBlockInverse α hα B s).ofLp.1
        (pureFluxBlockInverse α hα B s).ofLp.2 =
      ⟪s.ofLp.1, (pureFluxBlockInverse α hα B s).ofLp.1⟫_ℝ +
        ⟪s.ofLp.2, (pureFluxBlockInverse α hα B s).ofLp.2⟫_ℝ := by
  rw [← pair_form_eq_energy hα B s, WithLp.prod_inner_apply]

/-- Splitting the source into its two slots splits the pair energy. -/
theorem pair_energy_split {α : ℝ} (hα : 0 < α) (B : X →L[ℝ] Y) (s₁ : Y) (s₂ : X) :
    let N := pureFluxBlockInverse α hα B
    pairEnergy' α (N (WithLp.toLp 2 (s₁, s₂))).ofLp.1 (N (WithLp.toLp 2 (s₁, s₂))).ofLp.2 =
      pairEnergy' α (N (WithLp.toLp 2 (s₁, 0))).ofLp.1 (N (WithLp.toLp 2 (s₁, 0))).ofLp.2 +
      pairEnergy' α (N (WithLp.toLp 2 (0, s₂))).ofLp.1 (N (WithLp.toLp 2 (0, s₂))).ofLp.2 := by
  intro N
  set a : pureFluxPair (Y := Y) (X := X) := WithLp.toLp 2 (s₁, 0)
  set b : pureFluxPair (Y := Y) (X := X) := WithLp.toLp 2 (0, s₂)
  have hs : (WithLp.toLp 2 (s₁, s₂) : pureFluxPair (Y := Y) (X := X)) = a + b := by
    apply (WithLp.prodContinuousLinearEquiv 2 ℝ Y X).injective
    simp [a, b]
  rw [hs]
  have hN : N (a + b) = N a + N b := map_add N a b
  obtain ⟨a1, a2⟩ := pair_inverse_equations hα B a
  obtain ⟨b1, b2⟩ := pair_inverse_equations hα B b
  have ha1 : a.ofLp.1 = s₁ := rfl
  have ha2 : a.ofLp.2 = 0 := rfl
  have hb1 : b.ofLp.1 = 0 := rfl
  have hb2 : b.ofLp.2 = s₂ := rfl
  rw [ha2] at a2; rw [hb1] at b1
  set y₁ := (N a).ofLp.1; set x₁ := (N a).ofLp.2
  set y₂ := (N b).ofLp.1; set x₂ := (N b).ofLp.2
  have cross : α * ⟪y₁, y₂⟫_ℝ + α * ⟪x₁, x₂⟫_ℝ = 0 := by
    have t1 : α * ⟪y₁, y₂⟫_ℝ = -⟪B.adjoint y₁, x₂⟫_ℝ := by
      have : α • y₂ = -(B x₂) := eq_neg_of_add_eq_zero_left b1
      rw [real_inner_comm, ← real_inner_smul_left, this, inner_neg_left,
        real_inner_comm, ContinuousLinearMap.adjoint_inner_left] 
    have t2 : α * ⟪x₁, x₂⟫_ℝ = ⟪B.adjoint y₁, x₂⟫_ℝ := by
      have : B.adjoint y₁ = α • x₁ := by
        have := a2; 
        have h' : -(B.adjoint y₁) = -(α • x₁) := eq_neg_of_add_eq_zero_left (by simpa using this)
        exact neg_injective h'
      rw [this, inner_smul_left]; simp
    linarith
  have hy : (N (a + b)).ofLp.1 = y₁ + y₂ := by rw [hN]; rfl
  have hx : (N (a + b)).ofLp.2 = x₁ + x₂ := by rw [hN]; rfl
  rw [hy, hx]
  unfold pairEnergy'
  have ny : ‖y₁ + y₂‖ ^ 2 = ‖y₁‖ ^ 2 + 2 * ⟪y₁, y₂⟫_ℝ + ‖y₂‖ ^ 2 := norm_add_sq_real _ _
  have nx : ‖x₁ + x₂‖ ^ 2 = ‖x₁‖ ^ 2 + 2 * ⟪x₁, x₂⟫_ℝ + ‖x₂‖ ^ 2 := norm_add_sq_real _ _
  rw [nx, ny]
  nlinarith [cross]

end

end ASDExplicitGamma.Scalar
