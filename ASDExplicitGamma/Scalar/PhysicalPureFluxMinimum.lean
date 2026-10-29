module

public import ASDExplicitGamma.Scalar.PhysicalPureFluxOperator

/-! Variational meaning of the inverse quadratic of the source block operator. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open scoped InnerProduct InnerProductSpace

noncomputable section

variable {Y X : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- The pure-flux constrained energy after minimizing the solenoidal part. -/
def pureFluxEnergy (α : ℝ) (A : X →L[ℝ] Y) (e : Y) (x : X) : ℝ :=
  α * ‖x‖ ^ 2 + α⁻¹ * ‖e - A x‖ ^ 2

/-- The pure-flux load in the first coordinate of `Y ⊕ X`. -/
def pureFluxLoad (e : Y) : pureFluxPair (Y := Y) (X := X) :=
  WithLp.toLp 2 (e, 0)

/-- The inverse quadratic supplied by the first-order source block. -/
noncomputable def pureFluxInverseQuadratic (α : ℝ) (hα : 0 < α)
    (A : X →L[ℝ] Y) (e : Y) : ℝ :=
  ⟪pureFluxLoad (Y := Y) (X := X) e,
    pureFluxBlockInverse α hα A
      (pureFluxLoad (Y := Y) (X := X) e)⟫_ℝ

/-- The inverse quadratic is attained as the minimum of the pure-flux
energy `α‖x‖² + α⁻¹‖e-Ax‖²`. -/
theorem pureFlux_block_inverse_minimizes {α : ℝ} (hα : 0 < α)
    (A : X →L[ℝ] Y) (e : Y) :
    ∃ x : X,
      pureFluxEnergy α A e x = pureFluxInverseQuadratic α hα A e ∧
      ∀ q : X, pureFluxEnergy α A e x ≤ pureFluxEnergy α A e q := by
  let f := pureFluxLoad (Y := Y) (X := X) e
  let z := pureFluxBlockInverse α hα A f
  let y : Y := z.fst
  let x : X := z.snd
  have hz : pureFluxBlockOperator α A z = f := by
    have h := congrArg (fun T : _ →L[ℝ] _ => T f)
      (pureFluxBlockInverse_left α hα A)
    simpa [z, ContinuousLinearMap.mul_def] using h
  have hsys := congrArg (fun w : pureFluxPair (Y := Y) (X := X) => w.ofLp) hz
  rw [pureFluxBlockOperator_apply] at hsys
  simp only [f, pureFluxLoad, WithLp.ofLp_toLp] at hsys
  have hfirst : α • y + A x = e := congrArg Prod.fst hsys
  have hsecond : -(A.adjoint y) + α • x = 0 := congrArg Prod.snd hsys
  have hstar : A.adjoint y = α • x := by
    have hneg : -(A.adjoint y) = -(α • x) :=
      eq_neg_of_add_eq_zero_left hsecond
    exact neg_injective hneg
  have hres : e - A x = α • y := by
    calc
      e - A x = (α • y + A x) - A x := by rw [hfirst]
      _ = α • y := by abel
  have hpair0 : ⟪f, z⟫_ℝ = ⟪e, y⟫_ℝ := by
    rw [WithLp.prod_inner_apply]
    simp [f, pureFluxLoad, y]
  have hpair : ⟪f, z⟫_ℝ = α * ‖y‖ ^ 2 + α * ‖x‖ ^ 2 := by
    calc
      ⟪f, z⟫_ℝ = ⟪e, y⟫_ℝ := hpair0
      _ = ⟪α • y + A x, y⟫_ℝ := by rw [hfirst]
      _ = α * ‖y‖ ^ 2 + ⟪A x, y⟫_ℝ := by
        rw [inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial,
          real_inner_self_eq_norm_sq]
      _ = α * ‖y‖ ^ 2 + ⟪A.adjoint y, x⟫_ℝ := by
        congr 1
        calc
          ⟪A x, y⟫_ℝ = ⟪y, A x⟫_ℝ := real_inner_comm _ _
          _ = ⟪A.adjoint y, x⟫_ℝ :=
            (ContinuousLinearMap.adjoint_inner_left A x y).symm
      _ = α * ‖y‖ ^ 2 + α * ‖x‖ ^ 2 := by
        rw [hstar, inner_smul_left, starRingEnd_apply, star_trivial,
          real_inner_self_eq_norm_sq]
  have hval : pureFluxEnergy α A e x = ⟪f, z⟫_ℝ := by
    rw [pureFluxEnergy, hres, norm_smul, Real.norm_eq_abs,
      abs_of_pos hα, mul_pow, hpair]
    field_simp [ne_of_gt hα]
    ring
  refine ⟨x, ?_, ?_⟩
  · simpa [pureFluxInverseQuadratic, f, z] using hval
  · intro q
    let d := q - x
    have hq : q = x + d := by simp [d]
    have hcross : ⟪A d, y⟫_ℝ = α * ⟪x, d⟫_ℝ := by
      calc
        ⟪A d, y⟫_ℝ = ⟪y, A d⟫_ℝ := real_inner_comm _ _
        _ = ⟪A.adjoint y, d⟫_ℝ :=
          (ContinuousLinearMap.adjoint_inner_left A d y).symm
        _ = ⟪α • x, d⟫_ℝ := by rw [hstar]
        _ = α * ⟪x, d⟫_ℝ := by
          simp only [inner_smul_left, starRingEnd_apply, star_trivial]
    have hcross2 : ⟪α • y, A d⟫_ℝ = α ^ 2 * ⟪x, d⟫_ℝ := by
      calc
        ⟪α • y, A d⟫_ℝ = α * ⟪y, A d⟫_ℝ := by
          simp only [inner_smul_left, starRingEnd_apply, star_trivial]
        _ = α * ⟪A d, y⟫_ℝ := by rw [real_inner_comm]
        _ = α ^ 2 * ⟪x, d⟫_ℝ := by rw [hcross]; ring
    have hresq : e - A q = α • y - A d := by
      calc
        e - A q = e - A (x + d) := by rw [hq]
        _ = e - (A x + A d) := by rw [map_add]
        _ = (e - A x) - A d := by abel
        _ = α • y - A d := by rw [hres]
    have hnormq : ‖q‖ ^ 2 = ‖x‖ ^ 2 +
        2 * ⟪x, d⟫_ℝ + ‖d‖ ^ 2 := by
      rw [hq, norm_add_sq_real]
    have hnormres : ‖e - A q‖ ^ 2 =
        α ^ 2 * ‖y‖ ^ 2 - 2 * α ^ 2 * ⟪x, d⟫_ℝ + ‖A d‖ ^ 2 := by
      rw [hresq, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
        abs_of_pos hα, mul_pow, hcross2]
      ring
    have hEx : pureFluxEnergy α A e x =
        α * ‖x‖ ^ 2 + α * ‖y‖ ^ 2 := by
      calc
        pureFluxEnergy α A e x = ⟪f, z⟫_ℝ := hval
        _ = α * ‖y‖ ^ 2 + α * ‖x‖ ^ 2 := hpair
        _ = α * ‖x‖ ^ 2 + α * ‖y‖ ^ 2 := by ring
    have hdiff : pureFluxEnergy α A e q =
        pureFluxEnergy α A e x + α * ‖d‖ ^ 2 + α⁻¹ * ‖A d‖ ^ 2 := by
      change α * ‖q‖ ^ 2 + α⁻¹ * ‖e - A q‖ ^ 2 = _
      rw [hnormq, hnormres, hEx]
      field_simp [ne_of_gt hα]
      ring
    rw [hdiff]
    have hpos : 0 ≤ α * ‖d‖ ^ 2 + α⁻¹ * ‖A d‖ ^ 2 :=
      add_nonneg (mul_nonneg hα.le (sq_nonneg ‖d‖))
        (mul_nonneg (inv_nonneg.mpr hα.le) (sq_nonneg ‖A d‖))
    calc
      pureFluxEnergy α A e x ≤
          pureFluxEnergy α A e x +
            (α * ‖d‖ ^ 2 + α⁻¹ * ‖A d‖ ^ 2) := le_add_of_nonneg_right hpos
      _ = pureFluxEnergy α A e x + α * ‖d‖ ^ 2 + α⁻¹ * ‖A d‖ ^ 2 := by ring

end

end ASDExplicitGamma.Scalar
