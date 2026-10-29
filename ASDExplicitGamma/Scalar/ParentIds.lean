module

public import ASDExplicitGamma.Scalar.PairedTwoSlotParentData

/-! The parent two-slot solution, with the identification of the inverse components with the gradients
of the potentials exposed (a copy of `two_slot_parent_core` with three extra conclusions). -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational
open scoped InnerProduct InnerProductSpace

noncomputable section

local instance parentFinite (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

theorem two_slot_parent_core_ids (Q : TriadicCube 2) {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) {F G : Vec 2 → Vec 2}
    (hF : MemVectorL2 (openCubeSet Q) F) (hG : MemVectorL2 (openCubeSet Q) G)
    (s₁ y : HilbertVectorL2 (openCubeSet Q))
    (s₂ x : (physicalPotentialSpace Q).toSubmodule)
    (hs1 : s₁ ∈ (physicalFluxSpace Q).toSubmodule)
    (hs1' : ∀ w ∈ (physicalFluxSpace Q).toSubmodule,
      ⟪s₁, w⟫_ℝ = ⟪toHilbertVectorL2OfVecField hF, w⟫_ℝ)
    (hs2' : ∀ w : (physicalPotentialSpace Q).toSubmodule,
      ⟪(s₂ : HilbertVectorL2 (openCubeSet Q)), (w : HilbertVectorL2 (openCubeSet Q))⟫_ℝ =
        ⟪toHilbertVectorL2OfVecField hG, (w : HilbertVectorL2 (openCubeSet Q))⟫_ℝ)
    (h1 : (ν / σ) • y + physicalProjectedCoefficient Q σ hσ k x = s₁)
    (h2 : -((physicalProjectedCoefficient Q σ hσ k).adjoint y) + (ν / σ) • x = s₂) :
    ∃ (φ : H10Function (openCubeSet Q)) (η : H1Function (openCubeSet Q)),
      IsSolenoidalOn (openCubeSet Q) (fun z =>
        (ν / σ) • η.grad z + shear' σ k z (φ.toH1Function.grad z) - F z) ∧
      IsSolenoidalOn (openCubeSet Q) (fun z =>
        (ν / σ) • φ.toH1Function.grad z + shear' σ k z (η.grad z) - G z) ∧
      ⟪s₁, y⟫_ℝ - ⟪(s₂ : HilbertVectorL2 (openCubeSet Q)), (x : HilbertVectorL2 (openCubeSet Q))⟫_ℝ =
        (∫ z in openCubeSet Q, vecDot (F z) (η.grad z) ∂volume) -
          ∫ z in openCubeSet Q, vecDot (G z) (φ.toH1Function.grad z) ∂volume ∧
      ⟪s₁, y⟫_ℝ + ⟪(s₂ : HilbertVectorL2 (openCubeSet Q)), (x : HilbertVectorL2 (openCubeSet Q))⟫_ℝ =
        (∫ z in openCubeSet Q, vecDot (F z) (η.grad z) ∂volume) +
          ∫ z in openCubeSet Q, vecDot (G z) (φ.toH1Function.grad z) ∂volume ∧
      ‖(x : HilbertVectorL2 (openCubeSet Q))‖ ^ 2 + ‖y‖ ^ 2 =
        (∫ z in openCubeSet Q, vecNormSq (φ.toH1Function.grad z) ∂volume) +
          ∫ z in openCubeSet Q, vecNormSq (η.grad z) ∂volume ∧
      y ∈ (physicalFluxSpace Q).toSubmodule ∧
      y = toHilbertVectorL2OfVecField η.grad_memVectorL2 ∧
      (x : HilbertVectorL2 (openCubeSet Q)) =
        toHilbertVectorL2OfVecField φ.toH1Function.grad_memVectorL2 := by
  have hα : 0 < ν / σ := div_pos hν hσ
  have hBx : ∀ x' : (physicalPotentialSpace Q).toSubmodule,
      (physicalProjectedCoefficient Q σ hσ k x' : HilbertVectorL2 (openCubeSet Q)) =
        (physicalFluxSpace Q).toSubmodule.starProjection
          (physicalPositiveShear Q σ hσ k (x' : HilbertVectorL2 (openCubeSet Q))) :=
    fun x' => rfl
  have hyK : y ∈ (physicalFluxSpace Q).toSubmodule := by
    have hy' : y = (ν / σ)⁻¹ • (s₁ - physicalProjectedCoefficient Q σ hσ k x) := by
      rw [← h1, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hα.ne', one_smul]
    rw [hy']
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hs1 (by
      rw [hBx x]; exact Submodule.starProjection_apply_mem _ _))
  -- the potential `η` of `y`
  have hyPot : IsPotentialOn (openCubeSet Q) (rep' y) := by
    apply IsPotentialOn.of_orthogonal_to_solenoidalZeroNormalTrace_of_memVectorL2_of_hodgeConverseCriterion
      (hodgeConverseCriterion_of_isOpenBoundedConvexDomain
        (isOpenBoundedConvexDomain_openCubeSet Q)) (rep_memL2 y)
    intro g hg hsol
    have hgmem : toHilbertVectorL2OfVecField hg ∈
        (physicalSolenoidalSpace Q).toSubmodule := by
      change toHilbertVectorL2OfVecField hg ∈
        PotentialSolenoidalExact.solenoidalZeroNormalTrace (openCubeSet Q)
      rw [PotentialSolenoidalExact.mem_solenoidalZeroNormalTrace_iff]
      intro u
      rw [show u.gradToHilbertVectorL2 = toHilbertVectorL2OfVecField u.grad_memVectorL2 from rfl,
        inner_ofField]
      have := hsol u
      simpa [vecDot_comm] using this
    have horth : ⟪toHilbertVectorL2OfVecField hg, y⟫_ℝ = 0 := by
      have := (Submodule.mem_orthogonal _ _).1 hyK _ hgmem
      exact this
    have hint := inner_ofField hg (rep_memL2 y)
    rw [hilbert_rebuild y, horth] at hint
    simpa [vecDot_comm] using hint.symm
  obtain ⟨η, hη⟩ := hyPot
  obtain ⟨φ, hφ⟩ := (PotentialSolenoidalExact.mem_potentialZeroTrace_iff _).1 x.2
  have hyη : y = toHilbertVectorL2OfVecField η.grad_memVectorL2 := by
    rw [← hilbert_rebuild y]
    exact ofField_eq' _ _ hη.symm
  have hxφ : (x : HilbertVectorL2 (openCubeSet Q)) =
      toHilbertVectorL2OfVecField φ.toH1Function.grad_memVectorL2 := hφ.symm
  have hφL := φ.toH1Function.grad_memVectorL2
  have hηL := η.grad_memVectorL2
  have hshφ := shear_memL2 hν hσ k hφL
  have hshη := shear_memL2 hν hσ k hηL
  have hPx : physicalPositiveShear Q σ hσ k (x : HilbertVectorL2 (openCubeSet Q)) =
      toHilbertVectorL2OfVecField hshφ := by
    rw [hxφ]; exact positiveShear_ofField Q hν hσ k hφL
  have hPy : physicalPositiveShear Q σ hσ k y = toHilbertVectorL2OfVecField hshη := by
    rw [hyη]; exact positiveShear_ofField Q hν hσ k hηL
  have hFH := hF
  have hflux : ∀ w ∈ (physicalFluxSpace Q).toSubmodule,
      (ν / σ) * ⟪y, w⟫_ℝ + ⟪physicalPositiveShear Q σ hσ k (x : HilbertVectorL2 (openCubeSet Q)), w⟫_ℝ =
        ⟪toHilbertVectorL2OfVecField hF, w⟫_ℝ := by
    intro w hw
    have h := hs1' w hw
    rw [← h1, inner_add_left, real_inner_smul_left, hBx x,
      Submodule.inner_starProjection_left_eq_right,
      (Submodule.starProjection_eq_self_iff).2 hw] at h
    exact h
  have hpot : ∀ w : (physicalPotentialSpace Q).toSubmodule,
      (ν / σ) * ⟪(x : HilbertVectorL2 (openCubeSet Q)), (w : HilbertVectorL2 (openCubeSet Q))⟫_ℝ +
        ⟪physicalPositiveShear Q σ hσ k y, (w : HilbertVectorL2 (openCubeSet Q))⟫_ℝ =
        ⟪toHilbertVectorL2OfVecField hG, (w : HilbertVectorL2 (openCubeSet Q))⟫_ℝ := by
    intro w
    have h := hs2' w
    rw [← h2] at h
    simp only [Submodule.coe_add, Submodule.coe_neg, Submodule.coe_smul, inner_add_left,
      inner_neg_left, real_inner_smul_left] at h
    have hadj : ⟪(physicalProjectedCoefficient Q σ hσ k).adjoint y, w⟫_ℝ =
        ⟪y, physicalProjectedCoefficient Q σ hσ k w⟫_ℝ :=
      ContinuousLinearMap.adjoint_inner_left _ w y
    rw [Submodule.coe_inner] at hadj
    have hadj2 : ⟪y, (physicalProjectedCoefficient Q σ hσ k w : HilbertVectorL2 (openCubeSet Q))⟫_ℝ =
        -⟪physicalPositiveShear Q σ hσ k y, (w : HilbertVectorL2 (openCubeSet Q))⟫_ℝ := by
      rw [hBx w, real_inner_comm, Submodule.inner_starProjection_left_eq_right,
        (Submodule.starProjection_eq_self_iff).2 hyK,
        positiveShear_skew Q σ hσ k, real_inner_comm]
    have hadj3 := hadj.trans hadj2
    linarith
  refine ⟨φ, η, ?_, ?_, ?_, ?_, ?_, hyK, hyη, hxφ⟩
  · intro ψ
    have hψ : toHilbertVectorL2OfVecField ψ.toH1Function.grad_memVectorL2 ∈
        (physicalFluxSpace Q).toSubmodule := gradHilbert_mem_flux Q ψ.toH1Function
    have h := hflux _ hψ
    rw [hyη, hPx, inner_ofField, inner_ofField, inner_ofField] at h
    rw [integral_expand (ν / σ) hηL hshφ hF ψ.toH1Function.grad_memVectorL2]
    linarith
  · intro ψ
    have hψ : toHilbertVectorL2OfVecField ψ.toH1Function.grad_memVectorL2 ∈
        (physicalPotentialSpace Q).toSubmodule :=
      (PotentialSolenoidalExact.mem_potentialZeroTrace_iff _).2 ⟨ψ, rfl⟩
    have h : (ν / σ) * ⟪(x : HilbertVectorL2 (openCubeSet Q)),
        toHilbertVectorL2OfVecField ψ.toH1Function.grad_memVectorL2⟫_ℝ +
        ⟪physicalPositiveShear Q σ hσ k y,
          toHilbertVectorL2OfVecField ψ.toH1Function.grad_memVectorL2⟫_ℝ =
        ⟪toHilbertVectorL2OfVecField hG,
          toHilbertVectorL2OfVecField ψ.toH1Function.grad_memVectorL2⟫_ℝ := hpot ⟨_, hψ⟩
    rw [hxφ, hPy, inner_ofField, inner_ofField, inner_ofField] at h
    rw [integral_expand (ν / σ) hφL hshη hG ψ.toH1Function.grad_memVectorL2]
    linarith
  · have a1 := hs1' y hyK
    have a2 := hs2' x
    have e1 : ⟪toHilbertVectorL2OfVecField hF, y⟫_ℝ =
        ∫ z in openCubeSet Q, vecDot (F z) (η.grad z) ∂volume := by
      rw [hyη, inner_ofField]
    have e2 : ⟪toHilbertVectorL2OfVecField hG, (x : HilbertVectorL2 (openCubeSet Q))⟫_ℝ =
        ∫ z in openCubeSet Q, vecDot (G z) (φ.toH1Function.grad z) ∂volume := by
      rw [hxφ, inner_ofField]
    rw [a1, a2, e1, e2]
  · have a1 := hs1' y hyK
    have a2 := hs2' x
    have e1 : ⟪toHilbertVectorL2OfVecField hF, y⟫_ℝ =
        ∫ z in openCubeSet Q, vecDot (F z) (η.grad z) ∂volume := by
      rw [hyη, inner_ofField]
    have e2 : ⟪toHilbertVectorL2OfVecField hG, (x : HilbertVectorL2 (openCubeSet Q))⟫_ℝ =
        ∫ z in openCubeSet Q, vecDot (G z) (φ.toH1Function.grad z) ∂volume := by
      rw [hxφ, inner_ofField]
    rw [a1, a2, e1, e2]
  · rw [hxφ, hyη, norm_sq_ofField, norm_sq_ofField]


end

end ASDExplicitGamma.Scalar
