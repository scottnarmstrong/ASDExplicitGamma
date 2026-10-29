module

public import ASDExplicitGamma.Scalar.PairedTwoSlotParent

/-! The two-slot NEW inverse on the parent cube, in function form. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational
open scoped InnerProduct InnerProductSpace

noncomputable section

local instance parentFinite' (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

theorem gradHilbert_mem_flux (Q : TriadicCube 2) (ψ : H1Function (openCubeSet Q)) :
    ψ.gradToHilbertVectorL2 ∈ (physicalFluxSpace Q).toSubmodule := by
  change ψ.gradToHilbertVectorL2 ∈ (PotentialSolenoidalExact.solenoidalZeroNormalTrace
    (openCubeSet Q))ᗮ
  rw [Submodule.mem_orthogonal]
  intro g hg
  exact (PotentialSolenoidalExact.mem_solenoidalZeroNormalTrace_iff g).1 hg ψ

theorem integral_expand {U : Set (Vec 2)} (α : ℝ) {u v f d : Vec 2 → Vec 2}
    (hu : MemVectorL2 U u) (hv : MemVectorL2 U v) (hf : MemVectorL2 U f)
    (hd : MemVectorL2 U d) [IsFiniteMeasure (volumeMeasureOn U)] :
    ∫ z in U, vecDot (α • u z + v z - f z) (d z) ∂volume =
      α * (∫ z in U, vecDot (u z) (d z) ∂volume) + (∫ z in U, vecDot (v z) (d z) ∂volume) -
        ∫ z in U, vecDot (f z) (d z) ∂volume := by
  have i1 := integrableOn_vecDot_of_memVectorL2 hu hd
  have i2 := integrableOn_vecDot_of_memVectorL2 hv hd
  have i3 := integrableOn_vecDot_of_memVectorL2 hf hd
  have e : (fun z => vecDot (α • u z + v z - f z) (d z)) =
      fun z => α * vecDot (u z) (d z) + vecDot (v z) (d z) - vecDot (f z) (d z) := by
    funext z
    rw [vecDot_sub_left'', vecDot_add_left, vecDot_smul_left]
  rw [e]
  have j1 : Integrable (fun z => α * vecDot (u z) (d z)) (volume.restrict U) := i1.const_mul α
  have j2 : Integrable (fun z => α * vecDot (u z) (d z) + vecDot (v z) (d z))
      (volume.restrict U) := j1.add i2
  have s1 := integral_sub j2 i3
  have s2 := integral_add j1 i2
  have s3 := integral_const_mul (μ := volume.restrict U) α (fun z => vecDot (u z) (d z))
  rw [s1, s2, s3]

theorem positiveShear_ofField (Q : TriadicCube 2) {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) {f : Vec 2 → Vec 2}
    (hf : MemVectorL2 (openCubeSet Q) f) :
    physicalPositiveShear Q σ hσ k (toHilbertVectorL2OfVecField hf) =
      toHilbertVectorL2OfVecField (shear_memL2 hν hσ k hf) := by
  rw [← hilbert_rebuild (physicalPositiveShear Q σ hσ k (toHilbertVectorL2OfVecField hf))]
  apply toHilbert_congr
  filter_upwards [rep_positiveShear Q σ hσ k (toHilbertVectorL2OfVecField hf),
    rep_ofField hf] with z h1 h2
  rw [h1, h2]

theorem two_slot_parent_core (Q : TriadicCube 2) {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
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
          ∫ z in openCubeSet Q, vecNormSq (η.grad z) ∂volume := by
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
  refine ⟨φ, η, ?_, ?_, ?_, ?_, ?_⟩
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

/-- The first (flux) component of the NEW inverse applied to a paired source. -/
noncomputable def twoSlotY (Q : TriadicCube 2) {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (s₁ : HilbertVectorL2 (openCubeSet Q))
    (s₂ : (physicalPotentialSpace Q).toSubmodule) : HilbertVectorL2 (openCubeSet Q) :=
  (pureFluxBlockInverse (Y := HilbertVectorL2 (openCubeSet Q))
    (X := (physicalPotentialSpace Q).toSubmodule) (ν / σ) (div_pos hν hσ)
    (physicalProjectedCoefficient Q σ hσ k) (WithLp.toLp 2 (s₁, s₂))).ofLp.1

/-- The second (potential) component of the NEW inverse applied to a paired source. -/
noncomputable def twoSlotX (Q : TriadicCube 2) {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (s₁ : HilbertVectorL2 (openCubeSet Q))
    (s₂ : (physicalPotentialSpace Q).toSubmodule) :
    (physicalPotentialSpace Q).toSubmodule :=
  (pureFluxBlockInverse (Y := HilbertVectorL2 (openCubeSet Q))
    (X := (physicalPotentialSpace Q).toSubmodule) (ν / σ) (div_pos hν hσ)
    (physicalProjectedCoefficient Q σ hσ k) (WithLp.toLp 2 (s₁, s₂))).ofLp.2

theorem twoSlot_eq1 (Q : TriadicCube 2) {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (s₁ : HilbertVectorL2 (openCubeSet Q))
    (s₂ : (physicalPotentialSpace Q).toSubmodule) :
    (ν / σ) • twoSlotY Q hν hσ k s₁ s₂ + physicalProjectedCoefficient Q σ hσ k
      (twoSlotX Q hν hσ k s₁ s₂) = s₁ :=
  (pair_inverse_equations (Y := HilbertVectorL2 (openCubeSet Q))
    (X := (physicalPotentialSpace Q).toSubmodule) (div_pos hν hσ)
    (physicalProjectedCoefficient Q σ hσ k) (WithLp.toLp 2 (s₁, s₂))).1

theorem twoSlot_eq2 (Q : TriadicCube 2) {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (s₁ : HilbertVectorL2 (openCubeSet Q))
    (s₂ : (physicalPotentialSpace Q).toSubmodule) :
    -((physicalProjectedCoefficient Q σ hσ k).adjoint (twoSlotY Q hν hσ k s₁ s₂)) +
      (ν / σ) • twoSlotX Q hν hσ k s₁ s₂ = s₂ :=
  (pair_inverse_equations (Y := HilbertVectorL2 (openCubeSet Q))
    (X := (physicalPotentialSpace Q).toSubmodule) (div_pos hν hσ)
    (physicalProjectedCoefficient Q σ hσ k) (WithLp.toLp 2 (s₁, s₂))).2

theorem twoSlot_J (Q : TriadicCube 2) {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (s₁ : HilbertVectorL2 (openCubeSet Q))
    (s₂ : (physicalPotentialSpace Q).toSubmodule) :
    ⟪pureFluxParity (Y := HilbertVectorL2 (openCubeSet Q))
        (X := (physicalPotentialSpace Q).toSubmodule) (WithLp.toLp 2 (s₁, s₂)),
      pureFluxBlockInverse (Y := HilbertVectorL2 (openCubeSet Q))
        (X := (physicalPotentialSpace Q).toSubmodule) (ν / σ) (div_pos hν hσ)
        (physicalProjectedCoefficient Q σ hσ k) (WithLp.toLp 2 (s₁, s₂))⟫_ℝ =
      ⟪s₁, twoSlotY Q hν hσ k s₁ s₂⟫_ℝ -
        ⟪(s₂ : HilbertVectorL2 (openCubeSet Q)),
          (twoSlotX Q hν hσ k s₁ s₂ : HilbertVectorL2 (openCubeSet Q))⟫_ℝ := by
  rw [pair_J_form (Y := HilbertVectorL2 (openCubeSet Q))
    (X := (physicalPotentialSpace Q).toSubmodule) (div_pos hν hσ)
    (physicalProjectedCoefficient Q σ hσ k) (WithLp.toLp 2 (s₁, s₂)), Submodule.coe_inner]
  rfl

theorem twoSlot_energy_split (Q : TriadicCube 2) {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (s₁ : HilbertVectorL2 (openCubeSet Q))
    (s₂ : (physicalPotentialSpace Q).toSubmodule) :
    pairEnergy' (ν / σ) (twoSlotY Q hν hσ k s₁ s₂) (twoSlotX Q hν hσ k s₁ s₂) =
      pairEnergy' (ν / σ) (twoSlotY Q hν hσ k s₁ 0) (twoSlotX Q hν hσ k s₁ 0) +
        pairEnergy' (ν / σ) (twoSlotY Q hν hσ k 0 s₂) (twoSlotX Q hν hσ k 0 s₂) :=
  pair_energy_split (Y := HilbertVectorL2 (openCubeSet Q))
    (X := (physicalPotentialSpace Q).toSubmodule) (div_pos hν hσ)
    (physicalProjectedCoefficient Q σ hσ k) s₁ s₂

theorem twoSlot_energy_norm (Q : TriadicCube 2) {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (s₁ : HilbertVectorL2 (openCubeSet Q))
    (s₂ : (physicalPotentialSpace Q).toSubmodule) :
    pairEnergy' (ν / σ) (twoSlotY Q hν hσ k s₁ s₂) (twoSlotX Q hν hσ k s₁ s₂) =
      (ν / σ) * (‖(twoSlotX Q hν hσ k s₁ s₂ : HilbertVectorL2 (openCubeSet Q))‖ ^ 2 +
        ‖twoSlotY Q hν hσ k s₁ s₂‖ ^ 2) := by
  unfold pairEnergy'
  rw [Submodule.coe_norm]

/-- The two-slot NEW inverse on the parent cube, in function form. -/
theorem two_slot_parent_data (Q : TriadicCube 2) {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) {F G : Vec 2 → Vec 2}
    (hF : MemVectorL2 (openCubeSet Q) F) (hG : MemVectorL2 (openCubeSet Q) G)
    (s₁ : HilbertVectorL2 (openCubeSet Q))
    (s₂ : (physicalPotentialSpace Q).toSubmodule)
    (hs1 : s₁ ∈ (physicalFluxSpace Q).toSubmodule)
    (hs1' : ∀ w ∈ (physicalFluxSpace Q).toSubmodule,
      ⟪s₁, w⟫_ℝ = ⟪toHilbertVectorL2OfVecField hF, w⟫_ℝ)
    (hs2' : ∀ w : (physicalPotentialSpace Q).toSubmodule,
      ⟪(s₂ : HilbertVectorL2 (openCubeSet Q)), (w : HilbertVectorL2 (openCubeSet Q))⟫_ℝ =
        ⟪toHilbertVectorL2OfVecField hG, (w : HilbertVectorL2 (openCubeSet Q))⟫_ℝ) :
    ∃ (φ : H10Function (openCubeSet Q)) (η : H1Function (openCubeSet Q)),
      IsSolenoidalOn (openCubeSet Q) (fun z =>
        (ν / σ) • η.grad z + shear' σ k z (φ.toH1Function.grad z) - F z) ∧
      IsSolenoidalOn (openCubeSet Q) (fun z =>
        (ν / σ) • φ.toH1Function.grad z + shear' σ k z (η.grad z) - G z) ∧
      ⟪s₁, twoSlotY Q hν hσ k s₁ s₂⟫_ℝ -
        ⟪(s₂ : HilbertVectorL2 (openCubeSet Q)),
          (twoSlotX Q hν hσ k s₁ s₂ : HilbertVectorL2 (openCubeSet Q))⟫_ℝ =
        (∫ z in openCubeSet Q, vecDot (F z) (η.grad z) ∂volume) -
          ∫ z in openCubeSet Q, vecDot (G z) (φ.toH1Function.grad z) ∂volume ∧
      ⟪s₁, twoSlotY Q hν hσ k s₁ s₂⟫_ℝ +
        ⟪(s₂ : HilbertVectorL2 (openCubeSet Q)),
          (twoSlotX Q hν hσ k s₁ s₂ : HilbertVectorL2 (openCubeSet Q))⟫_ℝ =
        (∫ z in openCubeSet Q, vecDot (F z) (η.grad z) ∂volume) +
          ∫ z in openCubeSet Q, vecDot (G z) (φ.toH1Function.grad z) ∂volume ∧
      ‖(twoSlotX Q hν hσ k s₁ s₂ : HilbertVectorL2 (openCubeSet Q))‖ ^ 2 +
          ‖twoSlotY Q hν hσ k s₁ s₂‖ ^ 2 =
        (∫ z in openCubeSet Q, vecNormSq (φ.toH1Function.grad z) ∂volume) +
          ∫ z in openCubeSet Q, vecNormSq (η.grad z) ∂volume := by
  obtain ⟨φ, η, hc, hd, hid, hplus, hnorm⟩ := two_slot_parent_core Q hν hσ k hF hG s₁
    (twoSlotY Q hν hσ k s₁ s₂) s₂ (twoSlotX Q hν hσ k s₁ s₂) hs1 hs1' hs2'
    (twoSlot_eq1 Q hν hσ k s₁ s₂) (twoSlot_eq2 Q hν hσ k s₁ s₂)
  exact ⟨φ, η, hc, hd, hid, hplus, hnorm⟩

end

end ASDExplicitGamma.Scalar
