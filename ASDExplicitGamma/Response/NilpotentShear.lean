module

public import Homogenization.CoarseGraining.MuWellPosedness
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

@[expose] public section

namespace ASDExplicitGamma.Response

open ContinuousLinearMap
open scoped RealInnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The affine shear used to perturb the Hilbert norm. -/
def nilpotentShearMap (C : H →L[ℝ] H) (ε : ℝ) : H →L[ℝ] H :=
  ContinuousLinearMap.id ℝ H + ε • C

/-- The Gram operator of the affine shear. -/
def nilpotentShearGram (C : H →L[ℝ] H) (ε : ℝ) : H →L[ℝ] H :=
  ContinuousLinearMap.id ℝ H + ε • (C + C.adjoint) + ε ^ 2 • (C.adjoint ∘L C)

private theorem nilpotentShearGram_inner (C : H →L[ℝ] H) (ε : ℝ) (x y : H) :
    inner ℝ (nilpotentShearGram C ε x) y =
      inner ℝ (nilpotentShearMap C ε x) (nilpotentShearMap C ε y) := by
  have hadj₁ : inner ℝ (C.adjoint x) y = inner ℝ x (C y) :=
    ContinuousLinearMap.adjoint_inner_left C y x
  have hadj₂ : inner ℝ (C.adjoint (C x)) y = inner ℝ (C x) (C y) :=
    ContinuousLinearMap.adjoint_inner_left C y (C x)
  simp only [nilpotentShearGram, nilpotentShearMap, add_apply,
    smul_apply, ContinuousLinearMap.id_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right]
  rw [hadj₁, ContinuousLinearMap.comp_apply, hadj₂]
  simp only [starRingEnd_apply, star_trivial]
  ring

omit [CompleteSpace H] in
private theorem nilpotentShearMap_leftInverse (C : H →L[ℝ] H) (ε : ℝ)
    (hC : C ∘L C = 0) :
    (ContinuousLinearMap.id ℝ H - ε • C) ∘L nilpotentShearMap C ε =
      ContinuousLinearMap.id ℝ H := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, nilpotentShearMap,
    add_apply, sub_apply, smul_apply, ContinuousLinearMap.id_apply]
  rw [map_add, map_smul]
  have hCx : C (C x) = 0 := by
    have h := congrArg (fun A : H →L[ℝ] H => A x) hC
    simpa only [ContinuousLinearMap.comp_apply, zero_apply] using h
  rw [hCx]
  module

omit [CompleteSpace H] in
private theorem nilpotentShearMap_rightInverse (C : H →L[ℝ] H) (ε : ℝ)
    (hC : C ∘L C = 0) :
    nilpotentShearMap C ε ∘L (ContinuousLinearMap.id ℝ H - ε • C) =
      ContinuousLinearMap.id ℝ H := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, nilpotentShearMap,
    add_apply, sub_apply, smul_apply, ContinuousLinearMap.id_apply]
  rw [map_sub, map_smul]
  have hCx : C (C x) = 0 := by
    have h := congrArg (fun A : H →L[ℝ] H => A x) hC
    simpa only [ContinuousLinearMap.comp_apply, zero_apply] using h
  rw [hCx]
  module

omit [CompleteSpace H] in
private theorem nilpotentShear_norm_lower (C : H →L[ℝ] H) (ε : ℝ)
    (hC : C ∘L C = 0) (x : H) :
    ‖x‖ ≤ (1 + |ε| * ‖C‖) * ‖nilpotentShearMap C ε x‖ := by
  have hinv := congrArg (fun A : H →L[ℝ] H => A x)
    (nilpotentShearMap_leftInverse C ε hC)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hinv
  have hrewrite : (ContinuousLinearMap.id ℝ H - ε • C) (nilpotentShearMap C ε x) =
      nilpotentShearMap C ε x - ε • C (nilpotentShearMap C ε x) := by
    simp [sub_apply, ContinuousLinearMap.id_apply, smul_apply]
  rw [hrewrite] at hinv
  calc
    ‖x‖ = ‖nilpotentShearMap C ε x - ε • C (nilpotentShearMap C ε x)‖ := by
      exact (congrArg norm hinv).symm
    _ ≤ ‖nilpotentShearMap C ε x‖ + ‖ε • C (nilpotentShearMap C ε x)‖ := norm_sub_le _ _
    _ = ‖nilpotentShearMap C ε x‖ + |ε| * ‖C (nilpotentShearMap C ε x)‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖nilpotentShearMap C ε x‖ + |ε| * ‖C‖ * ‖nilpotentShearMap C ε x‖ := by
      have h := C.le_opNorm (nilpotentShearMap C ε x)
      calc
        _ ≤ ‖nilpotentShearMap C ε x‖ + |ε| * (‖C‖ * ‖nilpotentShearMap C ε x‖) := by
          gcongr
        _ = _ := by ring
    _ = _ := by ring

private theorem nilpotentShearEnergy_coercive (C : H →L[ℝ] H) (ε : ℝ)
    (hC : C ∘L C = 0) :
    IsCoercive (Homogenization.energyBilinOfOperator (nilpotentShearGram C ε)) := by
  let a : ℝ := 1 + |ε| * ‖C‖
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨a⁻¹ ^ 2, by positivity, ?_⟩
  intro x
  rw [Homogenization.energyBilinOfOperator_apply, nilpotentShearGram_inner]
  have hnorm := nilpotentShear_norm_lower C ε hC x
  have hsq : (a⁻¹ * ‖x‖) ^ 2 ≤ ‖nilpotentShearMap C ε x‖ ^ 2 := by
    apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).2
    calc
      a⁻¹ * ‖x‖ ≤ a⁻¹ * (a * ‖nilpotentShearMap C ε x‖) := by
        exact mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr ha.le)
      _ = ‖nilpotentShearMap C ε x‖ := by field_simp [ne_of_gt ha]
  calc
    a⁻¹ ^ 2 * ‖x‖ * ‖x‖ = (a⁻¹ * ‖x‖) ^ 2 := by ring
    _ ≤ ‖nilpotentShearMap C ε x‖ ^ 2 := hsq
    _ = inner ℝ (nilpotentShearMap C ε x) (nilpotentShearMap C ε x) := by
      rw [real_inner_self_eq_norm_sq]

def nilpotentShearSubspaceOperator (V : ClosedSubmodule ℝ H)
    (C : H →L[ℝ] H) (ε : ℝ) : V.toSubmodule →L[ℝ] V.toSubmodule :=
  V.toSubmodule.orthogonalProjectionOnto ∘L
    nilpotentShearGram C ε ∘L V.toSubmodule.subtypeL

private theorem nilpotentShearSubspaceOperator_inner (V : ClosedSubmodule ℝ H)
    (C : H →L[ℝ] H) (ε : ℝ) (x y : V.toSubmodule) :
    inner ℝ (nilpotentShearSubspaceOperator V C ε x) y =
      inner ℝ (nilpotentShearGram C ε (x : H)) (y : H) := by
  exact V.toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_right y
    (nilpotentShearGram C ε (x : H))

theorem nilpotentShearSubspaceEnergy_coercive (V : ClosedSubmodule ℝ H)
    (C : H →L[ℝ] H) (ε : ℝ) (hC : C ∘L C = 0) :
    IsCoercive (Homogenization.energyBilinOfOperator
      (nilpotentShearSubspaceOperator V C ε)) := by
  let a : ℝ := 1 + |ε| * ‖C‖
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨a⁻¹ ^ 2, by positivity, ?_⟩
  intro x
  rw [Homogenization.energyBilinOfOperator_apply, nilpotentShearSubspaceOperator_inner,
    nilpotentShearGram_inner]
  have hnorm := nilpotentShear_norm_lower C ε hC (x : H)
  have hsq : (a⁻¹ * ‖(x : H)‖) ^ 2 ≤
      ‖nilpotentShearMap C ε (x : H)‖ ^ 2 := by
    apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).2
    calc
      a⁻¹ * ‖(x : H)‖ ≤ a⁻¹ * (a * ‖nilpotentShearMap C ε (x : H)‖) := by
        exact mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr ha.le)
      _ = ‖nilpotentShearMap C ε (x : H)‖ := by field_simp [ne_of_gt ha]
  calc
    a⁻¹ ^ 2 * ‖x‖ * ‖x‖ = (a⁻¹ * ‖(x : H)‖) ^ 2 := by
      change a⁻¹ ^ 2 * ‖(x : H)‖ * ‖(x : H)‖ = _
      ring
    _ ≤ ‖nilpotentShearMap C ε (x : H)‖ ^ 2 := hsq
    _ = inner ℝ (nilpotentShearMap C ε (x : H))
        (nilpotentShearMap C ε (x : H)) := by rw [real_inner_self_eq_norm_sq]

theorem nilpotentShearSubspaceOperator_eq_laxMilgram
    (V : ClosedSubmodule ℝ H) (C : H →L[ℝ] H) (ε : ℝ)
    (hC : C ∘L C = 0) :
    nilpotentShearSubspaceOperator V C ε =
      ((nilpotentShearSubspaceEnergy_coercive V C ε hC).continuousLinearEquivOfBilin).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  calc
    inner ℝ (nilpotentShearSubspaceOperator V C ε x) y =
        Homogenization.energyBilinOfOperator (nilpotentShearSubspaceOperator V C ε) x y := by
          rw [Homogenization.energyBilinOfOperator_apply]
    _ = inner ℝ
        ((nilpotentShearSubspaceEnergy_coercive V C ε hC).continuousLinearEquivOfBilin x) y :=
          (IsCoercive.continuousLinearEquivOfBilin_apply
            (nilpotentShearSubspaceEnergy_coercive V C ε hC) x y).symm

def nilpotentShearSubspaceUnit (V : ClosedSubmodule ℝ H)
    (C : H →L[ℝ] H) (ε : ℝ) (hC : C ∘L C = 0) :
    (V.toSubmodule →L[ℝ] V.toSubmodule)ˣ := by
  let e := (nilpotentShearSubspaceEnergy_coercive V C ε hC).continuousLinearEquivOfBilin
  refine ⟨nilpotentShearSubspaceOperator V C ε, e.symm.toContinuousLinearMap, ?_, ?_⟩
  · change nilpotentShearSubspaceOperator V C ε ∘L e.symm.toContinuousLinearMap = 1
    rw [nilpotentShearSubspaceOperator_eq_laxMilgram V C ε hC]
    ext x
    simp [e]
  · change e.symm.toContinuousLinearMap ∘L nilpotentShearSubspaceOperator V C ε = 1
    rw [nilpotentShearSubspaceOperator_eq_laxMilgram V C ε hC]
    ext x
    simp [e]

private theorem nilpotentShearSubspaceUnit_val (V : ClosedSubmodule ℝ H)
    (C : H →L[ℝ] H) (ε : ℝ) (hC : C ∘L C = 0) :
    ↑(nilpotentShearSubspaceUnit V C ε hC) = nilpotentShearSubspaceOperator V C ε := rfl

def nilpotentShearCorrection (V : ClosedSubmodule ℝ H)
    (C : H →L[ℝ] H) (S : H) (ε : ℝ) (hC : C ∘L C = 0) : V.toSubmodule :=
  -(nilpotentShearSubspaceUnit V C ε hC).inv
    (V.toSubmodule.orthogonalProjectionOnto (nilpotentShearGram C ε S))

def nilpotentShearMinimizer (V : ClosedSubmodule ℝ H)
    (C : H →L[ℝ] H) (S : H) (ε : ℝ) (hC : C ∘L C = 0) : H :=
  S + nilpotentShearCorrection V C S ε hC

/-- The affine shear minimizer is stationary against every closed-subspace variation. -/
theorem nilpotentShearMinimizer_firstVariation (V : ClosedSubmodule ℝ H)
    (C : H →L[ℝ] H) (S : H) (ε : ℝ) (hC : C ∘L C = 0)
    (Y : V.toSubmodule) :
    inner ℝ (nilpotentShearGram C ε (nilpotentShearMinimizer V C S ε hC)) (Y : H) = 0 := by
  let A := nilpotentShearSubspaceOperator V C ε
  let U := nilpotentShearSubspaceUnit V C ε hC
  let d := V.toSubmodule.orthogonalProjectionOnto (nilpotentShearGram C ε S)
  have hInv : A (U.inv d) = d := by
    have h := congrArg (fun B : V.toSubmodule →L[ℝ] V.toSubmodule => B d) U.val_inv
    change A (U.inv d) = d at h
    exact h
  have hCorr : A (nilpotentShearCorrection V C S ε hC) = -d := by
    change A (-U.inv d) = -d
    rw [map_neg, hInv]
  have hProj : inner ℝ (nilpotentShearGram C ε S) (Y : H) = inner ℝ d Y := by
    exact (V.toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_right Y
      (nilpotentShearGram C ε S)).symm
  have hCorrInner :
      inner ℝ (nilpotentShearGram C ε (nilpotentShearCorrection V C S ε hC)) (Y : H) =
        -inner ℝ d Y := by
    rw [← nilpotentShearSubspaceOperator_inner]
    rw [hCorr]
    simp
  change inner ℝ (nilpotentShearGram C ε
    (S + nilpotentShearCorrection V C S ε hC)) (Y : H) = 0
  rw [map_add, inner_add_left, hProj, hCorrInner]
  ring

/-- The minimum of the norm-squared objective on the affine shear of `S + V`. -/
def nilpotentShearMinimum (V : ClosedSubmodule ℝ H) (C : H →L[ℝ] H)
    (S : H) (ε : ℝ) (hC : C ∘L C = 0) : ℝ :=
  ‖nilpotentShearMap C ε (nilpotentShearMinimizer V C S ε hC)‖ ^ 2

private theorem nilpotentShearCorrection_mem (V : ClosedSubmodule ℝ H)
    (C : H →L[ℝ] H) (S : H) (ε : ℝ) (hC : C ∘L C = 0) :
    (nilpotentShearCorrection V C S ε hC : H) ∈ V.toSubmodule := by
  exact (nilpotentShearCorrection V C S ε hC).property

/-- The candidate realizes the minimum over the affine space `S + V`. -/
theorem nilpotentShearMinimizer_minimizes (V : ClosedSubmodule ℝ H)
    (C : H →L[ℝ] H) (S W : H) (ε : ℝ) (hC : C ∘L C = 0)
    (hW : W - S ∈ V.toSubmodule) :
    nilpotentShearMinimum V C S ε hC ≤
      ‖nilpotentShearMap C ε W‖ ^ 2 := by
  let Z := nilpotentShearMinimizer V C S ε hC
  have hY : W - Z ∈ V.toSubmodule := by
    have hcorr := nilpotentShearCorrection_mem V C S ε hC
    change W - (S + nilpotentShearCorrection V C S ε hC) ∈ V.toSubmodule
    have hEq : W - (S + nilpotentShearCorrection V C S ε hC) =
        (W - S) - nilpotentShearCorrection V C S ε hC := by abel
    rw [hEq]
    exact V.toSubmodule.sub_mem hW hcorr
  have hstat := nilpotentShearMinimizer_firstVariation V C S ε hC ⟨W - Z, hY⟩
  have hcross : inner ℝ (nilpotentShearMap C ε Z) (nilpotentShearMap C ε (W - Z)) = 0 := by
    rw [← nilpotentShearGram_inner]
    exact hstat
  have hcross' : inner ℝ (nilpotentShearMap C ε (W - Z))
      (nilpotentShearMap C ε Z) = 0 := by
    rw [real_inner_comm]
    exact hcross
  have henergy : ‖nilpotentShearMap C ε W‖ ^ 2 =
      ‖nilpotentShearMap C ε Z‖ ^ 2 +
        ‖nilpotentShearMap C ε (W - Z)‖ ^ 2 := by
    have hdecomp : W = Z + (W - Z) := by abel
    calc
      ‖nilpotentShearMap C ε W‖ ^ 2 =
          ‖nilpotentShearMap C ε (Z + (W - Z))‖ ^ 2 :=
            congrArg (fun x : H => ‖nilpotentShearMap C ε x‖ ^ 2) hdecomp
      _ = ‖nilpotentShearMap C ε Z +
          nilpotentShearMap C ε (W - Z)‖ ^ 2 := by rw [nilpotentShearMap, map_add]
      _ = ‖nilpotentShearMap C ε Z‖ ^ 2 +
          ‖nilpotentShearMap C ε (W - Z)‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
          ← real_inner_self_eq_norm_sq]
        simp only [inner_add_left, inner_add_right, hcross, hcross']
        ring
  change ‖nilpotentShearMap C ε Z‖ ^ 2 ≤ ‖nilpotentShearMap C ε W‖ ^ 2
  rw [henergy]
  linarith [sq_nonneg ‖nilpotentShearMap C ε (W - Z)‖]

private theorem nilpotentShearCorrection_mapInverse (V : ClosedSubmodule ℝ H)
    (C : H →L[ℝ] H) (S : H) (ε : ℝ) (hC : C ∘L C = 0) :
    nilpotentShearCorrection V C S ε hC =
      -(ContinuousLinearMap.inverse (nilpotentShearSubspaceOperator V C ε)
        (V.toSubmodule.orthogonalProjectionOnto (nilpotentShearGram C ε S))) := by
  let U := nilpotentShearSubspaceUnit V C ε hC
  let A := nilpotentShearSubspaceOperator V C ε
  let d := V.toSubmodule.orthogonalProjectionOnto (nilpotentShearGram C ε S)
  have h₁ : A ∘L U.inv = ContinuousLinearMap.id ℝ V.toSubmodule := by
    have h := congrArg (fun B : V.toSubmodule →L[ℝ] V.toSubmodule => B) U.val_inv
    change A ∘L U.inv = ContinuousLinearMap.id ℝ V.toSubmodule at h
    exact h
  have h₂ : U.inv ∘L A = ContinuousLinearMap.id ℝ V.toSubmodule := by
    have h := congrArg (fun B : V.toSubmodule →L[ℝ] V.toSubmodule => B) U.inv_val
    change U.inv ∘L A = ContinuousLinearMap.id ℝ V.toSubmodule at h
    exact h
  have hInv := ContinuousLinearMap.inverse_eq h₁ h₂
  change -U.inv d = -(ContinuousLinearMap.inverse A) d
  rw [hInv]

/-- The minimized shear energy is analytic in particular twice continuously differentiable. -/
theorem nilpotentShearMinimum_contDiffAt (V : ClosedSubmodule ℝ H)
    (C : H →L[ℝ] H) (S : H) (hC : C ∘L C = 0) (ε : ℝ) :
    ContDiffAt ℝ 2 (fun t => nilpotentShearMinimum V C S t hC) ε := by
  let F : ℝ → (V.toSubmodule →L[ℝ] V.toSubmodule) :=
    fun t => nilpotentShearSubspaceOperator V C t
  let d : ℝ → V.toSubmodule :=
    fun t => V.toSubmodule.orthogonalProjectionOnto (nilpotentShearGram C t S)
  let Z : ℝ → H := fun t => nilpotentShearMinimizer V C S t hC
  have hF : ContDiffAt ℝ 2 F ε := by
    dsimp [F]
    fun_prop [nilpotentShearSubspaceOperator, nilpotentShearGram]
  have hd : ContDiffAt ℝ 2 d ε := by
    dsimp [d]
    fun_prop [nilpotentShearGram]
  let e :=
    (nilpotentShearSubspaceEnergy_coercive V C ε hC).continuousLinearEquivOfBilin
  have hAt' : F ε = e.toContinuousLinearMap := by
    dsimp [F, e]
    exact nilpotentShearSubspaceOperator_eq_laxMilgram V C ε hC
  have hInvAt : ContDiffAt ℝ 2 ContinuousLinearMap.inverse (F ε) := by
    rw [hAt']
    exact _root_.contDiffAt_map_inverse (𝕜 := ℝ) e
  have hInv : ContDiffAt ℝ 2 (fun t => ContinuousLinearMap.inverse (F t)) ε :=
    hInvAt.comp ε hF
  have hApply : ContDiffAt ℝ 2 (fun t => (ContinuousLinearMap.inverse (F t)) (d t)) ε :=
    hInv.clm_apply hd
  have hCorrSub : ContDiffAt ℝ 2
      (fun t => nilpotentShearCorrection V C S t hC) ε := by
    have hEq : (fun t => nilpotentShearCorrection V C S t hC) =
        fun t => -(ContinuousLinearMap.inverse (F t) (d t)) := by
      funext t
      simpa only [F, d] using nilpotentShearCorrection_mapInverse V C S t hC
    rw [hEq]
    exact hApply.neg
  have hCorr : ContDiffAt ℝ 2
      (fun t => (nilpotentShearCorrection V C S t hC : H)) ε := by
    have hInclusion : ContDiffAt ℝ 2
        (fun _ : ℝ => V.toSubmodule.subtypeL) ε := contDiffAt_const
    exact hInclusion.clm_apply hCorrSub
  have hZ : ContDiffAt ℝ 2 Z ε := by
    dsimp [Z]
    simpa only [nilpotentShearMinimizer] using
      ((contDiffAt_const : ContDiffAt ℝ 2 (fun _ : ℝ => S) ε).add hCorr)
  have hShear : ContDiffAt ℝ 2
      (fun t => nilpotentShearMap C t (Z t)) ε := by
    dsimp [nilpotentShearMap]
    fun_prop
  have hInner : ContDiffAt ℝ 2
      (fun t => (innerSL ℝ) (nilpotentShearMap C t (Z t))
        (nilpotentShearMap C t (Z t))) ε := by
    exact (contDiffAt_const.clm_apply hShear).clm_apply hShear
  have hEnergy : (fun t => nilpotentShearMinimum V C S t hC) =
      fun t => (innerSL ℝ) (nilpotentShearMap C t (Z t))
        (nilpotentShearMap C t (Z t)) := by
    funext t
    simp [nilpotentShearMinimum, Z]
  rw [hEnergy]
  exact hInner

end

end ASDExplicitGamma.Response
