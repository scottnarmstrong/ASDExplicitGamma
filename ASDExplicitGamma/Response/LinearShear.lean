module

public import ASDExplicitGamma.Response.NilpotentShear
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.InnerProductSpace.Calculus

@[expose] public section

namespace ASDExplicitGamma.Response

noncomputable section

variable {B H : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def responseAdjointMap : (H →L[ℝ] H) →L[ℝ] (H →L[ℝ] H) where
  toFun := fun T => T.adjoint
  map_add' := by
    intro T R
    exact map_add ContinuousLinearMap.adjoint T R
  map_smul' := by
    intro r T
    calc
      ContinuousLinearMap.adjoint (r • T) =
          (starRingEnd ℝ) r • ContinuousLinearMap.adjoint T :=
        ContinuousLinearMap.adjoint.map_smulₛₗ r T
      _ = r • ContinuousLinearMap.adjoint T := by
        rw [starRingEnd_apply, star_trivial]
  cont := ContinuousLinearMap.adjoint.continuous

/-- A bounded linear family of nilpotent shears on a fixed Hilbert space. -/
def linearShearGram (C : B →L[ℝ] (H →L[ℝ] H)) (h : B) : H →L[ℝ] H :=
  ContinuousLinearMap.id ℝ H +
    1 • (C h + responseAdjointMap (C h)) +
    1 ^ 2 • (responseAdjointMap (C h) ∘L C h)

private theorem linearShearGram_eq_nilpotentShearGram
    (C : B →L[ℝ] (H →L[ℝ] H)) (h : B) :
    linearShearGram C h = nilpotentShearGram (C h) 1 := by
  ext x
  simp [linearShearGram, nilpotentShearGram, responseAdjointMap]

def linearShearSubspaceOperator (V : ClosedSubmodule ℝ H)
    (C : B →L[ℝ] (H →L[ℝ] H)) (h : B) :
    V.toSubmodule →L[ℝ] V.toSubmodule :=
  V.toSubmodule.orthogonalProjectionOnto ∘L
    linearShearGram C h ∘L V.toSubmodule.subtypeL

def linearShearCorrection (V : ClosedSubmodule ℝ H)
    (C : B →L[ℝ] (H →L[ℝ] H)) (S : H) (h : B)
    (hNil : ∀ x y, C x ∘L C y = 0) : V.toSubmodule :=
  -(nilpotentShearSubspaceUnit V (C h) 1 (hNil h h)).inv
    (V.toSubmodule.orthogonalProjectionOnto (linearShearGram C h S))

def linearShearMinimizer (V : ClosedSubmodule ℝ H)
    (C : B →L[ℝ] (H →L[ℝ] H)) (S : H) (h : B)
    (hNil : ∀ x y, C x ∘L C y = 0) : H :=
  S + linearShearCorrection V C S h hNil

def linearShearMinimum (V : ClosedSubmodule ℝ H)
    (C : B →L[ℝ] (H →L[ℝ] H)) (S : H) (h : B)
    (hNil : ∀ x y, C x ∘L C y = 0) : ℝ :=
  ‖nilpotentShearMap (C h) 1 (linearShearMinimizer V C S h hNil)‖ ^ 2

private theorem linearShearCorrection_eq_nilpotent (V : ClosedSubmodule ℝ H)
    (C : B →L[ℝ] (H →L[ℝ] H)) (S : H) (h : B)
    (hNil : ∀ x y, C x ∘L C y = 0) :
    linearShearCorrection V C S h hNil =
      nilpotentShearCorrection V (C h) S 1 (hNil h h) := by
  unfold linearShearCorrection nilpotentShearCorrection
  rw [linearShearGram_eq_nilpotentShearGram]

/-- The correction from the unperturbed load to the linear-family minimizer
belongs to the fixed variation subspace. -/
theorem linearShearMinimizer_sub_mem (V : ClosedSubmodule ℝ H)
    (C : B →L[ℝ] (H →L[ℝ] H)) (S : H) (h : B)
    (hNil : ∀ x y, C x ∘L C y = 0) :
    linearShearMinimizer V C S h hNil - S ∈ V.toSubmodule := by
  change S + (linearShearCorrection V C S h hNil : H) - S ∈ V.toSubmodule
  have hEq : S + (linearShearCorrection V C S h hNil : H) - S =
      (linearShearCorrection V C S h hNil : H) := by abel
  rw [hEq]
  exact (linearShearCorrection V C S h hNil).property

/-- The linear-family minimizer realizes the minimum over its affine space. -/
theorem linearShearMinimum_minimizes (V : ClosedSubmodule ℝ H)
    (C : B →L[ℝ] (H →L[ℝ] H)) (S W : H) (h : B)
    (hNil : ∀ x y, C x ∘L C y = 0)
    (hW : W - S ∈ V.toSubmodule) :
    linearShearMinimum V C S h hNil ≤
      ‖nilpotentShearMap (C h) 1 W‖ ^ 2 := by
  have hZ : linearShearMinimizer V C S h hNil =
      nilpotentShearMinimizer V (C h) S 1 (hNil h h) := by
    unfold linearShearMinimizer nilpotentShearMinimizer
    rw [linearShearCorrection_eq_nilpotent]
  have hMin : linearShearMinimum V C S h hNil =
      nilpotentShearMinimum V (C h) S 1 (hNil h h) := by
    simp [linearShearMinimum, nilpotentShearMinimum, hZ]
  rw [hMin]
  exact nilpotentShearMinimizer_minimizes V (C h) S W 1
    (hNil h h) hW

/-- Stationarity of the linear-family minimizer against the fixed variation
space. -/
theorem linearShearMinimizer_firstVariation (V : ClosedSubmodule ℝ H)
    (C : B →L[ℝ] (H →L[ℝ] H)) (S : H) (h : B)
    (hNil : ∀ x y, C x ∘L C y = 0) (Y : V.toSubmodule) :
    inner ℝ (linearShearGram C h (linearShearMinimizer V C S h hNil)) (Y : H) = 0 := by
  have hBase := nilpotentShearMinimizer_firstVariation V (C h) S 1 (hNil h h) Y
  rw [linearShearGram_eq_nilpotentShearGram]
  have hMin : linearShearMinimizer V C S h hNil =
      nilpotentShearMinimizer V (C h) S 1 (hNil h h) := by
    change S + (linearShearCorrection V C S h hNil : H) =
      S + (nilpotentShearCorrection V (C h) S 1 (hNil h h) : H)
    rw [linearShearCorrection_eq_nilpotent]
  rw [hMin]
  exact hBase

/-- Stationarity of the linear-family minimizer against the fixed variation
space. -/

private theorem linearShearOperator_eq_laxMilgram (V : ClosedSubmodule ℝ H)
    (C : B →L[ℝ] (H →L[ℝ] H)) (h : B) (hNil : ∀ x y, C x ∘L C y = 0) :
    linearShearSubspaceOperator V C h =
      ((nilpotentShearSubspaceEnergy_coercive V (C h) 1 (hNil h h)).continuousLinearEquivOfBilin).toContinuousLinearMap := by
  have hOp : linearShearSubspaceOperator V C h =
      nilpotentShearSubspaceOperator V (C h) 1 := by
    unfold linearShearSubspaceOperator nilpotentShearSubspaceOperator
    rw [linearShearGram_eq_nilpotentShearGram]
  rw [hOp]
  exact nilpotentShearSubspaceOperator_eq_laxMilgram V (C h) 1 (hNil h h)

private theorem linearShearSubspaceUnit_val (V : ClosedSubmodule ℝ H)
    (C : B →L[ℝ] (H →L[ℝ] H)) (h : B)
    (hNil : ∀ x y, C x ∘L C y = 0) :
    ↑(nilpotentShearSubspaceUnit V (C h) 1 (hNil h h)) =
      linearShearSubspaceOperator V C h := by
  change nilpotentShearSubspaceOperator V (C h) 1 =
    linearShearSubspaceOperator V C h
  exact (nilpotentShearSubspaceOperator_eq_laxMilgram V (C h) 1 (hNil h h)).trans
    (linearShearOperator_eq_laxMilgram V C h hNil).symm

private theorem linearShearCorrection_mapInverse (V : ClosedSubmodule ℝ H)
    (C : B →L[ℝ] (H →L[ℝ] H)) (S : H) (h : B)
    (hNil : ∀ x y, C x ∘L C y = 0) :
    linearShearCorrection V C S h hNil =
      -(ContinuousLinearMap.inverse (linearShearSubspaceOperator V C h)
        (V.toSubmodule.orthogonalProjectionOnto (linearShearGram C h S))) := by
  let U := nilpotentShearSubspaceUnit V (C h) 1 (hNil h h)
  let A := linearShearSubspaceOperator V C h
  let d := V.toSubmodule.orthogonalProjectionOnto (linearShearGram C h S)
  have h₁ : A ∘L U.inv = ContinuousLinearMap.id ℝ V.toSubmodule := by
    ext x
    have hRaw := congrArg (fun T : V.toSubmodule →L[ℝ] V.toSubmodule => T x) U.val_inv
    have h := by simpa only [mul_apply_eq_comp, one_apply_eq_self] using hRaw
    rw [linearShearSubspaceUnit_val] at h
    change A (U.inv x) = x at h
    simpa [A] using h
  have h₂ : U.inv ∘L A = ContinuousLinearMap.id ℝ V.toSubmodule := by
    ext x
    have hRaw := congrArg (fun T : V.toSubmodule →L[ℝ] V.toSubmodule => T x) U.inv_val
    have h := by simpa only [mul_apply_eq_comp, one_apply_eq_self] using hRaw
    rw [linearShearSubspaceUnit_val] at h
    change U.inv (A x) = x at h
    simpa [A] using h
  have hInv := ContinuousLinearMap.inverse_eq h₁ h₂
  change -U.inv d = -(ContinuousLinearMap.inverse A) d
  rw [hInv]

/-- The minimum for a continuous linear nilpotent shear family is C² Fréchet
on its fixed Hilbert space. -/
theorem linearShearMinimum_contDiffAt (V : ClosedSubmodule ℝ H)
    (C : B →L[ℝ] (H →L[ℝ] H)) (S : H) (h : B)
    (hNil : ∀ x y, C x ∘L C y = 0) :
    ContDiffAt ℝ 2 (fun x => linearShearMinimum V C S x hNil) h := by
  let F : B → (V.toSubmodule →L[ℝ] V.toSubmodule) :=
    fun x => linearShearSubspaceOperator V C x
  let d : B → V.toSubmodule :=
    fun x => V.toSubmodule.orthogonalProjectionOnto (linearShearGram C x S)
  let Z : B → H := fun x => linearShearMinimizer V C S x hNil
  have hF : ContDiffAt ℝ 2 F h := by
    dsimp [F, linearShearSubspaceOperator, linearShearGram]
    fun_prop
  have hd : ContDiffAt ℝ 2 d h := by
    dsimp [d, linearShearGram]
    fun_prop
  let e :=
    (nilpotentShearSubspaceEnergy_coercive V (C h) 1 (hNil h h)).continuousLinearEquivOfBilin
  have hAt : F h = e.toContinuousLinearMap := by
    dsimp [F, e]
    exact linearShearOperator_eq_laxMilgram V C h hNil
  have hInvAt : ContDiffAt ℝ 2 ContinuousLinearMap.inverse (F h) := by
    rw [hAt]
    exact _root_.contDiffAt_map_inverse (𝕜 := ℝ) e
  have hInv : ContDiffAt ℝ 2 (fun x => ContinuousLinearMap.inverse (F x)) h :=
    hInvAt.comp h hF
  have hApply : ContDiffAt ℝ 2
      (fun x => (ContinuousLinearMap.inverse (F x)) (d x)) h :=
    hInv.clm_apply hd
  have hCorrSub : ContDiffAt ℝ 2 (fun x => linearShearCorrection V C S x hNil) h := by
    have hEq : (fun x => linearShearCorrection V C S x hNil) =
        fun x => -(ContinuousLinearMap.inverse (F x) (d x)) := by
      funext x
      simpa only [F, d] using linearShearCorrection_mapInverse V C S x hNil
    rw [hEq]
    exact hApply.neg
  have hCorr : ContDiffAt ℝ 2
      (fun x => (linearShearCorrection V C S x hNil : H)) h := by
    have hInclusion : ContDiffAt ℝ 2
        (fun _ : B => V.toSubmodule.subtypeL) h := contDiffAt_const
    exact hInclusion.clm_apply hCorrSub
  have hZ : ContDiffAt ℝ 2 Z h := by
    dsimp [Z, linearShearMinimizer]
    exact (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : B => S) h).add hCorr
  have hShear : ContDiffAt ℝ 2
      (fun x => nilpotentShearMap (C x) 1 (Z x)) h := by
    dsimp [nilpotentShearMap]
    fun_prop
  have hInner : ContDiffAt ℝ 2
      (fun x => (innerSL ℝ) (nilpotentShearMap (C x) 1 (Z x))
        (nilpotentShearMap (C x) 1 (Z x))) h :=
    (contDiffAt_const.clm_apply hShear).clm_apply hShear
  have hEnergy : (fun x => linearShearMinimum V C S x hNil) =
      fun x => (innerSL ℝ) (nilpotentShearMap (C x) 1 (Z x))
        (nilpotentShearMap (C x) 1 (Z x)) := by
    funext x
    simp [linearShearMinimum, Z]
  rw [hEnergy]
  exact hInner

/-- The linear-family nilpotent-shear minimum is globally twice continuously
differentiable, since the inverse formula is valid at every parameter. -/
theorem linearShearMinimum_contDiff (V : ClosedSubmodule ℝ H)
    (C : B →L[ℝ] (H →L[ℝ] H)) (S : H)
    (hNil : ∀ x y, C x ∘L C y = 0) :
    ContDiff ℝ 2 (fun h => linearShearMinimum V C S h hNil) := by
  rw [contDiff_iff_contDiffAt]
  intro h
  exact linearShearMinimum_contDiffAt V C S h hNil

private theorem hasFDerivAt_linearShearGram_apply
    (C : B →L[ℝ] (H →L[ℝ] H)) (S : H) :
    HasFDerivAt (fun h => linearShearGram C h S)
      ((ContinuousLinearMap.apply ℝ H S).comp (C + responseAdjointMap.comp C)) 0 := by
  let evalS : (H →L[ℝ] H) →L[ℝ] H := ContinuousLinearMap.apply ℝ H S
  have hC : HasFDerivAt (fun h => C h S) (evalS.comp C) 0 := by
    change HasFDerivAt (fun h => evalS (C h)) (evalS.comp C) 0
    exact (evalS.comp C).hasFDerivAt
  have hAdj : HasFDerivAt (fun h => responseAdjointMap (C h) S)
      (evalS.comp (responseAdjointMap.comp C)) 0 := by
    change HasFDerivAt (fun h => evalS ((responseAdjointMap.comp C) h))
      (evalS.comp (responseAdjointMap.comp C)) 0
    exact (evalS.comp (responseAdjointMap.comp C)).hasFDerivAt
  have hAdjOp : HasFDerivAt (fun h => responseAdjointMap (C h))
      (responseAdjointMap.comp C) 0 :=
    (responseAdjointMap.comp C).hasFDerivAt
  have hQuad : HasFDerivAt
      (fun h : B => responseAdjointMap (C h) (C h S))
      (0 : B →L[ℝ] H) (0 : B) := by
    have h := hAdjOp.clm_apply hC
    simpa [evalS, ContinuousLinearMap.apply_apply] using h
  have hConst : HasFDerivAt (fun _ : B => S) (0 : B →L[ℝ] H) (0 : B) := by
    exact hasFDerivAt_const (𝕜 := ℝ) (E := B) (F := H) S (0 : B)
  have hSum := ((hConst.add hC).add hAdj).add hQuad
  have hSum' : HasFDerivAt
    (fun h => S + C h S + responseAdjointMap (C h) S +
      responseAdjointMap (C h) (C h S))
    (evalS.comp C + evalS.comp (responseAdjointMap.comp C)) 0 := by
    convert hSum using 1
    · ext h
      simp
  convert hSum' using 1
  · ext h
    simp [linearShearGram, responseAdjointMap]
    abel
  · ext h
    simp [evalS, ContinuousLinearMap.comp_apply]

private theorem fderiv_linearShearGram_apply_zero
    (C : B →L[ℝ] (H →L[ℝ] H)) (S : H) (K : B) :
    fderiv ℝ (fun h => linearShearGram C h S) 0 K =
      C K S + responseAdjointMap (C K) S := by
  have h := congrArg (fun D : B →L[ℝ] H => D K)
    (hasFDerivAt_linearShearGram_apply C S).fderiv
  simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    add_apply] using h

private theorem linearShearGram_inner
    (C : B →L[ℝ] (H →L[ℝ] H)) (h : B) (x y : H) :
    inner ℝ (linearShearGram C h x) y =
      inner ℝ (nilpotentShearMap (C h) 1 x)
        (nilpotentShearMap (C h) 1 y) := by
  rw [linearShearGram_eq_nilpotentShearGram]
  have hadj₁ : inner ℝ ((C h).adjoint x) y = inner ℝ x (C h y) :=
    ContinuousLinearMap.adjoint_inner_left (C h) y x
  have hadj₂ : inner ℝ ((C h).adjoint (C h x)) y =
      inner ℝ (C h x) (C h y) :=
    ContinuousLinearMap.adjoint_inner_left (C h) y (C h x)
  simp only [nilpotentShearGram, nilpotentShearMap, add_apply,
    smul_apply, ContinuousLinearMap.id_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right]
  rw [hadj₁, ContinuousLinearMap.comp_apply, hadj₂]
  simp only [starRingEnd_apply, star_trivial]
  ring

private theorem orthogonalProjectionOnto_eq_zero_of_orthogonal
    (V : ClosedSubmodule ℝ H) (S : H)
    (hS : ∀ Y : V.toSubmodule, inner ℝ S (Y : H) = 0) :
    V.toSubmodule.orthogonalProjectionOnto S = 0 := by
  apply ext_inner_right ℝ
  intro Y
  rw [V.toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_right Y S]
  simp [hS Y]

private theorem linearShearGram_zero
    (C : B →L[ℝ] (H →L[ℝ] H)) : linearShearGram C 0 = ContinuousLinearMap.id ℝ H := by
  ext x
  simp [linearShearGram, responseAdjointMap]

private theorem linearShearSubspaceOperator_zero (V : ClosedSubmodule ℝ H)
    (C : B →L[ℝ] (H →L[ℝ] H)) :
    linearShearSubspaceOperator V C 0 = ContinuousLinearMap.id ℝ V.toSubmodule := by
  ext x
  dsimp [linearShearSubspaceOperator]
  rw [linearShearGram_zero]
  simpa only [ContinuousLinearMap.id_apply] using
    V.toSubmodule.starProjection_mem_subspace_eq_self x

private theorem linearShearProjection_source_zero (V : ClosedSubmodule ℝ H)
    (C : B →L[ℝ] (H →L[ℝ] H)) (S : H)
    (hS : ∀ Y : V.toSubmodule, inner ℝ S (Y : H) = 0) :
    V.toSubmodule.orthogonalProjectionOnto (linearShearGram C 0 S) = 0 := by
  rw [linearShearGram_zero]
  exact orthogonalProjectionOnto_eq_zero_of_orthogonal V S hS

private theorem linearShearCorrection_zero (V : ClosedSubmodule ℝ H)
    (C : B →L[ℝ] (H →L[ℝ] H)) (S : H)
    (hNil : ∀ x y, C x ∘L C y = 0)
    (hS : ∀ Y : V.toSubmodule, inner ℝ S (Y : H) = 0) :
    linearShearCorrection V C S 0 hNil = 0 := by
  unfold linearShearCorrection
  rw [linearShearProjection_source_zero V C S hS]
  simp

/-- At the base parameter, an orthogonal affine load has no correction, so
the minimum is its squared norm. -/
theorem linearShearMinimum_zero_eq_norm_sq (V : ClosedSubmodule ℝ H)
    (C : B →L[ℝ] (H →L[ℝ] H)) (S : H)
    (hNil : ∀ x y, C x ∘L C y = 0)
    (hS : ∀ Y : V.toSubmodule, inner ℝ S (Y : H) = 0) :
    linearShearMinimum V C S 0 hNil = ‖S‖ ^ 2 := by
  simp [linearShearMinimum, linearShearMinimizer,
    linearShearCorrection_zero V C S hNil hS, nilpotentShearMap]

private theorem linearShearSubspaceOperator_inner (V : ClosedSubmodule ℝ H)
    (C : B →L[ℝ] (H →L[ℝ] H)) (h : B) (x y : V.toSubmodule) :
    inner ℝ (linearShearSubspaceOperator V C h x) y =
      inner ℝ (linearShearGram C h (x : H)) (y : H) := by
  exact V.toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_right y
    (linearShearGram C h (x : H))

private theorem linearShearCorrection_stationarity (V : ClosedSubmodule ℝ H)
    (C : B →L[ℝ] (H →L[ℝ] H)) (S : H) (h : B)
    (hNil : ∀ x y, C x ∘L C y = 0) :
    linearShearSubspaceOperator V C h (linearShearCorrection V C S h hNil) +
      V.toSubmodule.orthogonalProjectionOnto (linearShearGram C h S) = 0 := by
  apply ext_inner_right ℝ
  intro Y
  have hVar := linearShearMinimizer_firstVariation V C S h hNil Y
  have hA := linearShearSubspaceOperator_inner V C h
    (linearShearCorrection V C S h hNil) Y
  have hd := V.toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_right Y
    (linearShearGram C h S)
  rw [inner_add_left, hA, hd]
  simp only [inner_zero_left]
  change inner ℝ (linearShearGram C h
    (S + (linearShearCorrection V C S h hNil : H))) (Y : H) = 0 at hVar
  rw [map_add, inner_add_left] at hVar
  rw [← hd, ← hA] at hVar
  linarith

private theorem linearShearCorrection_contDiffAt (V : ClosedSubmodule ℝ H)
    (C : B →L[ℝ] (H →L[ℝ] H)) (S : H) (h : B)
    (hNil : ∀ x y, C x ∘L C y = 0) :
    ContDiffAt ℝ 2 (fun x => linearShearCorrection V C S x hNil) h := by
  let F : B → (V.toSubmodule →L[ℝ] V.toSubmodule) :=
    fun x => linearShearSubspaceOperator V C x
  let d : B → V.toSubmodule :=
    fun x => V.toSubmodule.orthogonalProjectionOnto (linearShearGram C x S)
  have hF : ContDiffAt ℝ 2 F h := by
    dsimp [F, linearShearSubspaceOperator, linearShearGram]
    fun_prop
  have hd : ContDiffAt ℝ 2 d h := by
    dsimp [d, linearShearGram]
    fun_prop
  let e :=
    (nilpotentShearSubspaceEnergy_coercive V (C h) 1 (hNil h h)).continuousLinearEquivOfBilin
  have hAt : F h = e.toContinuousLinearMap := by
    dsimp [F, e]
    exact linearShearOperator_eq_laxMilgram V C h hNil
  have hInvAt : ContDiffAt ℝ 2 ContinuousLinearMap.inverse (F h) := by
    rw [hAt]
    exact _root_.contDiffAt_map_inverse (𝕜 := ℝ) e
  have hInv : ContDiffAt ℝ 2 (fun x => ContinuousLinearMap.inverse (F x)) h :=
    hInvAt.comp h hF
  have hApply : ContDiffAt ℝ 2
      (fun x => (ContinuousLinearMap.inverse (F x)) (d x)) h :=
    hInv.clm_apply hd
  have hCorr : ContDiffAt ℝ 2
      (fun x => linearShearCorrection V C S x hNil) h := by
    have hEq : (fun x => linearShearCorrection V C S x hNil) =
        fun x => -(ContinuousLinearMap.inverse (F x) (d x)) := by
      funext x
      simpa only [F, d] using linearShearCorrection_mapInverse V C S x hNil
    rw [hEq]
    exact hApply.neg
  exact hCorr

private theorem linearShearCorrection_fderiv_zero (V : ClosedSubmodule ℝ H)
    (C : B →L[ℝ] (H →L[ℝ] H)) (S : H)
    (hNil : ∀ x y, C x ∘L C y = 0)
    (hS : ∀ Y : V.toSubmodule, inner ℝ S (Y : H) = 0) (K : B) :
    fderiv ℝ (fun h => linearShearCorrection V C S h hNil) 0 K =
      -V.toSubmodule.orthogonalProjectionOnto
        (C K S + responseAdjointMap (C K) S) := by
  let F : B → (V.toSubmodule →L[ℝ] V.toSubmodule) :=
    fun x => linearShearSubspaceOperator V C x
  let d : B → V.toSubmodule :=
    fun x => V.toSubmodule.orthogonalProjectionOnto (linearShearGram C x S)
  let corr : B → V.toSubmodule := fun x => linearShearCorrection V C S x hNil
  have hF : ContDiffAt ℝ 2 F 0 := by
    dsimp [F, linearShearSubspaceOperator, linearShearGram]
    fun_prop
  have hd : ContDiffAt ℝ 2 d 0 := by
    dsimp [d, linearShearGram]
    fun_prop
  have hcorr : ContDiffAt ℝ 2 corr 0 := by
    exact linearShearCorrection_contDiffAt V C S 0 hNil
  have hFd : DifferentiableAt ℝ F 0 := hF.differentiableAt (by norm_num)
  have hdd : DifferentiableAt ℝ d 0 := hd.differentiableAt (by norm_num)
  have hcd : DifferentiableAt ℝ corr 0 := hcorr.differentiableAt (by norm_num)
  have hFzero : F 0 = ContinuousLinearMap.id ℝ V.toSubmodule := by
    exact linearShearSubspaceOperator_zero V C
  have hcorrzero : corr 0 = 0 := by
    exact linearShearCorrection_zero V C S hNil hS
  have hStationary : (fun x => F x (corr x) + d x) = fun _ => 0 := by
    funext x
    exact linearShearCorrection_stationarity V C S x hNil
  have hProd : HasFDerivAt (fun x => F x (corr x))
      (F 0 ∘SL fderiv ℝ corr 0 + (fderiv ℝ F 0).flip (corr 0)) 0 :=
    hFd.hasFDerivAt.clm_apply hcd.hasFDerivAt
  have hSum : HasFDerivAt (fun x => F x (corr x) + d x)
      (F 0 ∘SL fderiv ℝ corr 0 + (fderiv ℝ F 0).flip (corr 0) +
        fderiv ℝ d 0) 0 := by
    exact hProd.add hdd.hasFDerivAt
  have hZeroDeriv := hSum.fderiv
  rw [hStationary] at hZeroDeriv
  simp at hZeroDeriv
  have hD : (fderiv ℝ d 0) K =
      V.toSubmodule.orthogonalProjectionOnto
        (C K S + responseAdjointMap (C K) S) := by
    have hg : DifferentiableAt ℝ (fun x => linearShearGram C x S) 0 :=
      (hasFDerivAt_linearShearGram_apply C S).differentiableAt
    have hDcomp : fderiv ℝ d 0 =
        V.toSubmodule.orthogonalProjectionOnto ∘SL
          fderiv ℝ (fun x => linearShearGram C x S) 0 := by
      simpa [d, Function.comp_def] using
        fderiv_comp (𝕜 := ℝ) (x := 0)
          V.toSubmodule.orthogonalProjectionOnto.hasFDerivAt.differentiableAt hg
    rw [hDcomp]
    change V.toSubmodule.orthogonalProjectionOnto
      (fderiv ℝ (fun x => linearShearGram C x S) 0 K) = _
    rw [fderiv_linearShearGram_apply_zero]
  have hAtK := congrArg (fun L : B →L[ℝ] V.toSubmodule => L K) hZeroDeriv
  rw [hFzero, hcorrzero] at hAtK
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    map_zero, add_zero, add_apply] at hAtK
  rw [hD] at hAtK
  exact eq_neg_of_add_eq_zero_left hAtK.symm

private theorem linearShearMinimizer_fderiv_zero (V : ClosedSubmodule ℝ H)
    (C : B →L[ℝ] (H →L[ℝ] H)) (S : H)
    (hNil : ∀ x y, C x ∘L C y = 0)
    (hS : ∀ Y : V.toSubmodule, inner ℝ S (Y : H) = 0) (K : B) :
    fderiv ℝ (fun h => linearShearMinimizer V C S h hNil) 0 K =
      -(V.toSubmodule.subtypeL
        (V.toSubmodule.orthogonalProjectionOnto
          (C K S + responseAdjointMap (C K) S))) := by
  let corr : B → V.toSubmodule := fun h => linearShearCorrection V C S h hNil
  let Z : B → H := fun h => linearShearMinimizer V C S h hNil
  have hCorr : ContDiffAt ℝ 2 corr 0 :=
    linearShearCorrection_contDiffAt V C S 0 hNil
  have hCorrDiff : DifferentiableAt ℝ corr 0 := hCorr.differentiableAt (by norm_num)
  have hIncl : HasFDerivAt (fun h => (corr h : H))
      (V.toSubmodule.subtypeL ∘SL fderiv ℝ corr 0) 0 := by
    convert V.toSubmodule.subtypeL.hasFDerivAt.comp 0
      hCorrDiff.hasFDerivAt using 1
    · ext h
      rfl
  have hZHas : HasFDerivAt Z
      (V.toSubmodule.subtypeL ∘SL fderiv ℝ corr 0) 0 := by
    have hc := (hasFDerivAt_const (𝕜 := ℝ) (E := B) (F := H) S (0 : B)).add hIncl
    convert hc using 1
    · ext h
      rfl
    · simp
  have hCorrD : fderiv ℝ corr 0 K =
      -V.toSubmodule.orthogonalProjectionOnto
        (C K S + responseAdjointMap (C K) S) := by
    simpa [corr] using linearShearCorrection_fderiv_zero V C S hNil hS K
  have hderiv := congrArg (fun D : B →L[ℝ] H => D K) hZHas.fderiv
  simp only [ContinuousLinearMap.comp_apply] at hderiv
  rw [hCorrD] at hderiv
  simpa [Z] using hderiv

/-- The first Fréchet derivative of the affine minimum at its base point. -/
theorem linearShearMinimum_fderiv_zero (V : ClosedSubmodule ℝ H)
    (C : B →L[ℝ] (H →L[ℝ] H)) (S : H)
    (hNil : ∀ x y, C x ∘L C y = 0)
    (hS : ∀ Y : V.toSubmodule, inner ℝ S (Y : H) = 0) (K : B) :
    fderiv ℝ (fun h => linearShearMinimum V C S h hNil) 0 K =
      2 * inner ℝ S (C K S) := by
  let A : B → (H →L[ℝ] H) := (fun _ : B => ContinuousLinearMap.id ℝ H) + C
  let Z : B → H := fun h => linearShearMinimizer V C S h hNil
  let W : B → H := fun h => nilpotentShearMap (C h) 1 (Z h)
  have hA : HasFDerivAt A C 0 := by
    have hc := (hasFDerivAt_const (𝕜 := ℝ) (E := B)
      (F := H →L[ℝ] H) (ContinuousLinearMap.id ℝ H) (0 : B)).add C.hasFDerivAt
    simpa only [zero_add] using hc
  have hCorr : ContDiffAt ℝ 2
      (fun h => linearShearCorrection V C S h hNil) 0 :=
    linearShearCorrection_contDiffAt V C S 0 hNil
  have hCorrDiff : DifferentiableAt ℝ
      (fun h => linearShearCorrection V C S h hNil) 0 :=
    hCorr.differentiableAt (by norm_num)
  have hIncl : HasFDerivAt
      (fun h => (linearShearCorrection V C S h hNil : H))
      (V.toSubmodule.subtypeL ∘SL
        fderiv ℝ (fun h => linearShearCorrection V C S h hNil) 0) 0 := by
    convert V.toSubmodule.subtypeL.hasFDerivAt.comp 0 hCorrDiff.hasFDerivAt using 1
    · ext h
      rfl
  have hZ : HasFDerivAt Z
      (V.toSubmodule.subtypeL ∘SL
        fderiv ℝ (fun h => linearShearCorrection V C S h hNil) 0) 0 := by
    have hc := (hasFDerivAt_const (𝕜 := ℝ) (E := B) (F := H) S (0 : B)).add hIncl
    convert hc using 1
    · ext h
      rfl
    · simp
  have hW : HasFDerivAt W
      (A 0 ∘SL (V.toSubmodule.subtypeL ∘SL
        fderiv ℝ (fun h => linearShearCorrection V C S h hNil) 0) +
        C.flip (Z 0)) 0 := by
    have hc := hA.clm_apply hZ
    convert hc using 1
    · ext h
      simp [W, A, nilpotentShearMap, one_smul]
  have hmin : (fun h => linearShearMinimum V C S h hNil) =
      fun h => ‖W h‖ ^ 2 := by
    funext h
    simp [linearShearMinimum, W, Z]
  have hmin' := hW.norm_sq.congr_fderiv rfl
  have hminFderiv := hmin'.fderiv
  rw [← hmin] at hminFderiv
  have hEval := congrArg (fun D : B →L[ℝ] ℝ => D K) hminFderiv
  have hZ0 : Z 0 = S := by
    simp [Z, linearShearMinimizer, linearShearCorrection_zero V C S hNil hS]
  rw [hZ0] at hEval
  have hA0 : A 0 = ContinuousLinearMap.id ℝ H := by simp [A]
  have hW0 : W 0 = S := by simp [W, Z, nilpotentShearMap, hZ0]
  rw [hA0, hW0] at hEval
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.flip_apply, innerSL_apply_apply, smul_apply, add_apply] at hEval
  rw [linearShearCorrection_fderiv_zero V C S hNil hS K] at hEval
  have hProj := hS (V.toSubmodule.orthogonalProjectionOnto
    (C K S + responseAdjointMap (C K) S))
  have hCorrInner : inner ℝ S
      (V.toSubmodule.subtypeL
        (-V.toSubmodule.orthogonalProjectionOnto
          (C K S + responseAdjointMap (C K) S))) = 0 := by
    change inner ℝ S
      (-(V.toSubmodule.orthogonalProjectionOnto
        (C K S + responseAdjointMap (C K) S) : H)) = 0
    rw [inner_neg_right, hProj]
    simp
  rw [inner_add_right, hCorrInner, zero_add] at hEval
  simpa [two_smul, two_mul] using hEval

/-- The envelope derivative of a linear nilpotent-shear minimum at every
coefficient point. -/
theorem linearShearMinimum_fderiv (V : ClosedSubmodule ℝ H)
    (C : B →L[ℝ] (H →L[ℝ] H)) (S : H) (h : B)
    (hNil : ∀ x y, C x ∘L C y = 0) (K : B) :
    fderiv ℝ (fun x => linearShearMinimum V C S x hNil) h K =
      2 * inner ℝ (nilpotentShearMap (C h) 1
        (linearShearMinimizer V C S h hNil))
        (C K (linearShearMinimizer V C S h hNil)) := by
  let A : B → (H →L[ℝ] H) := (fun _ : B => ContinuousLinearMap.id ℝ H) + C
  let Z : B → H := fun x => linearShearMinimizer V C S x hNil
  let W : B → H := fun x => nilpotentShearMap (C x) 1 (Z x)
  let corr : B → V.toSubmodule := fun x => linearShearCorrection V C S x hNil
  have hA : HasFDerivAt A C h := by
    have hc := (hasFDerivAt_const (𝕜 := ℝ) (E := B)
      (F := H →L[ℝ] H) (ContinuousLinearMap.id ℝ H) h).add C.hasFDerivAt
    simpa only [zero_add] using hc
  have hCorr : ContDiffAt ℝ 2 corr h :=
    linearShearCorrection_contDiffAt V C S h hNil
  have hCorrDiff : DifferentiableAt ℝ corr h := hCorr.differentiableAt (by norm_num)
  have hIncl : HasFDerivAt (fun x => (corr x : H))
      (V.toSubmodule.subtypeL ∘SL fderiv ℝ corr h) h := by
    convert V.toSubmodule.subtypeL.hasFDerivAt.comp h hCorrDiff.hasFDerivAt using 1
    ext x
    rfl
  have hZ : HasFDerivAt Z
      (V.toSubmodule.subtypeL ∘SL fderiv ℝ corr h) h := by
    have hc := (hasFDerivAt_const (𝕜 := ℝ) (E := B) (F := H) S h).add hIncl
    convert hc using 1
    · ext x
      rfl
    · simp
  have hW : HasFDerivAt W
      (A h ∘SL (V.toSubmodule.subtypeL ∘SL fderiv ℝ corr h) +
        C.flip (Z h)) h := by
    have hc := hA.clm_apply hZ
    convert hc using 1
    ext x
    simp [W, A, Z, nilpotentShearMap, one_smul]
  have hmin : (fun x => linearShearMinimum V C S x hNil) = fun x => ‖W x‖ ^ 2 := by
    funext x
    simp [linearShearMinimum, W, Z]
  have hMinFDeriv := (hW.norm_sq).fderiv
  rw [← hmin] at hMinFDeriv
  have hEval := congrArg (fun D : B →L[ℝ] ℝ => D K) hMinFDeriv
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    innerSL_apply_apply, smul_apply, add_apply] at hEval
  have hCancel : inner ℝ (W h)
      (A h (V.toSubmodule.subtypeL (fderiv ℝ corr h K)) + C K (Z h)) =
        inner ℝ (W h) (C K (Z h)) := by
    have hVar := linearShearMinimizer_firstVariation V C S h hNil
      (fderiv ℝ corr h K)
    rw [linearShearGram_inner] at hVar
    have hVar' : inner ℝ (W h)
        (A h (V.toSubmodule.subtypeL (fderiv ℝ corr h K))) = 0 := by
      simpa [W, Z, A, nilpotentShearMap, one_smul] using hVar
    rw [inner_add_right, hVar', zero_add]
  rw [hCancel] at hEval
  simpa [two_smul, two_mul, W, Z] using hEval

/-- The bilinear Hessian of the affine minimum at the base coefficient. -/
theorem linearShearMinimum_second_fderiv_zero (V : ClosedSubmodule ℝ H)
    (C : B →L[ℝ] (H →L[ℝ] H)) (S : H)
    (hNil : ∀ x y, C x ∘L C y = 0)
    (hS : ∀ Y : V.toSubmodule, inner ℝ S (Y : H) = 0)
    (Hdir K : B) :
    fderiv ℝ (fun x => fderiv ℝ
      (fun y => linearShearMinimum V C S y hNil) x K) 0 Hdir =
      2 * inner ℝ (C Hdir S) (C K S) -
        2 * inner ℝ
          (V.toSubmodule.orthogonalProjectionOnto
            (C Hdir S + responseAdjointMap (C Hdir) S) : H)
          (V.toSubmodule.orthogonalProjectionOnto
            (C K S + responseAdjointMap (C K) S) : H) := by
  let A : B → (H →L[ℝ] H) := (fun _ : B => ContinuousLinearMap.id ℝ H) + C
  let Z : B → H := fun x => linearShearMinimizer V C S x hNil
  let W : B → H := fun x => nilpotentShearMap (C x) 1 (Z x)
  let Q : B → H := fun x => C K (Z x)
  let corr : B → V.toSubmodule := fun x => linearShearCorrection V C S x hNil
  have hEnv : (fun x => fderiv ℝ
      (fun y => linearShearMinimum V C S y hNil) x K) =
      fun x => 2 * inner ℝ (W x) (Q x) := by
    funext x
    simpa [W, Q, Z] using linearShearMinimum_fderiv V C S x hNil K
  have hCorr : ContDiffAt ℝ 2 corr 0 :=
    linearShearCorrection_contDiffAt V C S 0 hNil
  have hCorrDiff : DifferentiableAt ℝ corr 0 := hCorr.differentiableAt (by norm_num)
  have hIncl : HasFDerivAt (fun x => (corr x : H))
      (V.toSubmodule.subtypeL ∘SL fderiv ℝ corr 0) 0 := by
    convert V.toSubmodule.subtypeL.hasFDerivAt.comp 0 hCorrDiff.hasFDerivAt using 1
    ext x
    rfl
  have hZ : HasFDerivAt Z
      (V.toSubmodule.subtypeL ∘SL fderiv ℝ corr 0) 0 := by
    have hc := (hasFDerivAt_const (𝕜 := ℝ) (E := B) (F := H) S 0).add hIncl
    convert hc using 1
    · ext x
      rfl
    · simp
  have hZdiff : DifferentiableAt ℝ Z 0 := hZ.differentiableAt
  have hZ0 : Z 0 = S := by
    simp [Z, linearShearMinimizer, linearShearCorrection_zero V C S hNil hS]
  have hA : HasFDerivAt A C 0 := by
    have hc := (hasFDerivAt_const (𝕜 := ℝ) (E := B)
      (F := H →L[ℝ] H) (ContinuousLinearMap.id ℝ H) 0).add C.hasFDerivAt
    simpa only [zero_add] using hc
  have hW : HasFDerivAt W
      (A 0 ∘SL fderiv ℝ Z 0 + C.flip (Z 0)) 0 := by
    have hc := hA.clm_apply hZdiff.hasFDerivAt
    convert hc using 1
    ext x
    simp [W, A, Z, nilpotentShearMap, one_smul]
  have hQ : HasFDerivAt Q ((C K) ∘SL fderiv ℝ Z 0) 0 := by
    have hc := (C K).hasFDerivAt.comp 0 hZdiff.hasFDerivAt
    convert hc using 1
    ext x
    rfl
  have hInner := hW.inner ℝ hQ
  rw [hEnv]
  rw [fderiv_const_mul hInner.differentiableAt 2]
  simp only [smul_apply]
  rw [fderiv_inner_apply ℝ hW.differentiableAt hQ.differentiableAt Hdir]
  let hP := V.toSubmodule.orthogonalProjectionOnto
    (C Hdir S + responseAdjointMap (C Hdir) S)
  have hZdir' : fderiv ℝ Z 0 Hdir = -(V.toSubmodule.subtypeL hP) := by
    simpa only [Z, hP, Submodule.subtypeL_apply] using
      linearShearMinimizer_fderiv_zero V C S hNil hS Hdir
  have hA0 : A 0 = ContinuousLinearMap.id ℝ H := by simp [A]
  have hWdir := congrArg (fun D : B →L[ℝ] H => D Hdir) hW.fderiv
  change fderiv ℝ W 0 Hdir =
    ((A 0 ∘SL fderiv ℝ Z 0) Hdir + (C.flip (Z 0)) Hdir) at hWdir
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply] at hWdir
  rw [hA0, hZ0, hZdir'] at hWdir
  simp only [ContinuousLinearMap.id_apply] at hWdir
  have hQdir := congrArg (fun D : B →L[ℝ] H => D Hdir) hQ.fderiv
  simp only [ContinuousLinearMap.comp_apply] at hQdir
  rw [hZdir'] at hQdir
  have hQ0 : Q 0 = C K S := by simp [Q, Z, hZ0]
  have hW0 : W 0 = S := by simp [W, Z, nilpotentShearMap, hZ0]
  rw [hWdir, hQdir, hW0, hQ0]
  let pH := (V.toSubmodule.orthogonalProjectionOnto
    (C Hdir S + responseAdjointMap (C Hdir) S) : H)
  let pK := (V.toSubmodule.orthogonalProjectionOnto
    (C K S + responseAdjointMap (C K) S) : H)
  have hAdj : inner ℝ S (C K (V.toSubmodule.subtypeL hP)) =
      inner ℝ (responseAdjointMap (C K) S) (V.toSubmodule.subtypeL hP) := by
    exact (ContinuousLinearMap.adjoint_inner_left (C K)
      (V.toSubmodule.subtypeL hP) S).symm
  have hProjection : inner ℝ
      (C K S + responseAdjointMap (C K) S) (V.toSubmodule.subtypeL hP) =
      inner ℝ (V.toSubmodule.subtypeL hP) pK := by
    calc
      _ = inner ℝ pK (V.toSubmodule.subtypeL hP) := by
        symm
        exact V.toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_right hP
          (C K S + responseAdjointMap (C K) S)
      _ = inner ℝ (V.toSubmodule.subtypeL hP) pK := real_inner_comm _ _
  have hCorrection : inner ℝ S (C K (-(V.toSubmodule.subtypeL hP))) +
      inner ℝ (-(V.toSubmodule.subtypeL hP)) (C K S) =
      - inner ℝ (V.toSubmodule.subtypeL hP) pK := by
    rw [map_neg, inner_neg_right, inner_neg_left]
    rw [hAdj]
    have hswap := real_inner_comm (V.toSubmodule.subtypeL hP) (C K S)
    rw [← hswap]
    have hsum : inner ℝ (C K S + responseAdjointMap (C K) S)
        (V.toSubmodule.subtypeL hP) =
        inner ℝ (C K S) (V.toSubmodule.subtypeL hP) +
        inner ℝ (responseAdjointMap (C K) S) (V.toSubmodule.subtypeL hP) :=
      inner_add_left _ _ _
    calc
      _ = -(inner ℝ (C K S) (V.toSubmodule.subtypeL hP) +
          inner ℝ (responseAdjointMap (C K) S) (V.toSubmodule.subtypeL hP)) := by ring
      _ = - inner ℝ (C K S + responseAdjointMap (C K) S)
          (V.toSubmodule.subtypeL hP) := by rw [hsum]
      _ = - inner ℝ (V.toSubmodule.subtypeL hP) pK := by rw [hProjection]
  rw [inner_add_left]
  change (2 : ℝ) * (inner ℝ S (C K (-(V.toSubmodule.subtypeL hP))) +
    (inner ℝ (-(V.toSubmodule.subtypeL hP)) (C K S) +
      inner ℝ (C Hdir S) (C K S))) = _
  rw [← add_assoc, hCorrection]
  change (2 : ℝ) * (-inner ℝ pH pK + inner ℝ (C Hdir S) (C K S)) =
    (2 : ℝ) * inner ℝ (C Hdir S) (C K S) - 2 * inner ℝ pH pK
  ring

/-- The mixed-family Hessian admits the usual trial-field upper bound. -/
theorem linearShearMinimum_trial_bound_zero (V : ClosedSubmodule ℝ H)
    (C : B →L[ℝ] (H →L[ℝ] H)) (S : H)
    (hNil : ∀ x y, C x ∘L C y = 0)
    (hS : ∀ Y : V.toSubmodule, inner ℝ S (Y : H) = 0)
    (Hdir : B) (Y : V.toSubmodule) :
    (1 / 2 : ℝ) * fderiv ℝ (fun x => fderiv ℝ
      (fun y => linearShearMinimum V C S y hNil) x Hdir) 0 Hdir ≤
      ‖C Hdir S + (Y : H)‖ ^ 2 + 2 * inner ℝ S (C Hdir (Y : H)) := by
  let p := V.toSubmodule.orthogonalProjectionOnto
    (C Hdir S + responseAdjointMap (C Hdir) S)
  have hHess := linearShearMinimum_second_fderiv_zero V C S hNil hS Hdir Hdir
  have hAdj : inner ℝ S (C Hdir (Y : H)) =
      inner ℝ (responseAdjointMap (C Hdir) S) (Y : H) := by
    exact (ContinuousLinearMap.adjoint_inner_left (C Hdir) (Y : H) S).symm
  have hProj : inner ℝ (C Hdir S + responseAdjointMap (C Hdir) S) (Y : H) =
      inner ℝ (p : H) (Y : H) := by
    symm
    exact V.toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_right Y
      (C Hdir S + responseAdjointMap (C Hdir) S)
  have hEnergy : ‖C Hdir S + (Y : H)‖ ^ 2 =
      ‖C Hdir S‖ ^ 2 + 2 * inner ℝ (C Hdir S) (Y : H) + ‖(Y : H)‖ ^ 2 := by
    exact norm_add_sq_real _ _
  have hEnergyP : ‖(Y : H) + (p : H)‖ ^ 2 =
      ‖(Y : H)‖ ^ 2 + 2 * inner ℝ (p : H) (Y : H) + ‖(p : H)‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_comm (Y : H) (p : H)]
  have hComplete : 0 ≤ ‖(Y : H)‖ ^ 2 +
      2 * inner ℝ (p : H) (Y : H) + ‖(p : H)‖ ^ 2 := by
    nlinarith [sq_nonneg (‖(Y : H) + (p : H)‖)]
  have hCompleteQ : 0 ≤ ‖(Y : H)‖ ^ 2 +
      2 * inner ℝ (C Hdir S + responseAdjointMap (C Hdir) S) (Y : H) +
        ‖(p : H)‖ ^ 2 := by
    rw [hProj]
    exact hComplete
  have hQinner : inner ℝ (C Hdir S + responseAdjointMap (C Hdir) S) (Y : H) =
      inner ℝ (C Hdir S) (Y : H) +
        inner ℝ (responseAdjointMap (C Hdir) S) (Y : H) := inner_add_left _ _ _
  have hCross : 2 * inner ℝ (C Hdir S) (Y : H) +
      2 * inner ℝ S (C Hdir (Y : H)) =
      2 * inner ℝ (C Hdir S + responseAdjointMap (C Hdir) S) (Y : H) := by
    rw [hAdj]
    calc
      _ = 2 * (inner ℝ (C Hdir S) (Y : H) +
          inner ℝ (responseAdjointMap (C Hdir) S) (Y : H)) := by ring
      _ = _ := by rw [← hQinner]
  have hHessNorm : fderiv ℝ (fun x => fderiv ℝ
      (fun y => linearShearMinimum V C S y hNil) x Hdir) 0 Hdir =
      2 * ‖C Hdir S‖ ^ 2 - 2 * ‖(p : H)‖ ^ 2 := by
    rw [hHess]
    simp only [p, real_inner_self_eq_norm_sq]
  rw [hHessNorm]
  rw [hEnergy]
  nlinarith [hCompleteQ, hCross]

end

end ASDExplicitGamma.Response
