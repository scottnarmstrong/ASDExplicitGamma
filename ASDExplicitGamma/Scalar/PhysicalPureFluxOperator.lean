module

public import ASDExplicitGamma.Scalar.ResolventHilbert
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The first-order pure-flux block operator used to identify the physical
constrained response with an OLD/New resolvent pair. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open scoped InnerProduct InnerProductSpace

noncomputable section

variable {Y X : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- The L² product carrier `Y ⊕ X`, represented by `WithLp 2`. -/
abbrev pureFluxPair := WithLp 2 (Y × X)

/-- The source first-order operator
`((α I, A), (-A*, α I))` on `Y ⊕ X`. -/
noncomputable def pureFluxBlockOperator (α : ℝ) (A : X →L[ℝ] Y) :
    pureFluxPair (Y := Y) (X := X) →L[ℝ]
      pureFluxPair (Y := Y) (X := X) := by
  let E := WithLp.prodContinuousLinearEquiv 2 ℝ Y X
  let fst : Y × X →L[ℝ] Y := ContinuousLinearMap.fst ℝ Y X
  let snd : Y × X →L[ℝ] X := ContinuousLinearMap.snd ℝ Y X
  let T : Y × X →L[ℝ] Y × X :=
    (α • fst + A.comp snd).prod (-(A.adjoint.comp fst) + α • snd)
  exact E.symm.toContinuousLinearMap.comp
    (T.comp E.toContinuousLinearMap)

/-- The parity involution is `diag(I,-I)`. -/
noncomputable def pureFluxParity :
    pureFluxPair (Y := Y) (X := X) →L[ℝ]
      pureFluxPair (Y := Y) (X := X) := by
  let E := WithLp.prodContinuousLinearEquiv 2 ℝ Y X
  let fst : Y × X →L[ℝ] Y := ContinuousLinearMap.fst ℝ Y X
  let snd : Y × X →L[ℝ] X := ContinuousLinearMap.snd ℝ Y X
  let T : Y × X →L[ℝ] Y × X := fst.prod (-snd)
  exact E.symm.toContinuousLinearMap.comp
    (T.comp E.toContinuousLinearMap)

@[simp] theorem pureFluxBlockOperator_apply (α : ℝ) (A : X →L[ℝ] Y)
    (z : pureFluxPair (Y := Y) (X := X)) :
    (pureFluxBlockOperator α A z).ofLp =
      (α • z.ofLp.1 + A z.ofLp.2,
        -(A.adjoint z.ofLp.1) + α • z.ofLp.2) := by
  simp [pureFluxBlockOperator, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.comp_apply]

omit [CompleteSpace Y] [CompleteSpace X] in
@[simp] theorem pureFluxParity_apply
    (z : pureFluxPair (Y := Y) (X := X)) :
    (pureFluxParity (Y := Y) (X := X) z).ofLp = (z.ofLp.1, -z.ofLp.2) := by
  simp [pureFluxParity, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.comp_apply]

/-- Adding a projected coefficient insertion adds precisely its skew block. -/
theorem pureFluxBlockOperator_add (α : ℝ) (A V : X →L[ℝ] Y) :
    pureFluxBlockOperator α A + pureFluxBlockOperator 0 V =
      pureFluxBlockOperator α (A + V) := by
  ext z
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ Y X).injective
  change (pureFluxBlockOperator α A z).ofLp +
      (pureFluxBlockOperator 0 V z).ofLp =
    (pureFluxBlockOperator α (A + V) z).ofLp
  rw [pureFluxBlockOperator_apply, pureFluxBlockOperator_apply,
    pureFluxBlockOperator_apply]
  ext <;> simp [add_apply, map_add] <;> abel

/-- The source block bilinear form is coercive with the molecular diagonal. -/
noncomputable def pureFluxBlockBilinear (α : ℝ) (A : X →L[ℝ] Y) :
    pureFluxPair (Y := Y) (X := X) →L[ℝ]
      pureFluxPair (Y := Y) (X := X) →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ
    (pureFluxPair (Y := Y) (X := X))
    (pureFluxPair (Y := Y) (X := X))
    (pureFluxPair (Y := Y) (X := X) →L[ℝ] ℝ))
      (innerSL ℝ)
      (pureFluxBlockOperator α A)

@[simp] theorem pureFluxBlockBilinear_apply (α : ℝ) (A : X →L[ℝ] Y)
    (z w : pureFluxPair (Y := Y) (X := X)) :
    pureFluxBlockBilinear α A z w =
      ⟪pureFluxBlockOperator α A z, w⟫_ℝ := by
  rfl

theorem pureFluxBlockBilinear_coercive {α : ℝ} (hα : 0 < α)
    (A : X →L[ℝ] Y) :
    IsCoercive (pureFluxBlockBilinear α A) := by
  refine ⟨α, hα, ?_⟩
  intro z
  rw [pureFluxBlockBilinear_apply, WithLp.prod_inner_apply,
    pureFluxBlockOperator_apply]
  let zy : Y := z.fst
  let zx : X := z.snd
  have hadj := ContinuousLinearMap.adjoint_inner_left A zx zy
  have hcross : ⟪A zx, zy⟫_ℝ = ⟪A.adjoint zy, zx⟫_ℝ := by
    calc
      ⟪A zx, zy⟫_ℝ = ⟪zy, A zx⟫_ℝ := real_inner_comm _ _
      _ = ⟪A.adjoint zy, zx⟫_ℝ := hadj.symm
  have hnorm : ‖z‖ ^ 2 = ‖zy‖ ^ 2 + ‖zx‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
  simp only [WithLp.ofLp_fst, WithLp.ofLp_snd]
  simp only [inner_add_left, inner_smul_left, inner_neg_left,
    starRingEnd_apply, star_trivial]
  rw [hcross]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  nlinarith [hnorm]

private theorem pureFluxBlockOperator_eq_laxMilgram (α : ℝ) (hα : 0 < α)
    (A : X →L[ℝ] Y) :
    ((pureFluxBlockBilinear_coercive hα A).continuousLinearEquivOfBilin).toContinuousLinearMap =
      pureFluxBlockOperator α A := by
  apply ContinuousLinearMap.ext
  intro z
  apply ext_inner_left ℝ
  intro w
  let E := (pureFluxBlockBilinear_coercive hα A).continuousLinearEquivOfBilin
  calc
    ⟪w, E z⟫_ℝ = ⟪E z, w⟫_ℝ := real_inner_comm _ _
    _ = pureFluxBlockBilinear α A z w :=
      (pureFluxBlockBilinear_coercive hα A).continuousLinearEquivOfBilin_apply z w
    _ = ⟪pureFluxBlockOperator α A z, w⟫_ℝ := pureFluxBlockBilinear_apply α A z w
    _ = ⟪w, pureFluxBlockOperator α A z⟫_ℝ := real_inner_comm _ _

/-- Lax--Milgram produces the actual bounded inverse of every source block
operator with positive molecular diagonal. -/
noncomputable def pureFluxBlockInverse (α : ℝ) (hα : 0 < α)
    (A : X →L[ℝ] Y) :
    pureFluxPair (Y := Y) (X := X) →L[ℝ]
      pureFluxPair (Y := Y) (X := X) := by
  exact ((pureFluxBlockBilinear_coercive hα A).continuousLinearEquivOfBilin).symm.toContinuousLinearMap

theorem pureFluxBlockInverse_left (α : ℝ) (hα : 0 < α)
    (A : X →L[ℝ] Y) :
    pureFluxBlockOperator α A * pureFluxBlockInverse α hα A = 1 := by
  let E := (pureFluxBlockBilinear_coercive hα A).continuousLinearEquivOfBilin
  have hE := pureFluxBlockOperator_eq_laxMilgram α hα A
  change pureFluxBlockOperator α A * E.symm.toContinuousLinearMap = 1
  rw [← hE]
  ext z
  exact E.apply_symm_apply z

theorem pureFluxBlockInverse_right (α : ℝ) (hα : 0 < α)
    (A : X →L[ℝ] Y) :
    pureFluxBlockInverse α hα A * pureFluxBlockOperator α A = 1 := by
  let E := (pureFluxBlockBilinear_coercive hα A).continuousLinearEquivOfBilin
  have hE := pureFluxBlockOperator_eq_laxMilgram α hα A
  change E.symm.toContinuousLinearMap * pureFluxBlockOperator α A = 1
  rw [← hE]
  ext z
  exact E.symm_apply_apply z

end

end ASDExplicitGamma.Scalar
