module

public import ASDExplicitGamma.Scalar.RefRough4
public import ASDExplicitGamma.Scalar.T4v2Final

/-! The forced part of the defect, componentwise: `forced_j = (Y_j, X_j − w̃_j)` with `(Y_j, X_j)`
the pair solution of the potential source `w̃_j = σ⁻¹ F(H_j) = −V_j^* e`. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Native
open Algsuperdiff.Section3
open scoped BigOperators InnerProductSpace

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

theorem rep_neg {U : Set (Vec 2)} [IsFiniteMeasure (volumeMeasureOn U)]
    (u : HilbertVectorL2 U) :
    rep' (-u) =ᵐ[volumeMeasureOn U] fun x i => -rep' u x i := by
  have hf := rep_memL2 u
  have hneg : MemVectorL2 U (fun x i => -rep' u x i) := hf.neg
  apply ae_of_toHilbert_eq (rep_memL2 (-u)) hneg
  rw [hilbert_rebuild]
  have h1 := toHilbertVectorL2OfVecField_sub (memVectorL2_const (U := U) (0 : Vec 2)) hf
  rw [toHilbert_zero, hilbert_rebuild, zero_sub] at h1
  rw [← h1]
  exact ofField_eq' _ _ (by funext x i; simp)

namespace Cfg''

variable (C : Cfg'')

/-- The forced potential source `w̃_j = σ⁻¹ F(H_j)`. -/
def wt (j : ℕ) : C.Xs := C.σ⁻¹ • C.Fl (C.Hs j)

theorem forcedR_fst (hQo : openCubeSet C.Q ⊆ openRectangle C.a C.b C.c C.d)
    (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (j : ℕ) :
    (C.forcedR old j).ofLp.1 =
      twoSlotY C.Q C.hν C.hσ (C.Rest old) 0 (C.wt j) := by
  rw [C.forcedR_eq hQo old j]
  change ((C.Bop old (inr'' (Y := C.Ys) (C.wt j))) - inr'' (Y := C.Ys) (C.wt j)).ofLp.1 = _
  have h0 : (inr'' (Y := C.Ys) (C.wt j)).ofLp.1 = 0 := rfl
  rw [WithLp.ofLp_sub, Prod.fst_sub, h0, sub_zero]
  rfl

theorem forcedR_snd (hQo : openCubeSet C.Q ⊆ openRectangle C.a C.b C.c C.d)
    (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (j : ℕ) :
    (C.forcedR old j).ofLp.2 =
      twoSlotX C.Q C.hν C.hσ (C.Rest old) 0 (C.wt j) - C.wt j := by
  rw [C.forcedR_eq hQo old j]
  change ((C.Bop old (inr'' (Y := C.Ys) (C.wt j))) - inr'' (Y := C.Ys) (C.wt j)).ofLp.2 = _
  have h0 : (inr'' (Y := C.Ys) (C.wt j)).ofLp.2 = C.wt j := rfl
  rw [WithLp.ofLp_sub, Prod.snd_sub, h0]
  rfl

theorem wt_eq (hQo : openCubeSet C.Q ⊆ openRectangle C.a C.b C.c C.d) (j : ℕ) :
    C.wt j = -(ContinuousLinearMap.adjoint (C.Vm (C.Hs j))) (physicalConstantLoad C.Q C.e) := by
  have h := C.flat_carrier_identity hQo (C.Hs j)
  have h2 := congrArg (fun w => C.σ⁻¹ • w) h
  simp only [smul_smul, inv_mul_cancel₀ C.hσ.ne', one_smul, smul_neg] at h2
  unfold wt
  rw [h2, neg_neg]

end Cfg''

end

end ASDExplicitGamma.Scalar
