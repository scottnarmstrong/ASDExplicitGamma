module

public import ASDExplicitGamma.Scalar.T4v2Alg
public import ASDExplicitGamma.Scalar.FwIdentMain

/-! T4 v2: the components of the corrected forced part of a mode with matching potential. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian MeasureTheory
open scoped InnerProductSpace

noncomputable section

theorem t4v2_alg {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (B : F →L[ℝ] F) (I : E →L[ℝ] F) (c : ℝ) (X : E) :
    B (I (c • -X)) - I (c • -X) = (-c) • (B (I X) - I X) := by
  simp only [smul_neg, map_neg, map_smul, neg_smul, smul_sub, neg_sub_neg]

namespace Cfg''

variable (C : Cfg'')

theorem Bop_eq_of_rest (old : C(closedRectangle C.a C.b C.c C.d, ℝ))
    (k : ResponseCoefficient (openCubeSet C.Q)) (hk : C.Rest old = k) :
    C.Bop old = pureFluxBlockInverse (C.ν / C.σ) (div_pos C.hν C.hσ)
      (physicalProjectedCoefficient C.Q C.σ C.hσ k) := by
  have h : C.Aold old = physicalProjectedCoefficient C.Q C.σ C.hσ k := by
    unfold Aold; rw [hk]
  unfold Bop
  rw [h]
  rfl

theorem forcedR_comp (hQ : openCubeSet C.Q ⊆ openRectangle C.a C.b C.c C.d)
    (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (j : ℕ)
    (k : ResponseCoefficient (openCubeSet C.Q)) (hk : C.Rest old = k)
    (u : H10Function (openCubeSet C.Q))
    (hF : C.Fl (C.Hs j) = -(fwLoad C.Q u)) :
    C.forcedR old j = (-C.σ⁻¹) • (fwPairSolution C.Q C.ν C.σ C.hν C.hσ k u -
      inr'' (Y := C.Ys) (X := C.Xs) (fwLoad C.Q u)) := by
  rw [C.forcedR_eq hQ, hF, C.Bop_eq_of_rest old k hk]
  exact t4v2_alg _ (inr'' (Y := C.Ys) (X := C.Xs)) C.σ⁻¹ (fwLoad C.Q u)

end Cfg''

end

end ASDExplicitGamma.Scalar
