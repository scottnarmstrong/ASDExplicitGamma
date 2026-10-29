module

public import ASDExplicitGamma.Scalar.RefSplit
public import ASDExplicitGamma.Scalar.RefCheckDelta

/-! T4 v2, algebra: the corrected forced part is `B_old (0, w̃) - (0, w̃)` with `w̃ = σ⁻¹ F(H_j)`. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace Cfg''

variable (C : Cfg'')

theorem forcedR_apply (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (j : ℕ) :
    C.forcedR old j = C.Bop old (pureFluxBlockOperator 0 (C.Vm (C.Hs j)) C.load) -
      C.σ • inr'' (Y := C.Ys) (X := C.Xs) (C.FlR (C.Hs j)) :=
  delta_apply' C.Vm C.FlR (C.Bop old) C.load C.σ (C.Hs j)

theorem sigma_FlR (j : ℕ) :
    C.σ • inr'' (Y := C.Ys) (X := C.Xs) (C.FlR (C.Hs j)) =
      inr'' (Y := C.Ys) (X := C.Xs) (C.σ⁻¹ • C.Fl (C.Hs j)) := by
  have h : C.FlR (C.Hs j) = ((C.σ ^ 2)⁻¹ : ℝ) • C.Fl (C.Hs j) := rfl
  rw [h, map_smul, smul_smul]
  have hσ := C.hσ.ne'
  have hc : C.σ * (C.σ ^ 2)⁻¹ = C.σ⁻¹ := by field_simp
  rw [hc, ← map_smul]

theorem forcedR_eq (hQ : openCubeSet C.Q ⊆ openRectangle C.a C.b C.c C.d)
    (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (j : ℕ) :
    C.forcedR old j =
      C.Bop old (inr'' (Y := C.Ys) (X := C.Xs) (C.σ⁻¹ • C.Fl (C.Hs j))) -
        inr'' (Y := C.Ys) (X := C.Xs) (C.σ⁻¹ • C.Fl (C.Hs j)) := by
  rw [C.forcedR_apply, C.Cload hQ j, C.sigma_FlR]

end Cfg''

end

end ASDExplicitGamma.Scalar
