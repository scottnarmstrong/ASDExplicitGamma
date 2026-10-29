module

public import ASDExplicitGamma.Scalar.T4v2Main

/-! T4 v2, part one for the actual configuration: the pathwise forced-budget identity. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open Algsuperdiff.Section3

noncomputable section

/-- **T4 INTERFACE v2, pathwise part** (proved; in fact with equality): for the actual
configuration and every `n`, the corrected forced weak budget is `σ⁻²` times `fwStar` of the
actual OLD maximizers of the q3 mode loads over the modes `t4v2S n`. -/
theorem T4v2_pathwise (M : ABKModel 2) (h : ℝ) (m : ℤ) {a b c d : ℝ} (hab : a < b)
    (hcd : c < d)
    (hQ : openCubeSet (originCube 2 (m + 129)) ⊆ openRectangle a b c d) (e : Vec 2)
    (n : ℕ) (ω : Cutoff.CutoffSample 2) :
    (finalCfg M h m hab hcd hQ e).forcedLamR n (olderField (closedRectangle a b c d) m ω) =
      (((finalCfg M h m hab hcd hQ e).σ ^ 2)⁻¹) *
        fwStar (t4v2S n) M m (originCube 2 (m + 1 + 128)) 134
          (lambda8Q3ParentModePotential M h e (m + 1))
          (oldMaxFam M m (originCube 2 (m + 1 + 128))
            (lambda8Q3ParentModePotential M h e (m + 1))) ω := by
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact (closedRectangle a b c d)
    (closedRectangle_isCompact a b c d)
  exact t4v2_pathwise_gen hab hcd M h m e (m + 129) (by ring) (hQcl' hab hcd _ hQ) hQ ell hK n ω

end

end ASDExplicitGamma.Scalar
