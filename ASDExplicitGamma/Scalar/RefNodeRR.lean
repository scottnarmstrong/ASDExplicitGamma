module

public import ASDExplicitGamma.Scalar.RefFinalRR2
public import ASDExplicitGamma.Scalar.RefBudget3T
public import ASDExplicitGamma.Scalar.RefRough10

/-! The corrected `SC-NEW-RESOLVENT-DEFECT` node with the provable explicit rough constant
`R = roughR = A² ((44/25)·(14103/10000) + 1)⁴`. No interface or rough-bound hypotheses remain:
only the standing hypotheses of the node. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open Algsuperdiff.Section3 ASDExplicitGamma.Native ASDExplicitGamma.Inverse Filter
open scoped InnerProductSpace BigOperators ENNReal Topology

noncomputable section

theorem sc_new_resolvent_defect_nodeRR (M : ABKModel 2) (h : ℝ) (m : ℤ) {a b c d : ℝ}
    (hab : a < b) (hcd : c < d)
    (hQ : openCubeSet (originCube 2 (m + 129)) ⊆ openRectangle a b c d) (e : Vec 2)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (hpast : ∀ n ≤ m, nativeInductionState M h n) (he : Book.Ch02.vecNorm e = 1)
    (he2 : vecNormSq e = 1) :
    Integrable (fun ω => max ((finalCfg M h m hab hcd hQ e).DactR m ω) 0)
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      ∫ ω, max ((finalCfg M h m hab hcd hQ e).DactR m ω) 0
          ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        (volume (openCubeSet (originCube 2 (m + 129)))).toReal *
          ((44 / 25 : ℝ) * ((finalCfg M h m hab hcd hQ e).amp ^ 2) ^ 2 *
            defectFdefR mainSourceMeanPrefix (xi'' M h m) (mStar' M) (14103 / 10000)
              (5 / 10 ^ 24) (14103 / 10000) (5 / 10 ^ 24) roughR) := by
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact (closedRectangle a b c d)
    (closedRectangle_isCompact a b c d)
  exact actual_defect_finalRR M h m hab hcd hQ e hM hγ (fun n hn => hpast n hn.le)
    mainSourceMeanPrefix (xi'' M h m) (mStar' M) (5 / 10 ^ 24) roughR
    (by unfold roughR defectA; positivity)
    (fun n => budget_Lam1T M h m hab hcd hQ e hM hγ hpast he he2 ell hK n)
    (fun n => budget_LamQ_rough M h m hab hcd hQ e hM hγ hpast he2 ell hK n)
    (sq_nonneg _)

end

end ASDExplicitGamma.Scalar
