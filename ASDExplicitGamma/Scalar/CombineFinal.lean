module

public import ASDExplicitGamma.Scalar.CombineMain
public import ASDExplicitGamma.Scalar.FlatQbigFinal

/-! SC-NEW-RESOLVENT-COMBINE: the literal fourth term of the physical four-term identity and the
paid one-shell charge. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open Algsuperdiff.Section3 ASDExplicitGamma.Native ASDExplicitGamma.Inverse Filter
open scoped InnerProductSpace BigOperators ENNReal Topology

noncomputable section

section Final

variable (M : ABKModel 2) (h : ℝ) (m : ℤ) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
  (hQ : openCubeSet (originCube 2 (m + 129)) ⊆ openRectangle a b c d) (e : Vec 2)

local notation "CC" => finalCfg M h m hab hcd hQ e

/-- The literal NEW-resolvent quartic equals `⟪J s₂, N s₂⟫` for the configuration `CC`. -/
theorem quartic_observable_eq (ω : Cutoff.CutoffSample 2) :
    physicalParityQuarticObservable (originCube 2 (m + 129)) M.nu
        (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).property
        (physicalResponseRestriction (originCube 2 (m + 129))
          (hQcl' hab hcd _ hQ)) e
        (physicalParityPairMap (K := closedRectangle a b c d) m ω) =
      ⟪(CC).Jop ((CC).s2R m ω), (CC).Nop m ω ((CC).s2R m ω)⟫_ℝ := by
  rfl

/-- **SC-NEW-RESOLVENT-COMBINE.**  Under the standing assumptions and the single named flat-leg
hypothesis `FlatExpectationBound` (together with the numerical cap of the flat leg), the actual
NEW-resolvent quartic satisfies `∫ Qt ≤ vol (amp²)² C♯(Fflat, Fdef)`, and the paid one-shell charge
is `C♯ · x/(1-x)`, `x = (11/5) γ`. -/
theorem sc_new_resolvent_combine (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (hpast : ∀ n ≤ m, nativeInductionState M h n) (he : Book.Ch02.vecNorm e = 1)
    (he2 : vecNormSq e = 1) {Fflat : ℝ}
    (hF : FlatExpectationBound M h m hab hcd hQ e Fflat)
    (hcap : Fflat ≤ (1557 / 1000 : ℝ) * ((14103 / 10000 : ℝ) + (513 / 500 : ℝ) * (5 / 10 ^ 24 : ℝ))) :
    (∫ ω, physicalParityQuarticObservable (originCube 2 (m + 129)) M.nu
        (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).property
        (physicalResponseRestriction (originCube 2 (m + 129))
          (hQcl' hab hcd _ hQ)) e
        (physicalParityPairMap (K := closedRectangle a b c d) m ω)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      (volume (openCubeSet (originCube 2 (m + 129)))).toReal * (((CC).amp ^ 2) ^ 2 *
        newResolventCSharp Fflat (defectFdefR mainSourceMeanPrefix (xi'' M h m)
          (mStar' M) (14103 / 10000) (5 / 10 ^ 24) (14103 / 10000) (5 / 10 ^ 24)
          roughR))) ∧
    ∀ γ : ℝ, 0 < γ → γ ≤ 17 / 50000 →
      newResolventCSharp Fflat (defectFdefR mainSourceMeanPrefix (xi'' M h m)
          (mStar' M) (14103 / 10000) (5 / 10 ^ 24) (14103 / 10000) (5 / 10 ^ 24)
          roughR) * ((3 : ℝ) ^ (2 * γ) - 1) ≤
        ((1557 / 1000 : ℝ) * ((14103 / 10000 : ℝ) + (513 / 500 : ℝ) * (5 / 10 ^ 24 : ℝ)) +
          (141 / 50 : ℝ) * Real.sqrt ((1557 / 1000 : ℝ) *
            ((14103 / 10000 : ℝ) + (513 / 500 : ℝ) * (5 / 10 ^ 24 : ℝ)) *
            defectFdefR mainSourceMeanPrefix (xi'' M h m)
          (mStar' M) (14103 / 10000) (5 / 10 ^ 24) (14103 / 10000) (5 / 10 ^ 24)
          roughR) +
          (44 / 25 : ℝ) * defectFdefR mainSourceMeanPrefix (xi'' M h m)
          (mStar' M) (14103 / 10000) (5 / 10 ^ 24) (14103 / 10000) (5 / 10 ^ 24)
          roughR) *
        (((11 / 5 : ℝ) * γ) / (1 - (11 / 5 : ℝ) * γ)) := by
  refine ⟨?_, fun γ hγ0 hγ1 => ?_⟩
  · have := sc_new_resolvent_combine_core M h m hab hcd hQ e hM hγ hpast he he2 hF
    simpa only [quartic_observable_eq M h m hab hcd hQ e] using this
  · exact new_resolvent_combine_paid_charge_of_component_bounds γ Fflat _ _ hγ0 hγ1
      ⟨hF.1, hcap⟩ (defectFdefR_nonneg _ _ _) le_rfl

/-- **SC-NEW-RESOLVENT-COMBINE, closed node**: only the standing assumptions. -/
theorem sc_new_resolvent_combine_node (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (hpast : ∀ n ≤ m, nativeInductionState M h n) (he : Book.Ch02.vecNorm e = 1)
    (he2 : vecNormSq e = 1) :
    (∫ ω, physicalParityQuarticObservable (originCube 2 (m + 129)) M.nu
        (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).property
        (physicalResponseRestriction (originCube 2 (m + 129))
          (hQcl' hab hcd _ hQ)) e
        (physicalParityPairMap (K := closedRectangle a b c d) m ω)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      (volume (openCubeSet (originCube 2 (m + 129)))).toReal * (((CC).amp ^ 2) ^ 2 *
        newResolventCSharp ((1557 / 1000 : ℝ) * ((14103 / 10000 : ℝ) + (513 / 500 : ℝ) * (5 / 10 ^ 24 : ℝ)))
          (defectFdefR mainSourceMeanPrefix (xi'' M h m)
          (mStar' M) (14103 / 10000) (5 / 10 ^ 24) (14103 / 10000) (5 / 10 ^ 24)
          roughR))) ∧
    ∀ γ : ℝ, 0 < γ → γ ≤ 17 / 50000 →
      newResolventCSharp ((1557 / 1000 : ℝ) * ((14103 / 10000 : ℝ) + (513 / 500 : ℝ) * (5 / 10 ^ 24 : ℝ)))
          (defectFdefR mainSourceMeanPrefix (xi'' M h m)
          (mStar' M) (14103 / 10000) (5 / 10 ^ 24) (14103 / 10000) (5 / 10 ^ 24)
          roughR) * ((3 : ℝ) ^ (2 * γ) - 1) ≤
        ((1557 / 1000 : ℝ) * ((14103 / 10000 : ℝ) + (513 / 500 : ℝ) * (5 / 10 ^ 24 : ℝ)) +
          (141 / 50 : ℝ) * Real.sqrt ((1557 / 1000 : ℝ) *
            ((14103 / 10000 : ℝ) + (513 / 500 : ℝ) * (5 / 10 ^ 24 : ℝ)) *
            defectFdefR mainSourceMeanPrefix (xi'' M h m)
          (mStar' M) (14103 / 10000) (5 / 10 ^ 24) (14103 / 10000) (5 / 10 ^ 24)
          roughR) +
          (44 / 25 : ℝ) * defectFdefR mainSourceMeanPrefix (xi'' M h m)
          (mStar' M) (14103 / 10000) (5 / 10 ^ 24) (14103 / 10000) (5 / 10 ^ 24)
          roughR) *
        (((11 / 5 : ℝ) * γ) / (1 - (11 / 5 : ℝ) * γ)) :=
  sc_new_resolvent_combine M h m hab hcd hQ e hM hγ hpast he he2
    (flat_expectation_package M h m hab hcd hQ e hM hγ (fun n hn => hpast n hn.le) he)
    le_rfl

end Final

end

end ASDExplicitGamma.Scalar
