module

public import ASDExplicitGamma.Scalar.DropFinal
public import ASDExplicitGamma.Scalar.CombineFinal

/-! Bridge from SC-NEW-RESOLVENT-COMBINE (`sc_new_resolvent_combine`, on a source rectangle)
to the quartic interface of the reciprocal drop (on `K = closure (cubeSet Q)`). -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open Algsuperdiff.Section3 ASDExplicitGamma.Native ASDExplicitGamma.Inverse Filter
open Algsuperdiff.Frozen.Assumptions
open Numerics.Mirror Numerics.Scalar

noncomputable section

/-- The restriction of the older field to the cube is independent of the ambient compact set. -/
theorem drop_R_older_eq (M : ABKModel 2) (Q : TriadicCube 2) (i : ℤ)
    {K1 K2 : Set (Vec 2)} [CompactSpace K1] [CompactSpace K2]
    (hQ1 : closure (openCubeSet Q) ⊆ K1) (hQ2 : closure (openCubeSet Q) ⊆ K2)
    (ell1 ell2 : ℤ) (hK1 : K1 ⊆ openCubeSet (originCube 2 ell1))
    (hK2 : K2 ⊆ openCubeSet (originCube 2 ell2)) (ω : Cutoff.CutoffSample 2) :
    physicalResponseRestriction Q hQ1 (olderField K1 i ω) =
      physicalResponseRestriction Q hQ2 (olderField K2 i ω) := by
  apply BoundedContinuousFunction.ext
  rintro ⟨y, hy⟩
  change olderField K1 i ω ⟨y, hQ1 hy⟩ = olderField K2 i ω ⟨y, hQ2 hy⟩
  rw [olderField_apply_eq_coefficientCutoff K1 M ell1 i hK1,
    olderField_apply_eq_coefficientCutoff K2 M ell2 i hK2]

theorem drop_R_fresh_eq (Q : TriadicCube 2) (i : ℤ)
    {K1 K2 : Set (Vec 2)} [CompactSpace K1] [CompactSpace K2]
    (hQ1 : closure (openCubeSet Q) ⊆ K1) (hQ2 : closure (openCubeSet Q) ⊆ K2)
    (ω : Cutoff.CutoffSample 2) :
    physicalResponseRestriction Q hQ1 (shellFieldScalarRestriction K1 (ω.1 (i + 1))) =
      physicalResponseRestriction Q hQ2 (shellFieldScalarRestriction K2 (ω.1 (i + 1))) := by
  apply BoundedContinuousFunction.ext
  rintro ⟨y, hy⟩
  rfl

theorem drop_quartic_K_transfer (M : ABKModel 2) (Q : TriadicCube 2) (i : ℤ)
    {K1 K2 : Set (Vec 2)} [CompactSpace K1] [CompactSpace K2]
    (hQ1 : closure (openCubeSet Q) ⊆ K1) (hQ2 : closure (openCubeSet Q) ⊆ K2)
    (ell1 ell2 : ℤ) (hK1 : K1 ⊆ openCubeSet (originCube 2 ell1))
    (hK2 : K2 ⊆ openCubeSet (originCube 2 ell2)) (σ : ℝ) (hσ : 0 < σ) (e : Vec 2)
    (ω : Cutoff.CutoffSample 2) :
    physicalParityQuarticObservable Q M.nu σ M.nu_pos hσ
        (physicalResponseRestriction Q hQ1) e
        (physicalParityPairMap (K := K1) i ω) =
      physicalParityQuarticObservable Q M.nu σ M.nu_pos hσ
        (physicalResponseRestriction Q hQ2) e
        (physicalParityPairMap (K := K2) i ω) := by
  have h1 := drop_R_older_eq M Q i hQ1 hQ2 ell1 ell2 hK1 hK2 ω
  have h2 := drop_R_fresh_eq Q i hQ1 hQ2 ω
  simp only [physicalParityQuarticObservable, physicalParityCoefficient,
    physicalParityPairMap, physicalParityFreshField]
  rw [h1, h2]

/-- The accepted defect value of SC-NEW-RESOLVENT-COMBINE at label `m`. -/
def dropFdef (M : ABKModel 2) (h : ℝ) (m : ℤ) : ℝ :=
  defectFdefR mainSourceMeanPrefix (xi'' M h m) (mStar' M) (14103 / 10000) (5 / 10 ^ 24)
    (14103 / 10000) (5 / 10 ^ 24) roughR

/-- SC-NEW-RESOLVENT-COMBINE gives the quartic interface of the drop, with the coefficient
`C♯(Fflat, Fdef)`. -/
theorem drop_quartic_bound_of_combine (M : ABKModel 2) (h : ℝ) (i : ℤ)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hQ : openCubeSet (originCube 2 (i + 129)) ⊆ openRectangle a b c d) (e : Vec 2)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (hpast : ∀ n ≤ i, nativeInductionState M h n) (he : Book.Ch02.vecNorm e = 1)
    (he2 : vecNormSq e = 1) {Fflat : ℝ}
    (hF : FlatExpectationBound M h i hab hcd hQ e Fflat)
    (hcap : Fflat ≤ (1557 / 1000 : ℝ) * ((14103 / 10000 : ℝ) + (513 / 500 : ℝ) * (5 / 10 ^ 24 : ℝ))) :
    NewResolventQuarticBound M h i e (newResolventCSharp Fflat (dropFdef M h i)) := by
  intro hσ
  have hcomb := (sc_new_resolvent_combine M h i hab hcd hQ e hM hγ hpast he he2 hF hcap).1
  have hQ2 := drop_hQ (i + 129)
  obtain ⟨ell1, hK1⟩ := exists_originCube_containing_compact (closedRectangle a b c d)
    (closedRectangle_isCompact a b c d)
  obtain ⟨ell2, hK2⟩ := exists_originCube_containing_compact
    (closure (cubeSet (originCube 2 (i + 129))))
    (isBounded_cubeSet (originCube 2 (i + 129))).isCompact_closure
  have heq : (∫ ω, physicalParityQuarticObservable (originCube 2 (i + 129)) M.nu
        (Annealed.sigmaBar M i : ℝ) M.nu_pos hσ
        (physicalResponseRestriction (originCube 2 (i + 129)) (drop_hQ (i + 129))) e
        (physicalParityPairMap (K := closure (cubeSet (originCube 2 (i + 129)))) i ω)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ∫ ω, physicalParityQuarticObservable (originCube 2 (i + 129)) M.nu
        (Annealed.sigmaBar M i : ℝ) M.nu_pos (Annealed.sigmaBar M i).property
        (physicalResponseRestriction (originCube 2 (i + 129))
          (hQcl' hab hcd _ hQ)) e
        (physicalParityPairMap (K := closedRectangle a b c d) i ω)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    exact (drop_quartic_K_transfer M (originCube 2 (i + 129)) i (hQcl' hab hcd _ hQ)
      (drop_hQ (i + 129)) ell1 ell2 hK1 hK2 _ _ e ω).symm
  rw [heq]
  exact hcomb

end

end ASDExplicitGamma.Scalar
