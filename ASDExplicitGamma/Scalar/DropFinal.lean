module

public import ASDExplicitGamma.Scalar.DropIncrement
public import ASDExplicitGamma.Statements.NativeInductionState
public import ASDExplicitGamma.Scalar.ColdReciprocalNormalization
public import ASDExplicitGamma.Scalar.MolecularStartupScale
public import ASDExplicitGamma.Scalar.ReciprocalMolecular
public import ASDExplicitGamma.Scalar.ReciprocalTrueFrame
public import ASDExplicitGamma.Scalar.StructuralContinuity
public import ASDExplicitGamma.Cold.NativeThetaScaling
public import ASDExplicitGamma.Numerics.Cold.Basic
public import ASDExplicitGamma.Scalar.ResolventCombine

/-! SC-ONE-SHELL-RECIPROCAL-DROP: the one-shell reciprocal decrement at label `i`, from the
parity split, the OLD Hessian trial, and the NEW-resolvent quartic bound (the single named
hypothesis delivered by SC-NEW-RESOLVENT-COMBINE). -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
open Set Filter Topology Algsuperdiff.Frozen.Assumptions
open Numerics.Mirror Numerics.Scalar

noncomputable section

/-- The interface delivered by SC-NEW-RESOLVENT-COMBINE at label `i`: the actual NEW-resolvent
quartic term of the physical four-term identity on the cube `Q = originCube 2 (i+129)` is at most
`vol(Q) · ((amp/σ̄_i)²)² · Cq`. -/
def NewResolventQuarticBound (M : ABKModel 2) (h : ℝ) (i : ℤ) (e : Vec 2) (Cq : ℝ) : Prop :=
  ∀ hσ : 0 < (Annealed.sigmaBar M i : ℝ),
    ∫ ω, physicalParityQuarticObservable (originCube 2 (i + 129)) M.nu
        (Annealed.sigmaBar M i : ℝ) M.nu_pos hσ
        (physicalResponseRestriction (originCube 2 (i + 129)) (drop_hQ (i + 129))) e
        (physicalParityPairMap (K := closure (cubeSet (originCube 2 (i + 129)))) i ω)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      (volume (openCubeSet (originCube 2 (i + 129)))).toReal *
        (((q3ModelAmplitude M h (i + 1) / (Annealed.sigmaBar M i : ℝ)) ^ 2) ^ 2 *
          Cq)

theorem drop_quartic_product_law (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (i : ℤ)
    (e : Vec 2) (hσ : 0 < (Annealed.sigmaBar M i : ℝ)) :
    ∫ ω, physicalParityQuarticObservable (originCube 2 (i + 129)) M.nu
        (Annealed.sigmaBar M i : ℝ) M.nu_pos hσ
        (physicalResponseRestriction (originCube 2 (i + 129)) (drop_hQ (i + 129))) e
        (physicalParityPairMap (K := closure (cubeSet (originCube 2 (i + 129)))) i ω)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure =
      ∫ p, physicalParityQuarticObservable (originCube 2 (i + 129)) M.nu
        (Annealed.sigmaBar M i : ℝ) M.nu_pos hσ
        (physicalResponseRestriction (originCube 2 (i + 129)) (drop_hQ (i + 129))) e p
        ∂(physicalParityProductLaw M i) := by
  let K := closure (cubeSet (originCube 2 (i + 129)))
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 (i + 129))).isCompact_closure
  have hX : Measurable (olderField K i) := measurable_olderField K ell i hK
  have hY : Measurable (physicalParityFreshField (K := K) i) :=
    (measurable_shellFieldScalarRestriction K).comp
      ((measurable_pi_apply (i + 1)).comp measurable_subtype_coe)
  have hpair : Measurable (physicalParityPairMap (K := K) i) := hX.prodMk hY
  obtain ⟨hmap, -⟩ := physical_resolvent_parity (originCube 2 (i + 129)) (drop_hQ (i + 129)) M
    ell i hK (Annealed.sigmaBar M i : ℝ) hσ e h hM
  have hcont := (physicalParity_observables_continuous' (originCube 2 (i + 129))
    (drop_hQ (i + 129)) M.nu (Annealed.sigmaBar M i : ℝ) M.nu_pos hσ e).2.2.2.1
  rw [← hmap, integral_map hpair.aemeasurable hcont.aestronglyMeasurable]

end

end ASDExplicitGamma.Scalar
