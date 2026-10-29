module

public import ASDExplicitGamma.Scalar.DropHeat

/-! Second-order expansion of the unit heat average through the scaled four-term parity
(SC-ONE-SHELL-RECIPROCAL-DROP): the Hessian term is the right derivative, and the one-shell
increment is the Hessian term plus the quartic term. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
open Set Filter Topology Algsuperdiff.Frozen.Assumptions

noncomputable section

theorem drop_hQ (n : ℤ) :
    closure (openCubeSet (originCube 2 n)) ⊆ closure (cubeSet (originCube 2 n)) :=
  closure_mono (openCubeSet_subset_cubeSet _)

/-- The heat-average increment at `t = s²` is the integrated parity response increment. -/
theorem drop_heat_increment (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (i n : ℤ)
    (e : Vec 2) (ell : ℤ)
    (hK : closure (cubeSet (originCube 2 n)) ⊆ openCubeSet (originCube 2 ell))
    (hσ : 0 < (Annealed.sigmaBar M i : ℝ)) (s : ℝ) (hs : 0 ≤ s) :
    modelHeatAverage (closure (cubeSet (originCube 2 n))) M i
        (oldHessianUnitObservable n M.nu (Annealed.sigmaBar M i : ℝ) e) (s ^ 2) -
      modelHeatAverage (closure (cubeSet (originCube 2 n))) M i
        (oldHessianUnitObservable n M.nu (Annealed.sigmaBar M i : ℝ) e) 0 =
    ∫ p, physicalParityResponseIncrement (originCube 2 n) M.nu (Annealed.sigmaBar M i : ℝ)
        M.nu_pos hσ (physicalResponseRestriction (originCube 2 n) (drop_hQ n)) e
        (p.1, s • p.2) ∂(physicalParityProductLaw M i) := by
  let K := closure (cubeSet (originCube 2 n))
  let Q := originCube 2 n
  let σ : ℝ := (Annealed.sigmaBar M i : ℝ)
  let Φ := oldHessianUnitObservable n M.nu σ e
  let ρ := (Cutoff.cutoffSampleLaw M).toMeasure
  let R := physicalResponseRestriction Q (drop_hQ n)
  let incr := physicalParityResponseIncrement Q M.nu σ M.nu_pos hσ R e
  have hint (t : ℝ) : Integrable (fun ω => Φ (modelInsertedScalar K i t ω)) ρ := by
    have := old_hessian_unit_integrable M h hM n i e t
    refine this.congr ?_
    filter_upwards with ω
    exact (old_hessian_unit_observable_inserted M n i t ω e).symm
  have hpoint (ω : Cutoff.CutoffSample 2) :
      incr ((physicalParityPairMap (K := K) i ω).1, s • (physicalParityPairMap (K := K) i ω).2) =
        Φ (modelInsertedScalar K i (s ^ 2) ω) - Φ (modelInsertedScalar K i 0 ω) := by
    have h1 : modelInsertedScalar K i (s ^ 2) ω =
        olderField K i ω + s • physicalParityFreshField (K := K) i ω := by
      unfold modelInsertedScalar
      rw [Real.sqrt_sq hs]
      rfl
    have h0 : modelInsertedScalar K i 0 ω = olderField K i ω := by
      unfold modelInsertedScalar
      rw [Real.sqrt_zero, zero_smul, add_zero]
    rw [h1, h0]
    unfold incr physicalParityResponseIncrement
    show _ = oldHessianUnitObservable n M.nu σ e _ - oldHessianUnitObservable n M.nu σ e _
    rw [drop_unit_observable_eq_open n M.nu σ M.nu_pos hσ e (drop_hQ n),
      drop_unit_observable_eq_open n M.nu σ M.nu_pos hσ e (drop_hQ n)]
    rfl
  have hpairMeas : Measurable (physicalParityPairMap (K := K) i) := by
    have hX : Measurable (olderField K i) := measurable_olderField K ell i hK
    have hY : Measurable (physicalParityFreshField (K := K) i) :=
      (measurable_shellFieldScalarRestriction K).comp
        ((measurable_pi_apply (i + 1)).comp measurable_subtype_coe)
    exact hX.prodMk hY
  obtain ⟨hmap, -⟩ := physical_resolvent_parity Q (drop_hQ n) M ell i hK σ hσ e h hM
  have hcont : Continuous (fun p : C(K, ℝ) × C(K, ℝ) => incr (p.1, s • p.2)) := by
    have := (physicalParity_observables_continuous' Q (drop_hQ n) M.nu σ M.nu_pos hσ e).2.2.2.2
    exact this.comp (by fun_prop)
  rw [← hmap, integral_map hpairMeas.aemeasurable hcont.aestronglyMeasurable]
  unfold modelHeatAverage
  rw [← integral_sub (hint _) (hint _)]
  exact (integral_congr_ae (Filter.Eventually.of_forall fun ω => (hpoint ω).symm))

end

end ASDExplicitGamma.Scalar
