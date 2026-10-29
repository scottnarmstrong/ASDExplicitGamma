module

public import ASDExplicitGamma.Scalar.DropExpansion

/-! One-shell increment split (SC-ONE-SHELL-RECIPROCAL-DROP):
`σ̄_i (r_{i+1}(Q) - r_i(Q)) = D + vol⁻¹ E[quartic]` with the Hessian drift `D` bounded by the
ten-term trial. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
open Set Filter Topology Algsuperdiff.Frozen.Assumptions
open Numerics.Mirror Numerics.Scalar

noncomputable section

theorem drop_increment_split (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ) (hpast : ∀ l < N, nativeInductionState M h l)
    (i : ℤ) (hi : i < N) (e : Vec 2) (he : vecDot e e = 1)
    (hσ : 0 < (Annealed.sigmaBar M i : ℝ)) :
    ∃ D : ℝ,
      D ≤ -((shellVarianceSum h M.gamma (i + 1) - shellVarianceSum h M.gamma i) /
        (Annealed.sigmaBar M i : ℝ) ^ 2) * evalReal scalarRealEnv lowerBaseExpr ∧
      (Annealed.sigmaBar M i : ℝ) *
          (physicalInverseResponse M (i + 1) (originCube 2 (i + 129)) e -
            physicalInverseResponse M i (originCube 2 (i + 129)) e) =
        D + (volume (openCubeSet (originCube 2 (i + 129)))).toReal⁻¹ *
          ∫ p, physicalParityQuarticObservable (originCube 2 (i + 129)) M.nu
            (Annealed.sigmaBar M i : ℝ) M.nu_pos hσ
            (physicalResponseRestriction (originCube 2 (i + 129)) (drop_hQ (i + 129))) e p
            ∂(physicalParityProductLaw M i) := by
  let n : ℤ := i + 129
  let K := closure (cubeSet (originCube 2 n))
  let Q := originCube 2 n
  let σ : ℝ := (Annealed.sigmaBar M i : ℝ)
  let Φ := oldHessianUnitObservable n M.nu σ e
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure
  have hΦ := old_hessian_unit_observable_C2 n M.nu σ M.nu_pos hσ e
  have hderiv := old_hessian_heat_deriv M h hM n i Φ hΦ
  have hD := old_hessian_trial_bound M h hM hg N hpast i hi e he
  set D : ℝ := (1/2 : ℝ) * modelHeatTraceAverage K M i Φ
    (pureFluxMainCubeQ3Directions n (q3ModelAmplitude M h (i+1)) (q3ModelLength (i+1))) 0 with hDdef
  obtain ⟨c, hc0, hcs⟩ := drop_scaled_terms Q (drop_hQ n) M i σ hσ e h hM
  let vinv := (volume (openCubeSet Q)).toReal⁻¹
  have hvinv : 0 ≤ vinv := inv_nonneg.mpr ENNReal.toReal_nonneg
  let EH := ∫ p, physicalParityHessianObservable Q M.nu σ M.nu_pos hσ
    (physicalResponseRestriction Q (drop_hQ n)) e p ∂(physicalParityProductLaw M i)
  let g := modelHeatAverage K M i Φ
  have hexp (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1) :
      g (s ^ 2) - g 0 = vinv * (s ^ 2 * EH +
        ∫ p, physicalParityQuarticObservable Q M.nu σ M.nu_pos hσ
          (physicalResponseRestriction Q (drop_hQ n)) e (p.1, s • p.2)
          ∂(physicalParityProductLaw M i)) := by
    rw [drop_heat_increment M h hM i n e ell hK hσ s h0]
    exact drop_scaled_parity Q (drop_hQ n) M ell i hK σ hσ e h hM s
      (by rw [abs_of_nonneg h0]; exact h1)
  have hDa : D = vinv * EH := by
    refine drop_derivative_unique g D (vinv * EH) (vinv * c) hderiv ?_
    intro s h0 h1
    have hq := (hcs s (by rw [abs_of_nonneg h0]; exact h1)).2.2.2.2
    rw [hexp s h0 h1]
    set EQ : ℝ := ∫ p, physicalParityQuarticObservable Q M.nu σ M.nu_pos hσ
          (physicalResponseRestriction Q (drop_hQ n)) e (p.1, s • p.2)
          ∂(physicalParityProductLaw M i) with hEQ
    have hr : vinv * (s ^ 2 * EH + EQ) - vinv * EH * s ^ 2 = vinv * EQ := by ring
    rw [hr, abs_mul, abs_of_nonneg hvinv]
    calc vinv * |EQ| ≤ vinv * (c * s ^ 4) := mul_le_mul_of_nonneg_left hq hvinv
      _ = vinv * c * s ^ 4 := by ring
  refine ⟨D, hD, ?_⟩
  have h1 := hexp 1 (by norm_num) le_rfl
  have hheat : oldHessianUnitHeat M n i e = g := old_hessian_unit_heat_eq M n i e
  have e1 : (Annealed.sigmaBar M i : ℝ) * physicalInverseResponse M (i + 1) (originCube 2 n) e =
      g 1 := by rw [← hheat]; exact (drop_heat_one M i n e).symm
  have e0 : (Annealed.sigmaBar M i : ℝ) * physicalInverseResponse M i (originCube 2 n) e =
      g 0 := by rw [← hheat]; exact (drop_heat_zero M i n e).symm
  rw [mul_sub, e1, e0]
  simp only [one_pow, one_smul] at h1
  rw [h1, hDa]
  change _ = vinv * EH + vinv * ∫ p, _ ∂_
  ring

end

end ASDExplicitGamma.Scalar
