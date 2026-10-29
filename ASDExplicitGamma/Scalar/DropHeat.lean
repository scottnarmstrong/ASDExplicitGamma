module

public import ASDExplicitGamma.Scalar.DropObservable

/-! Heat-average bookkeeping for SC-ONE-SHELL-RECIPROCAL-DROP: the endpoints `g 0`, `g 1` of
the unit heat average are `σ̄_i` times the physical inverse responses at labels `i`, `i + 1`; and
a one-sided derivative is identified from a second-order expansion. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
open Set Filter Topology Algsuperdiff.Frozen.Assumptions

noncomputable section

/-- A right derivative at `0` is identified by a second-order expansion in `√t`. -/
theorem drop_derivative_unique (g : ℝ → ℝ) (D a c : ℝ)
    (hD : HasDerivWithinAt g D (Ici 0) 0)
    (hexp : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → |g (s ^ 2) - g 0 - a * s ^ 2| ≤ c * s ^ 4) :
    D = a := by
  have hslope := (hasDerivWithinAt_iff_tendsto_slope.mp hD)
  have hset : (Ici (0 : ℝ) \ {0}) = Ioi 0 := by
    ext t; simp [lt_iff_le_and_ne, eq_comm]
  rw [hset] at hslope
  have h2 : Tendsto (fun t : ℝ => slope g 0 t) (𝓝[>] 0) (𝓝 a) := by
    have hz : Tendsto (fun t : ℝ => slope g 0 t - a) (𝓝[>] 0) (𝓝 0) := by
      have hc : Tendsto (fun t : ℝ => |c| * t) (𝓝[>] 0) (𝓝 0) := by
        have : Tendsto (fun t : ℝ => |c| * t) (𝓝 0) (𝓝 (|c| * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      refine squeeze_zero_norm' ?_ hc
      have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo (0 : ℝ) 1 :=
        Ioo_mem_nhdsGT (by norm_num)
      filter_upwards [hev] with t ht
      have hs := hexp (Real.sqrt t) (Real.sqrt_nonneg _)
        (by rw [Real.sqrt_le_one]; exact ht.2.le)
      rw [Real.sq_sqrt ht.1.le] at hs
      have hs4 : Real.sqrt t ^ 4 = t ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt ht.1.le]
      rw [hs4] at hs
      have : slope g 0 t - a = (g t - g 0 - a * t) / t := by
        have ht0 : t ≠ 0 := ht.1.ne'
        rw [slope_def_field]
        field_simp
        ring
      rw [this, Real.norm_eq_abs, abs_div, abs_of_pos ht.1, div_le_iff₀ ht.1]
      calc |g t - g 0 - a * t| ≤ c * t ^ 2 := hs
        _ ≤ |c| * t ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
        _ = |c| * t * t := by ring
    simpa using hz.add_const a
  exact tendsto_nhds_unique hslope h2

theorem drop_partial_zero (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) :
    Model.partialInsertedCoefficient M m 0 ω = Cutoff.coefficientCutoff M.nu m ω := by
  apply RegCoeffField.ext
  intro x
  change Cutoff.coefficientCutoff M.nu m ω x + Real.sqrt 0 • ShellField.forgetShell (ω.1 (m + 1)) x =
    Cutoff.coefficientCutoff M.nu m ω x
  rw [Real.sqrt_zero, zero_smul, add_zero]

theorem drop_partial_one (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) :
    Model.partialInsertedCoefficient M m 1 ω = Cutoff.coefficientCutoff M.nu (m + 1) ω := by
  apply RegCoeffField.ext
  intro x
  have h := Cutoff.cutoff_sub_cutoff_eq_finiteShellIncrement ω (n := m) (m := m + 1)
    (by omega) x
  have hinc : Cutoff.finiteShellIncrement ω.1 m (m + 1) x =
      ShellField.forgetShell (ω.1 (m + 1)) x := by
    rw [Cutoff.finiteShellIncrement_apply]
    have : Finset.Ioc m (m + 1) = {m + 1} := by
      ext k; simp only [Finset.mem_Ioc, Finset.mem_singleton]; omega
    rw [this, Finset.sum_singleton]
    rfl
  change Cutoff.coefficientCutoff M.nu m ω x + Real.sqrt 1 • ShellField.forgetShell (ω.1 (m + 1)) x =
    Cutoff.coefficientCutoff M.nu (m + 1) ω x
  rw [Real.sqrt_one, one_smul, Cutoff.coefficientCutoff_apply, Cutoff.coefficientCutoff_apply,
    ← hinc, ← h]
  abel

/-- `g(0) = σ̄_i r_i(Q)`. -/
theorem drop_heat_zero (M : ABKModel 2) (i n : ℤ) (e : Vec 2) :
    oldHessianUnitHeat M n i e 0 =
      (Annealed.sigmaBar M i : ℝ) * physicalInverseResponse M i (originCube 2 n) e :=
  drop_heat_eq_response M i n i 0 e (fun ω => by rw [drop_partial_zero])

/-- `g(1) = σ̄_i r_{i+1}(Q)`. -/
theorem drop_heat_one (M : ABKModel 2) (i n : ℤ) (e : Vec 2) :
    oldHessianUnitHeat M n i e 1 =
      (Annealed.sigmaBar M i : ℝ) * physicalInverseResponse M (i + 1) (originCube 2 n) e :=
  drop_heat_eq_response M i n (i + 1) 1 e (fun ω => by rw [drop_partial_one])

end

end ASDExplicitGamma.Scalar
