module

public import ASDExplicitGamma.Triadic.DiagCoordinateHat

/-! Tent-kernel integration by parts on source cell strips, without face traces. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory Filter Set
open scoped Topology

noncomputable section

theorem diagCutoff_tendsto_indicator (a L t : ℝ) :
    Tendsto (fun n : ℕ => Torus.cutoff a L (1 / ((n : ℝ) + 1)) t) atTop
      (𝓝 (if t ∈ Ioo a (a + L) then (1 : ℝ) else 0)) := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  by_cases ht : t ∈ Ioo a (a + L)
  · rw [ite_eq_left ht]
    have h2 : Tendsto (fun n => 2 * ε n) atTop (𝓝 0) := by
      simpa only [mul_zero] using hlim.const_mul 2
    have hl := (tendsto_order.1 h2).2 (t - a) (sub_pos.mpr ht.1)
    have hu := (tendsto_order.1 h2).2 (a + L - t) (sub_pos.mpr ht.2)
    have heq : ∀ᶠ n in atTop, Torus.cutoff a L (ε n) t = 1 := by
      filter_upwards [hl, hu] with n hn hn'
      exact Torus.cutoff_eq_one_of_deep (hε n) hn hn'
    exact tendsto_const_nhds.congr' (heq.mono fun _ h => h.symm)
  · rw [ite_eq_right ht]
    have heq : ∀ n, Torus.cutoff a L (ε n) t = 0 := by
      intro n
      by_contra h
      have hm := Torus.mem_Ioo_of_cutoff_ne_zero (hε n) h
      apply ht
      constructor <;> linarith only [hm.1, hm.2, hε n]
    exact tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun n => (heq n).symm)

/-- Cutting out a transverse cell strip does not create a boundary term
in the differentiated coordinate. The source potential is in H¹₀; the
H¹ test has no boundary condition. -/
theorem diagH10_stripIntegrationByParts (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q)) (w : H1Function (openCubeSet Q))
    (i s : Fin 2) (his : i ≠ s) (a L : ℝ) :
    (∫ x in openCubeSet Q,
      (if x s ∈ Ioo a (a + L) then (1 : ℝ) else 0) * (u.toH1Function.grad x i * w.toFun x)) =
      -∫ x in openCubeSet Q,
        (if x s ∈ Ioo a (a + L) then (1 : ℝ) else 0) * (u.toH1Function.toFun x * w.grad x i) := by
  let φ (n : ℕ) (x : Vec 2) := Torus.cutoff a L (1 / ((n : ℝ) + 1)) (x s)
  have hφ (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (φ n) :=
    (Torus.contDiff_cutoff a L _).comp (contDiff_apply ℝ ℝ s)
  have hDφ (n : ℕ) (x : Vec 2) : (fderiv ℝ (φ n) x) (basisVec i) = 0 := by
    have h := (Torus.hasDerivAt_cutoff a L (1 / ((n : ℝ) + 1)) (x s)).comp_hasFDerivAt (𝕜 := ℝ) x
      (hasFDerivAt_apply (𝕜 := ℝ) s x)
    change (fderiv ℝ (Torus.cutoff a L (1 / ((n : ℝ) + 1)) ∘ fun y : Vec 2 => y s) x) (basisVec i) = 0
    rw [h.fderiv]
    simp only [smul_apply, ContinuousLinearMap.proj_apply,
      smul_eq_mul, basisVec_apply, ite_eq_right his.symm, mul_zero]
  let W (n : ℕ) := diagMulSmooth Q w (φ n) (hφ n)
  have hW (n : ℕ) : (W n).toFun = fun x => φ n x * w.toFun x := rfl
  have hDW (n : ℕ) (x : Vec 2) : (W n).grad x i = φ n x * w.grad x i := by
    change φ n x * w.grad x i + w.toFun x * (fderiv ℝ (φ n) x) (basisVec i) = _
    rw [hDφ, mul_zero, add_zero]
  have heq (n : ℕ) :
      (∫ x in openCubeSet Q, φ n x * (u.toH1Function.grad x i * w.toFun x)) =
      -∫ x in openCubeSet Q, φ n x * (u.toH1Function.toFun x * w.grad x i) := by
    have h := diagH10_integrationByParts Q u (W n) i
    simp only [hW, hDW] at h
    simpa only [mul_left_comm, mul_assoc] using h
  have hleftInt : Integrable (fun x => u.toH1Function.grad x i * w.toFun x)
      (volume.restrict (openCubeSet Q)) := (u.toH1Function.gradMemL2 i).integrable_mul w.memL2
  have hrightInt : Integrable (fun x => u.toH1Function.toFun x * w.grad x i)
      (volume.restrict (openCubeSet Q)) := u.toH1Function.memL2.integrable_mul (w.gradMemL2 i)
  have hbound (n : ℕ) (x : Vec 2) : ‖φ n x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Torus.cutoff_nonneg _ _ _ _)]
    exact Torus.cutoff_le_one _ _ _ _
  have hl := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (openCubeSet Q))
    (fun x => ‖u.toH1Function.grad x i * w.toFun x‖)
    (fun n => ((hφ n).continuous.aestronglyMeasurable).mul hleftInt.aestronglyMeasurable)
    hleftInt.norm
    (fun n => Filter.Eventually.of_forall fun x => by
      change ‖φ n x * (u.toH1Function.grad x i * w.toFun x)‖ ≤
        ‖u.toH1Function.grad x i * w.toFun x‖
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hbound n x) (norm_nonneg _)).trans_eq (one_mul _))
    (Filter.Eventually.of_forall fun x => (diagCutoff_tendsto_indicator a L (x s)).mul_const
      (u.toH1Function.grad x i * w.toFun x))
  have hr := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (openCubeSet Q))
    (fun x => ‖u.toH1Function.toFun x * w.grad x i‖)
    (fun n => ((hφ n).continuous.aestronglyMeasurable).mul hrightInt.aestronglyMeasurable)
    hrightInt.norm
    (fun n => Filter.Eventually.of_forall fun x => by
      change ‖φ n x * (u.toH1Function.toFun x * w.grad x i)‖ ≤
        ‖u.toH1Function.toFun x * w.grad x i‖
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hbound n x) (norm_nonneg _)).trans_eq (one_mul _))
    (Filter.Eventually.of_forall fun x => (diagCutoff_tendsto_indicator a L (x s)).mul_const
      (u.toH1Function.toFun x * w.grad x i))
  apply tendsto_nhds_unique hl
  exact hr.neg.congr' (Filter.Eventually.of_forall fun n => (heq n).symm)

/-- The actual tent test identity on a transverse cell strip. -/
theorem diagH10_tentStrip (Q : TriadicCube 2) (u : H10Function (openCubeSet Q))
    (i s : Fin 2) (his : i ≠ s) (c : ℝ) {r : ℝ} (hr : 0 < r) (a L : ℝ) :
    (∫ x in openCubeSet Q,
      (if x s ∈ Ioo a (a + L) then (1 : ℝ) else 0) *
        (u.toH1Function.grad x i * diagHat ((x i - c) / r))) =
      -∫ x in openCubeSet Q,
        (if x s ∈ Ioo a (a + L) then (1 : ℝ) else 0) *
          (u.toH1Function.toFun x * diagHatSlope r (x i - c)) := by
  have h := diagH10_stripIntegrationByParts Q u (diagCoordinateHatH1 Q i c r) i s his a L
  rw [diagCoordinateHatH1_toFun Q i c hr] at h
  have heq : (fun x => (if x s ∈ Ioo a (a + L) then (1 : ℝ) else 0) *
      (u.toH1Function.toFun x * (diagCoordinateHatH1 Q i c r).grad x i)) =ᵐ[volume.restrict (openCubeSet Q)]
      (fun x => (if x s ∈ Ioo a (a + L) then (1 : ℝ) else 0) *
        (u.toH1Function.toFun x * diagHatSlope r (x i - c))) := by
    filter_upwards [diagCoordinateHatH1_grad_ae Q i c r] with x hx
    rw [hx]
    simp only [Pi.smul_apply, smul_eq_mul, basisVec_apply, ite_true, mul_one]
  rw [integral_congr_ae heq] at h
  exact h

end

end ASDExplicitGamma.Triadic
