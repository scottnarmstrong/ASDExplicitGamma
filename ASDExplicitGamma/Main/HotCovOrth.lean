module

public import ASDExplicitGamma.Triadic.PlanarSobolev
public import ASDExplicitGamma.Variational.CompatibleCoercivity

/-! MA-E-COVARIANCE, step 4: the exact zero identity
`∫_U ∇h · J ∇g = 0` for `h ∈ H¹₀(U)` and `g ∈ H¹(U)`.  It is proved from the
smooth approximations of `h`, the weak gradient of `g`, and the symmetry of
mixed second derivatives. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Filter Topology Homogenization ASDExplicitGamma.Triadic

noncomputable section

theorem hotcov_tendsto_integral_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f v : α → ℝ} {u : ℕ → α → ℝ}
    (hf : MemLp f 2 μ) (hu : ∀ n, MemLp (u n) 2 μ) (hv : MemLp v 2 μ)
    (h : Tendsto (fun n => eLpNorm (fun x => u n x - v x) 2 μ) atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, f x * u n x ∂μ) atTop (nhds (∫ x, f x * v x ∂μ)) := by
  have key : ∀ n, |(∫ x, f x * u n x ∂μ) - ∫ x, f x * v x ∂μ| ≤
      (eLpNorm f 2 μ).toReal * (eLpNorm (fun x => u n x - v x) 2 μ).toReal := by
    intro n
    have hw : MemLp (fun x => u n x - v x) 2 μ := (hu n).sub hv
    have hint1 : Integrable (fun x => f x * u n x) μ := hf.integrable_mul (hu n)
    have hint2 : Integrable (fun x => f x * v x) μ := hf.integrable_mul hv
    have heq : (∫ x, f x * u n x ∂μ) - ∫ x, f x * v x ∂μ = ∫ x, f x * (u n x - v x) ∂μ := by
      rw [← integral_sub hint1 hint2]
      congr 1; funext x; ring
    rw [heq]
    have hin := real_inner_le_norm (hf.toLp f) (hw.toLp _)
    have hin2 := abs_real_inner_le_norm (hf.toLp f) (hw.toLp _)
    rw [L2.inner_def] at hin2
    have e1 : ∫ x, inner ℝ ((hf.toLp f) x) ((hw.toLp _) x) ∂μ = ∫ x, f x * (u n x - v x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp, hw.coeFn_toLp] with x h1 h2
      rw [h1, h2]
      simp [mul_comm]
    rw [e1] at hin2
    have n1 : ‖hf.toLp f‖ = (eLpNorm f 2 μ).toReal := by
      rw [Lp.norm_toLp]
    have n2 : ‖hw.toLp _‖ = (eLpNorm (fun x => u n x - v x) 2 μ).toReal := by
      rw [Lp.norm_toLp]
    rw [n1, n2] at hin2
    exact hin2
  have hlim : Tendsto (fun n => (eLpNorm f 2 μ).toReal *
      (eLpNorm (fun x => u n x - v x) 2 μ).toReal) atTop (nhds 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    simpa using this.const_mul (eLpNorm f 2 μ).toReal
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
  simpa [Real.norm_eq_abs] using key n


theorem hotcov_fderiv_apply_const (a : Vec 2 → ℝ) (ha : ContDiff ℝ (⊤ : ℕ∞) a) (x : Vec 2) (i j : Fin 2) :
    (fderiv ℝ (fun y => (fderiv ℝ a y) (basisVec i)) x) (basisVec j) =
      (fderiv ℝ (fderiv ℝ a) x) (basisVec j) (basisVec i) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ a) := ha.fderiv_right (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ a) x := (h1.differentiable (by simp)).differentiableAt
  have := fderiv_clm_apply (c := fderiv ℝ a) (u := fun _ => basisVec i) (x := x) hd
    (differentiableAt_const _)
  rw [this]
  simp

theorem hotcov_approx_curl {U : Set (Vec 2)} (g : H1Function U) (a : Vec 2 → ℝ)
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hc : HasCompactSupport a) (hs : tsupport a ⊆ U) :
    ∫ x in U, g.grad x 1 * (fderiv ℝ a x) (basisVec 0) ∂volume =
      ∫ x in U, g.grad x 0 * (fderiv ℝ a x) (basisVec 1) ∂volume := by
  have hd : ∀ i : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun x => (fderiv ℝ a x) (basisVec i)) := by
    intro i
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ a) := ha.fderiv_right (by simp)
    exact h1.clm_apply contDiff_const
  have hcs : ∀ i : Fin 2, HasCompactSupport (fun x => (fderiv ℝ a x) (basisVec i)) :=
    fun i => hc.fderiv_apply ℝ (basisVec i)
  have hts : ∀ i : Fin 2, tsupport (fun x => (fderiv ℝ a x) (basisVec i)) ⊆ U := by
    intro i
    exact (tsupport_comp_subset (g := fun L : Vec 2 →L[ℝ] ℝ => L (basisVec i)) (by simp)
      (fderiv ℝ a)).trans ((tsupport_fderiv_subset ℝ).trans hs)
  have w1 := g.hasWeakGradient 1 _ (hd 0) (hcs 0) (hts 0)
  have w2 := g.hasWeakGradient 0 _ (hd 1) (hcs 1) (hts 1)
  simp only [hotcov_fderiv_apply_const a ha] at w1 w2
  have hsym : ∀ x, (fderiv ℝ (fderiv ℝ a) x) (basisVec 1) (basisVec 0) =
      (fderiv ℝ (fderiv ℝ a) x) (basisVec 0) (basisVec 1) := by
    intro x
    exact (ha.contDiffAt.isSymmSndFDerivAt (by simp [minSmoothness])) _ _
  simp only [hsym] at w1
  have := w1.symm.trans w2
  linarith

theorem hotcov_h10_h1_rotated_orth {U : Set (Vec 2)} (h : H10Function U) (g : H1Function U) :
    ∫ x in U, g.grad x 1 * h.toH1Function.grad x 0 ∂volume =
      ∫ x in U, g.grad x 0 * h.toH1Function.grad x 1 ∂volume := by
  have hDmem : ∀ n (i : Fin 2), MemLp (fun x => (fderiv ℝ (h.approx n) x) (basisVec i)) 2
      (volume.restrict U) := by
    intro n i
    have hc : Continuous (fun x => (fderiv ℝ (h.approx n) x) (basisVec i)) := by
      have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (h.approx n)) :=
        (h.approx_smooth n).fderiv_right (by simp)
      exact (h1.clm_apply contDiff_const).continuous
    exact hc.memLp_of_hasCompactSupport ((h.approx_hasCompactSupport n).fderiv_apply ℝ (basisVec i))
  have hlim1 := hotcov_tendsto_integral_mul (g.gradMemL2 1)
    (fun n => hDmem n 0) (h.toH1Function.gradMemL2 0) (h.tendsto_approx_grad 0)
  have hlim2 := hotcov_tendsto_integral_mul (g.gradMemL2 0)
    (fun n => hDmem n 1) (h.toH1Function.gradMemL2 1) (h.tendsto_approx_grad 1)
  have heq : ∀ n, (∫ x, g.grad x 1 * (fderiv ℝ (h.approx n) x) (basisVec 0) ∂(volume.restrict U)) =
      ∫ x, g.grad x 0 * (fderiv ℝ (h.approx n) x) (basisVec 1) ∂(volume.restrict U) :=
    fun n => hotcov_approx_curl g (h.approx n) (h.approx_smooth n) (h.approx_hasCompactSupport n)
      (h.approx_support_subset n)
  have hlim2' : Tendsto (fun n => ∫ x, g.grad x 1 * (fderiv ℝ (h.approx n) x) (basisVec 0)
      ∂(volume.restrict U)) atTop (nhds (∫ x, g.grad x 0 * h.toH1Function.grad x 1 ∂(volume.restrict U))) := by
    simpa only [heq] using hlim2
  exact tendsto_nhds_unique hlim1 hlim2'

/-- Exact zero identity for the rotated gradient pairing. -/
theorem hotcov_rot_grad_orth {U : Set (Vec 2)} (h : H10Function U) (g : H1Function U) :
    ∫ x in U, vecDot (planarQuarterTurn (h.toH1Function.grad x)) (g.grad x) ∂volume = 0 := by
  have h0 : Integrable (fun x => h.toH1Function.grad x 0 * g.grad x 1) (volume.restrict U) :=
    (h.toH1Function.gradMemL2 0).integrable_mul (g.gradMemL2 1)
  have h1 : Integrable (fun x => h.toH1Function.grad x 1 * g.grad x 0) (volume.restrict U) :=
    (h.toH1Function.gradMemL2 1).integrable_mul (g.gradMemL2 0)
  have heq : (fun x => vecDot (planarQuarterTurn (h.toH1Function.grad x)) (g.grad x)) =
      fun x => h.toH1Function.grad x 0 * g.grad x 1 - h.toH1Function.grad x 1 * g.grad x 0 := by
    funext x
    simp [vecDot, planarQuarterTurn, Fin.sum_univ_two]
    ring
  rw [heq, integral_sub h0 h1]
  have := hotcov_h10_h1_rotated_orth h g
  have c0 : ∫ x in U, h.toH1Function.grad x 0 * g.grad x 1 ∂volume =
      ∫ x in U, g.grad x 1 * h.toH1Function.grad x 0 ∂volume := by
    congr 1; funext x; ring
  have c1 : ∫ x in U, h.toH1Function.grad x 1 * g.grad x 0 ∂volume =
      ∫ x in U, g.grad x 0 * h.toH1Function.grad x 1 ∂volume := by
    congr 1; funext x; ring
  rw [c0, c1, this, sub_self]

/-- The same identity for any `H¹` function whose values are those of an `H¹₀`
function (zero trace in the sense of `MemH10`). -/
theorem hotcov_rot_grad_orth_of_memH10 {U : Set (Vec 2)} (hU : IsOpen U)
    [IsFiniteMeasure (volume.restrict U)]
    (f g : H1Function U) (hf : MemH10 U f.toFun) :
    ∫ x in U, vecDot (planarQuarterTurn (f.grad x)) (g.grad x) ∂volume = 0 := by
  obtain ⟨v, hv⟩ := hf
  have hae : ∀ i : Fin 2, (fun x => v.toH1Function.grad x i) =ᵐ[volume.restrict U]
      (fun x => f.grad x i) := by
    intro i
    apply HasWeakPartialDerivOn.ae_eq hU
    · exact IntegrableOn.locallyIntegrableOn ((v.toH1Function.gradMemL2 i).integrable one_le_two)
    · exact IntegrableOn.locallyIntegrableOn ((f.gradMemL2 i).integrable one_le_two)
    · exact v.toH1Function.hasWeakGradient i
    · have := f.hasWeakGradient i
      rw [← hv] at this
      exact this
  have heq : (fun x => vecDot (planarQuarterTurn (f.grad x)) (g.grad x)) =ᵐ[volume.restrict U]
      (fun x => vecDot (planarQuarterTurn (v.toH1Function.grad x)) (g.grad x)) := by
    have h0 := hae 0
    have h1 := hae 1
    filter_upwards [h0, h1] with x hx0 hx1
    simp only [vecDot, planarQuarterTurn, Fin.sum_univ_two] at *
    rw [hx0, hx1]
  rw [integral_congr_ae heq]
  exact hotcov_rot_grad_orth v g

end

end ASDExplicitGamma.Main
