module

public import Homogenization.Sobolev.H1.Algebra.H1Function
public import Homogenization.Sobolev.Truncation.WeakGradientLimit
public import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Convergence
public import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.SmoothRepresentative

/-! Multiplication of an H¹ factor by a bounded C¹ scalar multiplier. -/

@[expose] public section

open Homogenization MeasureTheory Filter
open scoped ENNReal

namespace ASDExplicitGamma.Scalar

/-- A C¹ function and its first derivatives are bounded on bounded open
convex domains, hence belong to L∞ there. -/
theorem contDiffOne_memLpTop_of_bounded_open_domain
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ 1 φ) :
    MemLp φ (⊤ : ENNReal) (MeasureTheory.volume.restrict U) ∧
      ∀ i : Fin d,
        MemLp (fun x => (fderiv ℝ φ x) (basisVec i)) (⊤ : ENNReal)
          (MeasureTheory.volume.restrict U) := by
  letI : IsFiniteMeasure (MeasureTheory.volume.restrict U) :=
    hU.isFiniteMeasure_restrict_volume
  let hclosure : IsCompact (closure U) :=
    hU.isBoundedDomain.isBounded.isCompact_closure
  let C : ℝ := Classical.choose
    (hclosure.exists_bound_of_continuousOn hφ.continuous.continuousOn)
  have hC : ∀ x ∈ closure U, ‖φ x‖ ≤ C :=
    Classical.choose_spec
      (hclosure.exists_bound_of_continuousOn hφ.continuous.continuousOn)
  refine ⟨?_, ?_⟩
  · apply MemLp.of_bound hφ.continuous.aestronglyMeasurable C
    rw [ae_restrict_iff' hU.isOpen.measurableSet]
    exact Filter.Eventually.of_forall fun x hx => hC x (subset_closure hx)
  · intro i
    have hDi : Continuous (fun x => (fderiv ℝ φ x) (basisVec i)) := by
      exact (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
    let Ci : ℝ := Classical.choose
      (hclosure.exists_bound_of_continuousOn hDi.continuousOn)
    have hCi : ∀ x ∈ closure U,
        ‖(fderiv ℝ φ x) (basisVec i)‖ ≤ Ci :=
      Classical.choose_spec
        (hclosure.exists_bound_of_continuousOn hDi.continuousOn)
    apply MemLp.of_bound hDi.aestronglyMeasurable Ci
    rw [ae_restrict_iff' hU.isOpen.measurableSet]
    exact Filter.Eventually.of_forall fun x hx => hCi x (subset_closure hx)

/-- A bounded C¹ multiplier preserves H¹ on a bounded open convex domain.
The weak product rule is obtained by multiplying the smooth convex-domain
approximants of the H¹ factor and closing the weak-gradient graph in L². -/
noncomputable def h1_mul_contDiffOne_memLpTop
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (hne : U.Nonempty) (u : H1Function U) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ 1 φ)
    (hφ_top : MemLp φ (⊤ : ENNReal) (MeasureTheory.volume.restrict U))
    (hDφ_top : ∀ i : Fin d,
      MemLp (fun x => (fderiv ℝ φ x) (basisVec i)) (⊤ : ENNReal)
        (MeasureTheory.volume.restrict U)) : H1Function U := by
  classical
  let μU : MeasureTheory.Measure (Vec d) := MeasureTheory.volume.restrict U
  let ρ : Vec d → ℝ := unitConvexApproxKernel
  let ε : ℕ → ℝ := unitConvexApproxScale
  let x0 : Vec d := Classical.choose hne
  have hx0 : x0 ∈ U := Classical.choose_spec hne
  have hr_exists : ∃ r : ℝ, 0 < r ∧ Metric.ball x0 r ⊆ U :=
    Metric.mem_nhds_iff.mp (hU.isOpen.mem_nhds hx0)
  let r : ℝ := Classical.choose hr_exists
  have hr_data : 0 < r ∧ Metric.ball x0 r ⊆ U := Classical.choose_spec hr_exists
  have hr : 0 < r := hr_data.1
  have hball0 : Metric.ball x0 r ⊆ U := hr_data.2
  let r0 : ℝ := r / 2
  have hr0 : 0 < r0 := by
    dsimp [r0]
    positivity
  have hball : Metric.closedBall x0 r0 ⊆ U := by
    refine (Metric.closedBall_subset_ball ?_).trans hball0
    dsimp [r0]
    exact half_lt_self hr
  let ψ : ℕ → Vec d → ℝ := fun n =>
    convexApproxSmoothRepresentative U ρ u.toFun x0 r0 (ε n)
  have hρ : IsConvexApproxKernel ρ := by
    simpa [ρ] using isConvexApproxKernel_unitConvexApproxKernel (d := d)
  have hε_pos : ∀ n : ℕ, 0 < ε n := by
    intro n
    dsimp [ε, unitConvexApproxScale]
    positivity
  have hε_eventually_lt_one : ∀ᶠ n : ℕ in atTop, ε n < 1 := by
    simpa [ε] using
      (((tendsto_order.1 tendsto_unitConvexApproxScale_zero).2 1 zero_lt_one).mono
        (fun _ hn => hn))
  have hψ_smooth : ∀ n : ℕ, ContDiff ℝ (⊤ : ℕ∞) (ψ n) := by
    intro n
    dsimp [ψ]
    exact contDiff_convexApproxSmoothRepresentative
      hU.isOpen.measurableSet hρ (by norm_num : (1 : ENNReal) ≤ 2)
      u.memL2 hr0 (hε_pos n)
  have hψ_memL2 : ∀ n : ℕ, MemLp (ψ n) 2 μU := by
    intro n
    let v : H1Function U :=
      H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU
        ((hψ_smooth n).of_le (by simp))
    simpa [ψ, v, H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
      H1Function.ofContDiffOnIsSobolevRegularDomain, μU] using v.memL2
  have hψ_grad_memL2 : ∀ n : ℕ, ∀ i : Fin d,
      MemLp (fun x => (fderiv ℝ (ψ n) x) (basisVec i)) 2 μU := by
    intro n i
    let v : H1Function U :=
      H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU
        ((hψ_smooth n).of_le (by simp))
    simpa [ψ, v, H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
      H1Function.ofContDiffOnIsSobolevRegularDomain, μU] using v.gradMemL2 i
  have hψ_tendsto :
      Tendsto (fun n => eLpNorm (fun x => ψ n x - u.toFun x) 2 μU)
        atTop (nhds 0) := by
    have hraw := tendsto_eLpNorm_sub_zero_unitConvexApproxSequence_of_memLpOn
      (U := U) hU (by norm_num : (1 : ENNReal) ≤ 2)
      (by simp : (2 : ENNReal) ≠ ⊤) u.memL2 hball hr0
    refine hraw.congr' ?_
    filter_upwards [hε_eventually_lt_one] with n hε1
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem hU.isOpen.measurableSet] with x hx
    have hEq := convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
      (u := u.toFun) hU hρ hx hball hr0 (hε_pos n) hε1
    simpa [ψ, ρ, ε, unitConvexApproxSequence] using hEq.symm
  have hψ_grad_tendsto : ∀ i : Fin d,
      Tendsto (fun n => eLpNorm
        (fun x => (fderiv ℝ (ψ n) x) (basisVec i) - u.grad x i) 2 μU)
        atTop (nhds 0) := by
    intro i
    have hraw := tendsto_eLpNorm_sub_zero_one_sub_mul_unitConvexApproxSequence_of_memLpOn
      (U := U) hU (by norm_num : (1 : ENNReal) ≤ 2)
      (by simp : (2 : ENNReal) ≠ ⊤) (u.grad_memL2 i) hball hr0
    refine hraw.congr' ?_
    filter_upwards [hε_eventually_lt_one] with n hε1
    apply eLpNorm_congr_ae
    have hbridge := ae_eq_fderiv_convexApproxSmoothRepresentative_apply_basisVec
      (U := U) (ρ := ρ) (u := u.toFun) (gi := fun y => u.grad y i)
      (i := i) (p := (2 : ENNReal)) hU hρ
      (by norm_num : (1 : ENNReal) ≤ 2) u.memL2 (u.grad_memL2 i)
      (u.hasWeakGradient i) hball hr0 (hε_pos n) hε1
    filter_upwards [hbridge, ae_restrict_mem hU.isOpen.measurableSet]
      with x hx hxU
    have hEq := convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
      (u := fun y => u.grad y i) hU hρ hxU hball hr0 (hε_pos n) hε1
    rw [hx]
    simpa [ψ, ρ, ε, unitConvexApproxSequence] using congrArg
      (fun t : ℝ => (1 - unitConvexApproxScale n) * t - u.grad x i) hEq.symm
  let Dφ : Vec d → Vec d := fun x i => (fderiv ℝ φ x) (basisVec i)
  let v (n : ℕ) : H1Function U :=
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU
      ((hφ.mul ((hψ_smooth n).of_le (by simp))))
  have hv (n : ℕ) : (v n).toFun = fun x => φ x * ψ n x := rfl
  have hDv (n : ℕ) : (v n).grad = fun x i =>
      φ x * (fderiv ℝ (ψ n) x) (basisVec i) + ψ n x * Dφ x i := by
    funext x
    funext i
    change (fderiv ℝ (fun y => φ y * ψ n y) x) (basisVec i) = _
    have hφdiff : DifferentiableAt ℝ φ x :=
      (hφ.differentiable (by norm_num)).differentiableAt
    have hψC1 : ContDiff ℝ 1 (ψ n) :=
      (hψ_smooth n).of_le (by norm_num)
    have hψdiff : DifferentiableAt ℝ (ψ n) x :=
      (hψC1.differentiable (by norm_num)).differentiableAt
    rw [fderiv_fun_mul hφdiff hψdiff]
    simp [Dφ]
  have hmem : MemLp (fun x => φ x * u.toFun x) 2 μU :=
    hφ_top.fun_mul (r := 2) u.memL2
  have hDmem (i : Fin d) : MemLp
      (fun x => φ x * u.grad x i + u.toFun x * Dφ x i) 2 μU := by
    have hfirst : MemLp (fun x => φ x * u.grad x i) 2 μU :=
      hφ_top.fun_mul (r := 2) (u.grad_memL2 i)
    have hsecond : MemLp (fun x => u.toFun x * Dφ x i) 2 μU := by
      simpa [Dφ, mul_comm] using (hDφ_top i).fun_mul (r := 2) u.memL2
    exact hfirst.add hsecond
  have hlim : Tendsto
      (fun n => eLpNorm (fun x => (v n).toFun x - φ x * u.toFun x) 2 μU)
      atTop (nhds 0) := by
    have hconst : Tendsto
        (fun n => eLpNorm φ ⊤ μU * eLpNorm (fun x => ψ n x - u.toFun x) 2 μU)
        atTop (nhds 0) := by
      simpa using ENNReal.Tendsto.const_mul hψ_tendsto
        (Or.inr hφ_top.eLpNorm_lt_top.ne)
    have hbound (n : ℕ) : eLpNorm
        (fun x => (v n).toFun x - φ x * u.toFun x) 2 μU ≤
        eLpNorm φ ⊤ μU * eLpNorm (fun x => ψ n x - u.toFun x) 2 μU := by
      have hEq : (fun x => (v n).toFun x - φ x * u.toFun x) =
          φ • (fun x => ψ n x - u.toFun x) := by
        funext x
        rw [hv]
        dsimp
        ring
      rw [hEq]
      exact eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm 2 hφ_top.aestronglyMeasurable
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hconst (fun n => zero_le) hbound
  have hDlim (i : Fin d) : Tendsto
      (fun n => eLpNorm
        (fun x => (v n).grad x i -
          (φ x * u.grad x i + u.toFun x * Dφ x i)) 2 μU)
      atTop (nhds 0) := by
    let A : ℕ → Vec d → ℝ := fun n x =>
      φ x * ((fderiv ℝ (ψ n) x) (basisVec i) - u.grad x i)
    let B : ℕ → Vec d → ℝ := fun n x =>
      Dφ x i * (ψ n x - u.toFun x)
    have hA (n : ℕ) : eLpNorm (A n) 2 μU ≤
        eLpNorm φ ⊤ μU * eLpNorm
          (fun x => (fderiv ℝ (ψ n) x) (basisVec i) - u.grad x i) 2 μU := by
      exact eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm 2 hφ_top.aestronglyMeasurable
    have hB (n : ℕ) : eLpNorm (B n) 2 μU ≤
        eLpNorm (Dφ · i) ⊤ μU * eLpNorm
          (fun x => ψ n x - u.toFun x) 2 μU := by
      calc
        eLpNorm (B n) 2 μU = eLpNorm
            ((Dφ · i) • (fun x => ψ n x - u.toFun x)) 2 μU := by
          rfl
        _ ≤ eLpNorm (Dφ · i) ⊤ μU * eLpNorm
            (fun x => ψ n x - u.toFun x) 2 μU :=
          eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm 2
            (hDφ_top i).aestronglyMeasurable
    have hA_tendsto : Tendsto (fun n => eLpNorm (A n) 2 μU) atTop (nhds 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds
        (by
          simpa using ENNReal.Tendsto.const_mul (hψ_grad_tendsto i)
            (Or.inr hφ_top.eLpNorm_lt_top.ne))
        (fun n => zero_le) hA
    have hB_tendsto : Tendsto (fun n => eLpNorm (B n) 2 μU) atTop (nhds 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds
        (by
          simpa using ENNReal.Tendsto.const_mul hψ_tendsto
            (Or.inr (hDφ_top i).eLpNorm_lt_top.ne))
        (fun n => zero_le) hB
    have hsum := hA_tendsto.add hB_tendsto
    have hdecomp (n : ℕ) :
        (fun x => (v n).grad x i -
          (φ x * u.grad x i + u.toFun x * Dφ x i)) = A n + B n := by
      funext x
      rw [hDv n]
      dsimp [A, B, Dφ]
      ring
    have hbound (n : ℕ) : eLpNorm
        (fun x => (v n).grad x i -
          (φ x * u.grad x i + u.toFun x * Dφ x i)) 2 μU ≤
        eLpNorm (A n) 2 μU + eLpNorm (B n) 2 μU := by
      rw [hdecomp n]
      exact eLpNorm_add_le (by norm_num : (1 : ENNReal) ≤ 2)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds (by simpa using hsum) (fun n => zero_le) hbound
  refine ⟨fun x => φ x * u.toFun x,
    fun x i => φ x * u.grad x i + u.toFun x * Dφ x i,
    hmem, hDmem,
    HasWeakGradientOn.of_tendsto_eLpNorm_two hmem hDmem
      (fun n => (v n).memL2) (fun n => (v n).gradMemL2)
      (fun n => (v n).hasWeakGradient) hlim hDlim⟩

end ASDExplicitGamma.Scalar
