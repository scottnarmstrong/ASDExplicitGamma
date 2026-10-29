module

public import ASDExplicitGamma.Cold.LipschitzWeakGradient
public import Homogenization.Sobolev.CubeEmbedding.Extension

/-! Bounded globally Lipschitz multipliers preserve `H¹` on the cube. -/

@[expose] public section

open MeasureTheory Filter Set Topology Homogenization
open scoped ENNReal NNReal

namespace ASDExplicitGamma.Scalar

theorem lipschitzOnWith_mul_bounded
    {d : ℕ} {U : Set (Vec d)} {f g : Vec d → ℝ}
    {Kf Kg Bf Bg : ℝ≥0}
    (hf : LipschitzOnWith Kf f U) (hg : LipschitzOnWith Kg g U)
    (hfb : ∀ x ∈ U, ‖f x‖ ≤ (Bf : ℝ))
    (hgb : ∀ x ∈ U, ‖g x‖ ≤ (Bg : ℝ)) :
    LipschitzOnWith (Bf * Kg + Bg * Kf) (fun x => f x * g x) U := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [dist_eq_norm, dist_eq_norm]
  have hfx := hf.dist_le_mul x hx y hy
  have hgx := hg.dist_le_mul x hx y hy
  rw [dist_eq_norm] at hfx hgx
  have hfactor : f x * g x - f y * g y =
      f x * (g x - g y) + (f x - f y) * g y := by ring
  rw [hfactor]
  calc
    ‖f x * (g x - g y) + (f x - f y) * g y‖
        ≤ ‖f x * (g x - g y)‖ + ‖(f x - f y) * g y‖ := norm_add_le _ _
    _ = ‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖ := by rw [norm_mul, norm_mul]
    _
        ≤ (Bf : ℝ) * ((Kg : ℝ) * ‖x - y‖) +
            ((Kf : ℝ) * ‖x - y‖) * (Bg : ℝ) := by
          apply add_le_add
          · calc
              ‖f x‖ * ‖g x - g y‖ ≤ (Bf : ℝ) * ‖g x - g y‖ :=
                mul_le_mul_of_nonneg_right (hfb x hx) (norm_nonneg _)
              _ ≤ (Bf : ℝ) * ((Kg : ℝ) * ‖x - y‖) :=
                mul_le_mul_of_nonneg_left hgx (by positivity)
          · calc
              ‖f x - f y‖ * ‖g y‖ ≤ ((Kf : ℝ) * ‖x - y‖) * ‖g y‖ :=
                mul_le_mul_of_nonneg_right hfx (norm_nonneg _)
              _ ≤ ((Kf : ℝ) * ‖x - y‖) * (Bg : ℝ) :=
                mul_le_mul_of_nonneg_left (hgb y hy) (by positivity)
    _ = ((Bf * Kg + Bg * Kf : ℝ≥0) : ℝ) * ‖x - y‖ := by
          simp only [NNReal.coe_add, NNReal.coe_mul]
          ring

/-- A bounded Lipschitz scalar multiplier acts on `H¹` on any bounded open
convex domain. The product rule follows by smooth approximation of the `H¹`
factor and closure of the weak-gradient graph in `L²`. -/
noncomputable def h1_mul_lipschitz
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (hne : U.Nonempty) (u : H1Function U) {φ : Vec d → ℝ} {C : ℝ≥0}
    (hφ : LipschitzWith C φ) : H1Function U := by
  classical
  let μ : Measure (Vec d) := volume.restrict U
  letI : IsFiniteMeasure μ := by
    simpa [μ] using hU.isFiniteMeasure_restrict_volume
  let hclosure : IsCompact (closure U) :=
    hU.isBoundedDomain.isBounded.isCompact_closure
  let hBφexists := hclosure.exists_bound_of_continuousOn hφ.continuous.continuousOn
  let Bφraw := Classical.choose hBφexists
  have hBφraw := Classical.choose_spec hBφexists
  let Bφ : ℝ≥0 := Real.toNNReal (max Bφraw 0)
  have hBφ : ∀ x ∈ closure U, ‖φ x‖ ≤ (Bφ : ℝ) := by
    intro x hx
    have h := hBφraw x hx
    have hle : ‖φ x‖ ≤ max Bφraw 0 := h.trans (le_max_left _ _)
    simpa [Bφ, Real.coe_toNNReal (max Bφraw 0) (le_max_right Bφraw 0)] using hle
  have hφtop : MemLp φ (⊤ : ENNReal) μ := by
    apply MemLp.of_bound hφ.continuous.aestronglyMeasurable (Bφ : ℝ)
    rw [ae_restrict_iff' hU.isOpen.measurableSet]
    exact Filter.Eventually.of_forall fun x hx => hBφ x (subset_closure hx)
  let Dφ : Vec d → Fin d → ℝ := fun x i =>
    ASDExplicitGamma.Cold.lipschitzWeakGradient φ x i
  have hDφtop (i : Fin d) : MemLp (fun x => Dφ x i) (⊤ : ENNReal) μ := by
    simpa [Dφ, ASDExplicitGamma.Cold.lipschitzWeakGradient] using
      (hφ.memLp_lineDeriv (μ := μ) (basisVec i))

  let x0 : Vec d := Classical.choose hne
  have hx0 : x0 ∈ U := Classical.choose_spec hne
  let hopen := Metric.isOpen_iff.mp hU.isOpen x0 hx0
  let r : ℝ := Classical.choose hopen
  have hr : 0 < r := (Classical.choose_spec hopen).1
  have hball0 : Metric.ball x0 r ⊆ U := (Classical.choose_spec hopen).2
  let r0 : ℝ := r / 2
  have hr0 : 0 < r0 := by dsimp [r0]; positivity
  have hball : Metric.closedBall x0 r0 ⊆ U := by
    refine (Metric.closedBall_subset_ball ?_).trans hball0
    dsimp [r0]
    linarith

  let ψ : ℕ → H1Function U := fun n =>
    H1Function.convexApproxSmoothH1 hU u x0 hr0 n
  have hψsmooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (ψ n).toFun := by
    dsimp [ψ]
    rw [H1Function.convexApproxSmoothH1_toFun]
    exact contDiff_convexApproxSmoothRepresentative hU.isOpen.measurableSet
      (isConvexApproxKernel_unitConvexApproxKernel (d := d))
      (by norm_num) u.memL2 hr0
      (H1Function.unitConvexApproxScale_pos_meanZero n)
  have hψsmoothVal (n : ℕ) :
      (ψ n).toFun = convexApproxSmoothRepresentative U
        (unitConvexApproxKernel (d := d)) u.toFun x0 r0
        (unitConvexApproxScale n) := by
    dsimp [ψ]
    exact H1Function.convexApproxSmoothH1_toFun hU u x0 hr0 n
  have hψgrad (n : ℕ) (x : Vec d) (i : Fin d) :
      (ψ n).grad x i = (fderiv ℝ (ψ n).toFun x) (basisVec i) := by
    have h := H1Function.convexApproxSmoothH1_grad hU u x0 hr0 n
    have hx := congrFun (congrFun h x) i
    simpa [ψ, hψsmoothVal n] using hx

  let prodLip : ℕ → ℝ≥0 := fun n => by
    let hKψexists := ((hψsmooth n).contDiffOn).exists_lipschitzOnWith
      (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ (0 : WithTop ℕ∞))
      (hU.convex.closure) hclosure
    let Kψraw := Classical.choose hKψexists
    have hKψraw := Classical.choose_spec hKψexists
    let Kψ : ℝ≥0 := Kψraw
    let hBψexists := hclosure.exists_bound_of_continuousOn
      (hψsmooth n).continuous.continuousOn
    let Bψraw := Classical.choose hBψexists
    have hBψraw := Classical.choose_spec hBψexists
    let Bψ : ℝ≥0 := Real.toNNReal (max Bψraw 0)
    have hBψ : ∀ x ∈ closure U, ‖(ψ n).toFun x‖ ≤ (Bψ : ℝ) := by
      intro x hx
      have h := hBψraw x hx
      have hle : ‖(ψ n).toFun x‖ ≤ max Bψraw 0 := h.trans (le_max_left _ _)
      simpa [Bψ, Real.coe_toNNReal (max Bψraw 0) (le_max_right Bψraw 0)] using hle
    let hψLipClosure : LipschitzOnWith Kψ (ψ n).toFun (closure U) := hKψraw
    let hψLipU : LipschitzOnWith Kψ (ψ n).toFun U :=
      hψLipClosure.mono subset_closure
    let hφLipU : LipschitzOnWith C φ U := hφ.lipschitzOnWith
    let hprod := lipschitzOnWith_mul_bounded hφLipU hψLipU
      (fun x hx => hBφ x (subset_closure hx))
      (fun x hx => hBψ x (subset_closure hx))
    exact Bφ * Kψ + Bψ * C

  have hprodLip (n : ℕ) : LipschitzOnWith (prodLip n)
      (fun x => φ x * (ψ n).toFun x) U := by
    dsimp [prodLip]
    let hKψexists := ((hψsmooth n).contDiffOn).exists_lipschitzOnWith
      (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ (0 : WithTop ℕ∞))
      (hU.convex.closure) hclosure
    let Kψraw := Classical.choose hKψexists
    have hKψraw := Classical.choose_spec hKψexists
    let Kψ : ℝ≥0 := Kψraw
    let hBψexists := hclosure.exists_bound_of_continuousOn
      (hψsmooth n).continuous.continuousOn
    let Bψraw := Classical.choose hBψexists
    have hBψraw := Classical.choose_spec hBψexists
    let Bψ : ℝ≥0 := Real.toNNReal (max Bψraw 0)
    have hBψ : ∀ x ∈ closure U, ‖(ψ n).toFun x‖ ≤ (Bψ : ℝ) := by
      intro x hx
      have h := hBψraw x hx
      have hle : ‖(ψ n).toFun x‖ ≤ max Bψraw 0 := h.trans (le_max_left _ _)
      simpa [Bψ, Real.coe_toNNReal (max Bψraw 0) (le_max_right Bψraw 0)] using hle
    have hψLipU : LipschitzOnWith Kψ (ψ n).toFun U :=
      hKψraw.mono subset_closure
    have hφLipU : LipschitzOnWith C φ U := hφ.lipschitzOnWith
    have hprod := lipschitzOnWith_mul_bounded hφLipU hψLipU
      (fun x hx => hBφ x (subset_closure hx))
      (fun x hx => hBψ x (subset_closure hx))
    simpa [prodLip, hBψ] using hprod

  let gext : ℕ → Vec d → ℝ := fun n => Classical.choose (hprodLip n).extend_real
  have hgextLip (n : ℕ) : LipschitzWith (prodLip n) (gext n) :=
    (Classical.choose_spec (hprodLip n).extend_real).1
  have hgextEq (n : ℕ) : EqOn (fun x => φ x * (ψ n).toFun x) (gext n) U :=
    (Classical.choose_spec (hprodLip n).extend_real).2

  let v (n : ℕ) : H1Function U := by
    letI : IsFiniteMeasure (volume.restrict U) := hU.isFiniteMeasure_restrict_volume
    let hBgexists := hclosure.exists_bound_of_continuousOn
      (hgextLip n).continuous.continuousOn
    let Bgraw := Classical.choose hBgexists
    have hBgraw := Classical.choose_spec hBgexists
    let Bg : ℝ := max Bgraw 0
    have hBg : ∀ x ∈ closure U, ‖gext n x‖ ≤ Bg := by
      intro x hx
      have h := hBgraw x hx
      exact h.trans (le_max_left _ _)
    have hmem : MemLp (gext n) 2 (volume.restrict U) := by
      apply MemLp.of_bound (hgextLip n).continuous.aestronglyMeasurable Bg
      rw [ae_restrict_iff' hU.isOpen.measurableSet]
      exact Filter.Eventually.of_forall fun x hx => hBg x (subset_closure hx)
    exact ASDExplicitGamma.Cold.lipschitzH1On U (hgextLip n) hmem

  have hvval (n : ℕ) : (v n).toFun =ᵐ[μ] fun x => φ x * (ψ n).toFun x := by
    filter_upwards [ae_restrict_mem hU.isOpen.measurableSet] with x hx
    exact (hgextEq n hx).symm

  have hvgrad (n : ℕ) (i : Fin d) : (fun x => (v n).grad x i) =ᵐ[μ]
      fun x => φ x * (ψ n).grad x i + (ψ n).toFun x * Dφ x i := by
    have hgderiv := ASDExplicitGamma.Cold.lipschitzWeakGradient_ae_eq_fderiv
      (hgextLip n)
    have hφderiv := ASDExplicitGamma.Cold.lipschitzWeakGradient_ae_eq_fderiv hφ
    have hφdiff := hφ.ae_differentiableAt (μ := volume)
    filter_upwards [ae_restrict_of_ae hgderiv, ae_restrict_of_ae hφderiv,
      ae_restrict_of_ae hφdiff, ae_restrict_mem hU.isOpen.measurableSet]
      with x hgn hφn hφdx hx
    have hψdx : DifferentiableAt ℝ (ψ n).toFun x :=
      (hψsmooth n).differentiable (by simp) x
    have hlocal : gext n =ᶠ[𝓝 x] fun y => φ y * (ψ n).toFun y := by
      filter_upwards [IsOpen.mem_nhds hU.isOpen hx] with y hy
      exact (hgextEq n hy).symm
    have hfd : fderiv ℝ (gext n) x =
        fderiv ℝ (fun y : Vec d => φ y * (ψ n).toFun y) x :=
      Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hlocal
    have hmul := fderiv_fun_mul hφdx hψdx
    have hψg := hψgrad n x i
    have hcoord := congrArg (fun T : Vec d →L[ℝ] ℝ => T (basisVec i)) (hfd.trans hmul)
    have hcoord' : (fderiv ℝ (gext n) x) (basisVec i) =
        φ x * (ψ n).grad x i + (ψ n).toFun x * Dφ x i := by
      calc
        (fderiv ℝ (gext n) x) (basisVec i) =
            (φ x • fderiv ℝ (ψ n).toFun x +
              (ψ n).toFun x • fderiv ℝ φ x) (basisVec i) := hcoord
        _ = φ x * (fderiv ℝ (ψ n).toFun x) (basisVec i) +
              (ψ n).toFun x * (fderiv ℝ φ x) (basisVec i) := by simp
        _ = φ x * (ψ n).grad x i + (ψ n).toFun x * Dφ x i := by
              rw [← hψg]
              dsimp [Dφ]
              rw [← hφn i]
    have hresult := (hgn i).trans hcoord'
    simpa [v, ASDExplicitGamma.Cold.lipschitzH1On,
      ASDExplicitGamma.Cold.lipschitzWeakGradient] using hresult

  have hmem : MemLp (fun x => φ x * u.toFun x) 2 μ :=
    hφtop.fun_mul (r := 2) u.memL2
  have hDmem (i : Fin d) : MemLp
      (fun x => φ x * u.grad x i + u.toFun x * Dφ x i) 2 μ := by
    have hfirst : MemLp (fun x => φ x * u.grad x i) 2 μ :=
      hφtop.fun_mul (r := 2) (u.gradMemL2 i)
    have hsecond : MemLp (fun x => u.toFun x * Dφ x i) 2 μ := by
      simpa [mul_comm] using (hDφtop i).fun_mul (r := 2) u.memL2
    exact hfirst.add hsecond

  have hψval : Tendsto (fun n => eLpNorm
      (fun x => (ψ n).toFun x - u.toFun x) 2 μ) atTop (𝓝 0) := by
    simpa [ψ, μ] using
      tendsto_eLpNorm_convexApproxSmoothH1 hU u hr0 hball
  have hψgradL2 (i : Fin d) : Tendsto (fun n => eLpNorm
      (fun x => (ψ n).grad x i - u.grad x i) 2 μ) atTop (𝓝 0) := by
    simpa [ψ, μ] using
      tendsto_eLpNorm_grad_convexApproxSmoothH1 hU u hr0 hball i

  have hlim : Tendsto
      (fun n => eLpNorm (fun x => (v n).toFun x - φ x * u.toFun x) 2 μ)
      atTop (𝓝 0) := by
    have hconst : Tendsto
        (fun n => eLpNorm φ ⊤ μ * eLpNorm
          (fun x => (ψ n).toFun x - u.toFun x) 2 μ) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hψval
        (Or.inr hφtop.eLpNorm_lt_top.ne)
    have hbound (n : ℕ) : eLpNorm
        (fun x => (v n).toFun x - φ x * u.toFun x) 2 μ ≤
        eLpNorm φ ⊤ μ * eLpNorm
          (fun x => (ψ n).toFun x - u.toFun x) 2 μ := by
      have hEq : (fun x => (v n).toFun x - φ x * u.toFun x) =ᵐ[μ]
          φ • (fun x => (ψ n).toFun x - u.toFun x) := by
        filter_upwards [hvval n] with x hx
        rw [hx]
        change φ x * (ψ n).toFun x - φ x * u.toFun x =
          φ x * ((ψ n).toFun x - u.toFun x)
        ring
      rw [eLpNorm_congr_ae hEq]
      exact eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm 2
        hφtop.aestronglyMeasurable
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hconst (fun n => zero_le) hbound

  have hDlim (i : Fin d) : Tendsto
      (fun n => eLpNorm (fun x => (v n).grad x i -
        (φ x * u.grad x i + u.toFun x * Dφ x i)) 2 μ) atTop (𝓝 0) := by
    let A : ℕ → Vec d → ℝ := fun n x =>
      φ x * ((ψ n).grad x i - u.grad x i)
    let B : ℕ → Vec d → ℝ := fun n x =>
      Dφ x i * ((ψ n).toFun x - u.toFun x)
    have hA (n : ℕ) : eLpNorm (A n) 2 μ ≤ eLpNorm φ ⊤ μ *
        eLpNorm (fun x => (ψ n).grad x i - u.grad x i) 2 μ :=
      eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm 2 hφtop.aestronglyMeasurable
    have hB (n : ℕ) : eLpNorm (B n) 2 μ ≤ eLpNorm (Dφ · i) ⊤ μ *
        eLpNorm (fun x => (ψ n).toFun x - u.toFun x) 2 μ :=
      eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm 2 (hDφtop i).aestronglyMeasurable
    have hAtend : Tendsto (fun n => eLpNorm (A n) 2 μ) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      · simpa using ENNReal.Tendsto.const_mul (hψgradL2 i)
          (Or.inr hφtop.eLpNorm_lt_top.ne)
      · exact fun n => zero_le
      · exact hA
    have hBtend : Tendsto (fun n => eLpNorm (B n) 2 μ) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      · simpa using ENNReal.Tendsto.const_mul hψval
          (Or.inr (hDφtop i).eLpNorm_lt_top.ne)
      · exact fun n => zero_le
      · exact hB
    have hsum := hAtend.add hBtend
    have hdecomp (n : ℕ) :
        (fun x => (v n).grad x i -
          (φ x * u.grad x i + u.toFun x * Dφ x i)) =ᵐ[μ] A n + B n := by
      filter_upwards [hvgrad n i] with x hx
      dsimp [A, B]
      rw [hx]
      ring
    have hbound (n : ℕ) : eLpNorm
        (fun x => (v n).grad x i -
          (φ x * u.grad x i + u.toFun x * Dφ x i)) 2 μ ≤
        eLpNorm (A n) 2 μ + eLpNorm (B n) 2 μ := by
      rw [eLpNorm_congr_ae (hdecomp n)]
      exact eLpNorm_add_le (by norm_num : (1 : ENNReal) ≤ 2)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds (by simpa using hsum) (fun n => zero_le) hbound

  exact ⟨fun x => φ x * u.toFun x,
    fun x i => φ x * u.grad x i + u.toFun x * Dφ x i,
    hmem, hDmem,
    HasWeakGradientOn.of_tendsto_eLpNorm_two hmem hDmem
      (fun n => (v n).memL2) (fun n => (v n).gradMemL2)
      (fun n => (v n).hasWeakGradient) hlim hDlim⟩

/-- The value representative chosen by `h1_mul_lipschitz` is the literal
pointwise product. -/
theorem h1_mul_lipschitz_toFun
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (hne : U.Nonempty) (u : H1Function U) {φ : Vec d → ℝ} {C : ℝ≥0}
    (hφ : LipschitzWith C φ) :
    (h1_mul_lipschitz hU hne u hφ).toFun = fun x => φ x * u.toFun x := by
  rfl

end ASDExplicitGamma.Scalar
