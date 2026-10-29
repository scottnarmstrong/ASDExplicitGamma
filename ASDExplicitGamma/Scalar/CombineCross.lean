module

public import ASDExplicitGamma.Scalar.CombineAdm

/-! The flat-leg cross term `⟪J s_def, N a⟫` of the actual NEW quartic: pathwise bound on Wick
truncations (with the AM-GM split), continuity of the truncations, measurability. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open Algsuperdiff.Section3 ASDExplicitGamma.Native ASDExplicitGamma.Inverse Filter
open scoped InnerProductSpace BigOperators ENNReal Topology

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

namespace Cfg''

variable (C : Cfg'') (m : ℤ)

/-- The cross term of the `n`-th Wick truncation of the defect source with the flat leg. -/
def crossTruncR (ω : Cutoff.CutoffSample 2) (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  ⟪C.Jop (C.sTruncR m ω n x), C.Nop m ω (C.aR m ω)⟫_ℝ

/-- The actual cross term `⟪J s_def, N a⟫`. -/
def crossActR (ω : Cutoff.CutoffSample 2) : ℝ :=
  ⟪C.Jop (C.sDefR m ω), C.Nop m ω (C.aR m ω)⟫_ℝ

theorem crossTruncR_tendsto (ω : Cutoff.CutoffSample 2) (x : ℕ → ℝ)
    (h : Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, x i • C.Hs i) Filter.atTop
      (nhds (C.z0 m ω))) :
    Filter.Tendsto (fun n => C.crossTruncR m ω n (fun i : Fin n => x i)) Filter.atTop
      (nhds (C.crossActR m ω)) := by
  have hs : Filter.Tendsto (fun n => C.sTruncR m ω n (fun i : Fin n => x i)) Filter.atTop
      (nhds (C.sDefR m ω)) := by
    have := sbil_tendsto C.Vm C.FlR (C.Bop (C.old m ω)) (C.U (C.old m ω)) C.σ h
    unfold sTruncR sDefR
    simpa only [Fin.sum_univ_eq_sum_range (fun i => x i • C.Hs i)] using this
  exact ((C.Jop.continuous.tendsto _).comp hs).inner tendsto_const_nhds

/-- The flat leg as a function of the fresh field `z`. -/
def aZ (z : C(closedRectangle C.a C.b C.c C.d, ℝ)) : C.Pr :=
  pureFluxBlockOperator 0 (C.Vm z) (C.σ • inr'' (Y := C.Ys) (C.FlR z))

theorem aZ_continuous : Continuous C.aZ := by
  have hcm : Continuous (fun z => pureFluxBlockOperator 0 (C.Vm z) :
      C(closedRectangle C.a C.b C.c C.d, ℝ) → (C.Pr →L[ℝ] C.Pr)) :=
    (blockCLM (Y := C.Ys) (X := C.Xs)).continuous.comp C.Vm.continuous
  exact hcm.clm_apply ((continuous_const (y := C.σ)).smul
    ((inr'' (Y := C.Ys)).continuous.comp C.FlR.continuous))

theorem crossTruncR_measurable (m : ℤ) (ell : ℤ) (hK : C.K ⊆ openCubeSet (originCube 2 ell))
    (n : ℕ) :
    Measurable (fun p : Cutoff.CutoffSample 2 × (ℕ → ℝ) =>
      C.crossTruncR m p.1 n (fun i : Fin n => p.2 i)) := by
  let Sq : C(closedRectangle C.a C.b C.c C.d, ℝ) × C(closedRectangle C.a C.b C.c C.d, ℝ) ×
      (Fin n → ℝ) → C.Pr := fun q =>
    ∑ i : Fin n, ∑ j : Fin n, (q.2.2 i * q.2.2 j) • C.TmR i j q.1
  have hS : Continuous Sq := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact ((((continuous_apply i).comp (continuous_snd.comp continuous_snd)).mul
      ((continuous_apply j).comp (continuous_snd.comp continuous_snd)))).smul
      ((C.TmR_continuous i j).comp continuous_fst)
  let Nq : C(closedRectangle C.a C.b C.c C.d, ℝ) × C(closedRectangle C.a C.b C.c C.d, ℝ) ×
      (Fin n → ℝ) → (C.Pr →L[ℝ] C.Pr) := fun q =>
    pureFluxBlockInverse C.α C.hα
      (physicalProjectedCoefficient C.Q C.σ C.hσ (C.Rest (q.1 + q.2.1)))
  have hN : Continuous Nq :=
    (blockInverse_continuous C.hα).comp
      ((projectedCoefficient_continuous C.Q C.σ C.hσ).comp (C.Rest.continuous.comp
        (continuous_fst.add (continuous_fst.comp continuous_snd))))
  have hA : Continuous (fun q : C(closedRectangle C.a C.b C.c C.d, ℝ) ×
      C(closedRectangle C.a C.b C.c C.d, ℝ) × (Fin n → ℝ) => C.aZ q.2.1) :=
    C.aZ_continuous.comp (continuous_fst.comp continuous_snd)
  have hG : Continuous (fun q => ⟪C.Jop (Sq q), Nq q (C.aZ q.2.1)⟫_ℝ) :=
    Continuous.inner (C.Jop.continuous.comp hS) (hN.clm_apply hA)
  have hmeas : Measurable (fun p : Cutoff.CutoffSample 2 × (ℕ → ℝ) =>
      (C.old m p.1, C.z0 m p.1, fun i : Fin n => p.2 i)) := by
    refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
    · exact (measurable_olderField C.K ell m hK).comp measurable_fst
    · exact (measurable_shellFieldScalarRestriction C.K).comp
        ((measurable_pi_apply (m + 1)).comp (measurable_subtype_coe.comp measurable_fst))
    · exact measurable_pi_iff.2 fun i => (measurable_pi_apply (i : ℕ)).comp measurable_snd
  have := hG.measurable.comp hmeas
  convert this using 1
  funext p
  unfold crossTruncR
  rw [sTruncR_eq, Nop_eq_old_add]
  rfl

theorem crossActR_measurable (m : ℤ) (ell : ℤ) (hK : C.K ⊆ openCubeSet (originCube 2 ell)) :
    Measurable (fun ω : Cutoff.CutoffSample 2 => C.crossActR m ω) := by
  let Sq : C(closedRectangle C.a C.b C.c C.d, ℝ) × C(closedRectangle C.a C.b C.c C.d, ℝ) →
      C.Pr := fun q =>
    pureFluxBlockOperator 0 (C.Vm q.2) (C.Bop q.1 (pureFluxBlockOperator 0 (C.Vm q.2)
      (C.U q.1)) - C.σ • inr'' (Y := C.Ys) (C.FlR q.2))
  have hcm : Continuous (fun z => pureFluxBlockOperator 0 (C.Vm z) :
      C(closedRectangle C.a C.b C.c C.d, ℝ) → (C.Pr →L[ℝ] C.Pr)) :=
    (blockCLM (Y := C.Ys) (X := C.Xs)).continuous.comp C.Vm.continuous
  have hS : Continuous Sq := by
    have h1 : Continuous (fun q : C(closedRectangle C.a C.b C.c C.d, ℝ) ×
        C(closedRectangle C.a C.b C.c C.d, ℝ) => pureFluxBlockOperator 0 (C.Vm q.2)) :=
      hcm.comp continuous_snd
    have hsm : Continuous (fun q : C(closedRectangle C.a C.b C.c C.d, ℝ) ×
        C(closedRectangle C.a C.b C.c C.d, ℝ) => C.σ • inr'' (Y := C.Ys) (C.FlR q.2)) :=
      (continuous_const (y := C.σ)).smul ((inr'' (Y := C.Ys)).continuous.comp
        (C.FlR.continuous.comp continuous_snd))
    exact h1.clm_apply (((C.Bop_continuousR.comp continuous_fst).clm_apply
      (h1.clm_apply (C.U_continuousR.comp continuous_fst))).sub hsm)
  let Nq : C(closedRectangle C.a C.b C.c C.d, ℝ) × C(closedRectangle C.a C.b C.c C.d, ℝ) →
      (C.Pr →L[ℝ] C.Pr) := fun q =>
    pureFluxBlockInverse C.α C.hα
      (physicalProjectedCoefficient C.Q C.σ C.hσ (C.Rest (q.1 + q.2)))
  have hN : Continuous Nq :=
    (blockInverse_continuous C.hα).comp
      ((projectedCoefficient_continuous C.Q C.σ C.hσ).comp (C.Rest.continuous.comp
        (continuous_fst.add continuous_snd)))
  have hA : Continuous (fun q : C(closedRectangle C.a C.b C.c C.d, ℝ) ×
      C(closedRectangle C.a C.b C.c C.d, ℝ) => C.aZ q.2) :=
    C.aZ_continuous.comp continuous_snd
  have hG : Continuous (fun q => ⟪C.Jop (Sq q), Nq q (C.aZ q.2)⟫_ℝ) :=
    Continuous.inner (C.Jop.continuous.comp hS) (hN.clm_apply hA)
  have hmeas : Measurable (fun ω : Cutoff.CutoffSample 2 => (C.old m ω, C.z0 m ω)) := by
    refine Measurable.prodMk ?_ ?_
    · exact measurable_olderField C.K ell m hK
    · exact (measurable_shellFieldScalarRestriction C.K).comp
        ((measurable_pi_apply (m + 1)).comp measurable_subtype_coe)
  have := hG.measurable.comp hmeas
  convert this using 1
  funext ω
  unfold crossActR sDefR
  rw [Nop_eq_old_add]
  rw [sbil_apply, delta_apply']
  rfl

end Cfg''

end

end ASDExplicitGamma.Scalar
