module

public import ASDExplicitGamma.Scalar.RefSnId

/-! Successor of the actual defect diagonal and its measurability. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open Algsuperdiff.Section3 ASDExplicitGamma.Native ASDExplicitGamma.Inverse Filter
open scoped InnerProductSpace BigOperators ENNReal Topology

noncomputable section

namespace Cfg''

variable (C : Cfg'') (m : ℤ)

/-- The physical defect source `s_def = C δu₁`. -/
def sDefR (ω : Cutoff.CutoffSample 2) : C.Pr :=
  sbil C.Vm C.FlR (C.Bop (C.old m ω)) (C.U (C.old m ω)) C.σ (C.z0 m ω) (C.z0 m ω)

/-- The actual defect diagonal `⟪J s_def, N s_def⟫`. -/
def DactR (ω : Cutoff.CutoffSample 2) : ℝ :=
  ⟪C.Jop (C.sDefR m ω), C.Nop m ω (C.sDefR m ω)⟫_ℝ

/-- The `n`-th Wick truncation of the defect source. -/
def sTruncR (ω : Cutoff.CutoffSample 2) (n : ℕ) (x : Fin n → ℝ) : C.Pr :=
  sbil C.Vm C.FlR (C.Bop (C.old m ω)) (C.U (C.old m ω)) C.σ (∑ i : Fin n, x i • C.Hs i)
    (∑ i : Fin n, x i • C.Hs i)

def DtruncR (ω : Cutoff.CutoffSample 2) (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  ⟪C.Jop (C.sTruncR m ω n x), C.Nop m ω (C.sTruncR m ω n x)⟫_ℝ

theorem DtruncR_le (M : ABKModel 2) (hν : C.ν = M.nu) (hσ' : C.σ = (Annealed.sigmaBar M m : ℝ))
    (ell : ℤ) (hK : C.K ⊆ openCubeSet (originCube 2 ell))
    (ω : Cutoff.CutoffSample 2) (n : ℕ) (x : Fin n → ℝ) :
    C.DtruncR m ω n x ≤
      (44 / 25 : ℝ) * ((volume (openCubeSet C.Q)).toReal *
        (bnew M m C.Q ω *
          (tiledPositiveEnergy C.Q 134 (psdDefectSource (C.BFoR (C.old m ω) n) x) +
           tiledPositiveEnergy C.Q 134 (psdDefectSource (C.BGoR (C.old m ω) n) x)))) := by
  have hsn := C.sn_identR (C.old m ω) n x
  have hF := C.BFoR_memL2 (C.old m ω) n x
  have hG := C.BGoR_memL2 (C.old m ω) n x
  have hB := Bnew_cell_bound M ell m C.Q ω C.K C.hQcl hK
  rw [← hν, ← hσ'] at hB
  have hFc := tiled_vec_admissible C.Q 134 (psdDefectSource (C.BFoR (C.old m ω) n) x)
  have hGc := tiled_vec_admissible C.Q 134 (psdDefectSource (C.BGoR (C.old m ω) n) x)
  have main := paired_two_slot_new_inverse_bound C.Q 134 C.hν C.hσ
    (C.Rest (modelInsertedScalar C.K m 1 ω)) hF hG hFc hGc hB
  unfold DtruncR sTruncR
  rw [hsn, Nop_eq]
  exact main

theorem DtruncR_tendsto (ω : Cutoff.CutoffSample 2) (x : ℕ → ℝ)
    (h : Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, x i • C.Hs i) Filter.atTop
      (nhds (C.z0 m ω))) :
    Filter.Tendsto (fun n => C.DtruncR m ω n (fun i : Fin n => x i)) Filter.atTop
      (nhds (C.DactR m ω)) := by
  have hs : Filter.Tendsto (fun n => C.sTruncR m ω n (fun i : Fin n => x i)) Filter.atTop
      (nhds (C.sDefR m ω)) := by
    have := sbil_tendsto C.Vm C.FlR (C.Bop (C.old m ω)) (C.U (C.old m ω)) C.σ h
    unfold sTruncR sDefR
    simpa only [Fin.sum_univ_eq_sum_range (fun i => x i • C.Hs i)] using this
  exact pairing_tendsto (C.Jop) (C.Nop m ω) hs


theorem Aold_continuousR : Continuous C.Aold :=
  (projectedCoefficient_continuous C.Q C.σ C.hσ).comp C.Rest.continuous

theorem Bop_continuousR : Continuous C.Bop :=
  (blockInverse_continuous C.hα).comp C.Aold_continuousR

theorem U_continuousR : Continuous C.U :=
  (C.Bop_continuousR).clm_apply continuous_const

/-- The mode pair `C_i δu_j` as a function of the OLD field. -/
def TmR (i j : ℕ) (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) : C.Pr :=
  pureFluxBlockOperator 0 (C.Vm (C.Hs i)) (C.deltaR old j)

theorem deltaR_continuous (j : ℕ) : Continuous (fun old => C.deltaR old j) := by
  have h : (fun old => C.deltaR old j) = fun old =>
      C.Bop old (pureFluxBlockOperator 0 (C.Vm (C.Hs j)) (C.U old)) -
        C.σ • inr'' (Y := C.Ys) (C.FlR (C.Hs j)) := by
    funext old
    exact delta_apply' C.Vm C.FlR (C.Bop old) (C.U old) C.σ (C.Hs j)
  rw [h]
  exact ((C.Bop_continuousR).clm_apply (continuous_const.clm_apply C.U_continuousR)).sub
    continuous_const

theorem TmR_continuous (i j : ℕ) : Continuous (C.TmR i j) :=
  continuous_const.clm_apply (C.deltaR_continuous j)

theorem sTruncR_eq (m : ℤ) (ω : Cutoff.CutoffSample 2) (n : ℕ) (x : Fin n → ℝ) :
    C.sTruncR m ω n x = ∑ i : Fin n, ∑ j : Fin n, (x i * x j) • C.TmR i j (C.old m ω) := by
  unfold sTruncR
  rw [sbil_expand]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [sbil_apply]
  rfl

theorem DtruncR_measurable (m : ℤ) (ell : ℤ) (hK : C.K ⊆ openCubeSet (originCube 2 ell)) (n : ℕ) :
    Measurable (fun p : Cutoff.CutoffSample 2 × (ℕ → ℝ) =>
      C.DtruncR m p.1 n (fun i : Fin n => p.2 i)) := by
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
  have hG : Continuous (fun q => ⟪C.Jop (Sq q), Nq q (Sq q)⟫_ℝ) :=
    Continuous.inner (C.Jop.continuous.comp hS) (hN.clm_apply hS)
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
  unfold DtruncR
  rw [sTruncR_eq, Nop_eq_old_add]
  rfl

theorem DactR_measurable (m : ℤ) (ell : ℤ) (hK : C.K ⊆ openCubeSet (originCube 2 ell)) :
    Measurable (fun ω : Cutoff.CutoffSample 2 => C.DactR m ω) := by
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
  have hG : Continuous (fun q => ⟪C.Jop (Sq q), Nq q (Sq q)⟫_ℝ) :=
    Continuous.inner (C.Jop.continuous.comp hS) (hN.clm_apply hS)
  have hmeas : Measurable (fun ω : Cutoff.CutoffSample 2 => (C.old m ω, C.z0 m ω)) := by
    refine Measurable.prodMk ?_ ?_
    · exact measurable_olderField C.K ell m hK
    · exact (measurable_shellFieldScalarRestriction C.K).comp
        ((measurable_pi_apply (m + 1)).comp measurable_subtype_coe)
  have := hG.measurable.comp hmeas
  convert this using 1
  funext ω
  unfold DactR sDefR
  rw [Nop_eq_old_add]
  rw [sbil_apply, delta_apply']
  rfl


end Cfg''

end

end ASDExplicitGamma.Scalar
