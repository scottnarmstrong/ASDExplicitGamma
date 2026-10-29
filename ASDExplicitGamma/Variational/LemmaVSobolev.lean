module

public import ASDExplicitGamma.Variational.LemmaVLift
public import Homogenization.Sobolev.Truncation.H10Limit
public import Homogenization.Sobolev.Truncation.Basic

/-! Multiplication of a zero-trace residual by a bounded weakly differentiable
scalar multiplier. Used for the W¹,∞ column-divergence lift. -/

@[expose] public section

namespace ASDExplicitGamma.Variational

open Homogenization MeasureTheory Filter Topology
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

noncomputable section

/-- Multiplication by an L∞ function preserves L² convergence. -/
theorem lemmaV_tendsto_mul_L2 {d : ℕ} {U : Set (Vec d)}
    {b f : Vec d → ℝ} {F : ℕ → Vec d → ℝ}
    (hb : MemLp b (⊤ : ENNReal) (volume.restrict U))
    (hF : Tendsto (fun n => eLpNorm (fun x => F n x - f x) 2 (volume.restrict U))
      atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => b x * F n x - b x * f x)
      2 (volume.restrict U)) atTop (𝓝 0) := by
  have ht := ENNReal.Tendsto.const_mul hF (Or.inr hb.eLpNorm_lt_top.ne)
  simp only [mul_zero] at ht
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun n => zero_le) (fun n => ?_)
  have heq : (fun x => b x * F n x - b x * f x) =
      b • (fun x => F n x - f x) := by
    funext x
    change b x * F n x - b x * f x = b x * (F n x - f x)
    ring
  rw [heq]
  exact eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm 2 hb.aestronglyMeasurable

/-- Addition preserves L² convergence, with the differences kept explicit. -/
theorem lemmaV_tendsto_add_L2 {d : ℕ} {U : Set (Vec d)}
    {f g : Vec d → ℝ} {F G : ℕ → Vec d → ℝ}
    (hF : Tendsto (fun n => eLpNorm (fun x => F n x - f x) 2 (volume.restrict U))
      atTop (𝓝 0))
    (hG : Tendsto (fun n => eLpNorm (fun x => G n x - g x) 2 (volume.restrict U))
      atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => (F n x + G n x) - (f x + g x))
      2 (volume.restrict U)) atTop (𝓝 0) := by
  have ht := hF.add hG
  simp only [add_zero] at ht
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun n => zero_le) (fun n => ?_)
  have heq : (fun x => (F n x + G n x) - (f x + g x)) =
      (fun x => F n x - f x) + (fun x => G n x - g x) := by
    funext x
    simp only [Pi.add_apply]
    ring
  rw [heq]
  exact eLpNorm_add_le (by norm_num)

/-- The product of an H¹₀ residual and a W¹,∞ scalar has an H¹₀ witness
with the usual product gradient, almost everywhere. No smoothness of the
multiplier is assumed. -/
theorem lemmaV_exists_H10_mul {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (r : H10Function U) (η : H1Function U)
    (hη : MemLp η (⊤ : ENNReal) (volume.restrict U))
    (hDη : ∀ i, MemLp (fun x => η.grad x i) (⊤ : ENNReal) (volume.restrict U)) :
    ∃ t : H10Function U,
      t.toH1Function.toFun = (fun x => η x * r x) ∧
      t.toH1Function.grad =ᵐ[volume.restrict U]
        (fun x i => η x * r.toH1Function.grad x i + r x * η.grad x i) := by
  let F : ℕ → H1Function U := fun n =>
    η.mulContDiffHasCompactSupport (r.approx_smooth n) (r.approx_hasCompactSupport n)
  let f : Vec d → ℝ := fun x => η x * r x
  let Df : Vec d → Vec d := fun x i =>
    η x * r.toH1Function.grad x i + r x * η.grad x i
  have hf : MemLp f 2 (volume.restrict U) := hη.fun_mul r.memL2
  have hDf : GradMemL2On U Df := by
    intro i
    exact (hη.fun_mul (r.gradMemL2 i)).add ((r.memL2).fun_mul (hDη i))
  have hfun : Tendsto (fun n => eLpNorm (fun x => (F n) x - f x)
      2 (volume.restrict U)) atTop (𝓝 0) := by
    have h := lemmaV_tendsto_mul_L2 hη r.tendsto_approx
    convert h using 1
    funext n
    congr 1
    funext x
    simp [F, f, H1Function.mulContDiffHasCompactSupport_toFun, mul_comm]
  have hgrad (i : Fin d) : Tendsto
      (fun n => eLpNorm (fun x => (F n).grad x i - Df x i)
        2 (volume.restrict U)) atTop (𝓝 0) := by
    have hA := lemmaV_tendsto_mul_L2 hη (r.tendsto_approx_grad i)
    have hB := lemmaV_tendsto_mul_L2 (hDη i) r.tendsto_approx
    have h := lemmaV_tendsto_add_L2 hA hB
    convert h using 1
    funext n
    congr 1
    funext x
    simp only [F, H1Function.mulContDiffHasCompactSupport_grad, Df]
    ring
  let p : H1Function U :=
    { toFun := f
      grad := Df
      memL2 := hf
      gradMemL2 := hDf
      hasWeakGradient := HasWeakGradientOn.of_tendsto_eLpNorm_two hf hDf
        (fun n => (F n).memL2) (fun n => (F n).gradMemL2)
        (fun n => (F n).hasWeakGradient) hfun hgrad }
  have hmem (n : ℕ) : MemH10 U (F n).toFun := by
    simpa only [F, H1Function.mulContDiffHasCompactSupport_toFun] using
      memH10_mul_of_contDiff_hasCompactSupport hU (r.approx_smooth n)
        (r.approx_hasCompactSupport n) (r.approx_support_subset n) η.memH1
  have hmemP : MemH10 U p.toFun := by
    apply memH10_of_tendsto_H1 hU p F hmem
    · simpa only [eLpNorm_sub_swap] using hfun
    · intro i
      simpa only [eLpNorm_sub_swap] using hgrad i
  obtain ⟨t, ht⟩ := hmemP
  refine ⟨t, ht, ?_⟩
  have hcoord (i : Fin d) : (fun x => t.grad x i) =ᵐ[volume.restrict U]
      (fun x => Df x i) := by
    have heq := HasWeakPartialDerivOn.ae_eq (i := i) (u := p.toFun) hU.isOpen
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((t.gradMemL2 i).locallyIntegrable (by norm_num)))
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((p.gradMemL2 i).locallyIntegrable (by norm_num)))
    have htw := t.hasWeakGradient i
    rw [ht] at htw
    exact heq htw (p.hasWeakGradient i)
  filter_upwards [ae_all_iff.2 hcoord] with x hx
  exact funext hx

/-- Weak gradients of H¹ functions with the same values agree almost everywhere. -/
theorem lemmaV_H1_grad_eq_ae {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {f g : H1Function U} (hfg : f.toFun = g.toFun) :
    f.grad =ᵐ[volume.restrict U] g.grad := by
  have hcoord (i : Fin d) : (fun x => f.grad x i) =ᵐ[volume.restrict U]
      (fun x => g.grad x i) := by
    have hf := f.hasWeakGradient i
    rw [hfg] at hf
    exact HasWeakPartialDerivOn.ae_eq hU
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((f.gradMemL2 i).locallyIntegrable (by norm_num)))
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((g.gradMemL2 i).locallyIntegrable (by norm_num))) hf (g.hasWeakGradient i)
  filter_upwards [ae_all_iff.2 hcoord] with x hx
  exact funext hx

/-- Column divergence of the planar weak matrix field `ηJ`. -/
def lemmaVPlanarWeakColumnDivergence {U : Set (Vec 2)} (η : H1Function U) :
    Vec 2 → Vec 2 := fun x => -matVecMul ASDExplicitGamma.Response.responsePlanarJ (η.grad x)

/-- The column-divergence cancellation for every H¹₀ residual and W¹,∞
planar skew direction. The test function has no boundary restriction. -/
theorem lemmaVPlanar_lift_cancellation {U : Set (Vec 2)}
    [IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsOpenBoundedConvexDomain U) (r : H10Function U) (η : H1Function U)
    (hη : MemLp η (⊤ : ENNReal) (volume.restrict U))
    (hDη : ∀ i, MemLp (fun x => η.grad x i) (⊤ : ENNReal) (volume.restrict U)) :
    IsSolenoidalZeroNormalTraceOn U (fun x =>
      η x • matVecMul ASDExplicitGamma.Response.responsePlanarJ (r.toH1Function.grad x) -
        r x • lemmaVPlanarWeakColumnDivergence η x) := by
  obtain ⟨t, _ht, hDt⟩ := lemmaV_exists_H10_mul hU r η hη hDη
  have ht := lemmaVPlanar_rotatedGradient_zeroNormal hU.isOpen t
  intro w
  have heq : (fun x => vecDot
      (η x • matVecMul ASDExplicitGamma.Response.responsePlanarJ (r.toH1Function.grad x) -
        r x • lemmaVPlanarWeakColumnDivergence η x) (w.grad x)) =ᵐ[volume.restrict U]
      (fun x => vecDot (matVecMul ASDExplicitGamma.Response.responsePlanarJ
        (t.toH1Function.grad x)) (w.grad x)) := by
    filter_upwards [hDt] with x hx
    rw [hx]
    congr 1
    ext i
    fin_cases i <;>
      simp [lemmaVPlanarWeakColumnDivergence, Homogenization.matVecMul,
        ASDExplicitGamma.Response.responsePlanarJ, Fin.sum_univ_two]
    ring
  rw [integral_congr_ae heq]
  exact ht w

/-- The planar row-form field for an abstract linear interpolant. -/
def lemmaVPlanarRowField {U : Set (Vec 2)}
    (I : H1Function U →ₗ[ℝ] H1Function U) (η v : H1Function U) : Vec 2 → Vec 2 :=
  fun x => η x • matVecMul ASDExplicitGamma.Response.responsePlanarJ ((I v).grad x) +
    (v - I v) x • lemmaVPlanarWeakColumnDivergence η x

/-- Abstract-interpolant lift: the difference between `H∇v` and the row-form
field is solenoidal with zero normal trace. Only the H¹₀ residual property
of this particular input is needed. -/
theorem lemmaV_lift_of_interpolant {U : Set (Vec 2)}
    [IsFiniteMeasure (volumeMeasureOn U)] (hU : IsOpenBoundedConvexDomain U)
    (I : H1Function U →ₗ[ℝ] H1Function U) (v η : H1Function U)
    (hres : MemH10 U (v - I v).toFun)
    (hη : MemLp η (⊤ : ENNReal) (volume.restrict U))
    (hDη : ∀ i, MemLp (fun x => η.grad x i) (⊤ : ENNReal) (volume.restrict U)) :
    IsSolenoidalZeroNormalTraceOn U (fun x =>
      η x • matVecMul ASDExplicitGamma.Response.responsePlanarJ (v.grad x) -
        lemmaVPlanarRowField I η v x) := by
  obtain ⟨r, hr⟩ := hres
  have hgrad := lemmaV_H1_grad_eq_ae hU.isOpen hr
  have h := lemmaVPlanar_lift_cancellation hU r η hη hDη
  intro w
  rw [← h w]
  apply integral_congr_ae
  filter_upwards [hgrad] with x hx
  rw [hx]
  congr 1
  ext i
  fin_cases i <;>
    simp [lemmaVPlanarRowField, lemmaVPlanarWeakColumnDivergence,
      H1Function.sub_toFun, H1Function.sub_grad, hr,
      Homogenization.matVecMul, ASDExplicitGamma.Response.responsePlanarJ,
      Fin.sum_univ_two] <;> ring

/-- L² regularity of a planar skew multiplier applied to a weak gradient. -/
theorem lemmaVPlanar_skewGradient_memL2 {U : Set (Vec 2)} (v : H1Function U)
    {η : Vec 2 → ℝ} (hη : MemLp η (⊤ : ENNReal) (volume.restrict U)) :
    MemVectorL2 U (fun x => η x •
      matVecMul ASDExplicitGamma.Response.responsePlanarJ (v.grad x)) := by
  apply MemLp.of_eval
  intro i
  fin_cases i
  · simpa [Homogenization.matVecMul, ASDExplicitGamma.Response.responsePlanarJ,
      Fin.sum_univ_two, Pi.neg_apply, volumeMeasureOn] using! (hη.fun_mul (v.gradMemL2 1)).neg
  · simpa [Homogenization.matVecMul, ASDExplicitGamma.Response.responsePlanarJ,
      Fin.sum_univ_two] using hη.fun_mul (v.gradMemL2 0)

/-- L² regularity of the abstract row-form field. -/
theorem lemmaVPlanarRowField_memL2 {U : Set (Vec 2)}
    (I : H1Function U →ₗ[ℝ] H1Function U) (η v : H1Function U)
    (hη : MemLp η (⊤ : ENNReal) (volume.restrict U))
    (hDη : ∀ i, MemLp (fun x => η.grad x i) (⊤ : ENNReal) (volume.restrict U)) :
    MemVectorL2 U (lemmaVPlanarRowField I η v) := by
  have hb : MemVectorL2 U (fun x => (v - I v) x •
      lemmaVPlanarWeakColumnDivergence η x) := by
    apply MemLp.of_eval
    intro i
    fin_cases i
    · simpa [lemmaVPlanarWeakColumnDivergence, Homogenization.matVecMul,
        ASDExplicitGamma.Response.responsePlanarJ, Fin.sum_univ_two] using
        (v - I v).memL2.fun_mul (hDη 1)
    · simpa [lemmaVPlanarWeakColumnDivergence, Homogenization.matVecMul,
        ASDExplicitGamma.Response.responsePlanarJ, Fin.sum_univ_two,
        Pi.neg_apply, volumeMeasureOn] using!
        ((v - I v).memL2.fun_mul (hDη 0)).neg
  exact (lemmaVPlanar_skewGradient_memL2 (I v) hη).add hb

/-- The lift identity as an equality of normalized pairings for every H¹
function w, including functions with nonzero boundary data. -/
theorem lemmaV_pairing_lift_of_interpolant {U : Set (Vec 2)}
    [IsFiniteMeasure (volumeMeasureOn U)] (hU : IsOpenBoundedConvexDomain U)
    (I : H1Function U →ₗ[ℝ] H1Function U) (v η w : H1Function U)
    (hres : MemH10 U (v - I v).toFun)
    (hη : MemLp η (⊤ : ENNReal) (volume.restrict U))
    (hDη : ∀ i, MemLp (fun x => η.grad x i) (⊤ : ENNReal) (volume.restrict U)) :
    volumeAverage U (fun x => vecDot
      (η x • matVecMul ASDExplicitGamma.Response.responsePlanarJ (v.grad x)) (w.grad x)) =
    volumeAverage U (fun x => vecDot (lemmaVPlanarRowField I η v x) (w.grad x)) := by
  have h := lemmaV_lift_of_interpolant hU I v η hres hη hDη w
  have hA := integrableOn_vecDot_of_memVectorL2
    (lemmaVPlanar_skewGradient_memL2 v hη) w.grad_memVectorL2
  have hF := integrableOn_vecDot_of_memVectorL2
    (lemmaVPlanarRowField_memL2 I η v hη hDη) w.grad_memVectorL2
  have hsub : (fun x => vecDot
      (η x • matVecMul ASDExplicitGamma.Response.responsePlanarJ (v.grad x) -
        lemmaVPlanarRowField I η v x) (w.grad x)) =
      fun x => vecDot (η x • matVecMul ASDExplicitGamma.Response.responsePlanarJ
        (v.grad x)) (w.grad x) - vecDot (lemmaVPlanarRowField I η v x) (w.grad x) := by
    funext x
    simp [vecDot, sub_mul, Finset.sum_sub_distrib]
  rw [hsub, integral_sub hA hF] at h
  unfold volumeAverage
  rw [sub_eq_zero.mp h]

end

end ASDExplicitGamma.Variational
