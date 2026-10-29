module

public import Algsuperdiff.Section3.Provider.Corrector.OmegaStream
public import Homogenization.Sobolev.PotentialSolenoidalL2Recovery
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

@[expose] public section

open MeasureTheory Homogenization
open Algsuperdiff.Probability.Stationary
open Algsuperdiff.Section3.Provider.Corrector

namespace ASDExplicitGamma.Model

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- A stationary solenoidal field annihilates each deterministic smooth
compactly supported physical gradient, almost surely. -/
theorem stationarySolenoidal_physical_test
    {X : Ω → HilbertVec d} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ)
    (hsol : hX.toLp X ∈ stationarySolenoidalSubspace (μ := μ) (d := d))
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∀ᵐ ω ∂μ, ∫ x, vecDot (realize X ω x).toVec
      (fun i => fderiv ℝ φ x (basisVec i)) = 0 := by
  have hint : ∀ᵐ ω ∂μ, ∀ i : Fin d,
      Integrable (fun x => kernelDeriv (kernelReflect φ) i x *
        coordField X i ((-x) +ᵥ ω)) volume := by
    apply ae_all_iff.mpr
    intro i
    simpa only [smul_eq_mul] using
      (ae_integrable_smul_comp_vadd (μ := μ)
        (continuous_kernelDeriv (contDiff_kernelReflect hφ) i)
        (integrable_kernelDeriv (hasCompactSupport_kernelReflect hc)
          (contDiff_kernelReflect hφ) i)
        (stronglyMeasurable_coordField hXm i) (memLp_coordField hXm hX i))
  filter_upwards [mollifyDiv_ae_eq_zero (hasCompactSupport_kernelReflect hc)
    (contDiff_kernelReflect hφ) hXm hX hsol, hint] with ω hzero hi
  have heq (i : Fin d) :
      (∫ x, kernelDeriv (kernelReflect φ) i x * coordField X i ((-x) +ᵥ ω)) =
        -(∫ x, (realize X ω x).toVec i * fderiv ℝ φ x (basisVec i)) := by
    rw [← integral_neg_eq_self (fun x =>
      kernelDeriv (kernelReflect φ) i x * coordField X i ((-x) +ᵥ ω))]
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [kernelDeriv_kernelReflect hφ i]
    simp only [kernelReflect, neg_neg, neg_mul, realize, coordField, kernelDeriv]
    ring
  have hi' (i : Fin d) : Integrable (fun x =>
      (realize X ω x).toVec i * fderiv ℝ φ x (basisVec i)) volume := by
    have hh := (hi i).comp_neg
    apply hh.neg.congr
    filter_upwards [] with x
    rw [kernelDeriv_kernelReflect hφ i]
    simp only [kernelReflect, Pi.neg_apply, neg_neg, neg_mul, realize, coordField, kernelDeriv]
    ring
  simp only [mollifyDiv, mollify, smul_eq_mul] at hzero
  simp_rw [heq] at hzero
  rw [Finset.sum_neg_distrib, neg_eq_zero] at hzero
  simpa only [vecDot, integral_finsetSum _ (fun i _ => hi' i)] using hzero

omit [SFinite μ] in
/-- On a separable test space, almost-sure annihilation of each test gives
one null set valid for every test. -/
theorem ae_forall_inner_eq_zero_of_forall_ae
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [SecondCountableTopology H] (Y : Ω → H) (S : Set H)
    (h : ∀ v ∈ S, ∀ᵐ ω ∂μ, inner ℝ (Y ω) v = 0) :
    ∀ᵐ ω ∂μ, ∀ v ∈ S, inner ℝ (Y ω) v = 0 := by
  obtain ⟨D, hc, hDS, hd⟩ := TopologicalSpace.exists_countable_dense_subset S
  filter_upwards [(ae_ball_iff hc).mpr (fun v hv => h v (hDS hv))] with ω hω v hv
  have hclosed : IsClosed {v : H | inner ℝ (Y ω) v = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  exact (hclosed.closure_subset_iff.mpr hω) (hd hv)

/-- Stationary solenoidality implies the physical weak divergence equation
on every bounded open observation set, with one exceptional null set. -/
theorem stationarySolenoidal_realize_isSolenoidalOn
    {U : Set (Vec d)} (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    {X : Ω → HilbertVec d} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ)
    (hsol : hX.toLp X ∈ stationarySolenoidalSubspace (μ := μ) (d := d)) :
    ∀ᵐ ω ∂μ, MemVectorL2 U (fun x => (realize X ω x).toVec) ∧
      IsSolenoidalOn U (fun x => (realize X ω x).toVec) := by
  classical
  let : IsFiniteMeasure (volumeMeasureOn U) := ⟨by simpa [volumeMeasureOn] using hfin.lt_top⟩
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let Y : Ω → HilbertVectorL2 U := fun ω =>
    if hm : MemHilbertVectorL2 U (realize X ω) then hm.toLp (realize X ω) else 0
  let S : Set (HilbertVectorL2 U) := {v | ∃ φ : Vec d → ℝ,
    ∃ hs : ContDiff ℝ (⊤ : ℕ∞) φ, ∃ hc : HasCompactSupport φ,
    ∃ hsub : tsupport φ ⊆ U,
    v = toHilbertVectorL2OfVecField
      (H10Function.ofContDiff hU hs hc hsub).toH1Function.grad_memVectorL2}
  have hpair (ω : Ω) (hm : MemHilbertVectorL2 U (realize X ω))
      (φ : Vec d → ℝ) (hs : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
      (hsub : tsupport φ ⊆ U) :
      inner ℝ (Y ω) (toHilbertVectorL2OfVecField
        (H10Function.ofContDiff hU hs hc hsub).toH1Function.grad_memVectorL2) =
      ∫ x in U, vecDot (realize X ω x).toVec
        (fun i => fderiv ℝ φ x (basisVec i)) := by
    simp only [Y, dite_eq_left hm]
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hm.coeFn_toLp, coeFn_toHilbertVectorL2OfVecField
      (H10Function.ofContDiff hU hs hc hsub).toH1Function.grad_memVectorL2]
      with x hx hg
    rw [hx, hg, HilbertVec.inner_def]
    rfl
  have ht : ∀ v ∈ S, ∀ᵐ ω ∂μ, inner ℝ (Y ω) v = 0 := by
    rintro v ⟨φ, hs, hc, hsub, rfl⟩
    filter_upwards [ae_memLp_two_realize (μ := μ) hfin hXm hX,
      stationarySolenoidal_physical_test hXm hX hsol hs hc] with ω hm hz
    rw [hpair ω hm φ hs hc hsub]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact hz
    · intro x hx
      have hx' : x ∉ tsupport φ := fun h => hx (hsub h)
      rw [fderiv_of_notMem_tsupport ℝ hx']
      simp [vecDot]
  have hall := ae_forall_inner_eq_zero_of_forall_ae Y S ht
  filter_upwards [hall, ae_memLp_two_realize (μ := μ) hfin hXm hX] with ω hω hm
  have hvec : MemVectorL2 U (fun x => (realize X ω x).toVec) := by
    exact (HilbertVec.continuousLinearEquivVec d).toContinuousLinearMap.comp_memLp' hm
  refine ⟨hvec, IsSolenoidalOn.of_test_of_contDiff_of_memVectorL2 hvec hU ?_⟩
  intro φ hs hc hsub
  rw [← hpair ω hm φ hs hc hsub]
  exact hω _ ⟨φ, hs, hc, hsub, rfl⟩

end ASDExplicitGamma.Model
