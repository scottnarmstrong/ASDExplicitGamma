module

public import ASDExplicitGamma.Model.StationaryPhysicalTests
public import Algsuperdiff.Section3.Provider.Corrector.RealizationTransfer

@[expose] public section

open MeasureTheory Homogenization
open Algsuperdiff.Probability.Stationary
open Algsuperdiff.Section3.Provider.Corrector

namespace ASDExplicitGamma.Model

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω}
variable [MeasurableConstVAdd (Vec d) Ω] [VAddInvariantMeasure (Vec d) Ω μ]

/-- A strongly measurable representative of the positive stationary projection. -/
noncomputable def stationaryProjectionRepr {F : Ω → HilbertVec d} (hF : MemLp F 2 μ) :
    Ω → HilbertVec d :=
  (Lp.aestronglyMeasurable (stationaryPotentialProjection (hF.toLp F))).mk _

theorem stronglyMeasurable_stationaryProjectionRepr
    {F : Ω → HilbertVec d} (hF : MemLp F 2 μ) :
    StronglyMeasurable (stationaryProjectionRepr hF) :=
  (Lp.aestronglyMeasurable (stationaryPotentialProjection (hF.toLp F))).stronglyMeasurable_mk

theorem memLp_stationaryProjectionRepr {F : Ω → HilbertVec d} (hF : MemLp F 2 μ) :
    MemLp (stationaryProjectionRepr hF) 2 μ :=
  (Lp.memLp (stationaryPotentialProjection (hF.toLp F))).ae_eq
    (Lp.aestronglyMeasurable (stationaryPotentialProjection (hF.toLp F))).ae_eq_mk

theorem toLp_stationaryProjectionRepr {F : Ω → HilbertVec d} (hF : MemLp F 2 μ) :
    (memLp_stationaryProjectionRepr hF).toLp (stationaryProjectionRepr hF) =
      stationaryPotentialProjection (hF.toLp F) := by
  apply Lp.ext
  exact (memLp_stationaryProjectionRepr hF).coeFn_toLp.trans
    (Lp.aestronglyMeasurable (stationaryPotentialProjection (hF.toLp F))).ae_eq_mk.symm

/-- The realized stationary projection has the same physical divergence as
its forcing. In particular the residual is locally square integrable and
annihilates every zero-trace Sobolev gradient. -/
theorem stationaryProjectionRepr_physical_residual
    [SFinite μ] [MeasurableVAdd₂ (Vec d) Ω]
    {U : Set (Vec d)} (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    {F : Ω → HilbertVec d} (hFm : StronglyMeasurable F) (hF : MemLp F 2 μ) :
    ∀ᵐ ω ∂μ,
      MemVectorL2 U (fun x => (realize F ω x - realize (stationaryProjectionRepr hF) ω x).toVec) ∧
      IsSolenoidalOn U
        (fun x => (realize F ω x - realize (stationaryProjectionRepr hF) ω x).toVec) := by
  have hR := hF.sub (memLp_stationaryProjectionRepr hF)
  have hmem : hR.toLp (F - stationaryProjectionRepr hF) ∈
      stationarySolenoidalSubspace (μ := μ) (d := d) := by
    rw [MemLp.toLp_sub hF (memLp_stationaryProjectionRepr hF), toLp_stationaryProjectionRepr]
    exact sub_stationaryPotentialProjection_mem_orthogonal (hF.toLp F)
  have hr := stationarySolenoidal_realize_isSolenoidalOn hU hfin
    (hFm.sub (stronglyMeasurable_stationaryProjectionRepr hF)) hR hmem
  simpa only [realize, Pi.sub_apply] using hr

end ASDExplicitGamma.Model
