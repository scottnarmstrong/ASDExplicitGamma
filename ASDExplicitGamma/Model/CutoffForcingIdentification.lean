module

public import ASDExplicitGamma.Model.CutoffStationaryEnergy
public import ASDExplicitGamma.Model.CutoffAction
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

@[expose] public section

open MeasureTheory Homogenization
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Corrector

namespace ASDExplicitGamma.Model

/-- The forcing series at the origin converges to the literal frozen cutoff. -/
theorem hasSum_cutoff_originForcing {d : ℕ} (e : Vec d) (m : ℤ)
    (ω : Cutoff.CutoffSample d) :
    HasSum (fun n : ℕ => layerForcing e (m - (n : ℤ)) (seqValuePath ω.1))
      (HilbertVec.ofVec (matVecMul (Cutoff.cutoffValue m ω 0) e)) := by
  have hentry (i j : Fin d) : HasSum (fun n : ℕ => ω.1 (m - (n : ℤ)) 0 i j)
      (Cutoff.cutoffValue m ω 0 i j) := by
    apply Summable.hasSum
    refine (Cutoff.lowerTailGood_summable ω.2 0 m).of_norm_bounded fun n => ?_
    apply Cutoff.abs_entry_le_localCubeControl 0
    rw [mem_openCubeSet_originCube_iff]
    intro k
    norm_num
  have hvec : HasSum (fun n : ℕ => matVecMul (ω.1 (m - (n : ℤ)) 0) e)
      (matVecMul (Cutoff.cutoffValue m ω 0) e) := by
    apply Pi.hasSum.mpr
    intro i
    simpa only [matVecMul] using
      (hasSum_sum (s := Finset.univ) (fun j _ => (hentry i j).mul_right (e j)))
  exact (HilbertVec.continuousLinearEquivVec d).symm.toContinuousLinearMap.hasSum hvec

/-- The completed stationary forcing pulled to the actual sample law. -/
noncomputable def cutoffForcingL2 {d : ℕ} (M : ABKModel d) (e : Vec d) (m : ℤ) :
    Algsuperdiff.Probability.Stationary.VectorL2 d (Cutoff.cutoffSampleLaw M).toMeasure :=
  carrierTransport (HilbertVec d) (measurePreserving_cutoffSeqPath M)
    (completedLayerForcingL2 M e m)

/-- Identification with the coefficient's actual skew forcing, rather than a
surrogate for it, on the exact cutoff-sample law. -/
theorem cutoffForcingL2_coeFn {d : ℕ} (M : ABKModel d) (e : Vec d) (m : ℤ) :
    (cutoffForcingL2 M e m : Cutoff.CutoffSample d → HilbertVec d) =ᵐ[
      (Cutoff.cutoffSampleLaw M).toMeasure]
      fun ω => HilbertVec.ofVec (matVecMul (Cutoff.cutoffValue m ω 0) e) := by
  have habs : (∑' n : ℕ, ‖layerForcingL2 M e (m - (n : ℤ))‖ₑ) ≠ ⊤ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr (summable_norm_completedLayerForcing M e m)
  have hsum := Lp.hasSum_coeFn_tsum habs
  have hlayer : ∀ᵐ F ∂(seqPathLaw M.P).toMeasure, ∀ n : ℕ,
      layerForcingL2 M e (m - (n : ℤ)) F = layerForcing e (m - (n : ℤ)) F :=
    ae_all_iff.mpr fun n => (memLp_two_layerForcing M e (m - (n : ℤ))).coeFn_toLp
  have hmp := measurePreserving_cutoffSeqPath M
  filter_upwards [coeFn_carrierTransport hmp (completedLayerForcingL2 M e m),
    hmp.quasiMeasurePreserving.ae hsum, hmp.quasiMeasurePreserving.ae hlayer] with ω hω hs hl
  change (carrierTransport (HilbertVec d) hmp (completedLayerForcingL2 M e m)) ω = _
  rw [hω]
  have hs' : HasSum (fun n : ℕ => layerForcing e (m - (n : ℤ)) (seqValuePath ω.1))
      (completedLayerForcingL2 M e m (seqValuePath ω.1)) := by
    change HasSum _ (completedLayerForcingL2 M e m (seqValuePath ω.1)) at hs
    convert hs using 1
    funext n
    exact (hl n).symm
  exact hs'.unique (hasSum_cutoff_originForcing e m ω)

/-- The literal origin forcing of the cutoff skew field. -/
noncomputable def cutoffOriginForcing {d : ℕ} (e : Vec d) (m : ℤ)
    (ω : Cutoff.CutoffSample d) : HilbertVec d :=
  HilbertVec.ofVec (matVecMul (Cutoff.cutoffValue m ω 0) e)

/-- The forcing representative is strongly measurable on the actual sample law. -/
theorem stronglyMeasurable_cutoffOriginForcing {d : ℕ} (e : Vec d) (m : ℤ) :
    StronglyMeasurable (cutoffOriginForcing e m) := by
  apply Measurable.stronglyMeasurable
  apply (HilbertVec.continuousLinearEquivVec d).symm.continuous.measurable.comp
  apply measurable_pi_iff.mpr
  intro i
  apply Finset.measurable_sum
  intro j hj
  exact (Cutoff.measurable_cutoff_apply_entry m 0 i j).mul_const (e j)

theorem memLp_cutoffOriginForcing {d : ℕ} (M : ABKModel d) (e : Vec d) (m : ℤ) :
    MemLp (cutoffOriginForcing e m) 2 (Cutoff.cutoffSampleLaw M).toMeasure :=
  (Lp.memLp (cutoffForcingL2 M e m)).ae_eq (cutoffForcingL2_coeFn M e m)

theorem toLp_cutoffOriginForcing {d : ℕ} (M : ABKModel d) (e : Vec d) (m : ℤ) :
    (memLp_cutoffOriginForcing M e m).toLp (cutoffOriginForcing e m) = cutoffForcingL2 M e m := by
  apply Lp.ext
  exact (memLp_cutoffOriginForcing M e m).coeFn_toLp.trans (cutoffForcingL2_coeFn M e m).symm

/-- The physical realization is the actual cutoff skew forcing at every point. -/
theorem realize_cutoffOriginForcing {d : ℕ} (e : Vec d) (m : ℤ)
    (ω : Cutoff.CutoffSample d) (x : Vec d) :
    realize (cutoffOriginForcing e m) ω x =
      HilbertVec.ofVec (matVecMul (Cutoff.cutoffValue m ω x) e) := by
  have h := congrArg (fun a : RegCoeffField d => a 0)
    (Cutoff.cutoff_translateCutoffSample m x ω)
  change Cutoff.cutoffValue m (x +ᵥ ω) 0 = Cutoff.cutoffValue m ω (0 + x) at h
  simp only [zero_add] at h
  change HilbertVec.ofVec (matVecMul (Cutoff.cutoffValue m (x +ᵥ ω) 0) e) = _
  rw [h]

/-- Exact half-variance energy on the literal cutoff-sample carrier. -/
theorem q3_cutoffForcing_projection_energy
    (M : ABKModel 2) (h : ℝ) (hM : ASDExplicitGamma.PlanarQ3Gaussian M h)
    {e : Vec 2} (he : Book.Ch02.vecNorm e = 1) (m : ℤ) :
    ‖Algsuperdiff.Probability.Stationary.stationaryPotentialProjection
      (cutoffForcingL2 M e m)‖ ^ 2 = shellVarianceSum h M.gamma m / 2 := by
  rw [cutoffForcingL2, stationaryPotentialProjection_carrierTransport
    (measurePreserving_cutoffSeqPath M) cutoffSeqPath_vadd,
    norm_carrierTransport, q3_completedLayerForcing_projection_energy M h hM he m]

end ASDExplicitGamma.Model
