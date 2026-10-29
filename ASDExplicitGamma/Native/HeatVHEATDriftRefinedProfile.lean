module

public import ASDExplicitGamma.Native.HeatVHEATDriftSourceIntegrand
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceTransport

/-! Exact consumption of the owner's refined centered source profile. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Response Scalar Variational Inverse Triadic Algsuperdiff.Section3
noncomputable section

/-- The literal sheared observer trace, with a stable completed-label argument. -/
def heatVHEATDriftObserverTrace (M : ABKModel 2) (n : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (a : ℝ) : ℝ :=
  modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n)
    (heatRefinedObserverShear (n-1) n 9 t ω a)

/-- Once the owner's field transport identifies a child with its canonical
source observer, its signed profile minus the exact diagonal center term is
precisely the physical bank integrand used in the expectation theorem.
This is a profile identity, not an assumed drift or bank estimate. -/
theorem heatVHEATDrift_refined_profile_eq_of_observer
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (i : nativeHeatQ3RefinedCarrierIndex)
    (d : Fin 9) (t : ℝ) (ω : Cutoff.CutoffSample 2) (a : ℝ)
    (f : C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)),ℝ))
    (hf : nativeHeat_translateTriadicFieldToOrigin (nativeHeatQ3RefinedCarrierChild m i) f =
      heatRefinedObserverShear (nativeHeatQ3RefinedCarrierChild m i).scale
        ((nativeHeatQ3RefinedCarrierChild m i).scale+1) 9 t ω a) :
    let n := (nativeHeatQ3RefinedCarrierChild m i).scale+1
    nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfile M h m i d (Annealed.sigmaBar M n) f =
      (2*heatVHEATDriftVariance M h n d*heatVHEATDriftKappa n d*
        heatVHEATDriftBank M n 9 t ω a d+
       heatVHEATDriftVariance M h n d*heatVHEATDriftMu d*
        (heatVHEATDriftBank M n 9 t ω a d)^2)*
      (heatVHEATDriftObserverTrace M n t ω a+4) := by
  dsimp only [heatVHEATDriftObserverTrace]
  have hlabel : (nativeHeatQ3RefinedCarrierChild m i).scale+1-1=
      (nativeHeatQ3RefinedCarrierChild m i).scale := by ring
  have hs : (nativeHeatQ3RefinedCarrierChild m i).scale+((d.val+2:ℕ):ℤ)=
      (nativeHeatQ3RefinedCarrierChild m i).scale+1+((d.val+1:ℕ):ℤ) := by omega
  have hd : d.val+2-1=d.val+1 := by omega
  have hbank (q n : ℤ) (hq : n-1=q) :
      heatVHEATDriftBank M n 9 t ω a d=
      max (lemmaVTileHistory (originCube 2 q) (pureFluxBankSourceDepth (d.val+2))
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
          (pureFluxOpenResponseRestriction q (heatRefinedObserverShear q n 9 t ω a))))
        (pureFluxSourceTileHistory (originCube 2 q) (pureFluxBankSourceDepth (d.val+2))
          (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
            (pureFluxOpenResponseRestriction q (heatRefinedObserverShear q n 9 t ω a)))) := by
    subst q
    rfl
  have htrace (q n : ℤ) (hq : n-1=q) :
      modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n)
        (heatRefinedObserverShear (n-1) n 9 t ω a)=
      modelTraceObservable q M.nu (Annealed.sigmaBar M n)
        (heatRefinedObserverShear q n 9 t ω a) := by
    subst q
    rfl
  rw [hbank _ _ hlabel,htrace _ _ hlabel]
  dsimp only [nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfile,
    nativeHeatQ3RefinedCarrierChildSignedDriftProfile,
    nativeHeatQ3RefinedCarrierChildCenterDriftProfile,
    heatVHEATDriftVariance,heatVHEATDriftKappa,heatVHEATDriftMu,
    ]
  simp only [hlabel,hd,hs,hf]
  ring

end
end ASDExplicitGamma.Native
