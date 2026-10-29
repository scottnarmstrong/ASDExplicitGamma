module

public import ASDExplicitGamma.Native.HeatVHEATDriftRefinedProfile
public import ASDExplicitGamma.Native.HeatVHEATSourceCarrierGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedShellLawGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceClocksGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceProfilesGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceTransportGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceGeometryGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceBankGen
public import ASDExplicitGamma.Native.HeatVHEATDriftBankIdentityGen
public import ASDExplicitGamma.Native.HeatVHEATDriftBankMeasurableGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceIntegrandGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceNormsGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceExpectationGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedCoefficientsGen
public import ASDExplicitGamma.Native.HeatVHEATDriftConfiguredCoefficientsGen
public import ASDExplicitGamma.Native.HeatVHEATDriftConfiguredExpectationGen

/-! The `ns`-shell generalization of `HeatVHEATDriftRefinedProfile`. -/

@[expose] public section


namespace ASDExplicitGamma.Native
open Homogenization Gaussian Response Scalar Variational Inverse Triadic Algsuperdiff.Section3
noncomputable section

variable (ns : ℕ)

/-- The literal sheared observer trace, with a stable completed-label argument. -/
def heatVHEATDriftObserverTraceGen (M : ABKModel 2) (n : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (a : ℝ) : ℝ :=
  modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n)
    (heatRefinedObserverShear (n-1) n ns t ω a)

/-- Once the owner's field transport identifies a child with its canonical
source observer, its signed profile minus the exact diagonal center term is
precisely the physical bank integrand used in the expectation theorem.
This is a profile identity, not an assumed drift or bank estimate. -/
theorem heatVHEATDrift_refined_profile_eq_of_observer_Gen
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (i : nativeHeatQ3RefinedCarrierIndex)
    (d : Fin ns) (t : ℝ) (ω : Cutoff.CutoffSample 2) (a : ℝ)
    (f : C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)),ℝ))
    (hf : nativeHeat_translateTriadicFieldToOrigin (nativeHeatQ3RefinedCarrierChild m i) f =
      heatRefinedObserverShear (nativeHeatQ3RefinedCarrierChild m i).scale
        ((nativeHeatQ3RefinedCarrierChild m i).scale+1) ns t ω a) :
    let n := (nativeHeatQ3RefinedCarrierChild m i).scale+1
    (nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfileGen ns) M h m i d (Annealed.sigmaBar M n) f =
      (2*(heatVHEATDriftVarianceGen ns) M h n d*(heatVHEATDriftKappaGen ns) n d*
        (heatVHEATDriftBankGen ns) M n ns t ω a d+
       (heatVHEATDriftVarianceGen ns) M h n d*(heatVHEATDriftMuGen ns) d*
        ((heatVHEATDriftBankGen ns) M n ns t ω a d)^2)*
      ((heatVHEATDriftObserverTraceGen ns) M n t ω a+4) := by
  dsimp only [heatVHEATDriftObserverTraceGen]
  have hlabel : (nativeHeatQ3RefinedCarrierChild m i).scale+1-1=
      (nativeHeatQ3RefinedCarrierChild m i).scale := by ring
  have hs : (nativeHeatQ3RefinedCarrierChild m i).scale+((d.val+2:ℕ):ℤ)=
      (nativeHeatQ3RefinedCarrierChild m i).scale+1+((d.val+1:ℕ):ℤ) := by omega
  have hd : d.val+2-1=d.val+1 := by omega
  have hbank (q n : ℤ) (hq : n-1=q) :
      (heatVHEATDriftBankGen ns) M n ns t ω a d=
      max (lemmaVTileHistory (originCube 2 q) (pureFluxBankSourceDepth (d.val+2))
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
          (pureFluxOpenResponseRestriction q (heatRefinedObserverShear q n ns t ω a))))
        (pureFluxSourceTileHistory (originCube 2 q) (pureFluxBankSourceDepth (d.val+2))
          (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
            (pureFluxOpenResponseRestriction q (heatRefinedObserverShear q n ns t ω a)))) := by
    subst q
    rfl
  have htrace (q n : ℤ) (hq : n-1=q) :
      modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n)
        (heatRefinedObserverShear (n-1) n ns t ω a)=
      modelTraceObservable q M.nu (Annealed.sigmaBar M n)
        (heatRefinedObserverShear q n ns t ω a) := by
    subst q
    rfl
  rw [hbank _ _ hlabel,htrace _ _ hlabel]
  dsimp only [nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfileGen,
    nativeHeatQ3RefinedCarrierChildSignedDriftProfileGen,
    nativeHeatQ3RefinedCarrierChildCenterDriftProfileGen,
    heatVHEATDriftVarianceGen,heatVHEATDriftKappaGen,heatVHEATDriftMuGen,
    ]
  simp only [hlabel,hd,hs,hf]
  ring

end
end ASDExplicitGamma.Native
