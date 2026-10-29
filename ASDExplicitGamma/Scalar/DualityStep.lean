module

public import ASDExplicitGamma.Scalar.DualAdmissibility

/-! Global convex duality for the actual OLD source maximizer and assembled cell patch. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response MeasureTheory

/-- The source OLD maximizing energy is bounded by every genuinely compatible dual competitor. -/
theorem scalar_old_maximizer_duality_bound (Q : TriadicCube 2) (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient (openCubeSet Q))
    (w : Vec 2 → Vec 2) (hw : MemVectorL2 (openCubeSet Q) w)
    (Z C : Vec 2 → BlockVec 2) (hZ : IsScalarOldMaximizer Q ν σ k w Z)
    (hC : ScalarCompatible (openCubeSet Q) C) :
    scalarFieldEnergy ν σ k Z ≤ scalarFieldEnergy ν σ k (scalarBottomLoad w+C) := by
  let X := scalarBottomLoad w+C
  have hX : MemBlockL2 (openCubeSet Q) X := (scalar_bottom_load_memL2 hw).add hC.1
  have h0 := scalar_compatible_exchange_pairing_zero hC hZ.1
  have hip := integrableOn_vecDot_of_memVectorL2 hw (memVectorL2_fst_of_memBlockL2 hZ.1.1)
  have hic1 := integrableOn_vecDot_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hC.1)
    (memVectorL2_fst_of_memBlockL2 hZ.1.1)
  have hic2 := integrableOn_vecDot_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hC.1)
    (memVectorL2_snd_of_memBlockL2 hZ.1.1)
  have hic : IntegrableOn (fun x => blockVecDot (scalarBlockExchange (C x)) (Z x)) (openCubeSet Q) :=
    hic1.add hic2
  have he : (fun x => blockVecDot (scalarBlockExchange (X x)) (Z x))=
      (fun x => vecDot (w x) (Z x).1+blockVecDot (scalarBlockExchange (C x)) (Z x)) := by
    funext x
    simp [X,scalarBottomLoad,scalarBlockExchange,blockVecDot,vecDot_add_left]
    ring
  have hp : volumeAverage (openCubeSet Q) (fun x => blockVecDot (scalarBlockExchange (X x)) (Z x))=
      scalarSourcePairing (openCubeSet Q) w Z := by
    unfold scalarSourcePairing volumeAverage
    rw [he,integral_add hip hic,h0,add_zero]
  have hb := scalar_field_fenchel Q ν σ hν hσ k hX hZ.1.1
  rw [hp,scalar_old_maximizer_energy_identity Q ν σ k w Z hZ] at hb
  linarith only [hb]

end ASDExplicitGamma.Scalar
