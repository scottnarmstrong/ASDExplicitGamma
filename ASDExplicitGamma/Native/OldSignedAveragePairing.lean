module

public import ASDExplicitGamma.Native.OldSignedVectorHaarPairing
public import ASDExplicitGamma.Scalar.ResidualSourcePairing

/-! Literal normalized vector averages in the same OLD weak/positive
pairing convention, for the mixed local trial terms. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Triadic ASDExplicitGamma.Scalar
noncomputable section

/-- The physical normalized vector pairing is the sum of its actual Haar
coordinate pairings, with integrability proved from source membership. -/
theorem old_signed_vector_average_pairing (Q : TriadicCube 2) (r f : Vec 2 → Vec 2)
    (hr : MemVectorL2 (openCubeSet Q) r) (hf : MemVectorL2 (openCubeSet Q) f) :
    volumeAverage (openCubeSet Q) (fun x => vecDot (r x) (f x))=
      ∑ k : Fin 2,pairing Q (fun x => r x k) (fun x => f x k) := by
  change volumeAverage (openCubeSet Q) (fun x => ∑ k : Fin 2,r x k*f x k)=_
  rw [volumeAverage_sum Finset.univ (fun k x => r x k*f x k)
    (fun k _ => (hr.eval k).integrable_mul (hf.eval k))]
  apply Finset.sum_congr rfl
  intro k _
  rw [pairing,cube_average_eq_volume_average_open]

/-- Constant-one weak/positive control of an actual local vector average.
No spatial independence or replacement of a joint product is used. -/
theorem old_signed_vector_average_pairing_bound (Q : TriadicCube 2) (r f : Vec 2 → Vec 2)
    (hr : MemVectorL2 (openCubeSet Q) r) (hf : MemVectorL2 (openCubeSet Q) f)
    (hs : ∀ k,Summable (fun j => (Real.sqrt 3)^(j+1)*energy Q
      (cubeIncrement Q (j+1) (fun x => f x k)))) :
    |volumeAverage (openCubeSet Q) (fun x => vecDot (r x) (f x))|≤
      vectorWeakHaarNorm Q r*vectorPositiveHaarNorm Q f := by
  rw [old_signed_vector_average_pairing Q r f hr hf]
  exact old_signed_vector_haar_pairing_bound Q r f
    (fun k => memLp_normalized_of_memL2On (hr.eval k))
    (fun k => memLp_normalized_of_memL2On (hf.eval k)) hs

end
end ASDExplicitGamma.Native
