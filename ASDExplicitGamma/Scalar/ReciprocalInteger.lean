module

public import ASDExplicitGamma.Scalar.ReciprocalTelescope
public import ASDExplicitGamma.Numerics.Scalar.Lower

/-! The source two-region conversion on integer completed labels. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Numerics Numerics.Mirror Numerics.Scalar

/-- SC-RECIPROCAL-TELESCOPE, with the source integer label interval and D128 normalization. -/
theorem reciprocal_telescope_int (nu K D : ℝ) (sigma r B : ℤ → ℝ) (n0 N : ℤ)
    (hN : n0<N) (hnu : 0<nu) (hK : 0≤K)
    (hs : ∀ i : ℤ, n0 ≤ i → i ≤ N → 0<sigma i)
    (hB : ∀ i : ℤ, n0 ≤ i → i < N → B i≤B (i+1))
    (hdrop : ∀ i : ℤ, n0 ≤ i → i < N → K*(B (i+1)-B i)/(sigma i)^3≤r i-r (i+1))
    (hlower : ∀ i : ℤ, n0 ≤ i → i ≤ N → 1≤sigma i*r i)
    (hupper : ∀ i : ℤ, n0 ≤ i → i < N → sigma i*r i≤1+D/2)
    (hstart : r n0≤nu⁻¹) (hfinal : ∀ i : ℤ, n0 ≤ i → i < N → sigma i≤sigma N) :
    nu^2+2*K/(1+3*D/2)*(B N-B n0)≤(sigma N)^2 := by
  let L : ℕ := (N-n0).toNat
  have hL : n0+(L:ℤ)=N := by dsimp [L]; omega
  have hLpos : 0<L := by dsimp [L]; omega
  have hindex (i : ℕ) : n0≤n0+(i:ℤ) := by omega
  have hindexle (i : ℕ) (hi : i≤L) : n0+(i:ℤ)≤N := by omega
  have hindexlt (i : ℕ) (hi : i<L) : n0+(i:ℤ)<N := by omega
  have h := reciprocal_telescope_nat nu K (1+D/2)
    (fun i => sigma (n0+(i:ℤ))) (fun i => r (n0+(i:ℤ))) (fun i => B (n0+(i:ℤ))) L
    hLpos hnu hK
    (fun i hi => hs _ (hindex i) (hindexle i hi))
    (fun i hi => by
      simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using (hB _ (hindex i) (hindexlt i hi)))
    (fun i hi => by
      simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using (hdrop _ (hindex i) (hindexlt i hi)))
    (fun i hi => hlower _ (hindex i) (hindexle i hi))
    (fun i hi => hupper _ (hindex i) (hindexlt i hi))
    (by simpa using hstart)
    (fun i hi => by simpa only [hL] using hfinal _ (hindex i) (hindexlt i hi))
  have hc : 3*(1+D/2)-2=1+3*D/2 := by ring
  simpa only [hL,Nat.cast_zero,add_zero,hc] using h

end ASDExplicitGamma.Scalar
