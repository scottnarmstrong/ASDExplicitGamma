module

public import ASDExplicitGamma.Native.ParentRowDerivativeMultiplier
public import ASDExplicitGamma.Native.ParentBoundarySourceTrace

/-! Full-band parent source multipliers with the exact mesh-five coefficient. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Main Triadic Cold Algsuperdiff.Section3
noncomputable section

/-- The actual parent source clock is exactly its two mesh covariance roots,
including the parent-to-cell factor 243. -/
theorem parent_row_source_multiplier_roots (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    parentBoundaryPotentialSourceClock Q 5 b L=
      (243*Real.sqrt (3991821961/14762250000:ℝ))*
        Real.sqrt ((156/5:ℝ)*(cubeScaleFactor Q/3^5)^2*b^2/L.val^2)+
      (22599/250:ℝ)*Real.sqrt ((46488/25:ℝ)*(cubeScaleFactor Q/3^5)^4*b^2/L.val^4) := by
  let r := cubeScaleFactor Q/3^5
  let K := 243*Real.sqrt (3991821961/14762250000:ℝ)
  have hr : 0≤r := div_nonneg (Triadic.cubeScaleFactor_pos' _).le (by positivity)
  have hK : 0≤K := by dsimp only [K]; positivity
  have he : Real.sqrt ((52/100:ℝ)^2*cubeScaleFactor Q^2+(662/1000:ℝ)^2*r^2)=K*r := by
    calc
      _ = Real.sqrt ((K*r)^2) := by
        congr 1
        dsimp only [K,r]
        rw [mul_pow,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤3991821961/14762250000)]
        ring
      _ = _ := Real.sqrt_sq (mul_nonneg hK hr)
  have hfirst : r*Real.sqrt ((156/5:ℝ)*b^2/L.val^2)=
      Real.sqrt ((156/5:ℝ)*r^2*b^2/L.val^2) := by
    rw [old_signed_radius_sqrt r _ hr]
    congr 1
    ring
  have hsecond : r^2*Real.sqrt ((46488/25:ℝ)*b^2/L.val^4)=
      Real.sqrt ((46488/25:ℝ)*r^4*b^2/L.val^4) := by
    rw [old_signed_radius_sqrt (r^2) _ (sq_nonneg _)]
    congr 1
    ring
  change Real.sqrt ((156/5:ℝ)*b^2/L.val^2)*
    Real.sqrt ((52/100:ℝ)^2*cubeScaleFactor Q^2+(662/1000:ℝ)^2*r^2)+
    (372/1000:ℝ)*cubeScaleFactor Q*r*Real.sqrt ((46488/25:ℝ)*b^2/L.val^4)=_
  rw [he]
  change _=K*Real.sqrt ((156/5:ℝ)*r^2*b^2/L.val^2)+
    (22599/250:ℝ)*Real.sqrt ((46488/25:ℝ)*r^4*b^2/L.val^4)
  rw [←hfirst,←hsecond]
  dsimp only [r]
  ring

/-- Finite Euclidean aggregation of all physical parent source rows preserves
the exact parent-to-cell coefficients and a single sqrt(theta). -/
theorem parent_row_band_source_multiplier
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (height : ℕ) :
    Real.sqrt (∑ i : Fin height,(parentBoundaryPotentialSourceClock (originCube 2 n) 5
      (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
      (q3ModelLength (n+((i.val+1:ℕ):ℤ))))^2)≤
    Real.sqrt (theta M)*
      ((243*Real.sqrt (3991821961/14762250000:ℝ))*Real.sqrt ((156/5:ℝ)*parentRowWeightedClock parentRowA2Weight height)+
        (22599/250:ℝ)*Real.sqrt ((46488/25:ℝ)*parentRowWeightedClock parentRowA4Weight height)) := by
  let r := cubeScaleFactor (originCube 2 n)/3^5
  let b := fun i : Fin height => q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ)
  let L := fun i : Fin height => q3ModelLength (n+((i.val+1:ℕ):ℤ))
  let E := fun i => (156/5:ℝ)*r^2*b i^2/(L i).val^2
  let G := fun i => (46488/25:ℝ)*r^4*b i^2/(L i).val^4
  have hm := old_signed_finite_sqrt_energy_bound E G
    (fun i => parentBoundaryPotentialSourceClock (originCube 2 n) 5 (b i) (L i))
    (by positivity : (0:ℝ)≤243*Real.sqrt (3991821961/14762250000:ℝ)) (by norm_num : (0:ℝ)≤22599/250)
    (fun i => by dsimp only [E]; positivity) (fun i => by dsimp only [G]; positivity)
    (fun i => parent_boundary_potential_source_clock_nonneg (originCube 2 n) 5 (b i) (L i))
    (fun i => (parent_row_source_multiplier_roots (originCube 2 n) (b i) (L i)).le)
  have hE : Real.sqrt (∑ i,E i)≤Real.sqrt (theta M)*
      Real.sqrt ((156/5:ℝ)*parentRowWeightedClock parentRowA2Weight height) := by
    have hh := parent_row_band_covariance_root M h hg n hstate height 1 (156/5) (by norm_num)
    change _≤Real.sqrt (theta M)*Real.sqrt ((156/5:ℝ)*
      parentRowWeightedClock (fun k => (1/9)^(k+6)) height)
    simpa only [Nat.mul_one,Nat.one_mul] using hh
  have hG : Real.sqrt (∑ i,G i)≤Real.sqrt (theta M)*
      Real.sqrt ((46488/25:ℝ)*parentRowWeightedClock parentRowA4Weight height) :=
    parent_row_band_covariance_root M h hg n hstate height 2 (46488/25) (by norm_num)
  exact hm.trans ((add_le_add
    (mul_le_mul_of_nonneg_left hE (by positivity : (0:ℝ)≤243*Real.sqrt (3991821961/14762250000:ℝ)))
    (mul_le_mul_of_nonneg_left hG (by norm_num : (0:ℝ)≤22599/250))).trans_eq (by ring))

end
end ASDExplicitGamma.Native
