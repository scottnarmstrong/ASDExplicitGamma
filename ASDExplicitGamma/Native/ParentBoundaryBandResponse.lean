module

public import ASDExplicitGamma.Native.GenericSourceBankAdapter

/-! Actual order-128 response profile on every simultaneous-band source cell.
The old completed frame is fixed independently of the cell refinement. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Inverse
open scoped ENNReal
noncomputable section

/-- Full response on the actual finite band, including arbitrary source-cell
refinement and all cross-cell correlations. No norm estimate is a premise. -/
theorem parent_boundary_band_cell_response_L128
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height r : ℕ)
    (Q : TriadicCube 2) (hQ : Q.scale=n-(r:ℤ))
    (hpast : ∀ k<n,nativeInductionState M h k) (weights : ℤ → ℝ)
    (hw : ∀ k∈Finset.Ioc n (n+(height:ℤ)),0≤weights k ∧ weights k≤1) :
    eLpNorm (nativeSourceFullResponseTrace M Q n (n+(height:ℤ)) weights)
      (ENNReal.ofReal 128) (Cutoff.cutoffSampleLaw M).toMeasure≤
      ENNReal.ofReal (4*((1009309/500000:ℝ)+M.gamma*
        (32474*((height:ℝ)+(r:ℝ)+1)+11483216))*
          (3:ℝ)^((2*(height:ℝ)+4*(r:ℝ)+4)*M.gamma)) := by

  have hh := full_response_bank128_outward M h hM hg Q
    (fun k hk => hpast k (by rw [hQ] at hk; omega)) (n+(height:ℤ)) n (by rw [hQ]; omega)
    (sourceBandWeights n weights)
    (source_band_weights_bounds (Q.scale-342) n (n+(height:ℤ)) weights hw)
  dsimp only at hh
  have he : (fun ω => rootTraceObservable M Q (Q.scale-342) (n+(height:ℤ)) n
      (sourceBandWeights n weights) ω/4) =
      (fun ω => nativeSourceFullResponseTrace M Q n (n+(height:ℤ)) weights ω/4) := by
    funext ω
    unfold rootTraceObservable nativeSourceFullResponseTrace
    rw [full_response_coefficient_promote M _ n (n+(height:ℤ)) (by rw [hQ]; omega) (by omega)]
  rw [he] at hh
  have hD : ((n+(height:ℤ):ℤ):ℝ)-(Q.scale:ℝ)+1=(height:ℝ)+(r:ℝ)+1 := by
    rw [hQ]
    push_cast
    ring
  have hK : n-Q.scale+1=(r:ℤ)+1 := by rw [hQ]; ring
  rw [hD,hK,Int.cast_add,Int.cast_natCast,Int.cast_one,abs_of_nonneg (by positivity)] at hh
  have hfun : nativeSourceFullResponseTrace M Q n (n+(height:ℤ)) weights =
      (4:ℝ) • (fun ω => nativeSourceFullResponseTrace M Q n (n+(height:ℤ)) weights ω/4) := by
    funext ω
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  rw [hfun,eLpNorm_const_smul,Real.enorm_eq_ofReal (by norm_num : (0:ℝ)≤4)]
  apply (mul_le_mul' le_rfl hh).trans
  rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤4)]
  apply ENNReal.ofReal_le_ofReal
  have hexp : 2*M.gamma*((height:ℝ)+(r:ℝ)+1)+2*M.gamma*((r:ℝ)+1)=
      (2*(height:ℝ)+4*(r:ℝ)+4)*M.gamma := by ring
  rw [hexp]
  exact le_of_eq (by ring)

end
end ASDExplicitGamma.Native
