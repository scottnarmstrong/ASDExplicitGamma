module

public import ASDExplicitGamma.Native.GenericSourceBandHeatW
public import ASDExplicitGamma.Gaussian.WholeRoot

public import ASDExplicitGamma.Native.NativeBandWeight

/-! Exact coefficient identification for the simultaneous source band. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Algsuperdiff.Frozen.Assumptions
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic ASDExplicitGamma.Response
noncomputable section

variable {W : NativeAmp}

/-- Consecutive finite source labels enumerate the complete physical band. -/
theorem native_source_band_index_sum_W (n : ℤ) (height : ℕ) (f : ℤ → ℝ) :
    (∑ i : Fin height, f (nativeSourceBandIndex n height i)) =
      ∑ j ∈ Finset.Ioc n (n+(height:ℤ)), f j := by
  have hlen : (n+(height:ℤ)-n).toNat=height := by omega
  have hfin : (∑ i : Fin height, f (n+1+(i.val:ℤ))) =
      ∑ j ∈ Finset.range height, f (n+1+(j:ℤ)) :=
    Fin.sum_univ_eq_sum_range (fun j => f (n+1+(j:ℤ))) height
  have hint : (∑ j ∈ Finset.Ioc n (n+(height:ℤ)), f j) =
      ∑ j ∈ Finset.range height, f (n+1+(j:ℤ)) := by
    rw [Int.Ioc_eq_finset_map,Finset.sum_map]
    simp only [Function.Embedding.trans_apply,Nat.castEmbedding_apply,addLeftEmbedding_apply,hlen]
  calc
    _ = ∑ i : Fin height, f (n+1+(i.val:ℤ)) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      dsimp [nativeSourceBandIndex]
      ring
    _ = _ := hfin
    _ = _ := hint.symm

/-- The simultaneous compact scalar is exactly the scalar entry of the
actual attenuated coefficient, retaining every shell in the finite band. -/
theorem native_source_band_scalar_apply_W (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (x : closure (cubeSet (originCube 2 n))) :
    nativeSourceBandScalar_W W n height t ω x =
      attenuatedCoefficient M n (n+(height:ℤ)) (nativeAttW W t) ω x 1 0 := by
  let K := closure (cubeSet (originCube 2 n))
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure
  simp only [nativeSourceBandScalar_W,ContinuousMap.add_apply,ContinuousMap.smul_apply,
    modelBandW,ContinuousMap.sum_apply,smul_eq_mul,nativeSourceBandCoef_W]
  rw [olderField_apply_eq_coefficientCutoff K M ell n hK ω x]
  rw [Finset.mul_sum]
  have hsum := native_source_band_index_sum_W n height
    (fun j => (Real.sqrt t * W.w j)*(shellFieldScalarRestriction K (ω.1 j) x))
  have hsum' : (∑ i : Fin height, Real.sqrt t * (W.w (nativeSourceBandIndex n height i) *
      (shellFieldScalarRestriction K (ω.1 (nativeSourceBandIndex n height i)) x))) =
      ∑ j ∈ Finset.Ioc n (n+(height:ℤ)), (Real.sqrt t * W.w j)*
        (shellFieldScalarRestriction K (ω.1 j) x) := by
    rw [← hsum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum']
  simp only [attenuatedCoefficient,nativeAttW,Matrix.add_apply,Matrix.sum_apply,
    Matrix.smul_apply,smul_eq_mul]
  rfl

private theorem source_band_symm_add_W (A B : Mat 2) :
    symmPart (A+B)=symmPart A+symmPart B := by
  ext i j
  simp only [symmPart,Matrix.add_apply]
  ring

/-- Every simultaneous source attenuation retains its fixed molecular symmetric part. -/
theorem native_source_band_attenuated_symm_W (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    symmPart (attenuatedCoefficient M n (n+(height:ℤ)) (nativeAttW W t) ω x)=
      M.nu • (1:Mat 2) := by
  unfold attenuatedCoefficient
  rw [source_band_symm_add_W,Cutoff.symmPart_coefficientCutoff]
  have hs : symmPart (∑ j ∈ Finset.Ioc n (n+(height:ℤ)),
      nativeAttW W t j • ShellField.forgetShell (ω.1 j) x)=0 := by
    ext i j
    simp only [symmPart,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,ShellField.forgetShell_apply]
    rw [←Finset.sum_add_distrib]
    apply (div_eq_zero_iff).mpr
    left
    apply Finset.sum_eq_zero
    intro k _
    rw [(ω.1 k).skew_entry x i j]
    ring
  rw [hs]
  simp

/-- A planar matrix with scalar molecular symmetric part is recovered from its skew entry. -/
theorem native_source_planar_of_symm_W (molecular : ℝ) (A : Mat 2)
    (hA : symmPart A=molecular • (1:Mat 2)) : responsePlanarCoefficient molecular (A 1 0)=A := by
  have h00 := congrFun (congrFun hA 0) 0
  have h11 := congrFun (congrFun hA 1) 1
  have h01 := congrFun (congrFun hA 0) 1
  norm_num [symmPart,Matrix.smul_apply,Matrix.one_apply] at h00 h11 h01
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [responsePlanarCoefficient,responsePlanarJ] <;> linarith

/-- On the observation cube, the simultaneous compact source scalar gives
precisely the actual attenuated physical coefficient with its fixed `M.nu`. -/
theorem native_source_band_coefficient_on_cube_W (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) (x : Vec 2) (hx : x ∈ cubeSet (originCube 2 n)) :
    responsePlanarCoefficientField M.nu
      (ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet (originCube 2 n))) ℝ ℝ
        (nativeSourceBandScalar_W W n height t ω)) x =
      attenuatedCoefficient M n (n+(height:ℤ)) (nativeAttW W t) ω x := by
  rw [responsePlanarCoefficientField,responseCoefficientExtension_eq _ hx,
    ContinuousMap.linearIsometryBoundedOfCompact_apply_apply,native_source_band_scalar_apply_W]
  exact native_source_planar_of_symm_W M.nu _ (native_source_band_attenuated_symm_W M n height t ω x)

end
end ASDExplicitGamma.Native
