module

public import ASDExplicitGamma.Native.ParentHistoryYoung
public import ASDExplicitGamma.Native.ParentHistoryRareNorms

/-! Honest centered-history moments before the sharp physical restoration. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Triadic Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The entire centered history has a coarse physical/Gaussian-square
majorant. This is only a finiteness argument; it is not the sharp panel cap. -/
theorem parent_history_centered_coarse_young
    (M : ABKModel 2) (P : TriadicCube 2) (n : ℤ) (height : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    (parentBoundaryCommonCenteredMaxHistory M P n height t ω).toReal ≤
      2*(parentBoundaryBandMaxTraceHistory M n height P t ω).toReal+4+
        4*(parentBoundaryCommonCubeCenterValue P n height t ω/(Annealed.sigmaBar M n:ℝ))^2*
          ((Annealed.sigmaBar M n:ℝ)/M.nu) := by
  let alpha := inverseHistoryDiscount
  let af := parentHistoryPhysicalFrame M P n height t ω
  let ac := parentHistoryCenteredFrame M P n height t ω
  let F := fun j : ℕ => oldSignedMaxTraceDepth P af j
  let C := fun j : ℕ => oldSignedMaxTraceDepth P ac j
  let K := 4+4*(parentBoundaryCommonCubeCenterValue P n height t ω/(Annealed.sigmaBar M n:ℝ))^2*
    ((Annealed.sigmaBar M n:ℝ)/M.nu)
  have ha0 := inverse_history_discount_range.1.le
  have ha1 := inverse_history_discount_range.2
  have hσ := (Annealed.sigmaBar_characterization M n).1
  have hEll (f : C(closure (cubeSet P),ℝ)) : IsEllipticFieldOn
      (M.nu/(Annealed.sigmaBar M n:ℝ))
      (((M.nu/(Annealed.sigmaBar M n:ℝ))^2+
        (‖parentBoundaryCommonOpenCubeCoefficient P f‖/(Annealed.sigmaBar M n:ℝ))^2)/
          (M.nu/(Annealed.sigmaBar M n:ℝ))) (openCubeSet P)
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
        (parentBoundaryCommonOpenCubeCoefficient P f)) :=
    responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet P) M.nu
      (Annealed.sigmaBar M n) M.nu_pos hσ _
  have hEllF := hEll (parentBoundaryCommonCubeBand P n height t ω)
  have hEllC := hEll (parentBoundaryCommonCubeCentered P n height t ω)
  have hsF : Summable (fun j : ℕ => alpha^j*F j) := old_signed_max_trace_series_summable P af hEllF
  have hsC : Summable (fun j : ℕ => alpha^j*C j) := old_signed_max_trace_series_summable P ac hEllC
  have hF0 (j : ℕ) : 0 ≤ F j := (old_signed_max_trace_depth_bounds P af hEllF j).1
  have hC0 (j : ℕ) : 0 ≤ C j := (old_signed_max_trace_depth_bounds P ac hEllC j).1
  have hgeom : Summable (fun j : ℕ => alpha^j) := summable_geometric_of_lt_one ha0 ha1
  have hpoint (j : ℕ) : alpha^j*C j ≤ 2*(alpha^j*F j)+K*alpha^j := by
    have hh := mul_le_mul_of_nonneg_left (parent_history_centered_depth_young M P n height t ω j)
      (pow_nonneg ha0 j)
    change alpha^j*C j ≤ alpha^j*(2*F j+4+
      4*(parentBoundaryCommonCubeCenterValue P n height t ω/(Annealed.sigmaBar M n:ℝ))^2*
        ((Annealed.sigmaBar M n:ℝ)/M.nu)) at hh
    exact hh.trans_eq (by dsimp only [K]; ring)
  have hsum := hsC.tsum_le_tsum hpoint ((hsF.mul_left 2).add (hgeom.mul_left K))
  rw [(hsF.mul_left 2).tsum_add (hgeom.mul_left K),tsum_mul_left,tsum_mul_left,
    tsum_geometric_of_lt_one ha0 ha1] at hsum
  have hnF : 0 ≤ oldSignedMaxTraceHistory P af := mul_nonneg (sub_nonneg.mpr ha1.le)
    (tsum_nonneg (fun j => mul_nonneg (pow_nonneg ha0 j) (hF0 j)))
  have hnC : 0 ≤ oldSignedMaxTraceHistory P ac := mul_nonneg (sub_nonneg.mpr ha1.le)
    (tsum_nonneg (fun j => mul_nonneg (pow_nonneg ha0 j) (hC0 j)))
  rw [parent_history_physical_history,parent_history_centered_history,
    ENNReal.toReal_ofReal hnF,ENNReal.toReal_ofReal hnC]
  calc
    oldSignedMaxTraceHistory P ac=(1-alpha)*(∑' j : ℕ,alpha^j*C j) := rfl
    _ ≤ (1-alpha)*(2*(∑' j : ℕ,alpha^j*F j)+K*(1-alpha)⁻¹) :=
      mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr ha1.le)
    _ = _ := by
      rw [mul_add,←mul_assoc (1-alpha) K, mul_comm (1-alpha) K,
        mul_assoc K,mul_inv_cancel₀ (sub_pos.mpr ha1).ne',mul_one]
      dsimp only [oldSignedMaxTraceHistory,K,alpha,F]
      ring

/-- The ACTUAL centered complete history belongs to L20 without a native
state assumption at the starting label. No infinity is erased by toReal. -/
theorem parent_history_centered_memLp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (P : TriadicCube 2) (n : ℤ) (r : ℕ) (hP : P.scale=n-(r:ℤ))
    (height : ℕ) (hpast : ∀ k<n,nativeInductionState M h k) (t : ℝ) (ht1 : t ≤ 1) :
    MemLp (fun ω => (parentBoundaryCommonCenteredMaxHistory M P n height t ω).toReal) 20
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let F := fun ω => (parentBoundaryBandMaxTraceHistory M n height P t ω).toReal
  let C := fun ω => (parentBoundaryCommonCenteredMaxHistory M P n height t ω).toReal
  let G := fun ω => parentBoundaryCommonCubeCenterValue P n height t ω/(Annealed.sigmaBar M n:ℝ)
  have hF : MemLp F 20 μ := parent_history_physical_memLp M h hM hg P n r hP height hpast t ht1
  have hG40 : MemLp G 40 μ := parent_boundary_common_cube_center_memLp M h hM P n height t 40 (by finiteness)
  have htriple : Real.HolderTriple 40 40 20 := by constructor <;> norm_num
  let parentHistoryFinitenessHolder : ENNReal.HolderTriple 40 40 20 := by
    simpa only [ENNReal.ofReal_ofNat] using htriple.ennrealOfReal
  have hGsq : MemLp (fun ω => G ω^2) 20 μ := by
    have he : (fun ω => G ω^2)=G*G := by funext ω; simp only [Pi.mul_apply,pow_two]
    rw [he]
    exact hG40.mul hG40
  let J := fun ω => 2*F ω+4+(4*((Annealed.sigmaBar M n:ℝ)/M.nu))*(G ω^2)
  have hJ : MemLp J 20 μ := ((hF.const_mul 2).add (memLp_const (4:ℝ))).add
    (hGsq.const_mul (4*((Annealed.sigmaBar M n:ℝ)/M.nu)))
  apply hJ.mono' ((parent_boundary_common_centered_history_measurable M P n height t).ennreal_toReal.aestronglyMeasurable)
  filter_upwards [] with ω
  rw [Real.norm_of_nonneg (ENNReal.toReal_nonneg : 0 ≤ C ω)]
  exact (parent_history_centered_coarse_young M P n height t ω).trans_eq (by dsimp only [J,F,G]; ring)

end
end ASDExplicitGamma.Native
