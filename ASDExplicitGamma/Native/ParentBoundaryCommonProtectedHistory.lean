module

public import ASDExplicitGamma.Native.ParentBoundaryCommonCenteredHistory
public import ASDExplicitGamma.Native.ParentBoundaryCommonProtectedTransport

/-! Complete actual history transport in the exact protected source frame. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The actual sharp drift depends on the observation cube only through its
scale. The common source square P is retained unchanged. -/
theorem parent_boundary_common_protected_drift_scale_eq
    (M : ABKModel 2) (h : ℝ) (P Q R : TriadicCube 2) (m n : ℤ) (height depth : ℕ)
    (hQR : Q.scale=R.scale) :
    parentBoundaryCommonProtectedRootDrift M h P Q m n height depth=
      parentBoundaryCommonProtectedRootDrift M h P R m n height depth := by
  simp only [parentBoundaryCommonProtectedRootDrift,parentBoundaryCommonProtectedShellCoefficient,
    parentBoundaryCommonRowCoefficient,diagMeshRadius,cubeScaleFactor,hQR]

/-- Exact sharp actual L20 spatial maximum bound, including the precise
9^(j/20) population payment. No independence or leaf estimate is assumed. -/
theorem parent_boundary_common_protected_depth_max_L20
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (P : TriadicCube 2) (n : ℤ) (r : ℕ) (hr : r ≤ 5) (hP : P.scale=n-(r:ℤ))
    (height : ℕ) (hheight : 1 ≤ height) (hpast : ∀ k<n,nativeInductionState M h k)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (j : ℕ) :
    eLpNorm (parentBoundaryCommonCenteredDepthMax M P n height t j) 20
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ((9:ℝ≥0∞)^j)^((1:ℝ)/20)*
        ENNReal.ofReal (lpNorm (cutoffTraceDefect M n (n-((r+j:ℕ):ℤ))) 20 (Cutoff.cutoffSampleLaw M).toMeasure+
          t*parentBoundaryCommonProtectedRootDrift M h P (originCube 2 (n-((r+j:ℕ):ℤ))) (n-(j:ℤ)) n height (r+j)) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let B := lpNorm (cutoffTraceDefect M n (n-((r+j:ℕ):ℤ))) 20 μ+
    t*parentBoundaryCommonProtectedRootDrift M h P (originCube 2 (n-((r+j:ℕ):ℤ))) (n-(j:ℤ)) n height (r+j)
  let f := fun Q : SquareCells P j => fun ω => ENNReal.ofReal
    (squareTrace Q.val M.nu (Annealed.sigmaBar M n) (parentBoundaryCommonCubeObserved Q.property n height t ω))
  have hf (Q : SquareCells P j) : Measurable (f Q) :=
    (parent_boundary_common_cube_trace_measurable M Q.property n height t).ennreal_ofReal
  have hb (Q : SquareCells P j) (_hQ : Q ∈ (Finset.univ : Finset (SquareCells P j))) :
      eLpNorm (f Q) 20 μ ≤ ENNReal.ofReal B := by
    have hscale : Q.val.scale=n-((r+j:ℕ):ℤ) := by
      rw [scale_eq_sub_of_mem_descendantsAtDepth Q.property,hP]
      push_cast
      ring
    let T := fun ω => squareTrace Q.val M.nu (Annealed.sigmaBar M n)
      (parentBoundaryCommonCubeObserved Q.property n height t ω)
    have hT0 (ω) : 0 ≤ T ω := parent_boundary_common_square_trace_nonneg Q.val M.nu (Annealed.sigmaBar M n)
      M.nu_pos (Annealed.sigmaBar_characterization M n).1 _
    have hm : MemLp T 20 μ := by
      simpa only [show ENNReal.ofReal (20:ℝ)=(20:ℝ≥0∞) by norm_num] using
        (parent_boundary_common_cube_trace_memLp M h hM Q.property n height hheight t 20 (by norm_num)).1
    change eLpNorm (ENNReal.ofReal ∘ T) 20 μ ≤ _
    rw [eLpNorm_ofReal T (Filter.Eventually.of_forall hT0),←ENNReal.ofReal_toReal hm.eLpNorm_ne_top]
    apply ENNReal.ofReal_le_ofReal
    have hQm : Q.val.scale ≤ n-(j:ℤ) := by omega
    have hgap : n-(j:ℤ)-Q.val.scale ≤ 5 := by omega
    have hmn : n-(j:ℤ) ≤ n := by omega
    have hh := parent_boundary_common_protected_root_transport M h hM hg Q.property (n-(j:ℤ)) n
      hQm hgap hmn (r+j) hscale height hheight hpast t ht0 ht1
    rw [hscale,parent_boundary_common_protected_drift_scale_eq M h P Q.val
      (originCube 2 (n-((r+j:ℕ):ℤ))) (n-(j:ℤ)) n height (r+j) (by change Q.val.scale=n-((r+j:ℕ):ℤ); exact hscale)] at hh
    exact hh
  have hmax := history_finite_max_L20 μ Finset.univ f hf (ENNReal.ofReal B) hb
  have hcard : ((Finset.univ : Finset (SquareCells P j)).card:ℝ≥0∞)=(9:ℝ≥0∞)^j := by
    simp only [Finset.card_univ,SquareCells,Fintype.card_coe,descendantsAtDepth_card]
    norm_num
  rw [hcard] at hmax
  exact hmax


/-- Exact complete physical drift clock for a common-centered source-square
history. It is defined in extended reals before any finiteness comparison. -/
def parentBoundaryCommonProtectedHistoryDrift (M : ABKModel 2) (h : ℝ) (P : TriadicCube 2)
    (n : ℤ) (height r : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (1-inverseHistoryDiscount)*∑' j : ℕ,ENNReal.ofReal
    (coldHistoryBeta^j*parentBoundaryCommonProtectedRootDrift M h P
      (originCube 2 (n-((r+j:ℕ):ℤ))) (n-(j:ℤ)) n height (r+j))

/-- The complete ACTUAL centered maximum history obeys the native initial
strong-history cap plus time times its actual physical drift clock. All
spatial populations and infinitely many depths remain in the conclusion.
No history, norm, derivative or geometric-sum estimate is a premise. -/
theorem parent_boundary_common_protected_history_transport
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (P : TriadicCube 2) (n : ℤ) (r : ℕ) (hr : r ≤ 5) (hP : P.scale=n-(r:ℤ))
    (hstate : nativeInductionState M h n) (height : ℕ) (hheight : 1 ≤ height)
    (hpast : ∀ k<n,nativeInductionState M h k) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    eLpNorm (parentBoundaryCommonCenteredMaxHistory M P n height t) 20
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((coldHistoryBeta^r)⁻¹*((2379/2500:ℝ)*theta M))+
        ENNReal.ofReal t*parentBoundaryCommonProtectedHistoryDrift M h P n height r := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let S := (2379/2500:ℝ)*theta M
  let B := fun j : ℕ => lpNorm (cutoffTraceDefect M n (n-((r+j:ℕ):ℤ))) 20 μ
  let D := fun j : ℕ => parentBoundaryCommonProtectedRootDrift M h P (originCube 2 (n-((r+j:ℕ):ℤ))) (n-(j:ℤ)) n height (r+j)
  let F := fun j : ℕ => fun ω => ENNReal.ofReal (inverseHistoryDiscount^j)*
    parentBoundaryCommonCenteredDepthMax M P n height t j ω
  have hD (j) : 0 ≤ D j := parent_boundary_common_protected_root_drift_nonneg M h P _ (n-(j:ℤ)) n height _
  have hB (j) : 0 ≤ B j := lpNorm_nonneg
  have hbeta (j) : 0 ≤ coldHistoryBeta^j := pow_nonneg coldHistoryBeta_pos.le _
  have ha : 0 ≤ 1-inverseHistoryDiscount := sub_nonneg.mpr inverse_history_discount_range.2.le
  have hm (j) : Measurable (F j) :=
    (parent_boundary_common_centered_depth_max_measurable M P n height t j).const_mul _
  have hb (j : ℕ) : eLpNorm (F j) 20 μ ≤ ENNReal.ofReal (coldHistoryBeta^j*(B j+t*D j)) := by
    change eLpNorm (fun ω => ENNReal.ofReal (inverseHistoryDiscount^j)*
      parentBoundaryCommonCenteredDepthMax M P n height t j ω) 20 μ ≤ _
    rw [history_constant_mul_L20 μ _ _ (parent_boundary_common_centered_depth_max_measurable M P n height t j)]
    have hh := parent_boundary_common_protected_depth_max_L20 M h hM hg P n r hr hP height hheight hpast t ht0 ht1 j
    apply (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq
    rw [←mul_assoc,old_signed_max_history_population_weight,←ENNReal.ofReal_mul (hbeta j)]
  have hs := old_signed_shifted_strong_profile M n r S
    (mul_nonneg (by norm_num) (cold_theta_pos M).le) hstate.2.1
  have hsplit : (∑' j : ℕ,ENNReal.ofReal (coldHistoryBeta^j*(B j+t*D j)))=
      (∑' j : ℕ,ENNReal.ofReal (coldHistoryBeta^j*B j))+
        ENNReal.ofReal t*(∑' j : ℕ,ENNReal.ofReal (coldHistoryBeta^j*D j)) := by
    have he (j : ℕ) : ENNReal.ofReal (coldHistoryBeta^j*(B j+t*D j))=
        ENNReal.ofReal (coldHistoryBeta^j*B j)+ENNReal.ofReal t*ENNReal.ofReal (coldHistoryBeta^j*D j) := by
      rw [mul_add,ENNReal.ofReal_add (mul_nonneg (hbeta j) (hB j))
        (mul_nonneg (hbeta j) (mul_nonneg ht0 (hD j)))]
      rw [←ENNReal.ofReal_mul ht0]
      congr 1
      ring
    simp_rw [he]
    rw [ENNReal.tsum_add,ENNReal.tsum_mul_left]
  have hinitial : ENNReal.ofReal (1-inverseHistoryDiscount)*(∑' j : ℕ,ENNReal.ofReal (coldHistoryBeta^j*B j)) ≤
      ENNReal.ofReal ((coldHistoryBeta^r)⁻¹*S) := by
    rw [←ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (hbeta j) (hB j)) hs.1,
      ←ENNReal.ofReal_mul ha]
    exact ENNReal.ofReal_le_ofReal hs.2
  change eLpNorm (fun ω => ENNReal.ofReal (1-inverseHistoryDiscount)*∑' j : ℕ,F j ω) 20 μ ≤ _
  rw [history_constant_mul_L20 μ _ _ (Measurable.tsum hm)]
  have hh := mul_le_mul_of_nonneg_left
    ((history_ennreal_tsum_L20 μ F hm).trans (ENNReal.tsum_le_tsum hb))
    (show (0:ℝ≥0∞) ≤ ENNReal.ofReal (1-inverseHistoryDiscount) from bot_le)
  rw [hsplit,mul_add] at hh
  apply hh.trans
  exact add_le_add hinitial (le_of_eq (by
    change ENNReal.ofReal (1-inverseHistoryDiscount)*(ENNReal.ofReal t*∑' j : ℕ,ENNReal.ofReal (coldHistoryBeta^j*D j))=
      ENNReal.ofReal t*(ENNReal.ofReal (1-inverseHistoryDiscount)*∑' j : ℕ,ENNReal.ofReal (coldHistoryBeta^j*D j))
    ac_rfl))

end
end ASDExplicitGamma.Native
