module

public import ASDExplicitGamma.Native.ParentHistoryFrames
public import ASDExplicitGamma.Native.ParentBoundaryCommonHistoryRestore
public import ASDExplicitGamma.Triadic.HaarNormTriangle
public import ASDExplicitGamma.Native.ParentBoundaryCommonHistoryTheta

/-! Complete discounted-depth square-root restoration on the actual cutoff law.
The frame identities are adapted from an earlier version of the argument. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ProbabilityTheory Response Scalar Variational Gaussian Inverse Main Triadic Cold Algsuperdiff.Section3
open scoped ENNReal Nat
noncomputable section

theorem parent_history_sqrt_restore_pointwise
    (M : ABKModel 2) (P : TriadicCube 2) (n : ℤ) (height : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2)
    (hbank : lemmaVInverseHistory P
        (parentHistoryPhysicalFrame M P n height t ω) ((3:ℝ)^(1/4:ℝ)) ≤
      parentBoundaryCommonSingletonHistory M P n n height t ω) :
    Real.sqrt ((parentBoundaryBandMaxTraceHistory M n height P t ω).toReal) ≤
      Real.sqrt ((parentBoundaryCommonCenteredMaxHistory M P n height t ω).toReal) +
        |parentBoundaryCommonCubeCenterValue P n height t ω /
          (Annealed.sigmaBar M n:ℝ)| *
          Real.sqrt (2*parentBoundaryCommonSingletonHistory M P n n height t ω) := by
  classical
  let α : ℝ := inverseHistoryDiscount
  let q : ℝ := (3:ℝ)^(1/4:ℝ)
  let af := parentHistoryPhysicalFrame M P n height t ω
  let ac := parentHistoryCenteredFrame M P n height t ω
  let F := fun j : ℕ => oldSignedMaxTraceDepth P af j
  let C := fun j : ℕ => oldSignedMaxTraceDepth P ac j
  let D := fun j : ℕ => lemmaVInverseDepthMax P af j
  let G := parentBoundaryCommonCubeCenterValue P n height t ω /
    (Annealed.sigmaBar M n:ℝ)
  let B := parentBoundaryCommonSingletonHistory M P n n height t ω
  let a := fun j : ℕ => Real.sqrt ((1-α)*α^j*C j)
  let b := fun j : ℕ => |G| * Real.sqrt ((1-α)*α^j*(2*D j))
  let c := fun j : ℕ => Real.sqrt ((1-α)*α^j*F j)
  have hσ : 0 < (Annealed.sigmaBar M n:ℝ) :=
    (Annealed.sigmaBar_characterization M n).1
  have hEllF : IsEllipticFieldOn (M.nu/(Annealed.sigmaBar M n:ℝ))
      (((M.nu/(Annealed.sigmaBar M n:ℝ))^2+
          (‖parentBoundaryCommonOpenCubeCoefficient P
            (parentBoundaryCommonCubeBand P n height t ω)‖/
          (Annealed.sigmaBar M n:ℝ))^2)/(M.nu/(Annealed.sigmaBar M n:ℝ)))
      (openCubeSet P) af := by
    exact responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet P) M.nu (Annealed.sigmaBar M n) M.nu_pos hσ
      (parentBoundaryCommonOpenCubeCoefficient P
        (parentBoundaryCommonCubeBand P n height t ω))
  have hEllC : IsEllipticFieldOn (M.nu/(Annealed.sigmaBar M n:ℝ))
      (((M.nu/(Annealed.sigmaBar M n:ℝ))^2+
        (‖parentBoundaryCommonOpenCubeCoefficient P
          (parentBoundaryCommonCubeCentered P n height t ω)‖/
          (Annealed.sigmaBar M n:ℝ))^2)/(M.nu/(Annealed.sigmaBar M n:ℝ)))
      (openCubeSet P) ac := by
    exact responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet P) M.nu (Annealed.sigmaBar M n) M.nu_pos hσ
      (parentBoundaryCommonOpenCubeCoefficient P
        (parentBoundaryCommonCubeCentered P n height t ω))
  have hFseries : Summable (fun j : ℕ => α^j*F j) := by
    simpa only [α,F] using old_signed_max_trace_series_summable P af hEllF
  have hCseries : Summable (fun j : ℕ => α^j*C j) := by
    simpa only [α,C] using old_signed_max_trace_series_summable P ac hEllC
  have hDseries : Summable (fun j : ℕ => α^j*D j) := by
    have hh := lemmaVInverseHistory_summable P hEllF
      (Real.one_lt_rpow (by norm_num) (by norm_num) : 1 < (3:ℝ)^(1/4:ℝ))
    simpa only [α,D,inverse_history_discount_eq] using hh
  have hα0 : 0 ≤ α := inverse_history_discount_range.1.le
  have hα1 : α < 1 := inverse_history_discount_range.2
  have hwt (j : ℕ) : 0 ≤ (1-α)*α^j :=
    mul_nonneg (sub_nonneg.mpr hα1.le) (pow_nonneg hα0 j)
  have hF0 (j : ℕ) : 0 ≤ F j := by
    exact (old_signed_max_trace_depth_bounds P af hEllF j).1
  have hC0 (j : ℕ) : 0 ≤ C j := by
    exact (old_signed_max_trace_depth_bounds P ac hEllC j).1
  have hD0 (j : ℕ) : 0 ≤ D j := lemmaVInverseDepthMax_nonneg P af j
  have hdepth (j : ℕ) : Real.sqrt (F j) ≤ Real.sqrt (C j)+|G| * Real.sqrt (2*D j) := by
    have hupper : F j ≤ (Real.sqrt (C j)+|G| * Real.sqrt (2*D j))^2 := by
      unfold F C D G af ac
      unfold oldSignedMaxTraceDepth
      apply Book.Ch02.finsetSupReal_le _ (descendantsAtDepth_nonempty P j)
      intro R hR
      have hcenter : traceDefect (openCubeSet R)
          (parentHistoryCenteredFrame M P n height t ω) 1 ≤
            oldSignedMaxTraceDepth P (parentHistoryCenteredFrame M P n height t ω) j := by
        unfold oldSignedMaxTraceDepth
        exact le_csSup ((Set.toFinite _).image _).bddAbove ⟨R,hR,rfl⟩
      have hcell := parent_boundary_common_cell_physical_trace_restore M P R j hR n height t ω
      have htrace : traceDefect (cubeSet R)
          (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω)
          (Annealed.sigmaBar M n) =
        traceDefect (openCubeSet R)
          (parentHistoryPhysicalFrame M P n height t ω) 1 := by
        have hm := parent_boundary_common_cube_band_coarse_frame M P n height t ω
          (Annealed.sigmaBar M n) (Annealed.sigmaBar_characterization M n).1 hR
        have hm' : coarseBlockMatrix (openCubeSet R)
            (parentHistoryPhysicalFrame M P n height t ω) =
          frameMatrix (Annealed.sigmaBar M n)
            (coarseBlockMatrix (cubeSet R)
              (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω)) := by
          calc
            _ = coarseBlockMatrix (cubeSet R) (parentHistoryPhysicalFrame M P n height t ω) :=
              (coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R
                (parentHistoryPhysicalFrame M P n height t ω)).symm
            _ = _ := hm
        unfold traceDefect
        rw [hm']
        simp [frameMatrix,Matrix.trace_smul,smul_eq_mul]
      rw [htrace] at hcell
      have hroot := Real.sqrt_le_sqrt hcenter
      have hsum : Real.sqrt (traceDefect (openCubeSet R)
          (parentHistoryCenteredFrame M P n height t ω) 1) +
          |parentBoundaryCommonCubeCenterValue P n height t ω /
            (Annealed.sigmaBar M n:ℝ)| *
            Real.sqrt (2*lemmaVInverseDepthMax P
              (parentHistoryPhysicalFrame M P n height t ω) j) ≤
          Real.sqrt (oldSignedMaxTraceDepth P
              (parentHistoryCenteredFrame M P n height t ω) j) +
            |parentBoundaryCommonCubeCenterValue P n height t ω /
              (Annealed.sigmaBar M n:ℝ)| *
              Real.sqrt (2*lemmaVInverseDepthMax P
                (parentHistoryPhysicalFrame M P n height t ω) j) :=
        add_le_add_left hroot _
      have hsum0 : 0 ≤ Real.sqrt (traceDefect (openCubeSet R)
          (parentHistoryCenteredFrame M P n height t ω) 1) +
          |parentBoundaryCommonCubeCenterValue P n height t ω /
            (Annealed.sigmaBar M n:ℝ)| *
            Real.sqrt (2*lemmaVInverseDepthMax P
              (parentHistoryPhysicalFrame M P n height t ω) j) :=
        add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (abs_nonneg _)
          (Real.sqrt_nonneg _))
      have hsum1 : 0 ≤ Real.sqrt (oldSignedMaxTraceDepth P
          (parentHistoryCenteredFrame M P n height t ω) j) +
          |parentBoundaryCommonCubeCenterValue P n height t ω /
            (Annealed.sigmaBar M n:ℝ)| *
            Real.sqrt (2*lemmaVInverseDepthMax P
              (parentHistoryPhysicalFrame M P n height t ω) j) :=
        add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (abs_nonneg _)
          (Real.sqrt_nonneg _))
      have hsq := (sq_le_sq₀ hsum0 hsum1).mpr hsum
      have hcell' := hcell.trans hsq
      exact hcell'
    have hS : 0 ≤ Real.sqrt (C j)+|G| * Real.sqrt (2*D j) :=
      add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
    exact (Real.sqrt_le_iff).mpr ⟨hS,hupper⟩
  have haSq (j : ℕ) : a j^2=(1-α)*α^j*C j := by
    dsimp [a]
    exact Real.sq_sqrt (mul_nonneg (hwt j) (hC0 j))
  have hbSq (j : ℕ) : b j^2=2 * |G|^2*((1-α)*α^j*D j) := by
    dsimp [b]
    rw [mul_pow,Real.sq_sqrt (mul_nonneg (hwt j) (mul_nonneg (by norm_num) (hD0 j)))]
    ring
  have hcSq (j : ℕ) : c j^2=(1-α)*α^j*F j := by
    dsimp [c]
    exact Real.sq_sqrt (mul_nonneg (hwt j) (hF0 j))
  have ha : Summable (fun j : ℕ => a j^2) := by
    rw [show (fun j : ℕ => a j^2)=fun j => (1-α)*(α^j*C j) from by
      funext j
      rw [haSq j]
      ring]
    exact hCseries.mul_left (1-α)
  have hb : Summable (fun j : ℕ => b j^2) := by
    rw [show (fun j : ℕ => b j^2)=fun j => (2 * |G|^2*(1-α))*(α^j*D j) from by
      funext j
      rw [hbSq j]
      ring]
    exact hDseries.mul_left (2 * |G|^2*(1-α))
  have hc : Summable (fun j : ℕ => c j^2) := by
    rw [show (fun j : ℕ => c j^2)=fun j => (1-α)*(α^j*F j) from by
      funext j
      rw [hcSq j]
      ring]
    exact hFseries.mul_left (1-α)
  have hpoint (j : ℕ) : c j ≤ a j+b j := by
    calc
      c j = Real.sqrt ((1-α)*α^j)*Real.sqrt (F j) := by
        dsimp [c]
        rw [Real.sqrt_mul (hwt j)]
      _ ≤ Real.sqrt ((1-α)*α^j)*
          (Real.sqrt (C j)+|G| * Real.sqrt (2*D j)) :=
        mul_le_mul_of_nonneg_left (hdepth j) (Real.sqrt_nonneg _)
      _ = a j+b j := by
        calc
          _ = Real.sqrt ((1-α)*α^j)*Real.sqrt (C j)+
              |G| * (Real.sqrt ((1-α)*α^j)*Real.sqrt (2*D j)) := by ring
          _ = Real.sqrt ((1-α)*α^j*C j)+
              |G| * Real.sqrt ((1-α)*α^j*(2*D j)) := by
            rw [← Real.sqrt_mul (hwt j),← Real.sqrt_mul (hwt j)]
          _ = _ := by
            dsimp [a,b]
  have htriangle := Triadic.sqrt_tsum_sq_le_of_pointwise ha hb
    (fun j => Real.sqrt_nonneg _) hpoint
  have hFroot :
      Real.sqrt ((parentBoundaryBandMaxTraceHistory M n height P t ω).toReal) =
        Real.sqrt (oldSignedMaxTraceHistory P af) := by
    have hFn : 0 ≤ oldSignedMaxTraceHistory P af := by
      unfold oldSignedMaxTraceHistory
      exact mul_nonneg (sub_nonneg.mpr hα1.le)
        (tsum_nonneg (fun j => mul_nonneg (pow_nonneg hα0 j) (hF0 j)))
    rw [parent_history_physical_history M P n height t ω,
      ENNReal.toReal_ofReal hFn]
  have hCroot :
      Real.sqrt ((parentBoundaryCommonCenteredMaxHistory M P n height t ω).toReal) =
        Real.sqrt (oldSignedMaxTraceHistory P ac) := by
    have hCn : 0 ≤ oldSignedMaxTraceHistory P ac := by
      unfold oldSignedMaxTraceHistory
      exact mul_nonneg (sub_nonneg.mpr hα1.le)
        (tsum_nonneg (fun j => mul_nonneg (pow_nonneg hα0 j) (hC0 j)))
    rw [parent_history_centered_history M P n height t ω,
      ENNReal.toReal_ofReal hCn]
  have hFsum : (∑' j : ℕ,c j^2)=oldSignedMaxTraceHistory P af := by
    unfold oldSignedMaxTraceHistory
    calc
      (∑' j : ℕ,c j^2) = ∑' j : ℕ,(1-α)*(α^j*F j) := by
        apply tsum_congr
        intro j
        rw [hcSq j]
        ring
      _ = (1-α)*(∑' j : ℕ,α^j*F j) := tsum_mul_left
      _ = _ := by rfl
  have hCsum : (∑' j : ℕ,a j^2)=oldSignedMaxTraceHistory P ac := by
    unfold oldSignedMaxTraceHistory
    calc
      (∑' j : ℕ,a j^2) = ∑' j : ℕ,(1-α)*(α^j*C j) := by
        apply tsum_congr
        intro j
        rw [haSq j]
        ring
      _ = (1-α)*(∑' j : ℕ,α^j*C j) := tsum_mul_left
      _ = _ := by rfl
  have hqinv : q⁻¹=α := by
    exact inverse_history_discount_eq.symm
  have hinv : lemmaVInverseHistory P af q =
      (1-α)*(∑' j : ℕ,α^j*D j) := by
    unfold lemmaVInverseHistory
    rw [hqinv]
  have hBsum : (∑' j : ℕ,b j^2)=|G|^2*(2*lemmaVInverseHistory P af q) := by
    calc
      (∑' j : ℕ,b j^2) = ∑' j : ℕ,(2 * |G|^2*(1-α))*(α^j*D j) := by
        apply tsum_congr
        intro j
        rw [hbSq j]
        ring
      _ = (2 * |G|^2*(1-α))*(∑' j : ℕ,α^j*D j) := tsum_mul_left
      _ = |G|^2*(2*lemmaVInverseHistory P af q) := by rw [hinv]; ring
  have hbroot : Real.sqrt (∑' j : ℕ,b j^2) =
      |G| * Real.sqrt (2*lemmaVInverseHistory P af q) := by
    rw [hBsum,Real.sqrt_mul (sq_nonneg |G|),Real.sqrt_sq_eq_abs]
    rw [abs_of_nonneg (abs_nonneg G)]
  have htriangle' : Real.sqrt (oldSignedMaxTraceHistory P af) ≤
      Real.sqrt (oldSignedMaxTraceHistory P ac)+
        |G| * Real.sqrt (2*lemmaVInverseHistory P af q) := by
    calc
      _ = Real.sqrt (∑' j : ℕ,c j^2) := by rw [hFsum]
      _ ≤ Real.sqrt (∑' j : ℕ,a j^2)+Real.sqrt (∑' j : ℕ,b j^2) := htriangle.2
      _ = _ := by rw [hCsum,hbroot]
  rw [hFroot,hCroot]
  have hbank2 : 2*lemmaVInverseHistory P af q ≤ 2*B := by nlinarith [hbank]
  calc
    _ ≤ Real.sqrt (oldSignedMaxTraceHistory P ac)+
        |G| * Real.sqrt (2*lemmaVInverseHistory P af q) := htriangle'
    _ ≤ Real.sqrt (oldSignedMaxTraceHistory P ac)+|G| * Real.sqrt (2*B) := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hbank2) (abs_nonneg G)) _
    _ = _ := by simp only [G,B]

theorem parent_history_sqrt_restore_ae
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (P : TriadicCube 2) (n : ℤ)
    (r : ℕ) (hr : r ≤ 5) (hP : P.scale=n-(r:ℤ))
    (height : ℕ) (hpast : ∀ k<n,nativeInductionState M h k)
    (t : ℝ) (ht1 : t ≤ 1) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Real.sqrt ((parentBoundaryBandMaxTraceHistory M n height P t ω).toReal) ≤
        Real.sqrt ((parentBoundaryCommonCenteredMaxHistory M P n height t ω).toReal) +
          |parentBoundaryCommonCubeCenterValue P n height t ω /
            (Annealed.sigmaBar M n:ℝ)| *
            Real.sqrt (2*parentBoundaryCommonSingletonHistory M P n n height t ω) := by
  have hbank0 := parent_boundary_common_singleton_physical_source M h hM hg P n n
    (by rw [hP]; omega) (by rw [hP]; omega) le_rfl height hpast t ht1
  filter_upwards [hbank0] with ω hω
  have hσne : (Annealed.sigmaBar M n:ℝ) ≠ 0 := (Annealed.sigmaBar_characterization M n).1.ne'
  have hmax : max
      (lemmaVTileHistory P 0 (parentHistoryPhysicalFrame M P n height t ω))
      (pureFluxSourceTileHistory P 0 (parentHistoryPhysicalFrame M P n height t ω)) ≤
      parentBoundaryCommonSingletonHistory M P n n height t ω := by
    change max
        (lemmaVTileHistory P 0 (parentHistoryPhysicalFrame M P n height t ω))
        (pureFluxSourceTileHistory P 0 (parentHistoryPhysicalFrame M P n height t ω)) ≤
      ((Annealed.sigmaBar M n:ℝ)/(Annealed.sigmaBar M n:ℝ))*
        parentBoundaryCommonSingletonHistory M P n n height t ω at hω
    simpa only [div_self hσne, one_mul] using hω
  have hrootmem : P ∈ descendantsAtDepth P 0 := by simp
  have hbank : lemmaVInverseHistory P
      (parentHistoryPhysicalFrame M P n height t ω) ((3:ℝ)^(1/4:ℝ)) ≤
      parentBoundaryCommonSingletonHistory M P n n height t ω := by
    exact (pureFlux_source_tile_history_member_le P 0 _ P hrootmem).trans
      (le_trans (le_max_right _ _) hmax)
  exact parent_history_sqrt_restore_pointwise M P n height t ω hbank

end
end ASDExplicitGamma.Native
