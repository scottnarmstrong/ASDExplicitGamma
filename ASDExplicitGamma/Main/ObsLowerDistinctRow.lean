module

public import ASDExplicitGamma.Main.ObsLowerValueRow
public import ASDExplicitGamma.Main.HilbertCoordinateMembership
public import ASDExplicitGamma.Main.HilbertPositiveTriangle
public import ASDExplicitGamma.Triadic.DiagEstimates
public import ASDExplicitGamma.Triadic.PositiveNormAggregation

/-! The uncentered covariance feedback row (distinct first potentials) on every aligned source
mesh. The value cap is `b`; no centering and no dependence on the root scale. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped BigOperators
noncomputable section

local instance pureFluxCenteredRowFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume


theorem obsDirection_grad (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (w : WhiteNoise) (x : Vec 2) (i : Fin 2) :
    (mainQ3DirectionW2 Q b L w).value.grad x i =
      q3Convolution b L (mainQ3JetIndex (.first i)) w x := by
  exact mainQ3DirectionW2_jet Q b L w (.first i) x

/-- The row sum retains a distinct potential in each covariance direction. -/
def obsDistinctRow {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (m : ℕ)
    (z : ι → H10Function (openCubeSet Q)) : Vec 2 → Vec 2 :=
  fun x => ∑ l ∈ s, lemmaVPlanarRowField (diagInterpolant Q m)
    (mainQ3DirectionW2 Q b L (e l)).value (z l).toH1Function x

private theorem obs_distinct_tile_bound {ι : Type*}
    (e : HilbertBasis ι ℝ WhiteNoise) (s : Finset ι) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (m : ℕ)
    (z : ι → H10Function (openCubeSet Q))
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q m) :
    let I := diagInterpolant Q m
    let S := obsDistinctRow e s b L Q m z
    let M := Real.sqrt (b^2)
    let G := Real.sqrt ((78/5:ℝ)*b^2/L.1^2)
    let H := Real.sqrt ((23244/25:ℝ)*b^2/L.1^4)
    (∀ i : Fin 2, Summable (fun k => (Real.sqrt 3)^(k+1)*energy U
      (cubeIncrement U (k+1) (fun x => S x i)))) ∧
    vectorPositiveHaarNorm U S ≤
      (M+cubeScaleFactor U*planarC1*G)*
        Real.sqrt (∑ l : s, vectorPositiveHaarEnergy U (I (z l).toH1Function).grad) +
      G*Real.sqrt (∑ l : s, primalEnergy U (Real.sqrt 3)
        ((z l).toH1Function-I (z l).toH1Function).toFun) +
      cubeScaleFactor U*planarC1*H*Real.sqrt (∑ l : s, energy U
        ((z l).toH1Function-I (z l).toH1Function).toFun) := by
  intro I S M G H
  let F : Vec 2 → EuclideanSpace ℝ (s × Fin 2) :=
    fun x => WithLp.toLp 2 (fun p => (I (z p.1).toH1Function).grad x p.2)
  let R : Vec 2 → EuclideanSpace ℝ s := fun x => WithLp.toLp 2
    (fun l => (-((z l).toH1Function-I (z l).toH1Function)).toFun x)
  let A := obsValueRow e s b L U
  let B := pureFluxQ3DerivativeRow e s b L U
  let C := fun x => A.toFun x (F x)+B.toFun x (R x)
  have hzero (l : ι) : lemmaVAffinePotential
      (isOpenBoundedConvexDomain_openCubeSet Q) 0 (z l) = (z l).toH1Function := by
    ext x
    · simp only [lemmaVAffinePotential, H1Function.add_toFun,
        H1Function.affineOnIsSobolevRegularDomain_apply]
      simp
    · simp only [lemmaVAffinePotential, H1Function.add_grad,
        H1Function.affineOnIsSobolevRegularDomain_grad]
      simp only [zero_add]
  have hFmem : MemLp F 2 (normalizedCubeMeasure U) := by
    apply memLp_piLp_iff.mpr
    intro p
    exact memLp_on_descendant_of_memLp hU
      ((I (z p.1).toH1Function).grad_memL2_normalizedCubeMeasure p.2)
  have hFP := main_hilbert_summable_of_coordinates U hFmem (fun p => by
    simpa only [hzero, F, WithLp.ofLp_toLp, I] using
      diagInterpolant_gradient_summable Q m 0 (z p.1) U hU p.2)
  have hRmem : MemLp R 2 (normalizedCubeMeasure U) := by
    apply memLp_piLp_iff.mpr
    intro l
    exact ((-((z l).toH1Function-I (z l).toH1Function)).restrictToOpenSubcube hU).memL2_normalizedCubeMeasure
  have hRP := main_hilbert_summable_of_coordinates U hRmem (fun l => by
    let r := (-((z l).toH1Function-I (z l).toH1Function)).restrictToOpenSubcube hU
    exact positiveHaarIncrementSeries_summable U r.memL2_normalizedCubeMeasure
      r.grad_memL2_normalizedCubeMeasure r.hasWeakGradient)
  have hq : 1 < Real.sqrt 3 := by
    nlinarith only [Real.sqrt_nonneg (3:ℝ), Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  have hq9 : Real.sqrt 3 < 9 := by
    nlinarith only [Real.sqrt_nonneg (3:ℝ), Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  have hM : ∀ᵐ x ∂normalizedCubeMeasure U, ‖A.toFun x‖ ≤ M :=
    Filter.Eventually.of_forall (fun x => obsValueRow_norm_le e s b L U x)
  have hG : ∀ᵐ x ∂normalizedCubeMeasure U, ‖B.toFun x‖ ≤ G :=
    Filter.Eventually.of_forall (pureFluxQ3DerivativeRow_norm_le e s b L U)
  have hDA : ∀ᵐ x ∂normalizedCubeMeasure U, ∀ c : EuclideanSpace ℝ (s × Fin 2),
      (∑ i, ‖A.grad x i c‖^2) ≤ G^2*‖c‖^2 := by
    apply Filter.Eventually.of_forall
    intro x c
    dsimp only [G]
    rw [Real.sq_sqrt (by positivity : 0 ≤ (78/5:ℝ)*b^2/L.1^2)]
    exact obsValueRow_combined_gradient_le e s b L U x c
  have hDB : ∀ᵐ x ∂normalizedCubeMeasure U, ∀ c : EuclideanSpace ℝ s,
      (∑ i, ‖B.grad x i c‖^2) ≤ H^2*‖c‖^2 := by
    apply Filter.Eventually.of_forall
    intro x c
    dsimp only [H]
    rw [Real.sq_sqrt (by positivity : 0 ≤ (23244/25:ℝ)*b^2/L.1^4)]
    exact pureFluxQ3DerivativeRow_combined_gradient_le e s b L U x c
  have ha := pureFlux_positive_product_of_combined_bounds A hq hq9 hFmem hFP
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hM hDA
  have hb := pureFlux_positive_product_of_combined_bounds B hq hq9 hRmem hRP
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hG hDB
  have hc1 : Real.sqrt (haarPoincareM2 (Real.sqrt 3)) = planarC1 := by
    unfold haarPoincareM2
    rw [mul_comm (1-Real.sqrt 3/9)]
    rfl
  rw [hc1] at ha hb
  have hAmem := A.product_memLp hFmem
  have hBmem := B.product_memLp hRmem
  have hCmem : MemLp C 2 (normalizedCubeMeasure U) := hAmem.add hBmem
  have hc := main_hilbert_positive_add U hAmem hBmem ha.1 hb.1
  have hCcoord (i : Fin 2) : MemLp (fun x => (C x).ofLp i) 2 (normalizedCubeMeasure U) := by
    let pr : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) i
    simpa only [pr, Function.comp_def, PiLp.proj_apply] using pr.comp_memLp' hCmem
  have hCP (i : Fin 2) := main_hilbert_coordinate_summable U hCmem hc.1 i
  have hrow : S = fun x => planarQuarterTurn (fun i => (C x).ofLp i) := by
    funext x i
    change (∑ l ∈ s, lemmaVPlanarRowField I
      (mainQ3DirectionW2 Q b L (e l)).value (z l).toH1Function x) i = _
    simp only [Finset.sum_apply, lemmaVH2_rowField_eq]
    rw [← Finset.sum_coe_sort s]
    fin_cases i <;>
      simp [C, A, B, F, R, obsValueRow_apply,
        pureFluxQ3DerivativeRow_apply, mainQ3DirectionW2_value,
        obsDirection_grad, planarQuarterTurn, H1Function.neg_toFun,
        Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
        mul_add, add_mul, sub_mul, mul_sub, mul_comm, mul_left_comm, mul_assoc] <;> ring
  have hnorm : vectorPositiveHaarNorm U S = hilbertPositiveHaarNorm U (Real.sqrt 3) C := by
    rw [hrow, vectorPositiveHaarNorm_quarterTurn]
    simpa only [WithLp.toLp_ofLp] using
      (main_hilbertPositive_eq_vectorPositive U hCcoord hCP).symm
  have hPF : hilbertPositiveHaarNorm U (Real.sqrt 3) F =
      Real.sqrt (∑ l : s, vectorPositiveHaarEnergy U (I (z l).toH1Function).grad) := by
    unfold hilbertPositiveHaarNorm
    rw [main_hilbertPrimalEnergy_euclidean U hFmem hFP]
    simp only [F, WithLp.ofLp_toLp, Fintype.sum_prod_type, vectorPositiveHaarEnergy]
  have hPR : hilbertPositiveHaarNorm U (Real.sqrt 3) R =
      Real.sqrt (∑ l : s, primalEnergy U (Real.sqrt 3)
        ((z l).toH1Function-I (z l).toH1Function).toFun) := by
    unfold hilbertPositiveHaarNorm
    rw [main_hilbertPrimalEnergy_euclidean U hRmem hRP]
    simp only [R, WithLp.ofLp_toLp, H1Function.neg_toFun, primalEnergy_neg]
  have hLR : hilbertL2Norm U R = Real.sqrt (∑ l : s, energy U
      ((z l).toH1Function-I (z l).toH1Function).toFun) := by
    unfold hilbertL2Norm
    rw [main_hilbertEnergy_euclidean U hRmem]
    simp only [R, WithLp.ofLp_toLp, H1Function.neg_toFun, energy_neg]
  have hLF := main_hilbertL2_le_positive U hFmem hFP
  have hcoef : 0 ≤ cubeScaleFactor U*planarC1*G :=
    mul_nonneg (mul_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' U).le
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  refine ⟨?_, ?_⟩
  · rw [hrow]
    exact positive_series_quarterTurn U (fun x i => (C x).ofLp i) hCP
  · rw [hnorm]
    have hfirst : M*hilbertPositiveHaarNorm U (Real.sqrt 3) F +
        cubeScaleFactor U*planarC1*G*hilbertL2Norm U F ≤
      M*hilbertPositiveHaarNorm U (Real.sqrt 3) F +
        cubeScaleFactor U*planarC1*G*hilbertPositiveHaarNorm U (Real.sqrt 3) F :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hLF hcoef)
    have hsum := (hc.2.trans (add_le_add ha.2 hb.2)).trans
      (add_le_add hfirst (le_refl _))
    rw [hPF, hPR, hLR] at hsum
    convert hsum using 1 <;> ring


/-- The genuine centered feedback row on any aligned DIAG source mesh.
Its covariance operator moments are 15.6 and 929.76, with no common-input premise. -/
theorem obs_distinct_h10_row_bound {ι : Type*}
    (e : HilbertBasis ι ℝ WhiteNoise) (s : Finset ι) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (m : ℕ)
    (z : ι → H10Function (openCubeSet Q)) :
    let S := obsDistinctRow e s b L Q m z
    (∀ U ∈ descendantsAtDepth Q m, ∀ i : Fin 2,
      Summable (fun k => (Real.sqrt 3)^(k+1)*energy U
        (cubeIncrement U (k+1) (fun x => S x i)))) ∧
    Real.sqrt (lemmaVTiledPositiveEnergy Q m S) ≤
      (Real.sqrt (b^2) +
        diagMeshRadius Q m*(36/25)*Real.sqrt ((78/5)*b^2/L.1^2) +
        (diagMeshRadius Q m)^2*(57/200)*Real.sqrt ((23244/25)*b^2/L.1^4))*
          Real.sqrt (∑ l ∈ s, lemmaVTiledWeakEnergy Q m (z l).toH1Function.grad) := by
  intro S
  let I := diagInterpolant Q m
  let r := diagMeshRadius Q m
  let M := Real.sqrt (b^2)
  let G := Real.sqrt ((78/5:ℝ)*b^2/L.1^2)
  let H := Real.sqrt ((23244/25:ℝ)*b^2/L.1^4)
  let W := ∑ l : s, lemmaVTiledWeakEnergy Q m (z l).toH1Function.grad
  let E := fun U : TriadicCube 2 => vectorPositiveHaarEnergy U S
  let F := fun U : TriadicCube 2 =>
    ∑ l : s, vectorPositiveHaarEnergy U (I (z l).toH1Function).grad
  let P := fun U : TriadicCube 2 => ∑ l : s, primalEnergy U (Real.sqrt 3)
    ((z l).toH1Function-I (z l).toH1Function).toFun
  let N := fun U : TriadicCube 2 => ∑ l : s, energy U
    ((z l).toH1Function-I (z l).toH1Function).toFun
  have hr : 0 ≤ r := (diagMeshRadius_pos Q m).le
  have hG : 0 ≤ G := Real.sqrt_nonneg _
  have hH : 0 ≤ H := Real.sqrt_nonneg _
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  have hc1 : 0 ≤ planarC1 := Real.sqrt_nonneg _
  have hW : 0 ≤ W := Finset.sum_nonneg fun l _ => lemmaVTiledWeakEnergy_nonneg Q m _
  have hlocal (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q m) :=
    obs_distinct_tile_bound e s b L Q m z U hU
  have hE (U : TriadicCube 2) (_hU : U ∈ descendantsAtDepth Q m) : 0 ≤ E U :=
    vectorPositiveHaarEnergy_nonneg U S
  have hF (U : TriadicCube 2) (_hU : U ∈ descendantsAtDepth Q m) : 0 ≤ F U :=
    Finset.sum_nonneg fun l _ => vectorPositiveHaarEnergy_nonneg U _
  have hP (U : TriadicCube 2) (_hU : U ∈ descendantsAtDepth Q m) : 0 ≤ P U :=
    Finset.sum_nonneg fun l _ => primalEnergy_nonneg U _ (Real.sqrt_nonneg _) _
  have hN (U : TriadicCube 2) (_hU : U ∈ descendantsAtDepth Q m) : 0 ≤ N U :=
    Finset.sum_nonneg fun l _ => energy_nonneg U _
  have hlocalNorm (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q m) :
      Real.sqrt (E U) ≤ (M+r*planarC1*G)*Real.sqrt (F U) +
        G*Real.sqrt (P U)+r*planarC1*H*Real.sqrt (N U) := by
    have h := (hlocal U hU).2
    rw [cubeScaleFactor_descendant_eq_div_pow hU] at h
    exact h
  have hagg := sqrt_descendantsAverage_energy_bound_three Q m E F P N
    (add_nonneg hM (mul_nonneg (mul_nonneg hr hc1) hG)) hG
    (mul_nonneg (mul_nonneg hr hc1) hH) hE hF hP hN hlocalNorm
  have havgSum (f : s → TriadicCube 2 → ℝ) :
      descendantsAverage Q m (fun U => ∑ l : s, f l U) =
        ∑ l : s, descendantsAverage Q m (f l) := by
    dsimp only [descendantsAverage]
    rw [Finset.sum_comm, Finset.mul_sum]
  have hFavg : descendantsAverage Q m F =
      ∑ l : s, lemmaVTiledPositiveEnergy Q m (I (z l).toH1Function).grad :=
    havgSum _
  have hPavg : descendantsAverage Q m P =
      ∑ l : s, diagTiledScalarPositiveEnergy Q m
        ((z l).toH1Function-I (z l).toH1Function).toFun := havgSum _
  have hNavg : descendantsAverage Q m N =
      ∑ l : s, energy Q ((z l).toH1Function-I (z l).toH1Function).toFun := by
    rw [havgSum]
    apply Finset.sum_congr rfl
    intro l hl
    exact (energy_eq_descendantsAverage Q m
      ((z l).toH1Function-I (z l).toH1Function).memL2_normalizedCubeMeasure).symm
  have hFle : descendantsAverage Q m F ≤ W := by
    rw [hFavg]
    exact Finset.sum_le_sum fun l _ => diagInterpolant_h10_gradient_energy_le Q m (z l)
  have hPle : descendantsAverage Q m P ≤ (r*(2/Real.pi+1/2))^2*W := by
    rw [hPavg]
    calc
      _ ≤ ∑ l : s, r^2*(2/Real.pi+1/2)^2*
          lemmaVTiledWeakEnergy Q m (z l).toH1Function.grad :=
        Finset.sum_le_sum fun l _ => diagInterpolant_h10_residual_positive_energy_le Q m (z l)
      _ = _ := by rw [← Finset.mul_sum]; ring
  have hNle : descendantsAverage Q m N ≤ (r*(planarC0+1/2))^2*W := by
    rw [hNavg]
    calc
      _ ≤ ∑ l : s, r^2*(planarC0+1/2)^2*
          lemmaVTiledWeakEnergy Q m (z l).toH1Function.grad :=
        Finset.sum_le_sum fun l _ => diagInterpolant_h10_residual_L2_energy_le Q m (z l)
      _ = _ := by rw [← Finset.mul_sum]; ring
  have hPF := Real.sqrt_le_sqrt hFle
  have hPP := diagSqrt_energy_bound hW
    (mul_nonneg hr (by positivity : 0 ≤ 2/Real.pi+1/2)) hPle
  have hPN := diagSqrt_energy_bound hW
    (mul_nonneg hr (add_nonneg (Real.sqrt_nonneg _) (by norm_num))) hNle
  have h1 : r*(planarC1+2/Real.pi+1/2)*G ≤ r*(36/25)*G :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left lemmaVH2C1_outward hr) hG
  have h2 : r^2*(planarC1*(planarC0+1/2))*H ≤ r^2*(57/200)*H :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left lemmaVH2C2_outward (sq_nonneg r)) hH
  refine ⟨fun U hU => (hlocal U hU).1, ?_⟩
  have hbound : Real.sqrt (lemmaVTiledPositiveEnergy Q m S) ≤
      (M+r*(36/25)*G+r^2*(57/200)*H)*Real.sqrt W := by
    calc
      _ ≤ (M+r*planarC1*G)*Real.sqrt (descendantsAverage Q m F) +
          G*Real.sqrt (descendantsAverage Q m P) +
          r*planarC1*H*Real.sqrt (descendantsAverage Q m N) := hagg
      _ ≤ (M+r*planarC1*G)*Real.sqrt W +
          G*(r*(2/Real.pi+1/2)*Real.sqrt W)+
          r*planarC1*H*(r*(planarC0+1/2)*Real.sqrt W) :=
        add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left hPF (add_nonneg hM (mul_nonneg (mul_nonneg hr hc1) hG)))
          (mul_le_mul_of_nonneg_left hPP hG))
          (mul_le_mul_of_nonneg_left hPN (mul_nonneg (mul_nonneg hr hc1) hH))
      _ = (M+r*(planarC1+2/Real.pi+1/2)*G+
          r^2*(planarC1*(planarC0+1/2))*H)*Real.sqrt W := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (add_le_add (add_le_add le_rfl h1) h2) (Real.sqrt_nonneg W)
  have hWsum : W = ∑ l ∈ s, lemmaVTiledWeakEnergy Q m (z l).toH1Function.grad :=
    Finset.sum_coe_sort s (fun l => lemmaVTiledWeakEnergy Q m (z l).toH1Function.grad)
  rw [hWsum] at hbound
  simpa only [M, G, H, r] using hbound

end
end ASDExplicitGamma.Inverse
