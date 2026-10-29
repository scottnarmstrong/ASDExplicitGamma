module

public import ASDExplicitGamma.Native.ParentBoundaryCommonDistinctTile

/-! Complete tiling aggregation of the common-center distinct-potential row. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Main Triadic Variational Inverse
open scoped BigOperators
noncomputable section

/-- Common-center operator row coefficient, with the actual parent value radius. -/
def parentBoundaryCommonFeedbackCoefficient (P Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (m : ℕ) : ℝ :=
  Real.sqrt (b^2*((78/5:ℝ)/2)*(cubeScaleFactor P/L.1)^2) +
    diagMeshRadius Q m*(36/25)*Real.sqrt ((78/5)*b^2/L.1^2) +
    (diagMeshRadius Q m)^2*(57/200)*Real.sqrt ((23244/25)*b^2/L.1^4)

/-- The genuine centered feedback row on any aligned DIAG source mesh.
Its value radius is the original parent radius; its covariance operator
moments are 15.6 and 929.76, with no common-input premise. -/
theorem parent_boundary_common_distinct_h10_row_bound {ι : Type*}
    (e : HilbertBasis ι ℝ WhiteNoise) (s : Finset ι) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (P0 Q : TriadicCube 2) (m : ℕ)
    (hQP : cubeSet Q ⊆ cubeSet P0)
    (z : ι → H10Function (openCubeSet Q)) :
    let S := parentBoundaryCommonDistinctRow e s b L P0 Q m z
    (∀ U ∈ descendantsAtDepth Q m, ∀ i : Fin 2,
      Summable (fun k => (Real.sqrt 3)^(k+1)*energy U
        (cubeIncrement U (k+1) (fun x => S x i)))) ∧
    Real.sqrt (lemmaVTiledPositiveEnergy Q m S) ≤
      (Real.sqrt (b^2*((78/5:ℝ)/2)*(cubeScaleFactor P0/L.1)^2) +
        diagMeshRadius Q m*(36/25)*Real.sqrt ((78/5)*b^2/L.1^2) +
        (diagMeshRadius Q m)^2*(57/200)*Real.sqrt ((23244/25)*b^2/L.1^4))*
          Real.sqrt (∑ l ∈ s, lemmaVTiledWeakEnergy Q m (z l).toH1Function.grad) := by
  intro S
  let I := diagInterpolant Q m
  let r := diagMeshRadius Q m
  let M := Real.sqrt (b^2*((78/5:ℝ)/2)*(cubeScaleFactor P0/L.1)^2)
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
    parent_boundary_common_distinct_tile_bound e s b L P0 Q m hQP z U hU
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
end ASDExplicitGamma.Native
