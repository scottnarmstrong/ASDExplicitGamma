module

public import ASDExplicitGamma.Native.ParentBoundaryCommonPowerExpectation
public import ASDExplicitGamma.Native.OldSignedFiniteMinkowski

/-! Exact common-parent/child-mesh shell shapes before finite covariance aggregation. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Algsuperdiff.Section3
noncomputable section

private theorem parent_common_cube_scale_pos (P : TriadicCube 2) : 0 < cubeScaleFactor P := by
  exact zpow_pos (by norm_num : (0:ℝ)<3) P.scale

private theorem parent_common_sqrt_value (b K r : ℝ) (hK : 0 ≤ K) (hr : 0 ≤ r) :
    Real.sqrt (b^2*K*r^2)=|b| *Real.sqrt K*r := by
  rw [Real.sqrt_mul (mul_nonneg (sq_nonneg b) hK),Real.sqrt_mul (sq_nonneg b),
    Real.sqrt_sq_eq_abs,Real.sqrt_sq hr]

private theorem parent_common_sqrt_gradient (b K L s : ℝ) (hK : 0 ≤ K) (hL : 0 < L) :
    s*Real.sqrt (K*b^2/L^2)=|b| *Real.sqrt K*(s/L) := by
  rw [Real.sqrt_div (mul_nonneg hK (sq_nonneg b)),Real.sqrt_mul hK,
    Real.sqrt_sq_eq_abs,Real.sqrt_sq hL.le]
  ring

private theorem parent_common_sqrt_hessian (b K L s : ℝ) (hK : 0 ≤ K) :
    s^2*Real.sqrt (K*b^2/L^4)=|b| *Real.sqrt K*(s/L)^2 := by
  rw [Real.sqrt_div (mul_nonneg hK (sq_nonneg b)),Real.sqrt_mul hK,
    Real.sqrt_sq_eq_abs,show L^4=(L^2)^2 by ring,Real.sqrt_sq (sq_nonneg L)]
  ring

/-- Exact source A-column shape. The common-parent radius stays in the
constant term, while only the observed square sets the derivative mesh. -/
theorem parent_boundary_common_row_coefficient_shape
    (P Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l}) :
    parentBoundaryCommonRowCoefficient P Q b L 0=
      |b| *(Real.sqrt (39/5:ℝ)*(cubeScaleFactor P/L.val)+
        (36/25:ℝ)*Real.sqrt (156/5:ℝ)*(cubeScaleFactor Q/L.val)+
        (57/200:ℝ)*Real.sqrt (46488/25:ℝ)*(cubeScaleFactor Q/L.val)^2) := by
  have hP : 0 ≤ cubeScaleFactor P/L.val := div_nonneg (parent_common_cube_scale_pos P).le L.property.le
  unfold parentBoundaryCommonRowCoefficient
  simp only [diagMeshRadius,pow_zero,div_one]
  norm_num only [show (78/5:ℝ)/2=39/5 by norm_num]
  rw [parent_common_sqrt_value b (39/5) _ (by norm_num) hP]
  have hg := parent_common_sqrt_gradient b (156/5) L.val (cubeScaleFactor Q) (by norm_num) L.property
  have hh := parent_common_sqrt_hessian b (46488/25) L.val (cubeScaleFactor Q) (by norm_num)
  calc
    _ = |b| *Real.sqrt (39/5:ℝ)*(cubeScaleFactor P/L.val)+
        (36/25:ℝ)*(cubeScaleFactor Q*Real.sqrt ((156/5:ℝ)*b^2/L.val^2))+
        (57/200:ℝ)*((cubeScaleFactor Q)^2*Real.sqrt ((46488/25:ℝ)*b^2/L.val^4)) := by ring
    _ = _ := by rw [hg,hh]; ring

/-- Exact source B-column bracket shape, with the lower derivative traces
15.6 and929.76 rather than the Hilbert--Schmidt A-column traces. -/
theorem parent_boundary_common_bracket_coefficient_shape
    (P Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l}) :
    |b| *lemmaVH2Bn (cubeScaleFactor P/L.val) (diagMeshRadius Q 0/L.val)=
      |b| *(Real.sqrt (39/5:ℝ)*(cubeScaleFactor P/L.val)+
        (36/25:ℝ)*Real.sqrt (78/5:ℝ)*(cubeScaleFactor Q/L.val)+
        (57/200:ℝ)*Real.sqrt (23244/25:ℝ)*(cubeScaleFactor Q/L.val)^2) := by
  norm_num [lemmaVH2Bn,lemmaVH2R1,lemmaVH2A2,lemmaVH2C1,lemmaVH2C2,diagMeshRadius]

/-- Finite complete-shell aggregation pays the Euclidean covariance norm,
with no factor depending on the number of shells. The two summed clocks
are precisely the source second/fourth spatial moment clocks. -/
theorem parent_boundary_common_band_row_norm_bound
    {I : Type*} [Fintype I] (P Q : TriadicCube 2) (b : I → ℝ) (L : I → {l : ℝ // 0 < l}) :
    Real.sqrt (∑ i,(parentBoundaryCommonRowCoefficient P Q (b i) (L i) 0)^2) ≤
      (Real.sqrt (39/5:ℝ)+(36/25:ℝ)*Real.sqrt (156/5:ℝ)*(cubeScaleFactor Q/cubeScaleFactor P))*
        Real.sqrt (∑ i,(b i)^2*(cubeScaleFactor P/(L i).val)^2)+
      ((57/200:ℝ)*Real.sqrt (46488/25:ℝ)*(cubeScaleFactor Q/cubeScaleFactor P)^2)*
        Real.sqrt (∑ i,(b i)^2*(cubeScaleFactor P/(L i).val)^4) := by
  let z := cubeScaleFactor Q/cubeScaleFactor P
  let E := fun i => (b i)^2*(cubeScaleFactor P/(L i).val)^2
  let F := fun i => (b i)^2*(cubeScaleFactor P/(L i).val)^4
  have hz : 0 ≤ z := div_nonneg (parent_common_cube_scale_pos Q).le (parent_common_cube_scale_pos P).le
  apply old_signed_finite_sqrt_energy_bound E F _ (by positivity) (by positivity)
    (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (fun _ => mul_nonneg (sq_nonneg _) (pow_nonneg (div_nonneg (parent_common_cube_scale_pos P).le (L _).property.le) _))
  · intro i
    have hm := (diagMeshRadius_pos Q 0).le
    unfold parentBoundaryCommonRowCoefficient
    positivity
  · intro i
    have hr : 0 ≤ cubeScaleFactor P/(L i).val := div_nonneg (parent_common_cube_scale_pos P).le (L i).property.le
    have hE : Real.sqrt (E i)=|b i| *(cubeScaleFactor P/(L i).val) := by
      dsimp only [E]
      rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,Real.sqrt_sq hr]
    have hF : Real.sqrt (F i)=|b i| *(cubeScaleFactor P/(L i).val)^2 := by
      dsimp only [F]
      rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,
        show (cubeScaleFactor P/(L i).val)^4=((cubeScaleFactor P/(L i).val)^2)^2 by ring,
        Real.sqrt_sq (sq_nonneg _)]
    have hmesh : cubeScaleFactor Q/(L i).val=z*(cubeScaleFactor P/(L i).val) := by
      dsimp only [z]
      field_simp [(parent_common_cube_scale_pos P).ne']
    rw [parent_boundary_common_row_coefficient_shape,hE,hF,hmesh]
    exact le_of_eq (by ring)

end
end ASDExplicitGamma.Native
