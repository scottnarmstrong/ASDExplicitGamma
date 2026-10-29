module

public import ASDExplicitGamma.Scalar.DefectResolventCarriers
public import ASDExplicitGamma.Gaussian.CovarianceRow
public import ASDExplicitGamma.Gaussian.GeneratorBounds
public import ASDExplicitGamma.Variational.ProjectedSource
public import ASDExplicitGamma.Scalar.DefectEnergyHilbert
public import ASDExplicitGamma.Triadic.DiagInterpolant

/-! Class-invariant building blocks for the physical projected-source defect
on the actual zero-trace H10 graph carrier. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational

noncomputable section

private theorem open_ae_to_normalized (Q : TriadicCube 2)
    {f g : Vec 2 → Vec 2}
    (h : f =ᵐ[volumeMeasureOn (openCubeSet Q)] g) :
    f =ᵐ[normalizedCubeMeasure Q] g := by
  change f =ᵐ[volume.restrict (openCubeSet Q)] g at h
  rw [← volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] at h
  exact Measure.ae_smul_measure h (ENNReal.ofReal ((cubeVolume Q)⁻¹))

private theorem open_ae_to_cube (Q : TriadicCube 2)
    {f g : Vec 2 → ℝ}
    (h : f =ᵐ[volumeMeasureOn (openCubeSet Q)] g) :
    f =ᵐ[volume.restrict (cubeSet Q)] g := by
  change f =ᵐ[volume.restrict (openCubeSet Q)] g at h
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
  exact h

/-- The concrete DIAG interpolant is unchanged when the H1 value and weak
gradient are changed only on null sets. This makes its nodal means a map of
the actual H10 graph class. -/
theorem diagInterpolant_eq_of_h1_ae (Q : TriadicCube 2) (j : ℕ)
    (v w : H1Function (openCubeSet Q))
    (hval : v.toFun =ᵐ[volumeMeasureOn (openCubeSet Q)] w.toFun)
    (hgrad : v.grad =ᵐ[volumeMeasureOn (openCubeSet Q)] w.grad) :
    diagInterpolant Q j v = diagInterpolant Q j w := by
  have hgradN := open_ae_to_normalized Q hgrad
  have hgradCoord (i : Fin 2) :
      (fun x => v.grad x i) =ᵐ[normalizedCubeMeasure Q]
        (fun x => w.grad x i) :=
    hgradN.mono fun x hx => congrFun hx i
  have hmean : diagMeanGradientLinear Q v = diagMeanGradientLinear Q w := by
    funext i
    change cubeAverage Q (fun x => v.grad x i) =
      cubeAverage Q (fun x => w.grad x i)
    rw [cubeAverage_eq_integral_normalizedCubeMeasure,
      cubeAverage_eq_integral_normalizedCubeMeasure]
    exact integral_congr_ae (hgradCoord i)
  have hvalCube := open_ae_to_cube Q hval
  have hres : (diagResidualLinear Q v).toFun =ᵐ[
      volumeMeasureOn (openCubeSet Q)] (diagResidualLinear Q w).toFun := by
    have haff : diagAffineLinear Q (diagMeanGradientLinear Q v) =
        diagAffineLinear Q (diagMeanGradientLinear Q w) := congrArg
          (diagAffineLinear Q) hmean
    have haffFun := congrArg (fun z : H1Function (openCubeSet Q) => z.toFun) haff
    simp only [diagResidualLinear, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, H1Function.sub_toFun]
    filter_upwards [hval] with x hx
    rw [hx, congrFun haffFun x]
  have hresCube := open_ae_to_cube Q hres
  have hprojection : diagProjectionLinear Q j (diagResidualLinear Q v) =
      diagProjectionLinear Q j (diagResidualLinear Q w) := by
    funext x
    rw [diagProjectionLinear_apply, diagProjectionLinear_apply]
    exact congrFun (lemmaV_cubeProjection_congr_ae Q j hresCube) x
  have hnodal : diagNodalValuesLinear Q j v = diagNodalValuesLinear Q j w := by
    funext z
    change diagOddNodalMean (cubeCorner Q) (diagMeshRadius Q j) (3 ^ j)
        (diagProjectionLinear Q j (diagResidualLinear Q v))
        (diagInteriorVertexIndex j z) =
      diagOddNodalMean (cubeCorner Q) (diagMeshRadius Q j) (3 ^ j)
        (diagProjectionLinear Q j (diagResidualLinear Q w))
        (diagInteriorVertexIndex j z)
    rw [hprojection]
  simp only [diagInterpolant, LinearMap.add_apply, LinearMap.comp_apply]
  rw [hmean, hnodal]

/-- For fixed q3 insertion mode, the physical Lemma-V shear source depends
only on the H1 value and gradient classes of its potential. -/
noncomputable def defectPotentialSourceFieldH1 (Q : TriadicCube 2)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex)
    (v : H1Function (openCubeSet Q)) : Vec 2 → Vec 2 :=
  planarShearSourceField (diagInterpolant Q 0)
    (mainQ3DirectionW2 Q b L (whiteBasis n)) v

theorem defectPotentialSourceField_congr_ae (Q : TriadicCube 2)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex)
    (v w : H1Function (openCubeSet Q))
    (hval : v.toFun =ᵐ[volumeMeasureOn (openCubeSet Q)] w.toFun)
    (hgrad : v.grad =ᵐ[volumeMeasureOn (openCubeSet Q)] w.grad) :
    defectPotentialSourceFieldH1 Q b L n v =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      defectPotentialSourceFieldH1 Q b L n w := by
  have hI := diagInterpolant_eq_of_h1_ae Q 0 v w hval hgrad
  have hItoFun := congrArg (fun z : H1Function (openCubeSet Q) => z.toFun) hI
  have hIgrad := congrArg (fun z : H1Function (openCubeSet Q) => z.grad) hI
  let η := mainQ3DirectionW2 Q b L (whiteBasis n)
  filter_upwards [hval] with x hv
  ext i
  simp only [defectPotentialSourceFieldH1, planarShearSourceField,
    H1Function.sub_toFun]
  rw [congrFun hIgrad x, congrFun hItoFun x, hv]

/-- The physical source shear is linear in its zero-trace potential. -/
theorem defectPotentialSourceFieldH1_add (Q : TriadicCube 2)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex)
    (v w : H1Function (openCubeSet Q)) :
    defectPotentialSourceFieldH1 Q b L n (v + w) =
      fun x => defectPotentialSourceFieldH1 Q b L n v x +
        defectPotentialSourceFieldH1 Q b L n w x := by
  funext x
  funext i
  simp only [defectPotentialSourceFieldH1, planarShearSourceField,
    LinearMap.map_add, H1Function.add_grad, H1Function.sub_toFun,
    H1Function.add_toFun]
  fin_cases i <;> simp [planarShearSourceField, planarQuarterTurn] <;> ring_nf

/-- The physical source shear is homogeneous in its zero-trace potential. -/
theorem defectPotentialSourceFieldH1_smul (Q : TriadicCube 2)
    (b c : ℝ) (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex)
    (v : H1Function (openCubeSet Q)) :
    defectPotentialSourceFieldH1 Q b L n (c • v) =
      fun x => c • defectPotentialSourceFieldH1 Q b L n v x := by
  funext x
  funext i
  simp only [defectPotentialSourceFieldH1, planarShearSourceField,
    LinearMap.map_smul, H1Function.smul_grad, H1Function.sub_toFun,
    H1Function.smul_toFun]
  fin_cases i <;> simp [planarShearSourceField, planarQuarterTurn] <;> ring_nf

/-- The physical source field evaluated at the canonical H10 representative
of a weak-Haar graph-carrier point. -/
noncomputable def defectPotentialSourceFieldCarrier (Q : TriadicCube 2)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex)
    (x : defectWeakPotential Q) : Vec 2 → Vec 2 :=
  defectPotentialSourceFieldH1 Q b L n
    (defectWeakPotentialRepresentative Q x).toH1Function

private theorem defectWeakPotentialRepresentative_add_value_ae
    (Q : TriadicCube 2) (x y : defectWeakPotential Q) :
    (defectWeakPotentialRepresentative Q (x + y)).toH1Function.toFun =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      fun p => (defectWeakPotentialRepresentative Q x).toH1Function.toFun p +
        (defectWeakPotentialRepresentative Q y).toH1Function.toFun p := by
  let rxy := defectWeakPotentialRepresentative Q (x + y)
  let rx := defectWeakPotentialRepresentative Q x
  let ry := defectWeakPotentialRepresentative Q y
  have hval : rxy.toH1Function.toScalarL2 =
      rx.toH1Function.toScalarL2 + ry.toH1Function.toScalarL2 := by
    rw [defectWeakPotentialRepresentative_value Q (x + y),
      defectWeakPotentialRepresentative_value Q x,
      defectWeakPotentialRepresentative_value Q y]
    rfl
  have hvalAE := MeasureTheory.Lp.ext_iff.mp hval
  filter_upwards [hvalAE, rxy.toH1Function.coeFn_toScalarL2,
    rx.toH1Function.coeFn_toScalarL2, ry.toH1Function.coeFn_toScalarL2,
    MeasureTheory.Lp.coeFn_add rx.toH1Function.toScalarL2
      ry.toH1Function.toScalarL2] with p hp hxy hx hy hadd
  have hpoint : rxy.toH1Function.toFun p =
      rx.toH1Function.toFun p + ry.toH1Function.toFun p := by
    calc
      rxy.toH1Function.toFun p = (rxy.toH1Function.toScalarL2 :
          ScalarL2 (openCubeSet Q)) p := hxy.symm
      _ = (rx.toH1Function.toScalarL2 + ry.toH1Function.toScalarL2) p := hp
      _ = ((rx.toH1Function.toScalarL2 : ScalarL2 (openCubeSet Q)) p) +
          ((ry.toH1Function.toScalarL2 : ScalarL2 (openCubeSet Q)) p) := hadd
      _ = _ := by rw [hx, hy]
  simpa [rxy, rx, ry] using hpoint

private theorem defectWeakPotentialRepresentative_add_gradient_ae
    (Q : TriadicCube 2) (x y : defectWeakPotential Q) :
    (defectWeakPotentialRepresentative Q (x + y)).toH1Function.grad =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      fun p => (defectWeakPotentialRepresentative Q x).toH1Function.grad p +
        (defectWeakPotentialRepresentative Q y).toH1Function.grad p := by
  let rxy := defectWeakPotentialRepresentative Q (x + y)
  let rx := defectWeakPotentialRepresentative Q x
  let ry := defectWeakPotentialRepresentative Q y
  have hgrad : rxy.toH1Function.gradToHilbertVectorL2 =
      rx.toH1Function.gradToHilbertVectorL2 + ry.toH1Function.gradToHilbertVectorL2 := by
    rw [defectWeakPotentialRepresentative_gradient Q (x + y),
      defectWeakPotentialRepresentative_gradient Q x,
      defectWeakPotentialRepresentative_gradient Q y]
    rfl
  have hgradAE := MeasureTheory.Lp.ext_iff.mp hgrad
  filter_upwards [hgradAE, rxy.toH1Function.coeFn_gradToHilbertVectorL2,
    rx.toH1Function.coeFn_gradToHilbertVectorL2,
    ry.toH1Function.coeFn_gradToHilbertVectorL2,
    MeasureTheory.Lp.coeFn_add rx.toH1Function.gradToHilbertVectorL2
      ry.toH1Function.gradToHilbertVectorL2] with p hp hxy hx hy hadd
  have hfield : HilbertVec.ofVec (rxy.toH1Function.grad p) =
      HilbertVec.ofVec (rx.toH1Function.grad p + ry.toH1Function.grad p) := by
    calc
      HilbertVec.ofVec (rxy.toH1Function.grad p) =
          (rxy.toH1Function.gradToHilbertVectorL2 :
            HilbertVectorL2 (openCubeSet Q)) p := hxy.symm
      _ = (rx.toH1Function.gradToHilbertVectorL2 +
          ry.toH1Function.gradToHilbertVectorL2) p := hp
      _ = ((rx.toH1Function.gradToHilbertVectorL2 :
          HilbertVectorL2 (openCubeSet Q)) p) +
          ((ry.toH1Function.gradToHilbertVectorL2 :
          HilbertVectorL2 (openCubeSet Q)) p) := hadd
      _ = _ := by rw [hx, hy]; simp [hilbertifyVecField]
  have hback : rxy.toH1Function.grad p =
      rx.toH1Function.grad p + ry.toH1Function.grad p := by
    funext i
    have hi := congrArg (fun z : HilbertVec 2 => z i) hfield
    simpa [HilbertVec.ofVec] using hi
  simpa [rxy, rx, ry] using hback

/-- The source operator on the completed graph carrier respects addition at
the level of its physical vector field. -/
theorem defectPotentialSourceFieldCarrier_add_ae (Q : TriadicCube 2)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex)
    (x y : defectWeakPotential Q) :
    defectPotentialSourceFieldCarrier Q b L n (x + y) =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      fun p => defectPotentialSourceFieldCarrier Q b L n x p +
        defectPotentialSourceFieldCarrier Q b L n y p := by
  let rx := defectWeakPotentialRepresentative Q x
  let ry := defectWeakPotentialRepresentative Q y
  let rxy := defectWeakPotentialRepresentative Q (x + y)
  have hsource := defectPotentialSourceField_congr_ae Q b L n
    rxy.toH1Function (rx.toH1Function + ry.toH1Function)
    (defectWeakPotentialRepresentative_add_value_ae Q x y)
    (defectWeakPotentialRepresentative_add_gradient_ae Q x y)
  filter_upwards [hsource] with p hp
  rw [defectPotentialSourceFieldH1_add] at hp
  exact hp

private theorem defectWeakPotentialRepresentative_smul_value_ae
    (Q : TriadicCube 2) (c : ℝ) (x : defectWeakPotential Q) :
    (defectWeakPotentialRepresentative Q (c • x)).toH1Function.toFun =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      fun p => c * (defectWeakPotentialRepresentative Q x).toH1Function.toFun p := by
  let rc := defectWeakPotentialRepresentative Q (c • x)
  let rx := defectWeakPotentialRepresentative Q x
  have hval : rc.toH1Function.toScalarL2 = c • rx.toH1Function.toScalarL2 := by
    rw [defectWeakPotentialRepresentative_value Q (c • x),
      defectWeakPotentialRepresentative_value Q x]
    rfl
  have hvalAE := MeasureTheory.Lp.ext_iff.mp hval
  filter_upwards [hvalAE, rc.toH1Function.coeFn_toScalarL2,
    rx.toH1Function.coeFn_toScalarL2,
    MeasureTheory.Lp.coeFn_smul c rx.toH1Function.toScalarL2] with p hp hc hx hsmul
  have hpoint : rc.toH1Function.toFun p =
      c * rx.toH1Function.toFun p := by
    calc
      rc.toH1Function.toFun p = (rc.toH1Function.toScalarL2 :
          ScalarL2 (openCubeSet Q)) p := hc.symm
      _ = (c • rx.toH1Function.toScalarL2) p := hp
      _ = c * ((rx.toH1Function.toScalarL2 : ScalarL2 (openCubeSet Q)) p) := hsmul
      _ = _ := by rw [hx]
  simpa [rc, rx] using hpoint

private theorem defectWeakPotentialRepresentative_smul_gradient_ae
    (Q : TriadicCube 2) (c : ℝ) (x : defectWeakPotential Q) :
    (defectWeakPotentialRepresentative Q (c • x)).toH1Function.grad =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      fun p => c • (defectWeakPotentialRepresentative Q x).toH1Function.grad p := by
  let rc := defectWeakPotentialRepresentative Q (c • x)
  let rx := defectWeakPotentialRepresentative Q x
  have hgrad : rc.toH1Function.gradToHilbertVectorL2 =
      c • rx.toH1Function.gradToHilbertVectorL2 := by
    rw [defectWeakPotentialRepresentative_gradient Q (c • x),
      defectWeakPotentialRepresentative_gradient Q x]
    rfl
  have hgradAE := MeasureTheory.Lp.ext_iff.mp hgrad
  filter_upwards [hgradAE, rc.toH1Function.coeFn_gradToHilbertVectorL2,
    rx.toH1Function.coeFn_gradToHilbertVectorL2,
    MeasureTheory.Lp.coeFn_smul c rx.toH1Function.gradToHilbertVectorL2]
      with p hp hc hx hsmul
  have hfield : HilbertVec.ofVec (rc.toH1Function.grad p) =
      c • HilbertVec.ofVec (rx.toH1Function.grad p) := by
    calc
      HilbertVec.ofVec (rc.toH1Function.grad p) =
          (rc.toH1Function.gradToHilbertVectorL2 :
            HilbertVectorL2 (openCubeSet Q)) p := hc.symm
      _ = (c • rx.toH1Function.gradToHilbertVectorL2) p := hp
      _ = c • ((rx.toH1Function.gradToHilbertVectorL2 :
          HilbertVectorL2 (openCubeSet Q)) p) := hsmul
      _ = _ := by rw [hx]; simp [hilbertifyVecField]
  have hback : rc.toH1Function.grad p = c • rx.toH1Function.grad p := by
    funext i
    have hi := congrArg (fun z : HilbertVec 2 => z i) hfield
    simpa [HilbertVec.ofVec, Pi.smul_apply] using hi
  simpa [rc, rx] using hback

/-- The source operator on the completed graph carrier respects scalar
multiplication at the level of its physical vector field. -/
theorem defectPotentialSourceFieldCarrier_smul_ae (Q : TriadicCube 2)
    (b c : ℝ) (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex)
    (x : defectWeakPotential Q) :
    defectPotentialSourceFieldCarrier Q b L n (c • x) =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      fun p => c • defectPotentialSourceFieldCarrier Q b L n x p := by
  let rx := defectWeakPotentialRepresentative Q x
  let rc := defectWeakPotentialRepresentative Q (c • x)
  have hsource := defectPotentialSourceField_congr_ae Q b L n
    rc.toH1Function (c • rx.toH1Function)
    (defectWeakPotentialRepresentative_smul_value_ae Q c x)
    (defectWeakPotentialRepresentative_smul_gradient_ae Q c x)
  filter_upwards [hsource] with p hp
  rw [defectPotentialSourceFieldH1_smul] at hp
  exact hp

end
end ASDExplicitGamma.Scalar
