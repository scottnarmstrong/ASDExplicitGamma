module

public import ASDExplicitGamma.Main.CMRegularity
public import ASDExplicitGamma.Gaussian.Q3SobolevOperator
public import ASDExplicitGamma.Triadic.PlanarSobolev
public import Homogenization.Sobolev.H1.BasicLemmas

/-! Actual q3 factor directions as bounded weak W^{2,∞} multipliers. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open scoped RealInnerProductSpace ENNReal

/-- Every actual convolution coordinate has a global bound from its L2
kernel section. No spatial supremum estimate is a premise. -/
theorem main_q3_direction_norm_le (b : ℝ) (L : {l : ℝ // 0 < l}) (a : H3Index)
    (u : WhiteNoise) (x : Vec 2) :
    ‖q3Convolution b L a u x‖ ≤ ‖u‖*‖q3Section b L a 0‖ := by
  have he : ‖q3Section b L a x‖ = ‖q3Section b L a 0‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [gaussQ3Section_norm_sq, gaussQ3Section_norm_sq]
  exact (norm_inner_le_norm _ _).trans_eq (by rw [he])

/-- Uniform boundedness gives L-infinity on every measure, including both
normalizations used by the source Sobolev multiplier carrier. -/
theorem main_q3_direction_memLp_top (mu : Measure (Vec 2)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (a : H3Index) (u : WhiteNoise) : MemLp (q3Convolution b L a u) ⊤ mu :=
  memLp_top_of_bound (q3Convolution_continuous b L a u).aestronglyMeasurable _
    (Filter.Eventually.of_forall (main_q3_direction_norm_le b L a u))

/-- The classical convolution direction as the project's genuine weak H1
witness, with its actual coordinate derivatives. -/
noncomputable def mainQ3DirectionH1 (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (a : H3Index) (ha : a.1.1.val+a.1.2.val ≤ 2) (u : WhiteNoise) :
    H1Function (openCubeSet Q) :=
  H1Function.ofContDiffOnIsOpenBoundedConvexDomain (isOpenBoundedConvexDomain_openCubeSet Q)
    (q3Convolution_contDiff_one b L a ha u)

/-- The factor direction supplies every weak W^{2,∞} hypothesis of the
planar multiplier theorem. The molecular parameter and deterministic frame
are not altered or introduced by this analytic bundling. -/
noncomputable def mainQ3DirectionW2 (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (u : WhiteNoise) : PlanarW2Infinity Q := by
  let hz : h3Zero.1.1.val+h3Zero.1.2.val ≤ 2 := by decide
  have hn (i : Fin 2) :
      (h3Next h3Zero i hz).1.1.val+(h3Next h3Zero i hz).1.2.val ≤ 2 := by
    fin_cases i <;> norm_num [h3Next, h3Zero]
  refine { value := mainQ3DirectionH1 Q b L h3Zero hz u
           value_memLp_top := main_q3_direction_memLp_top _ b L h3Zero u
           gradient :=
             { component := fun i => mainQ3DirectionH1 Q b L (h3Next h3Zero i hz) (hn i) u
               component_memLp_top := fun i => main_q3_direction_memLp_top _ b L _ u
               derivative_memLp_top := ?_ }
           gradient_eq := ?_ }
  · intro i j
    change MemLp (fun x => (fderiv ℝ (q3Convolution b L (h3Next h3Zero i hz) u) x) (basisVec j)) ⊤ _
    simp_rw [q3Convolution_fderiv_basis b L _ (hn i) u]
    exact main_q3_direction_memLp_top _ b L _ u
  · intro i
    funext x
    change q3Convolution b L (h3Next h3Zero i hz) u x =
      (fderiv ℝ (q3Convolution b L h3Zero u) x) (basisVec i)
    exact (q3Convolution_fderiv_basis b L h3Zero hz u x i).symm

/-- The bundled weak multiplier has exactly the physical convolution value. -/
theorem mainQ3DirectionW2_value (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (u : WhiteNoise) (x : Vec 2) :
    (mainQ3DirectionW2 Q b L u).value x = q3Convolution b L h3Zero u x := rfl

end ASDExplicitGamma.Main
