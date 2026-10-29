module

public import ASDExplicitGamma.Native.ParentBoundarySourcePhysical

/-! Genuine positive-Haar membership of the physical parent source on
each independent comparison cell, before weighted projection. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main ASDExplicitGamma.Response ASDExplicitGamma.Variational
noncomputable section

/-- Each actual potential-times-derivative coordinate has the complete
positive Haar series, proved from a singleton Hilbert source column. -/
theorem parent_boundary_potential_source_positive (Q U : TriadicCube 2) (depth : ℕ)
    (hU : U ∈ descendantsAtDepth Q depth) (u : H10Function (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (i : Fin 2) :
    Summable (fun j => (Real.sqrt 3)^(j+1)*energy U (cubeIncrement U (j+1)
      (fun x => u.toH1Function x*(fderiv ℝ (q3Convolution b L h3Zero (whiteBasis n)) x) (basisVec i)))) := by
  classical
  let s : Finset whiteBasisIndex := {n}
  let v := u.toH1Function.restrictToOpenSubcube hU
  have hm : MemLp (fun x => u.toH1Function x • mainQ3FiniteColumn whiteBasis s b L x)
      2 (normalizedCubeMeasure U) :=
    (mainRankOneMultiplier U (mainQ3FiniteColumn whiteBasis s b L)
      (mainQ3FiniteColumn_contDiff whiteBasis s b L)).product_memLp v.memL2_normalizedCubeMeasure
  have hs := (main_q3_column_h1_product whiteBasis s b L U v).1
  let ni : s := ⟨n,Finset.mem_singleton_self n⟩
  have hh := main_hilbert_coordinate_summable U hm hs (ni,i)
  simpa only [mainQ3FiniteColumn,PiLp.smul_apply,smul_eq_mul,ni] using hh

/-- Literal quarter-turn identification of the actual parent source. -/
theorem parent_boundary_potential_source_field (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) :
    (fun x => -u.toH1Function x •
      lemmaVPlanarWeakColumnDivergence (mainQ3DirectionW2 Q b L (whiteBasis n)).value x) =
    fun x => planarQuarterTurn (fun i => u.toH1Function x*
      (fderiv ℝ (q3Convolution b L h3Zero (whiteBasis n)) x) (basisVec i)) := by
  funext x i
  fin_cases i <;> simp [lemmaVPlanarWeakColumnDivergence,matVecMul,responsePlanarJ,
    Fin.sum_univ_two,planarQuarterTurn]
  all_goals exact Or.inl rfl

/-- Every actual canonical parent source has all positive-Haar spatial
membership required by the sharp weighted pure-second projection. -/
theorem parent_boundary_actual_source_positive (Q U : TriadicCube 2) (depth : ℕ)
    (hU : U ∈ descendantsAtDepth Q depth)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (i : Fin 2) :
    Summable (fun j => (Real.sqrt 3)^(j+1)*energy U (cubeIncrement U (j+1)
      (fun x => (parentBoundaryOldSource Q nu sigma hnu hsigma k b L n P x).2 i))) := by
  let u := oldSignedCanonicalFirstCorrector Q (responseFramePlanarCoefficientField nu sigma k)
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) nu sigma hnu hsigma k) P
  have hf : (fun x => (parentBoundaryOldSource Q nu sigma hnu hsigma k b L n P x).2) =
      fun x => planarQuarterTurn (fun i => u.toH1Function x*
        (fderiv ℝ (q3Convolution b L h3Zero (whiteBasis n)) x) (basisVec i)) := by
    rw [parent_boundary_old_source_formula]
    simpa only [←neg_smul] using parent_boundary_potential_source_field Q u b L n
  have hp := parent_boundary_potential_source_positive Q U depth hU u b L n
  change Summable (fun j => (Real.sqrt 3)^(j+1)*energy U (cubeIncrement U (j+1)
    (fun x => ((fun y => (parentBoundaryOldSource Q nu sigma hnu hsigma k b L n P y).2) x) i)))
  rw [hf]
  fin_cases i
  · change Summable (fun j => (Real.sqrt 3)^(j+1)*energy U (cubeIncrement U (j+1)
      (fun x => -(u.toH1Function x*(fderiv ℝ (q3Convolution b L h3Zero (whiteBasis n)) x) (basisVec 1)))))
    simp_rw [Triadic.cubeIncrement_neg,Triadic.energy_neg]
    exact hp 1
  · simpa [planarQuarterTurn] using hp 0

end
end ASDExplicitGamma.Native
