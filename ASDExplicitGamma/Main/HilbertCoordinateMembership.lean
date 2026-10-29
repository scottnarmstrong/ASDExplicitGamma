module

public import ASDExplicitGamma.Main.HilbertFiniteCoordinates
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! Actual finite-coordinate membership and norm bridges for source vector fields. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open scoped BigOperators

/-- Positive-Haar membership follows from the actual finite coordinates. -/
theorem main_hilbert_summable_of_coordinates {κ : Type*} [Fintype κ]
    (Q : TriadicCube 2) {F : Vec 2 → EuclideanSpace ℝ κ}
    (hF : MemLp F 2 (normalizedCubeMeasure Q))
    (hP : ∀ i, Summable (fun k => (Real.sqrt 3)^(k+1)*
      energy Q (cubeIncrement Q (k+1) (fun x => (F x).ofLp i)))) :
    Summable (fun k => (Real.sqrt 3)^(k+1)*hilbertEnergy Q (hilbertCubeIncrement Q (k+1) F)) := by
  have hs := summable_sum (s := Finset.univ) (fun i _ => hP i)
  apply hs.congr
  intro k
  rw [main_hilbertEnergy_euclidean Q (hilbertCubeIncrement_memLp Q (k+1) F), Finset.mul_sum]
  simp_rw [main_hilbertIncrement_coordinate Q hF]

/-- The physical two-coordinate source vector has exactly its scalar
coordinate norm, not a sup norm or an extra sqrt2 multiple. -/
theorem main_hilbertPositive_eq_vectorPositive (Q : TriadicCube 2) {F : Vec 2 → Fin 2 → ℝ}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hP : ∀ i, Summable (fun k => (Real.sqrt 3)^(k+1)*energy Q (cubeIncrement Q (k+1) (fun x => F x i)))) :
    hilbertPositiveHaarNorm Q (Real.sqrt 3) (fun x => WithLp.toLp 2 (F x)) = vectorPositiveHaarNorm Q F := by
  have hm : MemLp (fun x => WithLp.toLp 2 (F x)) 2 (normalizedCubeMeasure Q) := memLp_piLp_iff.mpr hF
  have hp := main_hilbert_summable_of_coordinates Q hm hP
  rw [hilbertPositiveHaarNorm, main_hilbertPrimalEnergy_euclidean Q hm hp]
  rfl

/-- Every genuine positive-Haar input controls its own full L2 norm. -/
theorem main_hilbertL2_le_positive {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (Q : TriadicCube 2)
    {F : Vec 2 → E} (hf : MemLp F 2 (normalizedCubeMeasure Q))
    (hP : Summable (fun k => (Real.sqrt 3)^(k+1)*hilbertEnergy Q (hilbertCubeIncrement Q (k+1) F))) :
    hilbertL2Norm Q F ≤ hilbertPositiveHaarNorm Q (Real.sqrt 3) F := by
  have hq : 1 < Real.sqrt 3 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg (3:ℝ)]
  have he := (hilbert_sensitivity_tail_of_weight Q hq hf hP).2.1
  apply Real.sqrt_le_sqrt
  rw [he]
  exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hq.le)
    (tsum_nonneg fun k => mul_nonneg (by positivity) (hilbertEnergy_nonneg Q _)))

end ASDExplicitGamma.Main
