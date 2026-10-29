module

public import ASDExplicitGamma.Scalar.SmoothFeedbackVaryingSource
public import ASDExplicitGamma.Native.OldSignedAveragePairing
public import ASDExplicitGamma.Triadic.DiagBessel
public import ASDExplicitGamma.Triadic.PlanarPositiveGradient

/-! A source-pairing lower bound for the actual OLD local residual.

The mean term comes from the first-component mean identity for
`oldSignedCellResidual`; the oscillatory term uses constant-one Haar duality.
This is the source-side estimate needed in the parent-versus-cell gap bridge.
-/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Response Triadic
open ASDExplicitGamma.Native
open Algsuperdiff.Section3
open scoped BigOperators

noncomputable section

/-- The genuine order-`1/4` source regularity needed by the Λ8 top-force
pairing, including the positive Haar increments at base `sqrt 3`. -/
structure ScalarQuarterHaarAdmissible (R : TriadicCube 2) (f : Vec 2 → Vec 2) : Prop where
  memLp : MemLp f 2 (normalizedCubeMeasure R)
  increments : ∀ i, Summable (fun j : ℕ => (Real.sqrt 3)^(j+1) *
    energy R (cubeIncrement R (j+1) (fun x => f x i)))

/-- Coordinatewise `H1` representatives give the genuine order-`1/4`
source admissibility without an extra estimate hypothesis. -/
theorem smooth_feedback_quarter_haar_admissible_of_h1
    (R : TriadicCube 2) (f : Vec 2 → Vec 2)
    (g : Fin 2 → H1Function (openCubeSet R))
    (hfg : ∀ x i, f x i = (g i).toFun x) :
    ScalarQuarterHaarAdmissible R f := by
  refine ⟨?_, ?_⟩
  · apply memLp_pi_iff.mpr
    intro i
    have heq : (fun x => f x i) = (g i).toFun := by
      funext x
      exact hfg x i
    rw [heq]
    exact (g i).memL2_normalizedCubeMeasure
  · intro i
    have heq : (fun x => f x i) = (g i).toFun := by
      funext x
      exact hfg x i
    rw [heq]
    exact positiveHaarIncrementSeries_summable R
      (g i).memL2_normalizedCubeMeasure
      (g i).grad_memL2_normalizedCubeMeasure (g i).hasWeakGradient

/-- Centering a coordinatewise `H1` field preserves the source
order-`1/4` admissibility required by the local top-force pairing. -/
theorem smooth_feedback_centered_quarter_haar_admissible_of_h1
    (R : TriadicCube 2) (f : Vec 2 → Vec 2)
    (g : Fin 2 → H1Function (openCubeSet R))
    (hfg : ∀ x i, f x i = (g i).toFun x) :
    ScalarQuarterHaarAdmissible R
      (fun x => f x - fun i => cubeAverage R (fun y => f y i)) := by
  let mean : Vec 2 := fun i => cubeAverage R (fun x => f x i)
  let gcenter : Fin 2 → H1Function (openCubeSet R) := fun i =>
    g i - H1Function.const (U := openCubeSet R) (mean i)
  apply smooth_feedback_quarter_haar_admissible_of_h1 R _ gcenter
  intro x i
  simp [gcenter, mean, hfg x i]

private theorem smooth_feedback_cell_source_center_mean
    (R : TriadicCube 2) (f : Vec 2 → Vec 2)
    (hf : MemLp f 2 (normalizedCubeMeasure R)) (i : Fin 2) :
    cubeAverage R (fun x => f x i - cubeAverage R (fun y => f y i)) = 0 := by
  have hcoord : MemLp (fun x => f x i) 2 (normalizedCubeMeasure R) := by
    exact memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2
        (memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure R hf) i)
  rw [cubeAverage_sub_const_of_memLp_two R hcoord]
  ring

private theorem smooth_feedback_cell_source_centered_weak_le
    (R : TriadicCube 2) (g : Vec 2 → Vec 2)
    (hg : ∀ i, MemLp (fun x => g x i) 2 (normalizedCubeMeasure R))
    (c : Vec 2)
    (hc : ∀ i, cubeAverage R (fun x => g x i) = c i) :
    vectorWeakHaarEnergy R (fun x i => g x i - c i) ≤
      vectorWeakHaarEnergy R g := by
  unfold vectorWeakHaarEnergy
  apply Finset.sum_le_sum
  intro i hi
  have hcenter : (fun x => g x i - c i) =
      (fun x => g x i - cubeAverage R (fun y => g y i)) := by
    rw [hc i]
  rw [hcenter, diagDualEnergy_sub_mean R (Real.sqrt 3) (hg i)]
  nlinarith [sq_nonneg (cubeAverage R (fun y => g y i))]

theorem smooth_feedback_old_signed_cell_source_pairing_lower
    (Q R : TriadicCube 2) (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (f : Vec 2 → Vec 2)
    (hfQ : MemLp f 2 (normalizedCubeMeasure Q))
    (hfR : MemLp f 2 (normalizedCubeMeasure R))
    (hfcenter : ScalarQuarterHaarAdmissible R
      (fun x => f x - fun i => cubeAverage R (fun y => f y i))) :
    scalarSourcePairing (openCubeSet R) f
      (oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k
        (fun x => (f x, 0)) (scalar_source_block_memL2 Q hfQ)) ≥
      vecNormSq (fun i => cubeAverage R (fun x => f x i)) -
        Real.sqrt (vectorWeakHaarEnergy R (fun x i =>
          (oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k
            (fun x => (f x, 0)) (scalar_source_block_memL2 Q hfQ) x).1 i)) *
          Real.sqrt (vectorPositiveHaarEnergy R
            (fun x => f x - fun i => cubeAverage R (fun y => f y i))) := by
  classical
  let mean : Vec 2 := fun i => cubeAverage R (fun x => f x i)
  let fcenter : Vec 2 → Vec 2 := fun x => f x - mean
  let F : Vec 2 → BlockVec 2 := fun x => (f x, 0)
  let hF : MemBlockL2 (openCubeSet Q) F := scalar_source_block_memL2 Q hfQ
  let Y : Vec 2 → BlockVec 2 := oldSignedCellResidual Q R hRQ
    nu sigma hnu hsigma k F hF
  have hY : MemBlockL2 (openCubeSet R) Y :=
    (oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k F hF).property
  have hfVec : MemVectorL2 (openCubeSet R) f :=
    memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure R hfR
  have hYVec : MemVectorL2 (openCubeSet R) (fun x => (Y x).1) :=
    memVectorL2_fst_of_memBlockL2 hY
  have hYmean (i : Fin 2) : cubeAverage R (fun x => (Y x).1 i) = mean i := by
    simpa [Y, F, hF, mean] using
      smooth_feedback_old_signed_cell_residual_first_mean Q R hRQ
        nu sigma hnu hsigma k F hF i
  have hfcenterVec : MemVectorL2 (openCubeSet R) fcenter :=
    memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure R hfcenter.memLp
  have hYcenterVec : MemVectorL2 (openCubeSet R) (fun x => (Y x).1 - mean) := by
    have hconst : MemVectorL2 (openCubeSet R) (fun _ : Vec 2 => mean) := memLp_const mean
    exact hYVec.sub hconst
  have hPairF : scalarSourcePairing (openCubeSet R) f Y =
      ∑ i : Fin 2, pairing R (fun x => f x i) (fun x => (Y x).1 i) := by
    exact old_signed_vector_average_pairing R f (fun x => (Y x).1) hfVec hYVec
  have hPairC : scalarSourcePairing (openCubeSet R) fcenter
      (fun x => ((Y x).1 - mean, (Y x).2)) =
      ∑ i : Fin 2, pairing R (fun x => fcenter x i)
        (fun x => (Y x).1 i - mean i) := by
    exact old_signed_vector_average_pairing R fcenter (fun x => (Y x).1 - mean)
      hfcenterVec hYcenterVec
  have hcoordPair (i : Fin 2) : pairing R (fun x => f x i) (fun x => (Y x).1 i) =
      mean i ^ 2 + pairing R (fun x => fcenter x i)
        (fun x => (Y x).1 i - mean i) := by
    have hfcoord : MemLp (fun x => f x i) 2 (normalizedCubeMeasure R) := by
      exact memLp_normalized_of_memL2On (hfVec.eval i)
    have hycoord : MemLp (fun x => (Y x).1 i) 2 (normalizedCubeMeasure R) := by
      exact memLp_normalized_of_memL2On (hYVec.eval i)
    have hconst : MemLp (fun _ : Vec 2 => mean i) 2 (normalizedCubeMeasure R) := memLp_const _
    have hcenterAvg : cubeAverage R (fun x => fcenter x i) = 0 := by
      simpa [fcenter, mean] using smooth_feedback_cell_source_center_mean R f hfR i
    have hmeanPair : pairing R (fun _ : Vec 2 => mean i) (fun x => (Y x).1 i) =
        mean i ^ 2 := by
      rw [pairing]
      rw [cubeAverage_const_mul R (mean i) (fun x => (Y x).1 i), hYmean i]
      ring
    have hcenterConst : pairing R (fun x => fcenter x i) (fun _ : Vec 2 => mean i) = 0 := by
      rw [pairing]
      rw [show (fun x => fcenter x i * mean i) =
        (fun x => mean i * fcenter x i) by funext x; ring]
      rw [cubeAverage_const_mul R (mean i) (fun x => fcenter x i), hcenterAvg]
      simp
    have hcenterCoord : MemLp (fun x => fcenter x i) 2
        (normalizedCubeMeasure R) :=
      memLp_normalized_of_memL2On (hfcenterVec.eval i)
    have hsplit₁ := pairing_sub_left R hfcoord hconst hycoord
    have hsplit₂ := pairing_sub_right R hcenterCoord hycoord hconst
    have h₁ : pairing R (fun x => f x i) (fun x => (Y x).1 i) =
        pairing R (fun x => fcenter x i) (fun x => (Y x).1 i) + mean i ^ 2 := by
      have heq : pairing R (fun x => fcenter x i) (fun x => (Y x).1 i) =
          pairing R (fun x => f x i) (fun x => (Y x).1 i) - mean i ^ 2 := by
        calc
          _ = pairing R (fun x => f x i) (fun x => (Y x).1 i) -
              pairing R (fun x => mean i) (fun x => (Y x).1 i) := by
                simpa [fcenter, mean] using hsplit₁
          _ = _ := by rw [hmeanPair]
      linarith
    have h₂ : pairing R (fun x => fcenter x i) (fun x => (Y x).1 i) =
        pairing R (fun x => fcenter x i) (fun x => (Y x).1 i - mean i) := by
      have heq : pairing R (fun x => fcenter x i)
          (fun x => (Y x).1 i - mean i) =
          pairing R (fun x => fcenter x i) (fun x => (Y x).1 i) := by
        rw [hsplit₂, hcenterConst]
        ring
      exact heq.symm
    rw [h₁, h₂]
    ring
  have hdecomp : scalarSourcePairing (openCubeSet R) f Y =
      vecNormSq mean + scalarSourcePairing (openCubeSet R) fcenter
        (fun x => ((Y x).1 - mean, (Y x).2)) := by
    rw [hPairF, hPairC]
    have hsum : (∑ i : Fin 2, pairing R (fun x => f x i) (fun x => (Y x).1 i)) =
        vecNormSq mean + ∑ i : Fin 2, pairing R (fun x => fcenter x i)
          (fun x => (Y x).1 i - mean i) := by
      calc
        _ = ∑ i : Fin 2, (mean i ^ 2 + pairing R (fun x => fcenter x i)
            (fun x => (Y x).1 i - mean i)) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hcoordPair i
        _ = (∑ i : Fin 2, mean i ^ 2) +
            ∑ i : Fin 2, pairing R (fun x => fcenter x i)
              (fun x => (Y x).1 i - mean i) := Finset.sum_add_distrib
        _ = _ := by simp [vecNormSq, vecDot, Fin.sum_univ_two, pow_two]
    exact hsum
  have hcenterPair :
      scalarSourcePairing (openCubeSet R) fcenter
        (fun x => ((Y x).1 - mean, (Y x).2)) =
      ∑ i : Fin 2, pairing R (fun x => fcenter x i)
        (fun x => (Y x).1 i - mean i) := by
    exact old_signed_vector_average_pairing R fcenter (fun x => (Y x).1 - mean)
      hfcenterVec hYcenterVec
  have hcenterCoord (i : Fin 2) :
      MemLp (fun x => fcenter x i) 2 (normalizedCubeMeasure R) := by
    exact memLp_normalized_of_memL2On (hfcenterVec.eval i)
  have hYcenterCoord (i : Fin 2) :
      MemLp (fun x => (Y x).1 i - mean i) 2 (normalizedCubeMeasure R) := by
    exact memLp_normalized_of_memL2On (hYcenterVec.eval i)
  have hhaar := old_signed_vector_haar_pairing_bound R
    (fun x i => (Y x).1 i - mean i) fcenter
    hYcenterCoord hcenterCoord
    (fun i => hfcenter.increments i)
  have hweak : vectorWeakHaarEnergy R
        (fun x i => (Y x).1 i - mean i) ≤
      vectorWeakHaarEnergy R (fun x i => (Y x).1 i) := by
    exact smooth_feedback_cell_source_centered_weak_le R
      (fun x => (Y x).1) (fun i => memLp_normalized_of_memL2On (hYVec.eval i))
      mean hYmean
  have hhaarComm : |∑ i : Fin 2, pairing R (fun x => fcenter x i)
      (fun x => (Y x).1 i - mean i)| ≤
      Real.sqrt (vectorWeakHaarEnergy R
        (fun x i => (Y x).1 i - mean i)) *
        Real.sqrt (vectorPositiveHaarEnergy R fcenter) := by
    rw [show (∑ i : Fin 2, pairing R (fun x => fcenter x i)
        (fun x => (Y x).1 i - mean i)) =
      (∑ i : Fin 2, pairing R (fun x => (Y x).1 i - mean i) (fun x => fcenter x i)) by
        apply Finset.sum_congr rfl
        intro i hi
        exact pairing_comm R _ _]
    simpa [vectorWeakHaarNorm, vectorPositiveHaarNorm] using hhaar
  have hhaar' : |scalarSourcePairing (openCubeSet R) fcenter
      (fun x => ((Y x).1 - mean, (Y x).2))| ≤
      Real.sqrt (vectorWeakHaarEnergy R (fun x i => (Y x).1 i)) *
        Real.sqrt (vectorPositiveHaarEnergy R fcenter) := by
    rw [hcenterPair]
    calc
      |∑ i : Fin 2, pairing R (fun x => fcenter x i)
          (fun x => (Y x).1 i - mean i)| ≤
          Real.sqrt (vectorWeakHaarEnergy R
            (fun x i => (Y x).1 i - mean i)) *
            Real.sqrt (vectorPositiveHaarEnergy R fcenter) := hhaarComm
      _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.sqrt_le_sqrt hweak) (Real.sqrt_nonneg _)
  have hlower : scalarSourcePairing (openCubeSet R) fcenter
      (fun x => ((Y x).1 - mean, (Y x).2)) ≥
        -(Real.sqrt (vectorWeakHaarEnergy R (fun x i => (Y x).1 i)) *
          Real.sqrt (vectorPositiveHaarEnergy R fcenter)) := by
    exact (neg_le_neg hhaar').trans (neg_abs_le _)
  rw [hdecomp]
  have hmain : vecNormSq mean -
      Real.sqrt (vectorWeakHaarEnergy R (fun x i => (Y x).1 i)) *
        Real.sqrt (vectorPositiveHaarEnergy R fcenter) ≤
      vecNormSq mean + scalarSourcePairing (openCubeSet R) fcenter
        (fun x => ((Y x).1 - mean, (Y x).2)) := by linarith
  simpa [Y, fcenter, mean] using hmain

end

end ASDExplicitGamma.Scalar
