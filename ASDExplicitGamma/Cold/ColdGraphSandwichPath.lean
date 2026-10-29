module

public import ASDExplicitGamma.Cold.ColdGraphReflection
public import ASDExplicitGamma.Cold.GraphSandwichOrder
public import ASDExplicitGamma.Cold.GraphScalarAlgebra
public import ASDExplicitGamma.Cold.MatrixFrobeniusPairing

/-! # Actual source sandwich and its exact deterministic half-floor term -/

@[expose] public section
noncomputable section
open Homogenization Matrix
namespace ASDExplicitGamma.Cold

/-- Literal reflection is additive. -/
theorem coldGraphReflection_add (A B : FullBlockMat 2) :
    coldGraphReflection (A+B) = coldGraphReflection A+coldGraphReflection B := by
  ext i j
  simp only [coldGraphReflection_apply,Matrix.add_apply]

/-- The actual coarse response duality and source subadditivity imply the pathwise graph bound. -/
theorem cold_graph_source_sandwich {A X : FullBlockMat 2} (hA : A.PosDef)
    (hsub : (X-A).PosSemidef)
    (hdual : (coarseGramSwap*A*coarseGramSwap-A⁻¹).PosSemidef) :
    matrixFrobeniusSq (A-1) ≤
      matrixFrobeniusInner ((X-1)-coldGraphReflection (X-1)) (A-1)+
      matrixFrobeniusInner (X-1) (coldGraphReflection (X-1)) := by
  have hX : X.IsHermitian := by
    have h := hsub.1.add hA.1
    have he : (X-A)+A = X := by abel
    rwa [he] at h
  have hV : (coldGraphReflection (X-1)).IsHermitian := by
    have h := isHermitian_conjTranspose_mul_mul coarseGramSwap (hX.sub isHermitian_one)
    rwa [coarseGramSwap_isHermitian.eq] at h
  have hu : ((X-1)-(A-1)).PosSemidef := by
    have he : (X-1)-(A-1) = X-A := by abel
    rwa [he]
  have hl : ((A-1)+coldGraphReflection (X-1)).PosSemidef := by
    have h := cold_graph_lower_sandwich hA coarseGramSwap_isHermitian hdual hsub
    have he : (A-1)+coldGraphReflection (X-1) = A+coarseGramSwap*X*coarseGramSwap-2 • (1:FullBlockMat 2) := by
      unfold coldGraphReflection
      simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,coarseGramSwap_sq,two_smul]
      abel
    rwa [he]
  have h := cold_graph_sandwich_pathwise (hA.1.sub isHermitian_one) hu hl
  rw [← matrixFrobeniusInner_eq_trace_mul _ hV] at h
  exact h

/-- The exact deterministic expected-block term is at most half the squared source mean. -/
theorem cold_graph_half_deterministic {p q r s : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrp : r ≤ p) (hsq : s ≤ q) :
    matrixFrobeniusInner (coldGraphBlockMean p q-coldGraphReflection (coldGraphBlockMean p q))
      (coldGraphBlockMean r s)+
      matrixFrobeniusInner (coldGraphBlockMean p q) (coldGraphReflection (coldGraphBlockMean p q)) ≤
      (2*(p+q))^2/2 := by
  rw [coldGraphReflection_blockMean,matrixFrobeniusInner_sub_left,
    coldGraphBlockMean_inner,coldGraphBlockMean_inner,coldGraphBlockMean_inner]
  have h := cold_graph_half_bias hp hq hr hs hrp hsq
  nlinarith only [h]

end ASDExplicitGamma.Cold
