module

public import ASDExplicitGamma.Cold.ColdGraphSandwichPath

/-! # Exact annealed expansion of the actual two-sided matrix sandwich -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Matrix
open scoped ENNReal
namespace ASDExplicitGamma.Cold

/-- Mean zero removes only deterministic cross terms in the source sandwich. -/
theorem cold_graph_sandwich_expansion {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsProbabilityMeasure ℙ] (P Q : FullBlockMat 2) (E H : Ω → FullBlockMat 2)
    (hE : ∀ i j, MemLp (fun ω => E ω i j) 2 ℙ) (hH : ∀ i j, MemLp (fun ω => H ω i j) 2 ℙ)
    (hmeanE : matrixMean ℙ E = 0) (hmeanH : matrixMean ℙ H = Q) :
    matrixFrobeniusPairing ℙ (fun ω => (P+E ω)-coldGraphReflection (P+E ω)) H+
      matrixFrobeniusPairing ℙ (fun ω => P+E ω) (fun ω => coldGraphReflection (P+E ω)) =
      matrixFrobeniusInner (P-coldGraphReflection P) Q+matrixFrobeniusInner P (coldGraphReflection P)+
      matrixFrobeniusPairing ℙ (fun ω => E ω-coldGraphReflection (E ω)) H+
      matrixFrobeniusPairing ℙ E (fun ω => coldGraphReflection (E ω)) := by
  let RP := coldGraphReflection P
  let RE := fun ω => coldGraphReflection (E ω)
  have hP (i j) : MemLp (fun _ : Ω => P i j) 2 ℙ := memLp_const _
  have hRP (i j) : MemLp (fun _ : Ω => RP i j) 2 ℙ := memLp_const _
  have hRE (i j) : MemLp (fun ω => RE ω i j) 2 ℙ := memLp_coldGraphReflection hE i j
  have hV (i j) : MemLp (fun ω => (RP+RE ω) i j) 2 ℙ := (hRP i j).add (hRE i j)
  have hdiff (i j) : MemLp (fun ω => (E ω-RE ω) i j) 2 ℙ := (hE i j).sub (hRE i j)
  have hPD (i j) : MemLp (fun _ : Ω => (P-RP) i j) 2 ℙ := memLp_const _
  have hz : matrixFrobeniusInner P (0:FullBlockMat 2) = 0 := by simp [matrixFrobeniusInner]
  have hrz : matrixFrobeniusInner RP (0:FullBlockMat 2) = 0 := by simp [matrixFrobeniusInner]
  have hmeanRE : matrixMean ℙ RE = 0 := by
    rw [matrixMean_coldGraphReflection,hmeanE]
    ext i j
    simp only [coldGraphReflection_apply,Matrix.zero_apply]
  have hmeanRP : matrixMean ℙ (fun _ : Ω => RP) = RP := by
    ext i j
    simp only [matrixMean,integral_const,probReal_univ,one_smul]
  have hf : (fun ω => (P+E ω)-coldGraphReflection (P+E ω)) =
      (fun ω => (P-RP)+(E ω-RE ω)) := by
    funext ω
    rw [coldGraphReflection_add]
    dsimp only [RP,RE]
    abel
  have hv : (fun ω => coldGraphReflection (P+E ω)) = (fun ω => RP+RE ω) := by
    funext ω
    exact coldGraphReflection_add P (E ω)
  rw [hf,hv,matrixFrobeniusPairing_add_left hPD hdiff hH,
    matrixFrobeniusPairing_const_left (P-RP) H hH,hmeanH,
    matrixFrobeniusPairing_add_left (A := fun _ => P) (B := E) (C := fun ω => RP+RE ω) hP hE hV,
    matrixFrobeniusPairing_add_right hP hRP hRE,matrixFrobeniusPairing_add_right hE hRP hRE,
    matrixFrobeniusPairing_const_left P (fun _ => RP) hRP,hmeanRP,
    matrixFrobeniusPairing_const_left P RE hRE,hmeanRE,hz,
    matrixFrobeniusPairing_comm ℙ E (fun _ => RP),matrixFrobeniusPairing_const_left RP E hE,hmeanE,hrz]
  ring

end ASDExplicitGamma.Cold
