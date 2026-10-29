module

public import ASDExplicitGamma.Scalar.RefRough2

/-! The pathwise inner rough bound `√T ≤ (44/25) B* + 1` (unit `e`), alpha-free. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Native
open Algsuperdiff.Section3
open scoped BigOperators InnerProductSpace

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

theorem const_admissible (U : TriadicCube 2) (e : Vec 2) :
    MemLp (fun _ : Vec 2 => e) 2 (normalizedCubeMeasure U) ∧
      ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
        energy U (cubeIncrement U (j + 1) (fun x => (fun _ : Vec 2 => e) x i))) := by
  refine ⟨memLp_const e, fun i => ?_⟩
  have h : ∀ j : ℕ, (Real.sqrt 3) ^ (j + 1) *
      energy U (cubeIncrement U (j + 1) (fun x => (fun _ : Vec 2 => e) x i)) = 0 := by
    intro j
    have h0 : cubeIncrement U (j + 1) (fun x => (fun _ : Vec 2 => e) x i) = fun _ => 0 := by
      funext x
      exact cubeIncrement_succ_const U j (e i) x
    rw [h0]
    have h00 := cubeAverage_const U (0 : ℝ)
    simp [energy, pairing, h00]
  simp only [h]
  exact summable_zero

theorem weak_zero (Q : TriadicCube 2) (n : ℕ) :
    lemmaVTiledWeakEnergy Q n (fun _ : Vec 2 => (0 : Vec 2)) = 0 := by
  have := tiledWeak_const Q n 0
  simpa [vecNormSq, vecDot] using this

theorem weak_neg (U : TriadicCube 2) (f : Vec 2 → Vec 2) :
    vectorWeakHaarEnergy U (fun x i => -f x i) = vectorWeakHaarEnergy U f := by
  unfold vectorWeakHaarEnergy dualEnergy
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := sensitivity_primalEnergy_smul U (Real.sqrt 3)⁻¹ (fun x => f x i) (-1)
  have e1 : (fun x => -f x i) = fun x => (-1 : ℝ) * f x i := by funext x; ring
  rw [e1, h]; ring

theorem tiledWeak_neg (Q : TriadicCube 2) (n : ℕ) (f : Vec 2 → Vec 2) :
    lemmaVTiledWeakEnergy Q n (fun x i => -f x i) = lemmaVTiledWeakEnergy Q n f := by
  unfold lemmaVTiledWeakEnergy
  simp only [weak_neg]

end

end ASDExplicitGamma.Scalar
