module

public import ASDExplicitGamma.Scalar.RefBudget4
public import ASDExplicitGamma.Scalar.RefFinal
public import ASDExplicitGamma.Native.OldSignedCenteredPositive

/-! Elementary tile-energy facts for the rough bounds: constants and `L²`-versus-positive
energies. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Native
open scoped BigOperators

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

theorem primal_const (Q : TriadicCube 2) (q c : ℝ) :
    primalEnergy Q q (fun _ : Vec 2 => c) = c ^ 2 := by
  have h := old_signed_primal_sub_mean Q q (fun _ : Vec 2 => c) (memLp_const c)
  rw [cubeAverage_const] at h
  have h0 : (fun x : Vec 2 => (fun _ : Vec 2 => c) x - c) = fun _ => (0 : ℝ) := by
    funext x; simp
  rw [h0, old_signed_primal_zero] at h
  linarith

theorem weak_const (U : TriadicCube 2) (e : Vec 2) :
    vectorWeakHaarEnergy U (fun _ : Vec 2 => e) = vecNormSq e := by
  unfold vectorWeakHaarEnergy dualEnergy
  simp only [primal_const]
  simp [vecNormSq, vecDot]
  ring

theorem positive_const (U : TriadicCube 2) (e : Vec 2) :
    vectorPositiveHaarEnergy U (fun _ : Vec 2 => e) = vecNormSq e := by
  unfold vectorPositiveHaarEnergy
  simp only [primal_const]
  simp [vecNormSq, vecDot]
  ring

theorem tiledWeak_const (Q : TriadicCube 2) (n : ℕ) (e : Vec 2) :
    lemmaVTiledWeakEnergy Q n (fun _ : Vec 2 => e) = vecNormSq e := by
  unfold lemmaVTiledWeakEnergy
  simp only [weak_const, descendantsAverage_const]

theorem tiledPositive_const (Q : TriadicCube 2) (n : ℕ) (e : Vec 2) :
    lemmaVTiledPositiveEnergy Q n (fun _ : Vec 2 => e) = vecNormSq e := by
  unfold lemmaVTiledPositiveEnergy
  simp only [positive_const, descendantsAverage_const]

theorem energy_le_primal (R : TriadicCube 2) {f : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure R))
    (hP : Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy R (cubeIncrement R (j + 1) f))) :
    energy R f ≤ primalEnergy R (Real.sqrt 3) f := by
  have h1 : (1 : ℝ) ≤ Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hs := summable_cubeIncrement_energy R hf
  have hs' : Summable (fun j : ℕ => energy R (cubeIncrement R (j + 1) f)) :=
    (summable_nat_add_iff 1).mpr hs
  rw [← tsum_cubeIncrement_energy R hf, hs.tsum_eq_zero_add]
  unfold primalEnergy
  refine add_le_add le_rfl (Summable.tsum_le_tsum (fun k => ?_) hs' hP)
  have := one_le_pow₀ (n := k + 1) h1
  nlinarith [energy_nonneg R (cubeIncrement R (k + 1) f)]

theorem energyQ_le_positive (Q : TriadicCube 2) (n : ℕ) {F : Vec 2 → Vec 2}
    (hFQ : ∀ i : Fin 2, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hFc : ∀ U ∈ descendantsAtDepth Q n, MemLp F 2 (normalizedCubeMeasure U) ∧
      ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
        energy U (cubeIncrement U (j + 1) (fun x => F x i)))) :
    ∑ i : Fin 2, energy Q (fun x => F x i) ≤ lemmaVTiledPositiveEnergy Q n F := by
  have hi : ∀ i : Fin 2, energy Q (fun x => F x i) = descendantsAverage Q n
      (fun U => energy U (fun x => F x i)) := fun i => energy_eq_descendantsAverage Q n (hFQ i)
  simp only [hi]
  unfold lemmaVTiledPositiveEnergy vectorPositiveHaarEnergy
  rw [← descendantsAverage_sum]
  apply descendantsAverage_le
  intro U hU
  refine Finset.sum_le_sum fun i _ => energy_le_primal U ?_ ((hFc U hU).2 i)
  exact ((hFc U hU).1).eval i

end

end ASDExplicitGamma.Scalar
