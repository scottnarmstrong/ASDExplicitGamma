module

public import ASDExplicitGamma.Triadic.DiagBroken
public import ASDExplicitGamma.Triadic.DiagBessel

/-! Exact orthogonal affine splitting of the source broken Haar energies. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

local instance diagAffineEnergyFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

theorem diagPrimalEnergy_const_add (Q : TriadicCube 2) (q c : ℝ) {f : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    primalEnergy Q q (fun x => c+f x) = c^2+2*c*cubeAverage Q f+primalEnergy Q q f := by
  have heq : (fun x => c+f x) = fun x => f x-(-c) := by funext x; ring
  rw [heq]
  unfold primalEnergy
  simp only [cubeIncrement_zero, energy_projection_zero, diagIncrement_succ_sub_const Q _ hf,
    cubeAverage_sub_const_of_memLp_two Q hf]
  ring

theorem diagDescendantsAverage_add (Q : TriadicCube 2) (j : ℕ) (F G : TriadicCube 2 → ℝ) :
    descendantsAverage Q j (fun R => F R+G R) = descendantsAverage Q j F+descendantsAverage Q j G := by
  dsimp only [descendantsAverage]
  rw [Finset.sum_add_distrib]
  ring

theorem diagDescendantsAverage_const (Q : TriadicCube 2) (j : ℕ) (c : ℝ) :
    descendantsAverage Q j (fun _ => c) = c := by
  dsimp only [descendantsAverage]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((descendantsAtDepth Q j).card : ℝ) ≠ 0 := by
    rw [descendantsAtDepth_card]
    positivity
  field_simp

theorem diagDescendantsAverage_mul (Q : TriadicCube 2) (j : ℕ) (c : ℝ) (F : TriadicCube 2 → ℝ) :
    descendantsAverage Q j (fun R => c*F R) = c*descendantsAverage Q j F := by
  dsimp only [descendantsAverage]
  rw [← Finset.mul_sum]
  ring

theorem diagDescendantsAverage_congr (Q : TriadicCube 2) (j : ℕ) {F G : TriadicCube 2 → ℝ}
    (h : ∀ R ∈ descendantsAtDepth Q j, F R=G R) : descendantsAverage Q j F=descendantsAverage Q j G := by
  dsimp only [descendantsAverage]
  rw [Finset.sum_congr rfl h]

/-- Any actual H1 witness with zero trace has zero mean gradient. -/
theorem diagH1_mean_gradient_zero (Q : TriadicCube 2) (u : H1Function (openCubeSet Q))
    (hu : MemH10 (openCubeSet Q) u.toFun) (i : Fin 2) :
    cubeAverage Q (fun x => u.grad x i) = 0 := by
  obtain ⟨w, hw⟩ := hu
  have hg : (fun x => u.grad x i) =ᵐ[volume.restrict (openCubeSet Q)]
      (fun x => w.toH1Function.grad x i) := by
    apply HasWeakPartialDerivOn.ae_eq (isOpen_openCubeSet Q)
      (locallyIntegrableOn_of_locallyIntegrable_restrict ((u.gradMemL2 i).locallyIntegrable (by norm_num)))
      (locallyIntegrableOn_of_locallyIntegrable_restrict ((w.toH1Function.gradMemL2 i).locallyIntegrable (by norm_num)))
    · have h := u.hasWeakGradient i
      rw [← hw] at h
      exact h
    · exact w.toH1Function.hasWeakGradient i
  rw [← volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] at hg
  calc
    _ = cubeAverage Q (fun x => w.toH1Function.grad x i) := by
      unfold cubeAverage
      congr 1
      exact integral_congr_ae hg
    _ = 0 := cubeAverage_h10_gradient_eq_zero Q w i

/-- Affine and zero-mean gradient contributions are orthogonal in every
source tile-averaged Haar energy, independently of its positive/negative weight. -/
theorem diagTiledHaar_affine_split (Q : TriadicCube 2) (j : ℕ) (q : ℝ) (p : Vec 2)
    (u : H1Function (openCubeSet Q)) (hu : ∀ i, cubeAverage Q (fun x => u.grad x i) = 0) :
    descendantsAverage Q j (fun R => ∑ i, primalEnergy R q (fun x => p i+u.grad x i)) =
      (∑ i, p i^2) + descendantsAverage Q j (fun R => ∑ i, primalEnergy R q (fun x => u.grad x i)) := by
  have hmean (i : Fin 2) : descendantsAverage Q j (fun R => cubeAverage R (fun x => u.grad x i)) = 0 := by
    rw [← cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q j _
      (integrableOn_of_integrable_normalizedCubeMeasure Q
        ((u.grad_memL2_normalizedCubeMeasure i).integrable one_le_two)), hu]
  have hcoord (i : Fin 2) : descendantsAverage Q j (fun R => primalEnergy R q (fun x => p i+u.grad x i)) =
      p i^2+descendantsAverage Q j (fun R => primalEnergy R q (fun x => u.grad x i)) := by
    calc
      _ = descendantsAverage Q j (fun R => p i^2+2*p i*cubeAverage R (fun x => u.grad x i)+
          primalEnergy R q (fun x => u.grad x i)) := by
        apply diagDescendantsAverage_congr
        intro R hR
        exact diagPrimalEnergy_const_add R q (p i)
          (memLp_on_descendant_of_memLp hR (u.grad_memL2_normalizedCubeMeasure i))
      _ = _ := by
        rw [diagDescendantsAverage_add, diagDescendantsAverage_add, diagDescendantsAverage_const,
          diagDescendantsAverage_mul, hmean, mul_zero, add_zero]
  rw [descendantsAverage_sum]
  simp_rw [hcoord]
  rw [Finset.sum_add_distrib, descendantsAverage_sum]

/-- Source W(phi)^2 = |p|^2+W(f)^2 for the actual affine-data potential. -/
theorem diagTiledWeakEnergy_affinePotential (Q : TriadicCube 2) (j : ℕ) (p : Vec 2)
    (u : H10Function (openCubeSet Q)) :
    ASDExplicitGamma.Variational.lemmaVTiledWeakEnergy Q j
      (ASDExplicitGamma.Variational.lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u).grad =
        (∑ i, p i^2)+ASDExplicitGamma.Variational.lemmaVTiledWeakEnergy Q j u.toH1Function.grad := by
  unfold ASDExplicitGamma.Variational.lemmaVTiledWeakEnergy vectorWeakHaarEnergy dualEnergy
  apply diagTiledHaar_affine_split Q j (Real.sqrt 3)⁻¹ p u.toH1Function
  exact cubeAverage_h10_gradient_eq_zero Q u

/-- The interpolated affine gradient has the same exact orthogonal split. -/
theorem diagTiledPositiveEnergy_affineInterpolant (Q : TriadicCube 2) (j : ℕ) (p : Vec 2)
    (u : H10Function (openCubeSet Q)) :
    ASDExplicitGamma.Variational.lemmaVTiledPositiveEnergy Q j
      (diagInterpolant Q j (ASDExplicitGamma.Variational.lemmaVAffinePotential
        (isOpenBoundedConvexDomain_openCubeSet Q) p u)).grad =
      (∑ i, p i^2)+ASDExplicitGamma.Variational.lemmaVTiledPositiveEnergy Q j (diagInterpolant Q j u.toH1Function).grad := by
  rw [diagInterpolant_affinePotential]
  unfold ASDExplicitGamma.Variational.lemmaVTiledPositiveEnergy vectorPositiveHaarEnergy
  apply diagTiledHaar_affine_split Q j (Real.sqrt 3) p (diagInterpolant Q j u.toH1Function)
  exact diagH1_mean_gradient_zero Q _ (diagInterpolant_h10_memH10 Q j u)

end

end ASDExplicitGamma.Triadic
