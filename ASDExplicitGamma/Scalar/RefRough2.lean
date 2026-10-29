module

public import ASDExplicitGamma.Scalar.RefRoughBasic

/-! Rough pathwise bounds: the weak energy of a potential source is at most the positive energy
of its field, and the inner / forced budgets in terms of `B*`. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Native
open scoped BigOperators InnerProductSpace

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

theorem weak_potsource_le (nQ : ℤ) (G : Vec 2 → Vec 2)
    (hG : MemVectorL2 (openCubeSet (originCube 2 nQ)) G)
    (hGQ : ∀ i : Fin 2, MemLp (fun x => G x i) 2 (normalizedCubeMeasure (originCube 2 nQ)))
    (hGc : ∀ U ∈ descendantsAtDepth (originCube 2 nQ) 134, MemLp G 2 (normalizedCubeMeasure U) ∧
      ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
        energy U (cubeIncrement U (j + 1) (fun x => G x i)))) :
    lemmaVTiledWeakEnergy (originCube 2 nQ) 134
        (rep'' nQ (potMap (originCube 2 nQ)
          ((potSource (originCube 2 nQ) hG : (physicalPotentialSpace (originCube 2 nQ)).toSubmodule) :
            HilbertVectorL2 (openCubeSet (originCube 2 nQ))))).toH1Function.grad ≤
      lemmaVTiledPositiveEnergy (originCube 2 nQ) 134 G := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube 2 nQ))) :=
    (isOpenBoundedConvexDomain_openCubeSet (originCube 2 nQ)).isFiniteMeasure_restrict_volume
  set Q := originCube 2 nQ with hQ
  set X : (physicalPotentialSpace Q).toSubmodule := potSource Q hG with hX
  have hae : (rep'' nQ (potMap Q (X : HilbertVectorL2 (openCubeSet Q)))).toH1Function.grad =ᵐ[
      volumeMeasureOn (openCubeSet Q)] rep' (X : HilbertVectorL2 (openCubeSet Q)) := by
    apply ae_of_toHilbert_eq (rep'' nQ _).toH1Function.grad_memVectorL2 (rep_memL2 _)
    change (rep'' nQ _).toH1Function.gradToHilbertVectorL2 = _
    rw [rep_class, potMap_gradient, hilbert_rebuild]
  rw [tiledWeak_congr_ae Q 134 hae]
  have hmemQ : ∀ i : Fin 2, MemLp (fun x => (rep2 nQ 134 (X : HilbertVectorL2 (openCubeSet Q))).1 x i) 2
      (normalizedCubeMeasure Q) := fun i =>
    memLp_normalized_of_memL2On ((rep_memL2 _).eval i)
  have h1 : lemmaVTiledWeakEnergy Q 134 (rep' (X : HilbertVectorL2 (openCubeSet Q))) ≤
      ∑ i : Fin 2, energy Q (fun x => rep' (X : HilbertVectorL2 (openCubeSet Q)) x i) :=
    weak_le_sum_energy nQ 134 (rep2 nQ 134 (X : HilbertVectorL2 (openCubeSet Q))) hmemQ
  have h2 := sum_energy_rep nQ (X : HilbertVectorL2 (openCubeSet Q))
  have hnorm : ‖(X : HilbertVectorL2 (openCubeSet Q))‖ ≤ ‖toHilbertVectorL2OfVecField hG‖ :=
    (physicalPotentialSpace Q).toSubmodule.norm_starProjection_apply_le _
  have hn2 := norm_sq_ofField hG
  have hpair := old_signed_vector_average_pairing Q G G hG hG
  have hv : (volume (openCubeSet Q)).toReal = cubeVolume Q := volume_openCubeSet_toReal Q
  unfold volumeAverage at hpair
  rw [hv] at hpair
  have hvol := cubeVolume_pos Q
  have h3 : ∑ i : Fin 2, energy Q (fun x => G x i) =
      (cubeVolume Q)⁻¹ * ‖toHilbertVectorL2OfVecField hG‖ ^ 2 := by
    rw [hn2]
    exact hpair.symm
  have h4 : (cubeVolume Q)⁻¹ * ‖(X : HilbertVectorL2 (openCubeSet Q))‖ ^ 2 ≤
      (cubeVolume Q)⁻¹ * ‖toHilbertVectorL2OfVecField hG‖ ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) (inv_nonneg.mpr hvol.le)
  have h5 := energyQ_le_positive Q 134 hGQ hGc
  linarith

end

end ASDExplicitGamma.Scalar
