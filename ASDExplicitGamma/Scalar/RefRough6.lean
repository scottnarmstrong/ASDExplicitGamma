module

public import ASDExplicitGamma.Scalar.RefRough5

/-! Per-mode pair weak bound of the forced part. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Native
open Algsuperdiff.Section3
open scoped BigOperators InnerProductSpace

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

namespace Cfg''

variable (C : Cfg'')

/-- The `G`-slot field of the forced source of mode `j` (for the unit flux load `e`). -/
def Gj (j : ℕ) : TiledHaarField C.Q 134 :=
  gSlotOpt C.nQ 134 C.amp C.L (eOpt j) (rep2 C.nQ 134 (physicalConstantLoad C.Q C.e))

theorem forced_per (hQo : openCubeSet C.Q ⊆ openRectangle C.a C.b C.c C.d)
    (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (j : ℕ) {Bstar : ℝ} (hBs : 0 ≤ Bstar)
    (hB : ∀ U ∈ descendantsAtDepth C.Q 134, lemmaVInverseHistory U
      (responseFramePlanarCoefficientField C.ν C.σ (C.Rest old)) ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤ Bstar) :
    ∃ (φ : H10Function (openCubeSet C.Q)) (η : H1Function (openCubeSet C.Q)),
      φ.toH1Function.gradToHilbertVectorL2 =
          ((twoSlotX C.Q C.hν C.hσ (C.Rest old) 0 (C.wt j) : C.Xs) :
            HilbertVectorL2 (openCubeSet C.Q)) ∧
      η.gradToHilbertVectorL2 = twoSlotY C.Q C.hν C.hσ (C.Rest old) 0 (C.wt j) ∧
      lemmaVTiledWeakEnergy C.Q 134 φ.toH1Function.grad + lemmaVTiledWeakEnergy C.Q 134 η.grad ≤
        ((1 + (3 : ℝ) ^ (-(1 / 4 : ℝ))) * Bstar) ^ 2 * tiledPositiveEnergy C.Q 134 (C.Gj j) ∧
      lemmaVTiledWeakEnergy C.Q 134 (rep' ((C.wt j : C.Xs) : HilbertVectorL2 (openCubeSet C.Q))) ≤
        tiledPositiveEnergy C.Q 134 (C.Gj j) := by
  classical
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet C.Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet C.Q).isFiniteMeasure_restrict_volume
  have hG : MemVectorL2 (openCubeSet C.Q) (C.Gj j).1 :=
    gslotOpt_memL2 C.nQ 134 C.amp C.L (eOpt j) _
  have hGc := tiled_vec_admissible C.Q 134 (C.Gj j)
  have hGQ : ∀ i : Fin 2, MemLp (fun x => (C.Gj j).1 x i) 2 (normalizedCubeMeasure C.Q) := fun i =>
    memLp_normalized_of_memL2On (hG.eval i)
  have hwt : C.wt j = potSource C.Q hG := by
    rw [C.wt_eq hQo j]
    exact C.gslot_gen j (eOpt j) rfl (physicalConstantLoad C.Q C.e)
      (physicalConstantLoad_mem_fluxSpace C.Q C.e) hG
  have hF := zeroField_memL2 (openCubeSet C.Q)
  have hFc : ∀ U ∈ descendantsAtDepth C.Q 134, MemLp zeroField 2 (normalizedCubeMeasure U) ∧
      ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
        energy U (cubeIncrement U (j + 1) (fun x => zeroField x i))) :=
    fun U _ => ⟨zeroField_memLp U, fun i => zeroField_pos U i⟩
  have hs1' : ∀ w ∈ (physicalFluxSpace C.Q).toSubmodule,
      ⟪(0 : HilbertVectorL2 (openCubeSet C.Q)), w⟫_ℝ = ⟪toHilbertVectorL2OfVecField hF, w⟫_ℝ := by
    intro w _
    rw [inner_zeroField]; simp
  have hs2' : ∀ w : (physicalPotentialSpace C.Q).toSubmodule,
      ⟪((C.wt j : C.Xs) : HilbertVectorL2 (openCubeSet C.Q)),
        (w : HilbertVectorL2 (openCubeSet C.Q))⟫_ℝ =
        ⟪toHilbertVectorL2OfVecField hG, (w : HilbertVectorL2 (openCubeSet C.Q))⟫_ℝ := by
    intro w
    rw [hwt]
    exact potSource_inner C.Q hG w
  obtain ⟨φ, η, hxφ, hyη, hw⟩ := pair_weak_energy_bound C.Q 134 C.hν C.hσ (C.Rest old)
    hF hG hFc hGc 0 (C.wt j) (Submodule.zero_mem _) hs1' hs2' hBs hB
  have hPF : lemmaVTiledPositiveEnergy C.Q 134 zeroField = 0 := by
    change lemmaVTiledPositiveEnergy C.Q 134 (fun _ : Vec 2 => (0 : Vec 2)) = 0
    rw [tiledPositive_const]
    simp [vecNormSq, vecDot]
  refine ⟨φ, η, hxφ, hyη, ?_, ?_⟩
  · rw [hPF, zero_add] at hw
    exact hw
  · have h1 := weak_potsource_le C.nQ (C.Gj j).1 hG hGQ hGc
    have h2 : lemmaVTiledWeakEnergy C.Q 134 (rep' ((C.wt j : C.Xs) : HilbertVectorL2 (openCubeSet C.Q))) =
        lemmaVTiledWeakEnergy C.Q 134 (rep'' C.nQ (potMap C.Q
          ((potSource C.Q hG : C.Xs) : HilbertVectorL2 (openCubeSet C.Q)))).toH1Function.grad := by
      rw [hwt]
      symm
      apply tiledWeak_congr_ae
      apply ae_of_toHilbert_eq (rep'' C.nQ _).toH1Function.grad_memVectorL2 (rep_memL2 _)
      change (rep'' C.nQ _).toH1Function.gradToHilbertVectorL2 = _
      rw [rep_class, potMap_gradient, hilbert_rebuild]
    rw [h2]
    exact h1

end Cfg''

end

end ASDExplicitGamma.Scalar
