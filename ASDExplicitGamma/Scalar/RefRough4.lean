module

public import ASDExplicitGamma.Scalar.RefRough3
public import ASDExplicitGamma.Scalar.RefBudget
public import ASDExplicitGamma.Scalar.PairBlock

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

section Rough

variable (M : ABKModel 2) (h : ℝ) (m : ℤ) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
  (hQ : openCubeSet (originCube 2 (m + 129)) ⊆ openRectangle a b c d) (e : Vec 2)

include h hab hcd hQ

theorem T_rough (he2 : vecNormSq e = 1) (ell : ℤ)
    (hK : closedRectangle a b c d ⊆ openCubeSet (originCube 2 ell)) (ω : Cutoff.CutoffSample 2) :
    Real.sqrt (dirTiledBot M m (originCube 2 (m + 129)) e ω) ≤
      (44 / 25 : ℝ) * bhist M m (originCube 2 (m + 129)) 134 ω + 1 := by
  classical
  let C := finalCfg M h m hab hcd hQ e
  let old := olderField (closedRectangle a b c d) m ω
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet C.Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet C.Q).isFiniteMeasure_restrict_volume
  have hrest : C.Rest old = oldCutoffSkewCoefficient m C.Q ω :=
    rest_old_eq M (closedRectangle a b c d) ell m hK C.Q C.hQcl ω
  have hB : ∀ U ∈ descendantsAtDepth C.Q 134, lemmaVInverseHistory U
      (responseFramePlanarCoefficientField C.ν C.σ (C.Rest old)) ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤
        bhist M m C.Q 134 ω := by
    intro U hU
    rw [hrest]
    exact hist_le_Bhist M m C.Q U hU ω
  have hB0 := Bhist_nonneg M m C.Q 134 ω
  have hF : MemVectorL2 (openCubeSet C.Q) (fun _ : Vec 2 => C.e) := memVectorL2_const C.e
  have hG := zeroField_memL2 (openCubeSet C.Q)
  have hFc : ∀ U ∈ descendantsAtDepth C.Q 134, MemLp (fun _ : Vec 2 => C.e) 2 (normalizedCubeMeasure U) ∧
      ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
        energy U (cubeIncrement U (j + 1) (fun x => (fun _ : Vec 2 => C.e) x i))) :=
    fun U _ => const_admissible U C.e
  have hGc : ∀ U ∈ descendantsAtDepth C.Q 134, MemLp zeroField 2 (normalizedCubeMeasure U) ∧
      ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
        energy U (cubeIncrement U (j + 1) (fun x => zeroField x i))) :=
    fun U _ => ⟨zeroField_memLp U, fun i => zeroField_pos U i⟩
  have hs1 := physicalConstantLoad_mem_fluxSpace C.Q C.e
  have hs1' : ∀ w ∈ (physicalFluxSpace C.Q).toSubmodule,
      ⟪physicalConstantLoad C.Q C.e, w⟫_ℝ = ⟪toHilbertVectorL2OfVecField hF, w⟫_ℝ :=
    fun w _ => rfl
  have hs2' : ∀ w : (physicalPotentialSpace C.Q).toSubmodule,
      ⟪((0 : (physicalPotentialSpace C.Q).toSubmodule) : HilbertVectorL2 (openCubeSet C.Q)),
        (w : HilbertVectorL2 (openCubeSet C.Q))⟫_ℝ =
        ⟪toHilbertVectorL2OfVecField hG, (w : HilbertVectorL2 (openCubeSet C.Q))⟫_ℝ := by
    intro w
    rw [inner_zeroField]
    simp
  obtain ⟨φ, η, hxφ, hyη, hw⟩ := pair_weak_energy_bound C.Q 134 C.hν C.hσ (C.Rest old)
    hF hG hFc hGc (physicalConstantLoad C.Q C.e) 0 hs1 hs1' hs2' hB0 hB
  have hPF : lemmaVTiledPositiveEnergy C.Q 134 (fun _ : Vec 2 => C.e) = 1 := by
    rw [tiledPositive_const]; exact he2
  have hPG : lemmaVTiledPositiveEnergy C.Q 134 zeroField = 0 := by
    change lemmaVTiledPositiveEnergy C.Q 134 (fun _ : Vec 2 => (0 : Vec 2)) = 0
    rw [tiledPositive_const]
    simp [vecNormSq, vecDot]
  rw [hPF, hPG] at hw
  have hxφ' : φ.toH1Function.gradToHilbertVectorL2 = ((C.xIn old : C.Xs) : HilbertVectorL2 (openCubeSet C.Q)) := hxφ
  have hpot := C.pot_ae (C.xIn old) φ hxφ'
  have hy1 : η.gradToHilbertVectorL2 = (C.U old).ofLp.1 := hyη
  have hflux := C.flux_ae ((C.U old).ofLp.1) η hy1
  have hflat := final_flat_budget M h m hab hcd hQ e ell hK ω
  have hrepY := rep_sub_const C.Q ((C.U old).ofLp.1) C.e
  have hsplit := sum_split C.Q (J := 1)
    (fx := fun _ => φ.toH1Function.grad) (ix := fun _ => (fun _ : Vec 2 => (0 : Vec 2)))
    (dx := fun _ => (rep'' C.nQ (potMap C.Q ((C.xIn old : C.Xs) : HilbertVectorL2
      (openCubeSet C.Q)))).toH1Function.grad)
    (fy := fun _ => η.grad) (iy := fun _ => (fun _ : Vec 2 => -C.e))
    (dy := fun _ => (rep2 C.nQ 134 (C.yIn old)).1)
    (fun _ => φ.toH1Function.grad_memVectorL2) (fun _ => memVectorL2_const 0)
    (fun _ => η.grad_memVectorL2) (fun _ => memVectorL2_const (-C.e))
    (fun _ => hpot.mono fun x hx => by funext i; simp [hx])
    (fun _ => by
      have h1 : (rep2 C.nQ 134 (C.yIn old)).1 =ᵐ[volumeMeasureOn (openCubeSet C.Q)]
          fun x i => rep' ((C.U old).ofLp.1) x i - C.e i := hrepY
      filter_upwards [h1, hflux] with x hx1 hx2
      funext i
      have : rep' ((C.U old).ofLp.1) x = η.grad x := hx2
      rw [hx1, this]; simp [sub_eq_add_neg])
  simp only [Finset.univ_unique, Finset.sum_singleton] at hsplit
  rw [weak_zero, tiledWeak_const] at hsplit
  have hsq : Real.sqrt (lemmaVTiledWeakEnergy C.Q 134 φ.toH1Function.grad +
      lemmaVTiledWeakEnergy C.Q 134 η.grad) ≤ (1 + (3 : ℝ) ^ (-(1 / 4 : ℝ))) * bhist M m C.Q 134 ω := by
    calc _ ≤ Real.sqrt (((1 + (3 : ℝ) ^ (-(1 / 4 : ℝ))) * bhist M m C.Q 134 ω) ^ 2 * (1 + 0)) :=
          Real.sqrt_le_sqrt hw
      _ = _ := by
        rw [add_zero, mul_one, Real.sqrt_sq (mul_nonneg (by positivity) hB0)]
  have hc : (1 + (3 : ℝ) ^ (-(1 / 4 : ℝ))) ≤ 44 / 25 := by
    have := three_pow_neg_quarter_le
    linarith
  have he2' : vecNormSq C.e = 1 := he2
  have hneg : vecNormSq (-C.e) = 1 := by
    simpa [vecNormSq, vecDot] using he2'
  rw [hneg] at hsplit
  have hT : dirTiledBot M m C.Q e ω = lemmaVTiledWeakEnergy C.Q 134
      (rep'' C.nQ (potMap C.Q ((C.xIn old : C.Xs) : HilbertVectorL2 (openCubeSet C.Q)))).toH1Function.grad +
      lemmaVTiledWeakEnergy C.Q 134 (rep2 C.nQ 134 (C.yIn old)).1 := hflat.symm
  show Real.sqrt (dirTiledBot M m C.Q e ω) ≤ _
  rw [hT]
  calc _ ≤ _ := hsplit
    _ ≤ (44 / 25 : ℝ) * bhist M m C.Q 134 ω + 1 := by
      simp only [add_zero, zero_add]
      nlinarith [hsq, hc, hB0]

end Rough

end

end ASDExplicitGamma.Scalar
