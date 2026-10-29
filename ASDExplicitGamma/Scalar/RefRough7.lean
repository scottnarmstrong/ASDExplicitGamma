module

public import ASDExplicitGamma.Scalar.RefRough6

/-! The pathwise forced rough bound `√forced ≤ A |amp| ((44/25) B* + 1)` (unit `e`). -/

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

theorem forced_rough (hQo : openCubeSet C.Q ⊆ openRectangle C.a C.b C.c C.d)
    (hmesh : diagMeshRadius C.Q 134 ≤ C.L.1 / 729) (he2 : vecNormSq C.e = 1)
    (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (n : ℕ) {Bstar : ℝ} (hBs : 0 ≤ Bstar)
    (hB : ∀ U ∈ descendantsAtDepth C.Q 134, lemmaVInverseHistory U
      (responseFramePlanarCoefficientField C.ν C.σ (C.Rest old)) ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤ Bstar) :
    Real.sqrt (C.forcedLamR n old) ≤ defectA * |C.amp| * ((44 / 25 : ℝ) * Bstar + 1) := by
  classical
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet C.Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet C.Q).isFiniteMeasure_restrict_volume
  have key : ∀ j : Fin n, ∃ (φ : H10Function (openCubeSet C.Q)) (η : H1Function (openCubeSet C.Q)),
      φ.toH1Function.gradToHilbertVectorL2 =
          ((twoSlotX C.Q C.hν C.hσ (C.Rest old) 0 (C.wt j) : C.Xs) :
            HilbertVectorL2 (openCubeSet C.Q)) ∧
      η.gradToHilbertVectorL2 = twoSlotY C.Q C.hν C.hσ (C.Rest old) 0 (C.wt j) ∧
      lemmaVTiledWeakEnergy C.Q 134 φ.toH1Function.grad + lemmaVTiledWeakEnergy C.Q 134 η.grad ≤
        ((1 + (3 : ℝ) ^ (-(1 / 4 : ℝ))) * Bstar) ^ 2 * tiledPositiveEnergy C.Q 134 (C.Gj j) ∧
      lemmaVTiledWeakEnergy C.Q 134 (rep' ((C.wt j : C.Xs) : HilbertVectorL2 (openCubeSet C.Q))) ≤
        tiledPositiveEnergy C.Q 134 (C.Gj j) := fun j => C.forced_per hQo old j hBs hB
  choose φ η hxφ hyη hw hwt using key
  set g := rep2 C.nQ 134 (physicalConstantLoad C.Q C.e) with hg
  have hmem : ∀ z : C.Pr, MemVectorL2 (openCubeSet C.Q) (fun x => (rep'' C.nQ (potMap C.Q
      ((z.ofLp.2 : C.Xs) : HilbertVectorL2 (openCubeSet C.Q)))).toH1Function.grad x) :=
    fun z => (rep'' C.nQ _).toH1Function.grad_memVectorL2
  have hsplit := sum_split C.Q (J := n)
    (fx := fun j => (φ j).toH1Function.grad)
    (ix := fun j => rep' ((-(C.wt j) : C.Xs) : HilbertVectorL2 (openCubeSet C.Q)))
    (dx := fun j => (rep'' C.nQ (potMap C.Q (((C.forcedR old j).ofLp.2 : C.Xs) :
      HilbertVectorL2 (openCubeSet C.Q)))).toH1Function.grad)
    (fy := fun j => (η j).grad) (iy := fun _ => (fun _ : Vec 2 => (0 : Vec 2)))
    (dy := fun j => (rep2 C.nQ 134 (C.forcedR old j).ofLp.1).1)
    (fun j => (φ j).toH1Function.grad_memVectorL2) (fun j => rep_memL2 _)
    (fun j => (η j).grad_memVectorL2) (fun _ => memVectorL2_const 0)
    (fun j => by
      apply ae_add_of_classes ((φ j).toH1Function.grad_memVectorL2) (rep_memL2 _)
        ((rep'' C.nQ _).toH1Function.grad_memVectorL2)
      change (rep'' C.nQ _).toH1Function.gradToHilbertVectorL2 =
        (φ j).toH1Function.gradToHilbertVectorL2 + toHilbertVectorL2OfVecField (rep_memL2 _)
      rw [rep_class, potMap_gradient, hilbert_rebuild, hxφ, C.forcedR_snd hQo old j]
      simp [sub_eq_add_neg])
    (fun j => by
      have h1 := C.flux_ae ((C.forcedR old j).ofLp.1) (η j) (by rw [C.forcedR_fst hQo old j]; exact hyη j)
      filter_upwards [h1] with x hx
      funext i
      have : (rep2 C.nQ 134 (C.forcedR old j).ofLp.1).1 x = (η j).grad x := hx
      rw [this]; simp)
  simp only [weak_zero, Finset.sum_const_zero, add_zero] at hsplit
  have hkap := colKappa_sq_le C.Q 134 C.amp C.L hmesh
  have hk0 : 0 ≤ colKappa C.Q 134 C.amp C.L := colKappa_nonneg C.nQ 134 C.amp C.L
  have hWg : lemmaVTiledWeakEnergy C.Q 134 g.1 = 1 := by
    have h1 : g.1 =ᵐ[volumeMeasureOn (openCubeSet C.Q)] fun _ => C.e := by
      apply ae_of_toHilbert_eq (rep_memL2 _) (memVectorL2_const C.e)
      rw [hilbert_rebuild]; rfl
    rw [tiledWeak_congr_ae C.Q 134 h1, tiledWeak_const]; exact he2
  have hcol := gslotOpt_col C.nQ 134 C.amp C.L (fun i : Fin n => eOpt i) (eOpt_inj_fin n) g
  rw [hWg, mul_one] at hcol
  have hcolG : ∑ j : Fin n, tiledPositiveEnergy C.Q 134 (C.Gj j) ≤ colKappa C.Q 134 C.amp C.L ^ 2 := hcol
  set K0 : ℝ := ((1 + (3 : ℝ) ^ (-(1 / 4 : ℝ))) * Bstar) ^ 2 with hK0
  have hK00 : 0 ≤ K0 := sq_nonneg _
  have hP0 : ∀ j : Fin n, 0 ≤ tiledPositiveEnergy C.Q 134 (C.Gj j) := fun j => by
    unfold tiledPositiveEnergy lemmaVTiledPositiveEnergy descendantsAverage
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun U _ => vectorPositiveHaarEnergy_nonneg U _)
  have hAs : ∑ j : Fin n, lemmaVTiledWeakEnergy C.Q 134 (φ j).toH1Function.grad +
      ∑ j : Fin n, lemmaVTiledWeakEnergy C.Q 134 (η j).grad ≤
      K0 * colKappa C.Q 134 C.amp C.L ^ 2 := by
    rw [← Finset.sum_add_distrib]
    calc _ ≤ ∑ j : Fin n, K0 * tiledPositiveEnergy C.Q 134 (C.Gj j) := Finset.sum_le_sum fun j _ => hw j
      _ = K0 * ∑ j : Fin n, tiledPositiveEnergy C.Q 134 (C.Gj j) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hcolG hK00
  have hBs' : ∑ j : Fin n, lemmaVTiledWeakEnergy C.Q 134
      (rep' ((-(C.wt j) : C.Xs) : HilbertVectorL2 (openCubeSet C.Q))) ≤
      colKappa C.Q 134 C.amp C.L ^ 2 := by
    refine le_trans (Finset.sum_le_sum fun j _ => ?_) hcolG
    rw [Submodule.coe_neg, tiledWeak_congr_ae C.Q 134 (rep_neg (U := openCubeSet C.Q)
      ((C.wt j : C.Xs) : HilbertVectorL2 (openCubeSet C.Q))), tiledWeak_neg]
    exact hwt j
  have hc : (1 + (3 : ℝ) ^ (-(1 / 4 : ℝ))) ≤ 44 / 25 := by
    have := three_pow_neg_quarter_le
    linarith
  have hA0 : 0 ≤ defectA * |C.amp| := by unfold defectA; positivity
  have hkA : colKappa C.Q 134 C.amp C.L ≤ defectA * |C.amp| := by
    calc _ = Real.sqrt (colKappa C.Q 134 C.amp C.L ^ 2) := (Real.sqrt_sq hk0).symm
      _ ≤ Real.sqrt (defectA ^ 2 * C.amp ^ 2) := Real.sqrt_le_sqrt hkap
      _ = defectA * |C.amp| := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by unfold defectA; positivity),
          Real.sqrt_sq_eq_abs]
  have h1 : Real.sqrt (∑ j : Fin n, lemmaVTiledWeakEnergy C.Q 134 (φ j).toH1Function.grad +
      ∑ j : Fin n, lemmaVTiledWeakEnergy C.Q 134 (η j).grad) ≤
      (44 / 25 : ℝ) * Bstar * colKappa C.Q 134 C.amp C.L := by
    calc _ ≤ Real.sqrt (K0 * colKappa C.Q 134 C.amp C.L ^ 2) := Real.sqrt_le_sqrt hAs
      _ = (1 + (3 : ℝ) ^ (-(1 / 4 : ℝ))) * Bstar * colKappa C.Q 134 C.amp C.L := by
        rw [Real.sqrt_mul hK00, hK0, Real.sqrt_sq (mul_nonneg (by positivity) hBs),
          Real.sqrt_sq hk0]
      _ ≤ _ := by
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hBs) hk0
        linarith
  have h2 : Real.sqrt (∑ j : Fin n, lemmaVTiledWeakEnergy C.Q 134
      (rep' ((-(C.wt j) : C.Xs) : HilbertVectorL2 (openCubeSet C.Q)))) ≤
      colKappa C.Q 134 C.amp C.L := by
    calc _ ≤ Real.sqrt (colKappa C.Q 134 C.amp C.L ^ 2) := Real.sqrt_le_sqrt hBs'
      _ = _ := Real.sqrt_sq hk0
  have hfin : Real.sqrt (C.forcedLamR n old) ≤ (44 / 25 : ℝ) * Bstar * colKappa C.Q 134 C.amp C.L +
      colKappa C.Q 134 C.amp C.L := hsplit.trans (add_le_add h1 h2)
  calc _ ≤ _ := hfin
    _ ≤ defectA * |C.amp| * ((44 / 25 : ℝ) * Bstar + 1) := by
      have := mul_le_mul_of_nonneg_left hkA (show 0 ≤ (44 / 25 : ℝ) * Bstar + 1 by positivity)
      nlinarith [this]

end Cfg''

end

end ASDExplicitGamma.Scalar
