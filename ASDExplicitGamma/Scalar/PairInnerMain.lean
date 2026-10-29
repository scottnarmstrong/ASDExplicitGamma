module

public import ASDExplicitGamma.Scalar.PairInner
public import ASDExplicitGamma.Scalar.DefectT4Interface
public import ASDExplicitGamma.Scalar.DefectCfgId

/-! The inner part `B_old C_{H_j}(u₀ − (e,0))` of the first-response defect: its summed weak
budget is `((1 + 3^{-1/4}) B*)² A² amp² (W(x₀) + W(y₀ − e))`. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open Algsuperdiff.Section3 ASDExplicitGamma.Native ASDExplicitGamma.Inverse
open scoped BigOperators InnerProductSpace

noncomputable section


/-- The tiled weak energy depends only on the almost-everywhere class on the cube. -/
theorem tiledWeak_congr_ae (Q : TriadicCube 2) (n : ℕ) {F G : Vec 2 → Vec 2}
    (h : F =ᵐ[volumeMeasureOn (openCubeSet Q)] G) :
    lemmaVTiledWeakEnergy Q n F = lemmaVTiledWeakEnergy Q n G := by
  unfold lemmaVTiledWeakEnergy
  have : ∀ U ∈ descendantsAtDepth Q n, vectorWeakHaarEnergy U F = vectorWeakHaarEnergy U G := by
    intro U hU
    apply smooth_feedback_vector_weak_energy_congr_ae
    have hle : volumeMeasureOn (openCubeSet U) ≤ volumeMeasureOn (openCubeSet Q) :=
      Measure.restrict_mono_set volume (openCubeSet_subset_of_mem_descendantsAtDepth hU)
    exact ae_mono hle h
  unfold descendantsAverage
  apply congrArg (fun z : ℝ => ((descendantsAtDepth Q n).card : ℝ)⁻¹ * z)
  exact Finset.sum_congr rfl this

namespace Cfg''

variable (C : Cfg'')

/-- The flux defect `y₀ − e` of the flat response. -/
def yIn (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) : C.Ys :=
  (C.U old).ofLp.1 - physicalConstantLoad C.Q C.e

/-- The potential `x₀` of the flat response. -/
def xIn (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) : C.Xs := (C.U old).ofLp.2

theorem yIn_mem_flux (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) :
    C.yIn old ∈ (physicalFluxSpace C.Q).toSubmodule := by
  refine Submodule.sub_mem _ ?_ (physicalConstantLoad_mem_fluxSpace C.Q C.e)
  have hA : ∀ x, C.Aold old x ∈ (physicalFluxSpace C.Q).toSubmodule := fun x =>
    ((physicalFluxSpace C.Q).toSubmodule.orthogonalProjectionOnto _).2
  have hl : (C.load).ofLp.1 ∈ (physicalFluxSpace C.Q).toSubmodule :=
    physicalConstantLoad_mem_fluxSpace C.Q C.e
  exact blockInverse_fst_mem C.hα (C.Aold old) _ hA C.load hl

theorem inner_eq (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (j : ℕ) :
    C.inner old j = C.Bop old (WithLp.toLp 2 (C.Vm (C.Hs j) (C.xIn old),
      -(ContinuousLinearMap.adjoint (C.Vm (C.Hs j))) (C.yIn old))) := by
  unfold inner
  congr 1
  refine WithLp.ofLp_injective 2 ?_
  rw [pureFluxBlockOperator_apply]
  simp [xIn, yIn, load, pureFluxLoad]

theorem fslot_gen (i : ℕ) (o : Option whiteBasisIndex) (hio : eOpt i = o) (x : C.Xs)
    (hF : MemVectorL2 (openCubeSet C.Q) (fun p => -((rowEltOpt C.Q 134 C.amp C.L o
      (rep'' C.nQ (potMap C.Q (x : HilbertVectorL2 (openCubeSet C.Q))))).1 p))) :
    C.Vm (C.Hs i) x = fluxSource C.Q hF := by
  cases o with
  | none =>
    have h0 := Hs_none C i hio
    have hV : C.Vm (C.Hs i) = 0 := by rw [h0]; exact map_zero _
    have hz : (fun p => -((rowEltOpt C.Q 134 C.amp C.L none
        (rep'' C.nQ (potMap C.Q (x : HilbertVectorL2 (openCubeSet C.Q))))).1 p)) =
        fun _ => (0 : Vec 2) := by
      funext p; simp [rowEltOpt]
    rw [hV, fluxSource_congr C.Q hz hF (memVectorL2_const (U := openCubeSet C.Q) 0),
      fluxSource_zero]
    rfl
  | some l =>
    have hxr : (x : HilbertVectorL2 (openCubeSet C.Q)) =
        (rep'' C.nQ (potMap C.Q (x : HilbertVectorL2 (openCubeSet C.Q)))).toH1Function.gradToHilbertVectorL2 := by
      rw [rep_class]
      exact (potMap_gradient C.Q x).symm
    have hη : MemLp (mainQ3DirectionW2 C.Q C.amp C.L (whiteBasis l)).value.toFun ⊤
        (volume.restrict (openCubeSet C.Q)) :=
      (mainQ3DirectionW2 C.Q C.amp C.L (whiteBasis l)).value_memLp_top
    have hDη : ∀ i, MemLp (fun p => (mainQ3DirectionW2 C.Q C.amp C.L (whiteBasis l)).value.grad p i)
        ⊤ (volume.restrict (openCubeSet C.Q)) :=
      fun i => PlanarW2Infinity.gradient_memLp_top_volume _ i
    have hRw := lemmaVPlanarRowField_memL2 (diagInterpolant C.Q 134)
      (mainQ3DirectionW2 C.Q C.amp C.L (whiteBasis l)).value
      (rep'' C.nQ (potMap C.Q (x : HilbertVectorL2 (openCubeSet C.Q)))).toH1Function hη hDη
    rw [fslot_core C i l hio (rep'' C.nQ (potMap C.Q (x : HilbertVectorL2 (openCubeSet C.Q)))) x hxr hRw]
    refine fluxSource_congr C.Q ?_ hRw hF
    funext p
    change _ = -(rowField C.Q 134 C.amp C.L l
      (rep'' C.nQ (potMap C.Q (x : HilbertVectorL2 (openCubeSet C.Q)))) p)
    simp [rowField]

theorem gslot_gen (i : ℕ) (o : Option whiteBasisIndex) (hio : eOpt i = o)
    (y : C.Ys) (hy : y ∈ (physicalFluxSpace C.Q).toSubmodule)
    (hG : MemVectorL2 (openCubeSet C.Q)
      (gSlotOpt C.nQ 134 C.amp C.L o (rep2 C.nQ 134 y)).1) :
    -(ContinuousLinearMap.adjoint (C.Vm (C.Hs i))) y = potSource C.Q hG := by
  cases o with
  | none =>
    have h0 := Hs_none C i hio
    have hV : C.Vm (C.Hs i) = 0 := by rw [h0]; exact map_zero _
    have hz : (gSlotOpt C.nQ 134 C.amp C.L none (rep2 C.nQ 134 y)).1 =
        fun _ => (0 : Vec 2) := by
      funext p; simp [gSlotOpt]
    rw [hV, potSource_congr C.Q hz hG (memVectorL2_const (U := openCubeSet C.Q) 0),
      potSource_zero, adjoint_zero_apply, neg_zero]
  | some l => exact gslot_core C i l hio y hy hG

/-- The flux source `V_{H_j} x₀` of the inner part. -/
def innerS1 (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (j : ℕ) : C.Ys :=
  C.Vm (C.Hs j) (C.xIn old)

/-- The potential source `−V_{H_j}^* (y₀ − e)` of the inner part. -/
def innerS2 (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (j : ℕ) : C.Xs :=
  -(ContinuousLinearMap.adjoint (C.Vm (C.Hs j))) (C.yIn old)

theorem inner_fst (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (j : ℕ) :
    (C.inner old j).ofLp.1 = twoSlotY C.Q C.hν C.hσ (C.Rest old) (C.innerS1 old j)
      (C.innerS2 old j) := by
  rw [inner_eq]; rfl

theorem inner_snd (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (j : ℕ) :
    (C.inner old j).ofLp.2 = twoSlotX C.Q C.hν C.hσ (C.Rest old) (C.innerS1 old j)
      (C.innerS2 old j) := by
  rw [inner_eq]; rfl

theorem pot_ae (X : C.Xs) (φ : H10Function (openCubeSet C.Q))
    (h : φ.toH1Function.gradToHilbertVectorL2 = (X : HilbertVectorL2 (openCubeSet C.Q))) :
    (rep'' C.nQ (potMap C.Q (X : HilbertVectorL2 (openCubeSet C.Q)))).toH1Function.grad =ᵐ[
      volumeMeasureOn (openCubeSet C.Q)] φ.toH1Function.grad := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet C.Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet C.Q).isFiniteMeasure_restrict_volume
  apply ae_of_toHilbert_eq
  change (rep'' C.nQ (potMap C.Q (X : HilbertVectorL2 (openCubeSet C.Q)))).toH1Function.gradToHilbertVectorL2 =
    φ.toH1Function.gradToHilbertVectorL2
  rw [h, rep_class]
  exact potMap_gradient C.Q X

theorem flux_ae (Yh : C.Ys) (η : H1Function (openCubeSet C.Q))
    (h : η.gradToHilbertVectorL2 = Yh) :
    (rep2 C.nQ 134 Yh).1 =ᵐ[volumeMeasureOn (openCubeSet C.Q)] η.grad := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet C.Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet C.Q).isFiniteMeasure_restrict_volume
  apply ae_of_toHilbert_eq (rep_memL2 Yh) η.grad_memVectorL2
  change toHilbertVectorL2OfVecField (rep_memL2 Yh) = η.gradToHilbertVectorL2
  rw [h, hilbert_rebuild]

theorem inner_per (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (j : ℕ) {Bstar : ℝ}
    (hBs : 0 ≤ Bstar)
    (hB : ∀ U ∈ descendantsAtDepth C.Q 134, lemmaVInverseHistory U
      (responseFramePlanarCoefficientField C.ν C.σ (C.Rest old)) ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤ Bstar)
    (r : H10Function (openCubeSet C.Q))
    (hr : r = rep'' C.nQ (potMap C.Q ((C.xIn old : C.Xs) : HilbertVectorL2 (openCubeSet C.Q))))
    (g : TiledL2Field C.Q 134) (hg : g = rep2 C.nQ 134 (C.yIn old)) :
    lemmaVTiledWeakEnergy C.Q 134 (rep'' C.nQ (potMap C.Q ((C.inner old j).ofLp.2 :
        HilbertVectorL2 (openCubeSet C.Q)))).toH1Function.grad +
      lemmaVTiledWeakEnergy C.Q 134 (rep2 C.nQ 134 (C.inner old j).ofLp.1).1 ≤
    ((1 + (3 : ℝ) ^ (-(1 / 4 : ℝ))) * Bstar) ^ 2 *
      (tiledPositiveEnergy C.Q 134 (rowEltOpt C.Q 134 C.amp C.L (eOpt j) r) +
        tiledPositiveEnergy C.Q 134 (gSlotOpt C.nQ 134 C.amp C.L (eOpt j) g)) := by
  classical
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet C.Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet C.Q).isFiniteMeasure_restrict_volume
  have hF : MemVectorL2 (openCubeSet C.Q)
      (fun p => -((rowEltOpt C.Q 134 C.amp C.L (eOpt j) r).1 p)) :=
    (rowEltOpt_memL2 C.nQ 134 C.amp C.L (eOpt j) r).neg
  have hG := gslotOpt_memL2 C.nQ 134 C.amp C.L (eOpt j) g
  have hFc := tiled_vec_admissible C.Q 134 (-(rowEltOpt C.Q 134 C.amp C.L (eOpt j) r))
  have hGc := tiled_vec_admissible C.Q 134 (gSlotOpt C.nQ 134 C.amp C.L (eOpt j) g)
  have hs1 : C.innerS1 old j ∈ (physicalFluxSpace C.Q).toSubmodule :=
    vmap_mem_flux C.Q C.σ C.hσ _ _
  have hs1' : ∀ w ∈ (physicalFluxSpace C.Q).toSubmodule,
      ⟪C.innerS1 old j, w⟫_ℝ = ⟪toHilbertVectorL2OfVecField hF, w⟫_ℝ := by
    intro w hw
    have hx := fslot_gen C j (eOpt j) rfl (C.xIn old) (by rw [← hr]; exact hF)
    have : C.innerS1 old j = fluxSource C.Q hF := by
      subst hr
      exact hx
    rw [this]
    exact fluxSource_inner C.Q hF w hw
  have hs2' : ∀ w : (physicalPotentialSpace C.Q).toSubmodule,
      ⟪((C.innerS2 old j : C.Xs) : HilbertVectorL2 (openCubeSet C.Q)),
        (w : HilbertVectorL2 (openCubeSet C.Q))⟫_ℝ =
        ⟪toHilbertVectorL2OfVecField hG, (w : HilbertVectorL2 (openCubeSet C.Q))⟫_ℝ := by
    intro w
    have hy := gslot_gen C j (eOpt j) rfl (C.yIn old) (C.yIn_mem_flux old)
      (by rw [← hg]; exact hG)
    have : C.innerS2 old j = potSource C.Q hG := by
      subst hg
      exact hy
    rw [this]
    exact potSource_inner C.Q hG w
  obtain ⟨φ, η, hxφ, hyη, hw⟩ := pair_weak_energy_bound C.Q 134 C.hν C.hσ (C.Rest old)
    hF hG hFc hGc (C.innerS1 old j) (C.innerS2 old j) hs1 hs1' hs2' hBs hB
  rw [inner_fst, inner_snd]
  rw [tiledWeak_congr_ae C.Q 134 (pot_ae C _ φ hxφ),
    tiledWeak_congr_ae C.Q 134 (flux_ae C _ η hyη)]
  refine hw.trans (le_of_eq ?_)
  have e1 : lemmaVTiledPositiveEnergy C.Q 134 (fun p => -((rowEltOpt C.Q 134 C.amp C.L (eOpt j) r).1 p)) =
      tiledPositiveEnergy C.Q 134 (rowEltOpt C.Q 134 C.amp C.L (eOpt j) r) :=
    tiledPositiveEnergy_neg' C.Q 134 _
  rw [e1]
  rfl

theorem inner_weak_sum (hmesh : diagMeshRadius C.Q 134 ≤ C.L.1 / 729)
    (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (n : ℕ) {Bstar : ℝ} (hBs : 0 ≤ Bstar)
    (hB : ∀ U ∈ descendantsAtDepth C.Q 134, lemmaVInverseHistory U
      (responseFramePlanarCoefficientField C.ν C.σ (C.Rest old)) ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤ Bstar) :
    (∑ j : Fin n, lemmaVTiledWeakEnergy C.Q 134
        (rep'' C.nQ (potMap C.Q ((C.inner old j).ofLp.2 : HilbertVectorL2
          (openCubeSet C.Q)))).toH1Function.grad +
      ∑ j : Fin n, lemmaVTiledWeakEnergy C.Q 134 (rep2 C.nQ 134 (C.inner old j).ofLp.1).1) ≤
    ((1 + (3 : ℝ) ^ (-(1 / 4 : ℝ))) * Bstar) ^ 2 * (defectA ^ 2 * C.amp ^ 2) *
      (lemmaVTiledWeakEnergy C.Q 134 (rep'' C.nQ (potMap C.Q
          ((C.xIn old : C.Xs) : HilbertVectorL2 (openCubeSet C.Q)))).toH1Function.grad +
        lemmaVTiledWeakEnergy C.Q 134 (rep2 C.nQ 134 (C.yIn old)).1) := by
  classical
  have hK0 : 0 ≤ ((1 + (3 : ℝ) ^ (-(1 / 4 : ℝ))) * Bstar) ^ 2 := sq_nonneg _
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) fun j _ =>
    C.inner_per old j hBs hB _ rfl _ rfl
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  have he := eOpt_inj_fin n
  have c1 := rowOpt_col C.nQ 134 C.amp C.L (fun i : Fin n => eOpt i) he
    (rep'' C.nQ (potMap C.Q ((C.xIn old : C.Xs) : HilbertVectorL2 (openCubeSet C.Q))))
  have c2 := gslotOpt_col C.nQ 134 C.amp C.L (fun i : Fin n => eOpt i) he
    (rep2 C.nQ 134 (C.yIn old))
  have hk : colKappa C.Q 134 C.amp C.L ^ 2 ≤ defectA ^ 2 * C.amp ^ 2 :=
    colKappa_sq_le C.Q 134 C.amp C.L hmesh
  have hW1 := lemmaVTiledWeakEnergy_nonneg C.Q 134
    (rep'' C.nQ (potMap C.Q ((C.xIn old : C.Xs) : HilbertVectorL2 (openCubeSet C.Q)))).toH1Function.grad
  have hW2 := lemmaVTiledWeakEnergy_nonneg C.Q 134 (rep2 C.nQ 134 (C.yIn old)).1
  have hlin := add_le_add c1 c2
  rw [← mul_add] at hlin
  have hfin := hlin.trans (mul_le_mul_of_nonneg_right hk (add_nonneg hW1 hW2))
  refine hsum.trans ?_
  have := mul_le_mul_of_nonneg_left hfin hK0
  calc _ ≤ _ := this
    _ = _ := by ring

end Cfg''

end

end ASDExplicitGamma.Scalar
