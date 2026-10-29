module

public import ASDExplicitGamma.Scalar.FlatWickAdmissible

/-! The actual rotated q3 Wick representative of the flat source has genuine `H¹` components on
`Q` (this is the content of the proof of `flat_source_q3_actual_rotated_wick_admissible`, with
the `H¹` coordinates exported). -/

@[expose] public section

open MeasureTheory Homogenization
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic ASDExplicitGamma.Response
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped ENNReal NNReal Topology Matrix.Norms.Elementwise

namespace ASDExplicitGamma.Scalar

private theorem covarianceClamp_lipschitz
    (a b c d : ℝ) (hab : a < b) (hcd : c < d) :
    LipschitzWith 1 (lambda8CovarianceClamp a b c d hab hcd) := by
  have hfirst : LipschitzWith 1 (fun x : ℝ => lambda8CovarianceClampReal a b x) := by
    simpa [lambda8CovarianceClampReal, min_comm] using
      ((LipschitzWith.id.min_const b).const_max a)
  have hsecond : LipschitzWith 1 (fun x : ℝ => lambda8CovarianceClampReal c d x) := by
    simpa [lambda8CovarianceClampReal, min_comm] using
      ((LipschitzWith.id.min_const d).const_max c)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (lambda8CovarianceClamp a b c d hab hcd x)
      (lambda8CovarianceClamp a b c d hab hcd y) ≤ 1 * dist x y
  rw [Subtype.dist_eq]
  simp only [one_mul, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (x-y))).2
  intro i
  fin_cases i
  · change |lambda8CovarianceClampReal a b (x 0) -
      lambda8CovarianceClampReal a b (y 0)| ≤ ‖x-y‖
    have h := hfirst.norm_sub_le (x 0) (y 0)
    have h' : |lambda8CovarianceClampReal a b (x 0) -
        lambda8CovarianceClampReal a b (y 0)| ≤ |x 0-y 0| := by
      simpa only [Real.norm_eq_abs, NNReal.coe_one, one_mul] using h
    exact h'.trans (norm_le_pi_norm (x-y) 0)
  · change |lambda8CovarianceClampReal c d (x 1) -
      lambda8CovarianceClampReal c d (y 1)| ≤ ‖x-y‖
    have h := hsecond.norm_sub_le (x 1) (y 1)
    have h' : |lambda8CovarianceClampReal c d (x 1) -
        lambda8CovarianceClampReal c d (y 1)| ≤ |x 1-y 1| := by
      simpa only [Real.norm_eq_abs, NNReal.coe_one, one_mul] using h
    exact h'.trans (norm_le_pi_norm (x-y) 1)

private theorem q3_clampedShell_lipschitz
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (ω : Cutoff.CutoffSample 2) (k : ℤ) :
    ∃ C : ℝ≥0, LipschitzWith C (fun x : Vec 2 =>
      (ω.1 k (lambda8CovarianceClamp a b c d hab hcd x)) 1 0) := by
  let K := closedRectangle a b c d
  let φ : Vec 2 → ℝ := fun x => (ω.1 k x) 1 0
  have hφ : ContDiff ℝ 1 φ := by
    dsimp [φ]
    have hj : ContDiff ℝ 1 (ω.1 k) :=
      (ω.1 k).contDiff_two.of_le (by norm_num)
    exact (contDiff_apply_apply (𝕜 := ℝ) (E := ℝ) (n := 1)
      (1 : Fin 2) (0 : Fin 2)).comp hj
  have hKconv : Convex ℝ K := by
    have heq : K = (Set.univ : Set (Fin 2)).pi
        (fun i => if i = 0 then Set.Icc a b else Set.Icc c d) := by
      ext x
      simp [K, closedRectangle, Set.mem_pi, Fin.forall_fin_two]
    rw [heq]
    apply convex_pi
    intro i hi
    fin_cases i <;> simp only [ite_true, ite_false] <;>
      exact convex_Icc _ _
  obtain ⟨C, hKlip⟩ := hφ.contDiffOn.exists_lipschitzOnWith
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
    hKconv (closedRectangle_isCompact a b c d)
  have hclamp := covarianceClamp_lipschitz a b c d hab hcd
  have hval : LipschitzWith 1
      (fun y : closedRectangle a b c d => (y : Vec 2)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (x : Vec 2) (y : Vec 2) ≤
      ((1 : ℝ≥0) : ℝ) * dist (x : Vec 2) (y : Vec 2)
    rw [NNReal.coe_one, one_mul]
  have hclampVal : LipschitzWith 1
      (fun x : Vec 2 => (lambda8CovarianceClamp a b c d hab hcd x : Vec 2)) :=
    by
      change LipschitzWith 1
        ((fun y : closedRectangle a b c d => (y : Vec 2)) ∘
          lambda8CovarianceClamp a b c d hab hcd)
      simpa only [one_mul] using hval.comp hclamp
  have hmaps : Set.MapsTo
      (fun x : Vec 2 => (lambda8CovarianceClamp a b c d hab hcd x : Vec 2))
      Set.univ K := by
    intro x hx
    exact (lambda8CovarianceClamp a b c d hab hcd x).property
  have hcomp : LipschitzOnWith C
      (fun x : Vec 2 => φ (lambda8CovarianceClamp a b c d hab hcd x)) Set.univ := by
    simpa only [mul_one, Function.comp_def] using
      hKlip.comp hclampVal.lipschitzOnWith hmaps
  refine ⟨C, ?_⟩
  rw [lipschitzOnWith_univ] at hcomp
  simpa [φ, Function.comp_def] using hcomp

private theorem q3_load_component_lipschitz
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : Vec 2) (ω : Cutoff.CutoffSample 2) (k : ℤ) (i : Fin 2) :
    ∃ C : ℝ≥0, LipschitzWith C (fun x : Vec 2 =>
      lambda8Q3LoadField a b c d hab hcd e
        (shellFieldScalarRestriction (closedRectangle a b c d) (ω.1 k)) x i) := by
  obtain ⟨C, hC⟩ := q3_clampedShell_lipschitz hab hcd ω k
  let z : ℝ := matVecMul responsePlanarJ e i
  refine ⟨Real.nnabs z * C, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  change ‖((ω.1 k (lambda8CovarianceClamp a b c d hab hcd x)) 1 0) * z -
      ((ω.1 k (lambda8CovarianceClamp a b c d hab hcd y)) 1 0) * z‖ ≤ _
  rw [← sub_mul, Real.norm_eq_abs, abs_mul]
  have hscalar := hC.norm_sub_le x y
  rw [Real.norm_eq_abs] at hscalar
  calc
    |(ω.1 k (lambda8CovarianceClamp a b c d hab hcd x)) 1 0 -
        (ω.1 k (lambda8CovarianceClamp a b c d hab hcd y)) 1 0| * |z|
      ≤ ((C:ℝ) * ‖x-y‖) * |z| :=
        mul_le_mul_of_nonneg_right hscalar (abs_nonneg z)
    _ = ((Real.nnabs z * C : ℝ≥0):ℝ) * ‖x-y‖ := by
      simp only [NNReal.coe_mul, Real.coe_nnabs]
      ring

private noncomputable def q3_load_component_h1
    (Q : TriadicCube 2) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : Vec 2) (ω : Cutoff.CutoffSample 2) (k : ℤ) (i : Fin 2) :
    H1Function (openCubeSet Q) := by
  let f : Vec 2 → ℝ := fun x => lambda8Q3LoadField a b c d hab hcd e
    (shellFieldScalarRestriction (closedRectangle a b c d) (ω.1 k)) x i
  let hCexists := q3_load_component_lipschitz hab hcd e ω k i
  let C := Classical.choose hCexists
  have hC := Classical.choose_spec hCexists
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  letI : IsFiniteMeasure (volume.restrict (openCubeSet Q)) :=
    hU.isFiniteMeasure_restrict_volume
  have hclosure : IsCompact (closure (openCubeSet Q)) :=
    hU.isBoundedDomain.isBounded.isCompact_closure
  let hBexists := hclosure.exists_bound_of_continuousOn hC.continuous.continuousOn
  let B := Classical.choose hBexists
  have hB := Classical.choose_spec hBexists
  have hmem : MemLp f 2 (volume.restrict (openCubeSet Q)) := by
    apply MemLp.of_bound hC.continuous.aestronglyMeasurable B
    rw [ae_restrict_iff' hU.isOpen.measurableSet]
    exact Filter.Eventually.of_forall fun x hx => hB x (subset_closure hx)
  exact ASDExplicitGamma.Cold.lipschitzH1On (openCubeSet Q) hC hmem

private theorem shellValueLInf_ae_clamped
    (Q : TriadicCube 2) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (z : C(closedRectangle a b c d, ℝ)) :
    flatSourceQ3ShellValueLInf Q hab hcd z =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
        fun x => z (lambda8CovarianceClamp a b c d hab hcd x) := by
  let clamp : C(Vec 2, closedRectangle a b c d) :=
    ⟨lambda8CovarianceClamp a b c d hab hcd,
      flat_source_clamp_continuous a b c d hab hcd⟩
  let h3ToBounded : C(closedRectangle a b c d, ℝ) →L[ℝ]
      BoundedContinuousFunction (closedRectangle a b c d) ℝ :=
    (ContinuousMap.linearIsometryBoundedOfCompact
      (closedRectangle a b c d) ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  let bcf : BoundedContinuousFunction (Vec 2) ℝ :=
    (BoundedContinuousFunction.compContinuousCLM ℝ ℝ clamp) (h3ToBounded z)
  filter_upwards [BoundedContinuousFunction.coeFn_toLp
      (p := (∞ : ℝ≥0∞)) (μ := volumeMeasureOn (openCubeSet Q))
      (𝕜 := ℝ) bcf] with x hx
  simpa [flatSourceQ3ShellValueLInf, bcf, clamp, h3ToBounded] using hx

/-- The actual rotated q3 Wick representative is H¹ componentwise, hence
admissible for the positive-Haar source-history estimate. The outer physical
flux projection remains separate in the resolvent insertion. -/
theorem flat_wick_h1_components
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (e : Vec 2) (m : ℤ)
    (ω : Cutoff.CutoffSample 2) :
    let W := flatSourceQ3ActualWickRepresentative Q hab hcd e (m + 1) ω
    let Fflat : Vec 2 → Vec 2 := fun x =>
      planarQuarterTurn (hilbertVectorL2ToVectorL2 W x)
    ∃ G : Fin 2 → H1Function (openCubeSet Q), ∀ i : Fin 2,
      (G i).toFun =ᵐ[normalizedCubeMeasure Q] fun x => Fflat x i := by
  classical
  dsimp only
  let U := openCubeSet Q
  let K := closedRectangle a₀ b₀ c₀ d₀
  let z := shellFieldScalarRestriction K (ω.1 (m+1))
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  let ψ := flatSourceQ3ShellValueLInf Q hab hcd z
  let φ : Vec 2 → ℝ := fun x =>
    (ω.1 (m+1) (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x)) 1 0
  let p := lambda8Q3ProjectedLoadClass hU a₀ b₀ c₀ d₀ hab hcd e z
  let W := flatSourceQ3ActualWickRepresentative Q hab hcd e (m+1) ω
  let Fflat : Vec 2 → Vec 2 := fun x =>
    planarQuarterTurn (hilbertVectorL2ToVectorL2 W x)
  let L : Fin 2 → H1Function U := fun i =>
    q3_load_component_h1 Q hab hcd e ω (m+1) i
  have hfield : lambda8Q3LoadField a₀ b₀ c₀ d₀ hab hcd e z =
      lambda8H1ComponentField L := by
    funext x
    ext i
    rfl
  have hload : lambda8Q3LoadClass hU.1.measurableSet a₀ b₀ c₀ d₀ hab hcd e z =
      toHilbertVectorL2OfVecField (lambda8H1ComponentField_memVectorL2 L) := by
    change toHilbertVectorL2OfVecField
      (lambda8Q3LoadField_memVectorL2 hU.1.measurableSet
        a₀ b₀ c₀ d₀ hab hcd e z) = _
    exact Algsuperdiff.Section3.Provider.Diffusivity.Corrector.toHilbertVectorL2OfVecField_congr
      _ _ hfield
  obtain ⟨u, H, hprojection, hdivergence, hhessian⟩ :=
    lambda8DirichletProjection_hessian_source Q L
  have hp : p = u.toH1Function.gradToHilbertVectorL2 := by
    change lambda8DirichletProjection hU
      (lambda8Q3LoadClass hU.1.measurableSet a₀ b₀ c₀ d₀ hab hcd e z) = _
    rw [hload]
    exact hprojection
  have hW : W = ψ • p := by
    change flatSourceQ3ActualWickRepresentative Q hab hcd e (m+1) ω =
      flatSourceQ3ShellValueLInf Q hab hcd z •
        lambda8Q3ProjectedLoadClass hU a₀ b₀ c₀ d₀ hab hcd e z
    rw [flat_source_potential_carrier_wick_eq Q hab hcd e (m+1) ω]
    rw [flat_source_potential_carrier_coe]
  obtain ⟨Cφ, hφlip⟩ := q3_clampedShell_lipschitz hab hcd ω (m+1)
  have hψclampedRaw : ψ =ᵐ[volumeMeasureOn U] φ := by
    change flatSourceQ3ShellValueLInf Q hab hcd z =ᵐ[
      volumeMeasureOn U] fun x =>
        (ω.1 (m+1) (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x)) 1 0
    simpa [z, K, shellFieldScalarRestriction, planarShellScalarStream,
      planarShellMatrixEntry] using
      (shellValueLInf_ae_clamped Q hab hcd z)
  have hclampActualRaw : (fun x =>
      (ω.1 (m+1) (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x)) 1 0) =ᵐ[
        volumeMeasureOn U] fun x => (ω.1 (m+1) x) 1 0 := by
    filter_upwards [ae_restrict_mem hU.1.measurableSet] with x hx
    have hc := lambda8CovarianceClamp_eq_of_mem a₀ b₀ c₀ d₀ hab hcd (hQ hx)
    simpa using congrArg (fun y : closedRectangle a₀ b₀ c₀ d₀ =>
      (ω.1 (m+1) y) 1 0) hc
  have hψactualRaw : ψ =ᵐ[volumeMeasureOn U]
      fun x => (ω.1 (m+1) x) 1 0 := hψclampedRaw.trans hclampActualRaw
  have hψφraw : ψ =ᵐ[volumeMeasureOn U] φ :=
    hψactualRaw.trans hclampActualRaw.symm
  have hscale : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 := by
    apply ENNReal.ofReal_ne_zero_iff.mpr
    exact inv_pos.mpr (cubeVolume_pos Q)
  have hψφ : ψ =ᵐ[normalizedCubeMeasure Q] φ := by
    rw [show normalizedCubeMeasure Q =
      ENNReal.ofReal ((cubeVolume Q)⁻¹) • volumeMeasureOn U from
        normalizedCubeMeasure_eq_smul_open Q]
    exact (Measure.ae_ennreal_smul_measure_iff hscale).mpr hψφraw
  have rawToNorm {α : Type} {f g : Vec 2 → α}
      (h : f =ᵐ[volumeMeasureOn U] g) :
      f =ᵐ[normalizedCubeMeasure Q] g := by
    rw [normalizedCubeMeasure_eq_smul_open Q]
    exact (Measure.ae_ennreal_smul_measure_iff hscale).mpr h
  have hWraw : hilbertVectorL2ToVectorL2 W =ᵐ[volumeMeasureOn U]
      fun x => ψ x • hilbertVectorL2ToVectorL2 p x := by
    rw [hW]
    have hsmulLp : (ψ • p : HilbertVectorL2 U) =ᵐ[volumeMeasureOn U]
        fun x => ψ x • p x := by
      exact Lp.coeFn_lpSMul (p := (∞ : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
        (r := (2 : ℝ≥0∞)) ψ p
    filter_upwards [coeFn_hilbertVectorL2ToVectorL2 (U := U) (ψ • p),
      hsmulLp, coeFn_hilbertVectorL2ToVectorL2 (U := U) p]
      with x hprod hsmul hpv
    change hilbertVectorL2ToVectorL2 (ψ • p) x =
      ((ψ • p : HilbertVectorL2 U) x).toVec at hprod
    change (ψ • p : HilbertVectorL2 U) x = ψ x • p x at hsmul
    change hilbertVectorL2ToVectorL2 p x = (p x).toVec at hpv
    rw [hprod, hsmul, hpv]
    exact (HilbertVec.linearEquivVec 2).map_smul _ _
  have hWnorm := rawToNorm hWraw
  let V : Fin 2 → H1Function U := fun j =>
    h1_mul_lipschitz hU (Book.Ch02.openCubeSet_nonempty Q)
      (H.gradCoordH1Function j) hφlip
  let G : Fin 2 → H1Function U := fun i =>
    if i = 0 then -(V 1) else V 0
  have hGae (i : Fin 2) :
      (G i).toFun =ᵐ[normalizedCubeMeasure Q] fun x => Fflat x i := by
    have hcoordRaw (j : Fin 2) :
        hilbertVectorL2_normalizedCoordCLM Q j W =ᵐ[normalizedCubeMeasure Q]
          fun x => (hilbertVectorL2ToVectorL2 W x) j :=
      hilbertVectorL2_normalizedCoordCLM_ae Q j W
    have hcoordPraw (j : Fin 2) :
        hilbertVectorL2_normalizedCoordCLM Q j p =ᵐ[normalizedCubeMeasure Q]
          fun x => (hilbertVectorL2ToVectorL2 p x) j :=
      hilbertVectorL2_normalizedCoordCLM_ae Q j p
    have hcoordW (j : Fin 2) :
        hilbertVectorL2_normalizedCoordCLM Q j W =ᵐ[normalizedCubeMeasure Q]
          fun x => ψ x * (hilbertVectorL2_normalizedCoordCLM Q j p) x := by
      filter_upwards [hcoordRaw j, hWnorm, hcoordPraw j] with x hw hwp hpv
      rw [hw, hwp, hpv]
      simp
    have hpcoord (j : Fin 2) :
        hilbertVectorL2_normalizedCoordCLM Q j p =ᵐ[normalizedCubeMeasure Q]
          fun x => (H.gradCoordH1Function j).toFun x := by
      have hpc := hilbertVectorL2_normalizedCoordCLM_ae Q j p
      have hgradRaw : (fun x => (hilbertVectorL2ToVectorL2
          u.toH1Function.gradToHilbertVectorL2 x) j) =ᵐ[volumeMeasureOn U]
            fun x => (H.gradCoordH1Function j).toFun x := by
        have htransport := coeFn_hilbertVectorL2ToVectorL2
          (U := U) u.toH1Function.gradToHilbertVectorL2
        have hgrad := u.toH1Function.coeFn_gradToHilbertVectorL2
        filter_upwards [htransport, hgrad] with x ht hg
        have hvec : hilbertVectorL2ToVectorL2
            u.toH1Function.gradToHilbertVectorL2 x = u.toH1Function.grad x := by
          rw [ht, hg]
          simp [hilbertifyVecField]
        simpa only [HasWeakHessianOn.gradCoordH1Function_apply] using
          congrArg (fun v : Vec 2 => v j) hvec
      have hgradNorm := rawToNorm hgradRaw
      have hraw' : (fun x => (hilbertVectorL2ToVectorL2
          u.toH1Function.gradToHilbertVectorL2 x) j) =ᵐ[normalizedCubeMeasure Q]
            fun x => (H.gradCoordH1Function j).toFun x := hgradNorm
      have hpr : (fun x => (hilbertVectorL2ToVectorL2 p x) j) =ᵐ[
          normalizedCubeMeasure Q] fun x =>
            (hilbertVectorL2ToVectorL2 u.toH1Function.gradToHilbertVectorL2 x) j := by
        filter_upwards [] with x
        rw [hp]
      have hpcoord' : hilbertVectorL2_normalizedCoordCLM Q j p =ᵐ[
          normalizedCubeMeasure Q] fun x =>
            (H.gradCoordH1Function j).toFun x := by
        exact hpc.trans (hpr.trans hraw')
      exact hpcoord'
    have hcoord (j : Fin 2) :
        (fun x => Fflat x j) =ᵐ[normalizedCubeMeasure Q]
          (fun x => planarQuarterTurn
            (hilbertVectorL2ToVectorL2 W x) j) := by rfl
    have hVtoFun (j : Fin 2) : (V j).toFun = fun x =>
        φ x * (H.gradCoordH1Function j).toFun x := by
      simpa [V] using h1_mul_lipschitz_toFun hU
        (Book.Ch02.openCubeSet_nonempty Q) (H.gradCoordH1Function j) hφlip
    fin_cases i
    · filter_upwards [hcoordW 1, hcoordRaw 1, hpcoord 1, hcoord 0, hψφ]
        with x hw hr hp' hf hψx
      calc
        (G 0).toFun x = -(φ x * (H.gradCoordH1Function 1).toFun x) := by
          simp [G, H1Function.neg_toFun, hVtoFun]
        _ = -(ψ x * (hilbertVectorL2_normalizedCoordCLM Q 1 p) x) := by
          rw [← hψx, ← hp']
        _ = -(hilbertVectorL2_normalizedCoordCLM Q 1 W x) := by rw [hw]
        _ = -((hilbertVectorL2ToVectorL2 W x) 1) := by rw [hr]
        _ = Fflat x 0 := by rw [hf]; simp [Fflat, planarQuarterTurn]
    · filter_upwards [hcoordW 0, hcoordRaw 0, hpcoord 0, hcoord 1, hψφ]
        with x hw hr hp' hf hψx
      calc
        (G 1).toFun x = φ x * (H.gradCoordH1Function 0).toFun x := by
          simp [G, hVtoFun]
        _ = ψ x * (hilbertVectorL2_normalizedCoordCLM Q 0 p) x := by
          rw [← hψx, ← hp']
        _ = hilbertVectorL2_normalizedCoordCLM Q 0 W x := by rw [hw]
        _ = (hilbertVectorL2ToVectorL2 W x) 0 := by rw [hr]
        _ = Fflat x 1 := by rw [hf]; simp [Fflat, planarQuarterTurn]
  exact ⟨G, hGae⟩

end ASDExplicitGamma.Scalar
