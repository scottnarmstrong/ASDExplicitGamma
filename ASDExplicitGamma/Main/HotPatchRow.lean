module

public import ASDExplicitGamma.Main.HotPatchRowCopy
public import ASDExplicitGamma.Main.Q3MultiplierScale
public import ASDExplicitGamma.Main.Q3RowProduct
public import ASDExplicitGamma.Main.Q3RowCaps
public import ASDExplicitGamma.Main.Q3ColumnProduct
public import ASDExplicitGamma.Main.ColumnProductCaps
public import ASDExplicitGamma.Triadic.PlanarDirectionOperations
public import ASDExplicitGamma.Main.HotPatchSource
public import ASDExplicitGamma.Native.OldSignedQ3SourceAdmissibility

/-! Hot-patch trial, package C (tile level): on one source cell, the Hilbert
positive energy of the finite-mode hot row `rawRow(I,w) + (−φ)·column` is
bounded by the sum of the native `w`-row energy and the derivative-column energy
of the local corrector `φ`. -/

@[expose] public section

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Model ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Scalar
open scoped BigOperators

namespace ASDExplicitGamma.Inverse

local instance hotRowFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- Negation does not change the weak Haar energy of a vector field. -/
theorem vectorWeakHaarEnergy_neg_hot (U : TriadicCube 2) (F : Vec 2 → Fin 2 → ℝ) :
    vectorWeakHaarEnergy U (fun x i => -F x i) = vectorWeakHaarEnergy U F := by
  unfold vectorWeakHaarEnergy dualEnergy
  apply Finset.sum_congr rfl
  intro i _
  exact primalEnergy_neg U (Real.sqrt 3)⁻¹ (fun x => F x i)

/-- The local-corrector part of the hot row on a cell `U`. -/
noncomputable def hotRowCorrectorPart (s : Finset whiteBasisIndex) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (U : TriadicCube 2)
    (φU : H10Function (openCubeSet U)) (x : Vec 2) : EuclideanSpace ℝ (s × Fin 2) :=
  (-φU.toH1Function.toFun x) • mainQ3FiniteColumn whiteBasis s b L x

/-- Triangle inequality for the hot row on one cell. -/
theorem hot_row_tile_triangle (Q : TriadicCube 2) (j : ℕ)
    (w : H10Function (openCubeSet Q)) (s : Finset whiteBasisIndex)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q j) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (φU : H10Function (openCubeSet U)) :
    let C1 := pureFluxMainQ3FiniteRawRow whiteBasis s b L Q j w.toH1Function
    let C2 := hotRowCorrectorPart s b L U φU
    MemLp (fun x => C1 x + C2 x) 2 (normalizedCubeMeasure U) ∧
    Summable (fun k => (Real.sqrt 3)^(k+1) * hilbertEnergy U
      (hilbertCubeIncrement U (k+1) (fun x => C1 x + C2 x))) ∧
    Real.sqrt (hilbertPrimalEnergy U (Real.sqrt 3) (fun x => C1 x + C2 x)) ≤
      Real.sqrt (hilbertPrimalEnergy U (Real.sqrt 3) C1) +
        Real.sqrt (hilbertPrimalEnergy U (Real.sqrt 3) C2) := by
  intro C1 C2
  have hlocal := pureFluxMainQ3FiniteRawRow_tile_bound_hotcopy Q j 0 w s U hU b L
  dsimp only at hlocal
  rw [ASDExplicitGamma.Native.old_signed_zero_affine_potential] at hlocal
  have hA : MemLp C1 2 (normalizedCubeMeasure U) := hlocal.1
  have hPA := hlocal.2.1
  have hB : MemLp C2 2 (normalizedCubeMeasure U) := by
    let Mcol := mainRankOneMultiplier U (mainQ3FiniteColumn whiteBasis s b L)
      (mainQ3FiniteColumn_contDiff whiteBasis s b L)
    have hBpos := Mcol.product_memLp φU.toH1Function.memL2_normalizedCubeMeasure
    have hneg := hBpos.neg
    convert hneg using 1
    funext x
    simp [hotRowCorrectorPart, C2, Mcol, mainRankOneMultiplier, neg_smul]
  have hCol := main_q3_negative_column_h1_product whiteBasis s b L U φU.toH1Function
  have hAdd := main_hilbert_positive_add U hA hB hPA hCol.1
  refine ⟨hA.add hB, hAdd.1, ?_⟩
  simpa only [hilbertPositiveHaarNorm] using hAdd.2

/-- The corrector part of the hot row obeys the derivative-column bound with the
actual constant: this is the `k_d` estimate on the cell. -/
theorem hot_row_corrector_energy_le (s : Finset whiteBasisIndex) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (U : TriadicCube 2)
    (φU : H10Function (openCubeSet U)) :
    hilbertPrimalEnergy U (Real.sqrt 3) (hotRowCorrectorPart s b L U φU) ≤
      (mainQ3ColumnConstant (cubeScaleFactor U) b L.1 *
        vectorWeakHaarNorm U (fun x i => φU.toH1Function.grad x i)) ^ 2 := by
  have hneg (x : Vec 2) : (-φU).toH1Function.toFun x = -φU.toH1Function.toFun x := by
    change (-1 : ℝ) * φU.toH1Function.toFun x = _
    ring
  have hnegg (x : Vec 2) (i : Fin 2) :
      (-φU).toH1Function.grad x i = -φU.toH1Function.grad x i := by
    change (-1 : ℝ) * φU.toH1Function.grad x i = _
    ring
  have h := (main_q3_finite_column_product whiteBasis s b L U (-φU)).2
  have hx : (fun x => (-φU).toH1Function.toFun x • mainQ3FiniteColumn whiteBasis s b L x) =
      hotRowCorrectorPart s b L U φU := by
    funext x
    simp only [hotRowCorrectorPart]
    rw [hneg x]
  rw [hx] at h
  have hg : vectorWeakHaarNorm U (fun x i => (-φU).toH1Function.grad x i) =
      vectorWeakHaarNorm U (fun x i => φU.toH1Function.grad x i) := by
    unfold vectorWeakHaarNorm
    congr 1
    have hf : (fun x i => (-φU).toH1Function.grad x i) =
        fun x i => -φU.toH1Function.grad x i := by
      funext x i
      exact hnegg x i
    rw [hf]
    exact vectorWeakHaarEnergy_neg_hot U (fun x i => φU.toH1Function.grad x i)
  rw [hg] at h
  have h0 : 0 ≤ hilbertPrimalEnergy U (Real.sqrt 3) (hotRowCorrectorPart s b L U φU) := by
    unfold hilbertPrimalEnergy
    apply add_nonneg (hilbertEnergy_nonneg U _)
    exact tsum_nonneg fun k => mul_nonneg (by positivity) (hilbertEnergy_nonneg U _)
  have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rwa [Real.sq_sqrt h0] at hs

/-- Equality on the open cell gives equality almost everywhere for the normalized
cube measure. -/
theorem hot_ae_cube_of_open (U : TriadicCube 2) {α : Type*} {f g : Vec 2 → α}
    (h : ∀ x ∈ openCubeSet U, f x = g x) : f =ᵐ[normalizedCubeMeasure U] g := by
  have h1 : ∀ᵐ x ∂(MeasureTheory.volume.restrict (openCubeSet U)), f x = g x :=
    (ae_restrict_iff' (measurableSet_openCubeSet U)).2 (Filter.Eventually.of_forall h)
  have h2 : ∀ᵐ x ∂(cubeMeasure U), f x = g x := by
    rw [cubeMeasure, Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet U)]
    exact h1
  rw [normalizedCubeMeasure]
  exact Measure.ae_smul_measure h2 _

/-- Energy of a real field is unchanged by equality on the open cell. -/
theorem hot_primalEnergy_congr_open (U : TriadicCube 2) {f g : Vec 2 → ℝ}
    (h : ∀ x ∈ openCubeSet U, f x = g x) :
    primalEnergy U (Real.sqrt 3) f = primalEnergy U (Real.sqrt 3) g := by
  have hh := hot_ae_cube_of_open U h
  rw [← hilbertPrimalEnergy_real, ← hilbertPrimalEnergy_real]
  simp only [hilbertPrimalEnergy, hilbertCubeIncrement_congr_ae U _ hh]

open ASDExplicitGamma.Native in
/-- On one source cell `U`, the positive energy of the hot-patched source, summed over a
finite family of modes, is the Hilbert positive energy of the hot row
`rawRow(I,w) + (−φ_U)·column`. -/
theorem hot_source_tile_energy_eq (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (P : BlockVec 2) (s : Finset whiteBasisIndex)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    let w := hotPatchPotential Q depth nu sigma hnu hsigma k P
    let φU := oldSignedCellFirstCorrector Q U
      (openCubeSet_subset_of_mem_descendantsAtDepth hU) nu sigma hnu hsigma k
      (fun _ => P) (memLp_const P)
    let C1 := pureFluxMainQ3FiniteRawRow whiteBasis s b L Q depth w.toH1Function
    let C2 := hotRowCorrectorPart s b L U φU
    ∑ l ∈ s, vectorPositiveHaarEnergy U (fun x =>
      (hotPatchSource Q depth depth nu sigma hnu hsigma k b L l P x).2) =
      hilbertPrimalEnergy U (Real.sqrt 3) (fun x => C1 x + C2 x) := by
  intro w φU C1 C2
  classical
  let I := diagInterpolant Q depth
  let φ := hotGluedCorrector Q depth nu sigma hnu hsigma k P
  have htri := hot_row_tile_triangle Q depth w s U hU b L φU
  have hmem := htri.1
  have hsum := htri.2.1
  let C : Vec 2 → EuclideanSpace ℝ (s × Fin 2) := fun x => C1 x + C2 x
  have hrow (l : s) :
      vectorPositiveHaarEnergy U (fun x =>
        (hotPatchSource Q depth depth nu sigma hnu hsigma k b L l P x).2) =
      ∑ i : Fin 2, primalEnergy U (Real.sqrt 3) (fun x => (C x).ofLp (l, i)) := by
    let η := (mainQ3DirectionW2 Q b L (whiteBasis l)).value
    have hvalue (x : Vec 2) : η.toFun x =
        q3Convolution b L h3Zero (whiteBasis l) x := by
      rw [mainQ3DirectionW2_value]
    have hgrad (x : Vec 2) (i : Fin 2) : η.grad x i =
        (fderiv ℝ (q3Convolution b L h3Zero (whiteBasis l)) x) (basisVec i) := by
      have hj := mainQ3DirectionW2_jet Q b L (whiteBasis l) (.first i) x
      change (mainQ3DirectionW2 Q b L (whiteBasis l)).value.grad x i =
        q3Convolution b L (mainQ3JetIndex (.first i)) (whiteBasis l) x at hj
      have hderiv : (fderiv ℝ (q3Convolution b L h3Zero
          (whiteBasis l)) x) (basisVec i) =
          q3Convolution b L (mainQ3JetIndex (.first i))
            (whiteBasis l) x := by
        rw [q3Convolution_fderiv_basis b L h3Zero (by decide)]
        fin_cases i <;> norm_num [mainQ3JetIndex, h3Next, h3Zero,
          Model.Q3SpatialJet.count]
      exact hj.trans hderiv.symm
    let F : Vec 2 → Fin 2 → ℝ := fun x i =>
      η.toFun x * (I w.toH1Function).grad x i -
        η.grad x i * (w.toH1Function - I w.toH1Function).toFun x -
        η.grad x i * φU.toH1Function.toFun x
    have hcoord (x : Vec 2) (i : Fin 2) : (C x).ofLp (l, i) = F x i := by
      have h1 := pureFluxMainQ3FiniteRawRow_coordinate_hotcopy whiteBasis s b L Q depth
        w.toH1Function l i x
      simp only [C, C1, C2, hotRowCorrectorPart, PiLp.add_apply, PiLp.smul_apply,
        mainQ3FiniteColumn, smul_eq_mul, WithLp.ofLp_toLp] at h1 ⊢
      rw [h1]
      simp only [F]
      rw [hvalue, hgrad]
      ring
    have hsrc (x : Vec 2) (hx : x ∈ openCubeSet U) :
        (hotPatchSource Q depth depth nu sigma hnu hsigma k b L l P x).2 =
          planarQuarterTurn (fun i => -F x i) := by
      have hφ : φ.toH1Function x = φU.toH1Function x :=
        hot_glued_corrector_cell Q depth nu sigma hnu hsigma k P U hU x hx
      have e1 := congrFun (lemmaVH2_rowField_eq I η w.toH1Function) x
      have e2 := congrFun (lemmaVH2_rowField_eq
        (0 : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q)) η φ.toH1Function) x
      simp only [hotPatchSource, oldSignedLocalizedPotentialShear, Prod.snd_add]
      rw [e1, e2]
      funext i
      fin_cases i <;>
        simp [planarQuarterTurn, F, hφ] <;> ring
    calc vectorPositiveHaarEnergy U (fun x =>
          (hotPatchSource Q depth depth nu sigma hnu hsigma k b L l P x).2)
        = vectorPositiveHaarEnergy U (fun x => planarQuarterTurn (fun i => -F x i)) := by
          unfold vectorPositiveHaarEnergy
          apply Finset.sum_congr rfl
          intro i _
          apply hot_primalEnergy_congr_open
          intro x hx
          exact congrFun (hsrc x hx) i
      _ = vectorPositiveHaarEnergy U (fun x i => -F x i) :=
          main_vectorPositiveHaarEnergy_quarterTurn U (fun x i => -F x i)
      _ = ∑ i : Fin 2, primalEnergy U (Real.sqrt 3) (fun x => (C x).ofLp (l, i)) := by
          unfold vectorPositiveHaarEnergy
          apply Finset.sum_congr rfl
          intro i _
          have hf : (fun x => (C x).ofLp (l, i)) = fun x => F x i := by
            funext x
            exact hcoord x i
          rw [hf]
          exact primalEnergy_neg U (Real.sqrt 3) (fun x => F x i)
  calc ∑ l ∈ s, vectorPositiveHaarEnergy U (fun x =>
        (hotPatchSource Q depth depth nu sigma hnu hsigma k b L l P x).2)
      = ∑ l : s, vectorPositiveHaarEnergy U (fun x =>
        (hotPatchSource Q depth depth nu sigma hnu hsigma k b L l P x).2) :=
        (Finset.sum_coe_sort s _).symm
    _ = ∑ l : s, ∑ i : Fin 2, primalEnergy U (Real.sqrt 3) (fun x => (C x).ofLp (l, i)) := by
        apply Finset.sum_congr rfl
        intro l _
        exact hrow l
    _ = hilbertPrimalEnergy U (Real.sqrt 3) C := by
        symm
        rw [main_hilbertPrimalEnergy_euclidean U hmem hsum, Fintype.sum_prod_type]

end ASDExplicitGamma.Inverse
