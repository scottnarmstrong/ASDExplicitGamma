module

public import ASDExplicitGamma.Scalar.DefectCoeff
public import ASDExplicitGamma.Scalar.DefectKappa
public import ASDExplicitGamma.Scalar.DefectTruncation

/-! The symmetrized defect rows built from closed-graph potentials: Wick data and joint
measurability of the tiled positive-Haar energy of the truncated source. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  ASDExplicitGamma.Gaussian ASDExplicitGamma.Native Filter Topology
open scoped BigOperators

noncomputable section

local instance hMeasurable (nQ : ℤ) :
    MeasurableSpace (H10GraphClosedSpace (openCubeSet (originCube 2 nQ))) := borel _

local instance hBorel' (nQ : ℤ) :
    BorelSpace (H10GraphClosedSpace (openCubeSet (originCube 2 nQ))) := ⟨rfl⟩

theorem tpe_half_add_le (Q : TriadicCube 2) (m : ℕ) (a b : TiledHaarField Q m) :
    tiledPositiveEnergy Q m ((1 / 2 : ℝ) • (a + b)) ≤
      (tiledPositiveEnergy Q m a + tiledPositiveEnergy Q m b) / 2 := by
  have h1 := tiledPartialForm_tendsto Q m ((1 / 2 : ℝ) • (a + b))
  have h2 := ((tiledPartialForm_tendsto Q m a).add (tiledPartialForm_tendsto Q m b)).div_const 2
  refine le_of_tendsto_of_tendsto h1 h2 (Eventually.of_forall fun N => ?_)
  have h := (tiledPartialForm Q m N).two_mul_le a b
  simp only [map_smul, map_add, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
  rw [(tiledPartialForm Q m N).symm b a]
  nlinarith [h]

/-- The symmetrized source rows `(R_ij + R_ji)/2`, `R_ij = row(e_i)(d_j)`. -/
def symRows (nQ : ℤ) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l}) {n : ℕ}
    (e : Fin n → Option whiteBasisIndex)
    (d : Fin n → H10Function (openCubeSet (originCube 2 nQ))) :
    Fin n → Fin n → TiledHaarField (originCube 2 nQ) m := fun i j =>
  (1 / 2 : ℝ) • (rowEltOpt (originCube 2 nQ) m b L (e i) (d j) +
    rowEltOpt (originCube 2 nQ) m b L (e j) (d i))

theorem symRows_symm (nQ : ℤ) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l}) {n : ℕ}
    (e : Fin n → Option whiteBasisIndex)
    (d : Fin n → H10Function (openCubeSet (originCube 2 nQ))) (i j : Fin n) :
    symRows nQ m b L e d i j = symRows nQ m b L e d j i := by
  unfold symRows
  rw [add_comm]

theorem symRows_diag (nQ : ℤ) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l}) {n : ℕ}
    (e : Fin n → Option whiteBasisIndex)
    (d : Fin n → H10Function (openCubeSet (originCube 2 nQ))) (i : Fin n) :
    symRows nQ m b L e d i i = rowEltOpt (originCube 2 nQ) m b L (e i) (d i) := by
  unfold symRows
  rw [← two_smul ℝ, smul_smul]
  norm_num

/-- Symmetrization does not change the truncated source. -/
theorem psdDefectSource_symRows (nQ : ℤ) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l}) {n : ℕ}
    (e : Fin n → Option whiteBasisIndex)
    (d : Fin n → H10Function (openCubeSet (originCube 2 nQ))) (x : Fin n → ℝ) :
    psdDefectSource (symRows nQ m b L e d) x =
      psdDefectSource (fun i j => rowEltOpt (originCube 2 nQ) m b L (e i) (d j)) x := by
  unfold psdDefectSource symRows
  simp only [smul_add, Finset.sum_add_distrib, smul_smul]
  have h : ∑ i : Fin n, ∑ j : Fin n, (x i * x j * (1 / 2 : ℝ)) •
      rowEltOpt (originCube 2 nQ) m b L (e j) (d i) =
      ∑ i : Fin n, ∑ j : Fin n, (x i * x j * (1 / 2 : ℝ)) •
        rowEltOpt (originCube 2 nQ) m b L (e i) (d j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (x j) (x i)]
  rw [h, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← add_smul]
  congr 1
  ring

theorem symRows_wick (nQ : ℤ) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l}) {n : ℕ}
    (e : Fin n → Option whiteBasisIndex)
    (he : ∀ i j l, e i = some l → e j = some l → i = j)
    (d : Fin n → H10Function (openCubeSet (originCube 2 nQ))) :
    tiledPositiveEnergy (originCube 2 nQ) m (∑ i, symRows nQ m b L e d i i) +
        2 * ∑ i, ∑ j, tiledPositiveEnergy (originCube 2 nQ) m (symRows nQ m b L e d i j) ≤
      3 * colKappa (originCube 2 nQ) m b L ^ 2 *
        ∑ j, lemmaVTiledWeakEnergy (originCube 2 nQ) m (d j).toH1Function.grad := by
  have h := defect_rowcol_sum_le_opt nQ m b L e he d
  dsimp only at h
  have hdiag : ∑ i, symRows nQ m b L e d i i =
      ∑ i, rowEltOpt (originCube 2 nQ) m b L (e i) (d i) :=
    Finset.sum_congr rfl fun i _ => symRows_diag nQ m b L e d i
  rw [hdiag]
  have hoff : ∑ i, ∑ j, tiledPositiveEnergy (originCube 2 nQ) m (symRows nQ m b L e d i j) ≤
      ∑ i, ∑ j, tiledPositiveEnergy (originCube 2 nQ) m
        (rowEltOpt (originCube 2 nQ) m b L (e i) (d j)) := by
    calc _ ≤ ∑ i, ∑ j, ((tiledPositiveEnergy (originCube 2 nQ) m
            (rowEltOpt (originCube 2 nQ) m b L (e i) (d j)) +
          tiledPositiveEnergy (originCube 2 nQ) m
            (rowEltOpt (originCube 2 nQ) m b L (e j) (d i))) / 2) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            tpe_half_add_le _ m _ _
      _ = _ := by
          simp only [add_div, Finset.sum_add_distrib]
          rw [Finset.sum_comm (f := fun i j => tiledPositiveEnergy (originCube 2 nQ) m
            (rowEltOpt (originCube 2 nQ) m b L (e j) (d i)) / 2)]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
  linarith

theorem secondCountable (nQ : ℤ) :
    SecondCountableTopology (H10GraphClosedSpace (openCubeSet (originCube 2 nQ))) := by
  letI : IsSeparable (volumeMeasureOn (openCubeSet (originCube 2 nQ))) := inferInstance
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  have h1 : SecondCountableTopology (ScalarL2 (openCubeSet (originCube 2 nQ))) := inferInstance
  have h2 : SecondCountableTopology (HilbertVectorL2 (openCubeSet (originCube 2 nQ))) :=
    inferInstance
  have h3 : SecondCountableTopology (ScalarL2 (openCubeSet (originCube 2 nQ)) ×
      HilbertVectorL2 (openCubeSet (originCube 2 nQ))) := inferInstance
  exact TopologicalSpace.Subtype.secondCountableTopology _

theorem form_opt_measurable {𝒪 : Type*} [MeasurableSpace 𝒪] (nQ : ℤ) (m : ℕ) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (β : PsdForm (TiledHaarField (originCube 2 nQ) m))
    (hβ : ∀ x, β.form x x ≤ tiledPositiveEnergy (originCube 2 nQ) m x)
    (ea ec : Option whiteBasisIndex)
    (zj zl : 𝒪 → H10GraphClosedSpace (openCubeSet (originCube 2 nQ)))
    (hj : Measurable zj) (hl : Measurable zl) :
    Measurable fun o => β.form (rowEltOpt (originCube 2 nQ) m b L ea (rep'' nQ (zj o)))
      (rowEltOpt (originCube 2 nQ) m b L ec (rep'' nQ (zl o))) := by
  haveI := secondCountable nQ
  cases ea with
  | none => simp [rowEltOpt]
  | some a =>
    cases ec with
    | none => simp [rowEltOpt]
    | some c =>
      have h := (coef_continuous nQ m b L β hβ a c).measurable.comp (hj.prodMk hl)
      exact h

theorem symDefect_measurable {𝒪 : Type*} [MeasurableSpace 𝒪] (nQ : ℤ) (m : ℕ) (b : ℝ)
    (L : {l : ℝ // 0 < l}) {n : ℕ} (e : Fin n → Option whiteBasisIndex)
    (zs : Fin n → 𝒪 → H10GraphClosedSpace (openCubeSet (originCube 2 nQ)))
    (hz : ∀ j, Measurable (zs j)) :
    Measurable (fun p : 𝒪 × (ℕ → ℝ) =>
      tiledPositiveEnergy (originCube 2 nQ) m (psdDefectSource
        (symRows nQ m b L e (fun j => rep'' nQ (zs j p.1))) (fun i : Fin n => p.2 i))) := by
  refine measurable_of_tendsto_metrizable (f := fun N (p : 𝒪 × (ℕ → ℝ)) =>
    (tiledPartialForm (originCube 2 nQ) m N).form
      (psdDefectSource (symRows nQ m b L e (fun j => rep'' nQ (zs j p.1)))
        (fun i : Fin n => p.2 i))
      (psdDefectSource (symRows nQ m b L e (fun j => rep'' nQ (zs j p.1)))
        (fun i : Fin n => p.2 i))) (fun N => ?_) ?_
  · have hβ := tiledPartialForm_le (originCube 2 nQ) m N
    simp only [psdDefectSource_form_expansion]
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ => ?_
    have hy : ∀ i : Fin n, Measurable fun p : 𝒪 × (ℕ → ℝ) => p.2 (i : ℕ) :=
      fun i => (measurable_pi_apply (i : ℕ)).comp measurable_snd
    refine Measurable.mul (?_ : Measurable fun p : 𝒪 × (ℕ → ℝ) => _) ((((hy i).mul (hy j)).mul ((hy k).mul (hy l))))
    have key : ∀ (ea ec : Option whiteBasisIndex) (a c : Fin n),
        Measurable fun p : 𝒪 × (ℕ → ℝ) =>
          (tiledPartialForm (originCube 2 nQ) m N).form
            (rowEltOpt (originCube 2 nQ) m b L ea (rep'' nQ (zs a p.1)))
            (rowEltOpt (originCube 2 nQ) m b L ec (rep'' nQ (zs c p.1))) := by
      intro ea ec a c
      exact (form_opt_measurable nQ m b L _ hβ ea ec (fun o => zs a o) (fun o => zs c o)
        (hz a) (hz c)).comp measurable_fst
    simp only [symRows, map_smul, map_add, LinearMap.smul_apply, LinearMap.add_apply,
      smul_eq_mul]
    exact ((((key (e i) (e k) j l).add (key (e j) (e k) i l)).const_mul (1 / 2 : ℝ)).add
      (((key (e i) (e l) j k).add (key (e j) (e l) i k)).const_mul (1 / 2 : ℝ))).const_mul
      (1 / 2 : ℝ)
  · rw [tendsto_pi_nhds]
    intro p
    exact tiledPartialForm_tendsto (originCube 2 nQ) m _

end

end ASDExplicitGamma.Scalar
