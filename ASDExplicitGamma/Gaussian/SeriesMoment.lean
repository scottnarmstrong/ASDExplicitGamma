module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import ASDExplicitGamma.Gaussian.FiniteProduct
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Order.Basic

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix
open Filter
open scoped RealInnerProductSpace Topology
open scoped ENNReal NNReal

namespace ASDExplicitGamma.Gaussian

/-! Finite Gaussian moment comparison in Hilbert spaces. The proof diagonalizes the Gram operator,
uses orthogonal invariance of the finite product Gaussian law, and applies the `L^q` triangle
inequality to the nonnegative weighted coordinate squares. -/

/-- The product law of a countable sequence of independent standard real Gaussians. -/
noncomputable def standardGaussianInfinitePi : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

/-- The `n`th partial sum of a Hilbert-valued Gaussian series. -/
def gaussianPartialSum {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (v : ℕ → V) (n : ℕ) (ω : ℕ → ℝ) : V :=
  ∑ j ∈ Finset.range n, ω j • v j

private lemma eLpNorm'_infinitePi_restrict {ι : Type*} [Countable ι]
    {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [ContinuousENorm V]
    [OpensMeasurableSpace V] {I : Finset ι} (F : (I → ℝ) → V)
    (hF : Measurable F) (p : ℝ) :
    eLpNorm' (fun ω : (i : ι) → ℝ => F (I.restrict ω)) p
        (Measure.infinitePi (fun _ : ι => gaussianReal 0 1)) =
      eLpNorm' F p (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
  rw [eLpNorm'_eq_lintegral_enorm, eLpNorm'_eq_lintegral_enorm]
  have hmap : (Measure.infinitePi (fun _ : ι => gaussianReal 0 1)).map I.restrict =
      Measure.pi (fun _ : I => gaussianReal 0 1) := by
    exact Measure.infinitePi_map_restrict (μ := fun _ : ι => gaussianReal 0 1)
  congr 1
  calc
    _ = ∫⁻ z, ‖F z‖ₑ ^ p ∂(Measure.infinitePi (fun _ : ι => gaussianReal 0 1)).map I.restrict := by
      have hmeas : Measurable (fun z : I → ℝ => ‖F z‖ₑ ^ p) := by fun_prop
      exact (lintegral_map hmeas (Finset.measurable_restrict I)).symm
    _ = _ := by rw [hmap]

private lemma finiteTail_sum_le_tsum_shift {a : ℕ → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hA : Summable a) (n m : ℕ) (_hnm : n ≤ m) :
    (∑ j ∈ Finset.range m \ Finset.range n, a j) ≤ ∑' k, a (n + k) := by
  let I : Finset ℕ := Finset.range m \ Finset.range n
  let f : I → ℝ := fun i => a i.val
  let g : ℕ → ℝ := fun k => a (n + k)
  have htail : Summable g := by
    exact hA.comp_injective (by intro x y h; omega)
  have hi (i : I) : n ≤ i.val := by
    have hnot : ¬ i.val < n := by
      intro hlt
      have : i.val ∈ Finset.range n := Finset.mem_range.mpr hlt
      exact (Finset.mem_sdiff.mp (show i.val ∈ I from i.property)).2 this
    omega
  have hinj : Function.Injective (fun i : I => i.val - n) := by
    intro i j hij
    apply Subtype.ext
    exact (tsub_left_inj (hi i) (hi j)).mp hij
  have hnonneg (k : ℕ) (hk : k ∉ Set.range (fun i : I => i.val - n)) : 0 ≤ g k := ha _
  have hle (i : I) : f i ≤ g (i.val - n) := by
    dsimp [f, g]
    rw [show n + (i.val - n) = i.val from Nat.add_sub_of_le (hi i)]
  have hsum := (Summable.of_finite (f := f)).tsum_le_tsum_of_inj
    (fun i : I => i.val - n) hinj hnonneg hle htail
  simpa [I, f, g, tsum_fintype, Finset.sum_attach] using hsum

private lemma summable_shift_tsum_tendsto_zero {a : ℕ → ℝ} (hA : Summable a) :
    Tendsto (fun n => ∑' k, a (n + k)) atTop (𝓝 0) := by
  have hEq (n : ℕ) : (∑' k, a (n + k)) = (∑' k, a k) - ∑ k ∈ Finset.range n, a k := by
    have hs := hA.sum_add_tsum_nat_add n
    have hs' : ∑ i ∈ Finset.range n, a i + ∑' k, a (n + k) = ∑' k, a k := by
      simpa [Nat.add_comm] using hs
    linarith
  have hfun : (fun n => ∑' k, a (n + k)) =
      fun n => (∑' k, a k) - ∑ k ∈ Finset.range n, a k := by
    funext n
    exact hEq n
  have hlim : Tendsto (fun n => (∑' k, a k) - ∑ k ∈ Finset.range n, a k) atTop (𝓝 0) := by
    convert tendsto_const_nhds.sub hA.tendsto_sum_tsum_nat using 1
    simp
  simpa [hfun] using hlim

private lemma scalarGaussianLpMoment_lt_top (p : ℝ) (hp : 2 ≤ p) :
    eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1) < ∞ := by
  have hmem : MemLp (id : ℝ → ℝ) (ENNReal.ofReal p) (gaussianReal 0 1) :=
    memLp_id_gaussianReal' (ENNReal.ofReal p) ENNReal.ofReal_ne_top
  have hp0 : ENNReal.ofReal p ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hptop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have heq := eLpNorm_eq_eLpNorm' hp0 hptop hmem.aestronglyMeasurable
  rw [ENNReal.toReal_ofReal (by linarith)] at heq
  rw [← heq]
  exact hmem.eLpNorm_lt_top

private lemma gaussianTailMomentMajorant_tendsto {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (v : ℕ → V) {p : ℝ} (hp : 2 ≤ p)
    (hA : Summable (fun j => ‖v j‖ ^ 2)) :
    Tendsto (fun n => eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1) *
      ENNReal.ofReal (Real.sqrt (∑' k, ‖v (n + k)‖ ^ 2))) atTop (𝓝 0) := by
  let a : ℕ → ℝ := fun j => ‖v j‖ ^ 2
  let c : ℝ≥0∞ := eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1)
  have htail := summable_shift_tsum_tendsto_zero (a := a) hA
  have hsqrt : Tendsto (fun n => Real.sqrt (∑' k, a (n + k))) atTop (𝓝 0) := by
    simpa [a, Function.comp_def] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp htail
  have hofreal : Tendsto (fun n => ENNReal.ofReal (Real.sqrt (∑' k, a (n + k))))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hsqrt
  have hc : c ≠ ∞ := by
    dsimp [c]
    exact (scalarGaussianLpMoment_lt_top p hp).ne
  have hmajor : Tendsto (fun n => c * ENNReal.ofReal (Real.sqrt (∑' k, a (n + k))))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (ENNReal.continuous_const_mul hc).tendsto (0 : ℝ≥0∞) |>.comp hofreal
  simpa [a, c] using hmajor

private noncomputable def gramOp {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → V) :
    EuclideanSpace ℝ (ι) →ₗ[ℝ] EuclideanSpace ℝ (ι) :=
  (Matrix.gram ℝ v).toEuclideanLin

private lemma gramOp_isPositive {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → V) :
    (gramOp v).IsPositive := by
  rw [gramOp, Matrix.isPositive_toEuclideanLin_iff]
  exact Matrix.posSemidef_gram ℝ v

private lemma image_inner_gram {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → V)
    (x y : EuclideanSpace ℝ (ι)) :
    inner ℝ (∑ i, x i • v i) (∑ i, y i • v i) =
      inner ℝ x (gramOp v y) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  rw [gramOp, Matrix.toEuclideanLin]
  simp only [Matrix.toLin'_apply, Matrix.ofLp_toLpLin]
  simpa [dotProduct_comm] using
    (Matrix.star_dotProduct_gram_mulVec v x.ofLp y.ofLp).symm

private lemma coord_sum_repr {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis (ι) ℝ
    (EuclideanSpace ℝ (ι))) (z : ι → ℝ) :
    b.repr (∑ i, z i • b i) = WithLp.toLp 2 z := by
  ext i
  simp [Pi.single_apply]

private lemma basisFun_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    EuclideanSpace.basisFun (ι) ℝ i = WithLp.toLp 2 (Pi.single i (1 : ℝ)) := by
  ext j
  rw [EuclideanSpace.basisFun_apply]
  simp [EuclideanSpace.single, PiLp.single_apply, Pi.single_apply]

private lemma image_norm_sq_diag {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → V)
    (b : OrthonormalBasis (ι) ℝ (EuclideanSpace ℝ (ι)))
    (evals : ι → ℝ) (heig : ∀ i, gramOp v (b i) = evals i • b i)
    (z : ι → ℝ) :
    ‖∑ k, (∑ i, z i • b i) k • v k‖ ^ 2 = ∑ i, evals i * z i ^ 2 := by
  let T := gramOp v
  let y : EuclideanSpace ℝ (ι) := ∑ i, z i • b i
  have hy : b.repr y = WithLp.toLp 2 z := by
    dsimp [y]
    exact coord_sum_repr b z
  have hTy : T y = ∑ i, (evals i * z i) • b i := by
    dsimp [y, T]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_smul, heig]
    simp [smul_smul, mul_comm]
  have hspec : b.repr (T y) = WithLp.toLp 2 (fun i ↦ evals i * z i) := by
    rw [hTy]
    exact coord_sum_repr b _
  rw [← real_inner_self_eq_norm_sq]
  rw [image_inner_gram v y y]
  rw [← b.repr.inner_map_map y (T y)]
  rw [hy, hspec, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, pow_two, mul_comm, mul_left_comm]

private lemma eigenvalue_sum_eq_trace_gram {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → V)
    (hn : Module.finrank ℝ (EuclideanSpace ℝ ι) = Fintype.card ι) :
    ∑ i : ι, (gramOp_isPositive v).isSymmetric.eigenvalues hn (Fintype.equivFin ι i) =
      ∑ i, ‖v i‖ ^ 2 := by
  let T := gramOp v
  let hT := gramOp_isPositive v
  let hS := hT.isSymmetric
  calc
    ∑ i : ι, hS.eigenvalues hn (Fintype.equivFin ι i) =
        ∑ i : Fin (Fintype.card ι), hS.eigenvalues hn i := Equiv.sum_comp (Fintype.equivFin ι) _
    _ = T.trace ℝ (EuclideanSpace ℝ (ι)) := (hS.trace_eq_sum_eigenvalues hn).symm
    _ = ∑ i, ‖v i‖ ^ 2 := by
      rw [LinearMap.trace_eq_sum_inner T (EuclideanSpace.basisFun (ι) ℝ)]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← image_inner_gram v ((EuclideanSpace.basisFun (ι) ℝ) i)
        ((EuclideanSpace.basisFun (ι) ℝ) i)]
      rw [basisFun_coordinates]
      simp [Pi.single_apply]

private lemma eLpNorm'_eval_gaussianPi {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (p : ℝ) :
    eLpNorm' (fun x : ι → ℝ => x i) p
        (Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1) := by
  rw [eLpNorm'_eq_lintegral_enorm, eLpNorm'_eq_lintegral_enorm]
  congr 1
  exact (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).lintegral_comp
    (f := fun x : ℝ => ‖x‖ₑ ^ p) (by fun_prop)

private noncomputable def basisSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis (ι) ℝ (EuclideanSpace ℝ (ι)))
    (x : ι → ℝ) : EuclideanSpace ℝ (ι) := ∑ i, x i • b i

private noncomputable def gaussianSumMap {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → V)
    (x : EuclideanSpace ℝ (ι)) : V := ∑ i, x i • v i

private lemma eLpNorm'_squared_gaussianSum_basisChange {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → V)
    (b : OrthonormalBasis (ι) ℝ (EuclideanSpace ℝ (ι)))
    (evals : ι → ℝ) (heig : ∀ i, gramOp v (b i) = evals i • b i)
    (q : ℝ) :
    eLpNorm' (fun x : ι → ℝ => ‖gaussianSumMap v (WithLp.toLp 2 x)‖ ^ 2)
      q (Measure.pi (fun _ : ι => gaussianReal 0 1)) =
    eLpNorm' (fun x : ι → ℝ => ∑ i, evals i * (x i) ^ 2) q
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  let F : EuclideanSpace ℝ (ι) → ℝ := fun y => ‖gaussianSumMap v y‖ ^ 2
  have hFmeas : Measurable (fun y : EuclideanSpace ℝ (ι) => ‖F y‖ₑ ^ q) := by
    fun_prop [gaussianSumMap]
  have hPiMap : Measure.map (WithLp.toLp 2)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      stdGaussian (EuclideanSpace ℝ (ι)) := by
    simpa [ASDExplicitGamma.Gaussian.standardGaussianPi] using
      (ProbabilityTheory.map_pi_eq_stdGaussian (ι := ι))
  have hBasisMap : Measure.map (basisSum b)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      stdGaussian (EuclideanSpace ℝ (ι)) := by
    change Measure.map (fun x : ι → ℝ => ∑ i, x i • b i)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) = _
    simpa [ASDExplicitGamma.Gaussian.standardGaussianPi] using
      (stdGaussian_eq_map_pi_orthonormalBasis b).symm
  have hBasisMeas : Measurable (basisSum b) := by
    fun_prop [basisSum]
  have hLeft :
      (∫⁻ x : ι → ℝ, ‖F (WithLp.toLp 2 x)‖ₑ ^ q
        ∂(Measure.pi (fun _ : ι => gaussianReal 0 1))) =
      ∫⁻ y : EuclideanSpace ℝ (ι), ‖F y‖ₑ ^ q
        ∂stdGaussian (EuclideanSpace ℝ (ι)) := by
    rw [← hPiMap]
    exact (lintegral_map hFmeas (by fun_prop)).symm
  have hRight :
      (∫⁻ y : EuclideanSpace ℝ (ι), ‖F y‖ₑ ^ q
        ∂stdGaussian (EuclideanSpace ℝ (ι))) =
      ∫⁻ x : ι → ℝ, ‖F (basisSum b x)‖ₑ ^ q
        ∂(Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
    rw [← hBasisMap]
    exact lintegral_map hFmeas hBasisMeas
  have hPoint (x : ι → ℝ) :
      F (basisSum b x) = ∑ i, evals i * (x i) ^ 2 := by
    exact image_norm_sq_diag v b evals heig x
  rw [eLpNorm'_eq_lintegral_enorm, eLpNorm'_eq_lintegral_enorm]
  congr 1
  calc
    _ = ∫⁻ y : EuclideanSpace ℝ (ι), ‖F y‖ₑ ^ q
        ∂stdGaussian (EuclideanSpace ℝ (ι)) := hLeft
    _ = ∫⁻ x : ι → ℝ, ‖F (basisSum b x)‖ₑ ^ q
        ∂(Measure.pi (fun _ : ι => gaussianReal 0 1)) := hRight
    _ = _ := by congr 1; funext x; rw [hPoint]

/-- Dimension-independent Hilbert-valued Gaussian moment comparison. For every finite family in a
real inner product space and every `p ≥ 2`, the squared `Lᵖ` seminorm of its standard Gaussian sum
is bounded by the scalar standard Gaussian `Lᵖ` seminorm squared times the sum of squared vector
norms. -/
theorem eLpNorm'_finiteGaussianSum_sq_le {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → V) {p : ℝ} (hp : 2 ≤ p) :
    eLpNorm' (fun x : ι → ℝ => ∑ i, x i • v i) p
        (Measure.pi (fun _ : ι => gaussianReal 0 1)) ^ 2 ≤
      eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1) ^ 2 *
        ENNReal.ofReal (∑ i, ‖v i‖ ^ 2) := by
  let T := gramOp v
  let hT := gramOp_isPositive v
  let hS := hT.isSymmetric
  have hn : Module.finrank ℝ (EuclideanSpace ℝ ι) = Fintype.card ι := by simp
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let b0 : OrthonormalBasis (Fin (Fintype.card ι)) ℝ (EuclideanSpace ℝ ι) :=
    hS.eigenvectorBasis hn
  let b : OrthonormalBasis ι ℝ (EuclideanSpace ℝ ι) := b0.reindex e.symm
  let evals : ι → ℝ := fun i => hS.eigenvalues hn (e i)
  let q : ℝ := p / 2
  let μ := (Measure.pi (fun _ : ι => gaussianReal 0 1))
  let c : ℝ≥0∞ := eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1)
  have hq1 : 1 ≤ q := by dsimp [q]; linarith
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq1
  have hqmul : q * 2 = p := by dsimp [q]; ring
  have heig (i : ι) : T (b i) = evals i • b i := by
    dsimp [T, b, evals]
    rw [OrthonormalBasis.reindex_apply]
    exact hS.apply_eigenvectorBasis hn (e i)
  have heval (i : ι) : 0 ≤ evals i := by
    dsimp [evals]
    exact hT.nonneg_eigenvalues hn (e i)
  have htrace : ∑ i, evals i = ∑ i, ‖v i‖ ^ 2 := by
    exact eigenvalue_sum_eq_trace_gram v hn
  have hchange :
      eLpNorm' (fun x : ι → ℝ => ‖∑ i, x i • v i‖ ^ 2) q μ =
        eLpNorm' (fun x : ι → ℝ => ∑ i, evals i * (x i) ^ 2) q μ := by
    simpa [μ, q, b, evals, gaussianSumMap, T] using
      eLpNorm'_squared_gaussianSum_basisChange v b evals heig q
  have houter := eLpNorm'_norm_rpow
    (fun x : ι → ℝ => ∑ i, x i • v i) q 2 (μ := μ) (by norm_num)
  have houter' :
      eLpNorm' (fun x : ι → ℝ => ‖∑ i, x i • v i‖ ^ 2) q μ =
        eLpNorm' (fun x : ι → ℝ => ∑ i, x i • v i) (q * 2) μ ^ 2 := by
    convert houter using 1 <;> simp
  have hnormeq :
      eLpNorm' (fun x : ι → ℝ => ∑ i, x i • v i) p μ ^ 2 =
        eLpNorm' (fun x : ι → ℝ => ∑ i, evals i * (x i) ^ 2) q μ := by
    calc
      _ = eLpNorm' (fun x : ι → ℝ => ∑ i, x i • v i) (q * 2) μ ^ 2 := by
        rw [hqmul]
      _ = eLpNorm' (fun x : ι → ℝ => ‖∑ i, x i • v i‖ ^ 2) q μ := houter'.symm
      _ = _ := hchange
  have hsquare (i : ι) :
      eLpNorm' (fun x : ι → ℝ => (x i) ^ 2) q μ = c ^ 2 := by
    calc
      _ = eLpNorm' (fun x : ι → ℝ => ‖x i‖ ^ 2) q μ := by
        congr 1
        funext x
        simp [Real.norm_eq_abs, sq_abs]
      _ = eLpNorm' (fun x : ι → ℝ => x i) (q * 2) μ ^ 2 := by
        convert (eLpNorm'_norm_rpow (fun x : ι → ℝ => x i) q 2
          (μ := μ) (by norm_num)) using 1 <;> simp
      _ = c ^ 2 := by
        rw [hqmul, eLpNorm'_eval_gaussianPi]
  have hterm (i : ι) :
      eLpNorm' (fun x : ι → ℝ => evals i * (x i) ^ 2) q μ ≤
        ENNReal.ofReal (evals i) * c ^ 2 := by
    change eLpNorm' (evals i • fun x : ι → ℝ => (x i) ^ 2) q μ ≤ _
    rw [eLpNorm'_const_smul (evals i) hqpos, Real.enorm_of_nonneg (heval i), hsquare i]
  have hweighted :
      eLpNorm' (fun x : ι → ℝ => ∑ i, evals i * (x i) ^ 2) q μ ≤
        c ^ 2 * ENNReal.ofReal (∑ i, evals i) := by
    calc
      _ = eLpNorm' (∑ i ∈ Finset.univ,
          (fun x : ι → ℝ => evals i * (x i) ^ 2)) q μ := by
        congr 1
        funext x
        simp
      _ ≤ ∑ i ∈ Finset.univ,
          eLpNorm' (fun x : ι → ℝ => evals i * (x i) ^ 2) q μ := by
        apply eLpNorm'_sum_le
        · intro i hi
          have hm : Measurable (fun x : ι → ℝ => evals i * (x i) ^ 2) := by
            fun_prop
          exact hm.aestronglyMeasurable
        · exact hq1
      _ ≤ ∑ i ∈ Finset.univ, ENNReal.ofReal (evals i) * c ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact hterm i
      _ = c ^ 2 * ENNReal.ofReal (∑ i, evals i) := by
        rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg (fun i hi => heval i), mul_comm]
  rw [hnormeq]
  calc
    eLpNorm' (fun x : ι → ℝ => ∑ i, evals i * (x i) ^ 2) q μ ≤
        c ^ 2 * ENNReal.ofReal (∑ i, evals i) := hweighted
    _ = c ^ 2 * ENNReal.ofReal (∑ i, ‖v i‖ ^ 2) := by rw [htrace]

/-- The unsquared form of `eLpNorm'_finiteGaussianSum_sq_le`. -/
theorem eLpNorm'_finiteGaussianSum_le {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → V) {p : ℝ}
    (hp : 2 ≤ p) :
    eLpNorm' (fun x : ι → ℝ => ∑ i, x i • v i) p
        (Measure.pi (fun _ : ι => gaussianReal 0 1)) ≤
      eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1) *
        ENNReal.ofReal (Real.sqrt (∑ i, ‖v i‖ ^ 2)) := by
  let c : ℝ≥0∞ := eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1)
  let energy : ℝ := ∑ i, ‖v i‖ ^ 2
  have henergy : 0 ≤ energy := by
    dsimp [energy]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hc : (c ^ 2) ^ (1 / 2 : ℝ) = c := by
    rw [← ENNReal.rpow_natCast c 2, ← ENNReal.rpow_mul]
    norm_num
  have hsq := eLpNorm'_finiteGaussianSum_sq_le v hp
  calc
    _ = (eLpNorm' (fun x : ι → ℝ => ∑ i, x i • v i) p
          (Measure.pi (fun _ : ι => gaussianReal 0 1)) ^ 2) ^ (1 / 2 : ℝ) := by
      rw [← ENNReal.rpow_natCast _ 2]
      rw [← ENNReal.rpow_mul]
      norm_num
    _ ≤ (c ^ 2 * ENNReal.ofReal energy) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow hsq (by norm_num)
    _ = c * ENNReal.ofReal (Real.sqrt energy) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hc,
        ENNReal.ofReal_rpow_of_nonneg henergy (by norm_num), ← Real.sqrt_eq_rpow]
    _ = _ := by dsimp [c, energy]

/-- A finite tail of a Hilbert-valued Gaussian series obeys the same moment bound as a finite
Gaussian sum. -/
theorem eLpNorm'_gaussianPartialSum_sub_le {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    [OpensMeasurableSpace V]
    {v : ℕ → V} {n m : ℕ} (hnm : n ≤ m) {p : ℝ} (hp : 2 ≤ p) :
    eLpNorm' (fun ω => gaussianPartialSum v m ω - gaussianPartialSum v n ω) p
        (standardGaussianInfinitePi) ≤
      eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1) *
        ENNReal.ofReal (Real.sqrt (∑ j ∈ Finset.range m \ Finset.range n, ‖v j‖ ^ 2)) := by
  let I : Finset ℕ := Finset.range m \ Finset.range n
  let F : (I → ℝ) → V := fun z => ∑ i, z i • v i.val
  have hsub : Finset.range n ⊆ Finset.range m := Finset.range_mono hnm
  have hsum_subtype (ω : ℕ → ℝ) :
      ∑ j ∈ I, ω j • v j = ∑ i : I, ω i.val • v i.val := by
    exact Finset.sum_subtype I (fun _ => Iff.rfl) (fun j => ω j • v j)
  have hdiff (ω : ℕ → ℝ) :
      gaussianPartialSum v m ω - gaussianPartialSum v n ω = F (I.restrict ω) := by
    dsimp [F, I, gaussianPartialSum]
    rw [← Finset.sum_sdiff_eq_sub hsub]
    exact hsum_subtype ω
  have hFcont : Continuous F := by
    dsimp [F]
    fun_prop
  have hF : Measurable F := hFcont.measurable
  have henergy :
      ∑ i : I, ‖v i.val‖ ^ 2 = ∑ j ∈ I, ‖v j‖ ^ 2 := by
    exact (Finset.sum_subtype I (fun _ => Iff.rfl) (fun j => ‖v j‖ ^ 2)).symm
  calc
    _ = eLpNorm' (fun ω => F (I.restrict ω)) p standardGaussianInfinitePi :=
      eLpNorm'_congr_ae (ae_of_all _ hdiff)
    _ = eLpNorm' F p (Measure.pi (fun _ : I => gaussianReal 0 1)) := by
      simpa [standardGaussianInfinitePi] using eLpNorm'_infinitePi_restrict F hF p
    _ ≤ eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1) *
          ENNReal.ofReal (Real.sqrt (∑ i : I, ‖v i.val‖ ^ 2)) := by
      simpa [F] using eLpNorm'_finiteGaussianSum_le (fun i : I => v i.val) hp
    _ = _ := by rw [henergy]

private lemma eLpNorm'_gaussianPartialSum_sub_shift_le {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    [OpensMeasurableSpace V] (v : ℕ → V) {p : ℝ} (hp : 2 ≤ p)
    (hA : Summable (fun j => ‖v j‖ ^ 2)) {n m : ℕ} (hnm : n ≤ m) :
    eLpNorm' (fun ω => gaussianPartialSum v m ω - gaussianPartialSum v n ω) p
        standardGaussianInfinitePi ≤
      eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1) *
        ENNReal.ofReal (Real.sqrt (∑' k, ‖v (n + k)‖ ^ 2)) := by
  calc
    _ ≤ eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1) *
        ENNReal.ofReal (Real.sqrt (∑ j ∈ Finset.range m \ Finset.range n, ‖v j‖ ^ 2)) :=
      eLpNorm'_gaussianPartialSum_sub_le hnm hp
    _ ≤ _ := by
      gcongr
      exact finiteTail_sum_le_tsum_shift (fun j => sq_nonneg _) hA n m hnm

/-- The partial sums of a square-summable Hilbert Gaussian series are Cauchy in every `Lᵖ`,
`p ≥ 2`. -/
theorem eLpNorm'_gaussianPartialSum_cauchy {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    (v : ℕ → V) {p : ℝ} (hp : 2 ≤ p) (hA : Summable (fun j => ‖v j‖ ^ 2)) :
    ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n m, N ≤ n → N ≤ m →
      eLpNorm' (fun ω => gaussianPartialSum v n ω - gaussianPartialSum v m ω) p
        standardGaussianInfinitePi < ENNReal.ofReal ε := by
  let M : ℕ → ℝ≥0∞ := fun k => eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1) *
    ENNReal.ofReal (Real.sqrt (∑' j, ‖v (k + j)‖ ^ 2))
  have hM : Tendsto M atTop (𝓝 0) := by
    simpa [M] using gaussianTailMomentMajorant_tendsto v hp hA
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero] at hM
  obtain ⟨N, hN⟩ := hM (ENNReal.ofReal (ε / 2))
    (ENNReal.ofReal_pos.mpr (by linarith))
  refine ⟨N, fun n m hn hm => ?_⟩
  have hbound :
      eLpNorm' (fun ω => gaussianPartialSum v n ω - gaussianPartialSum v m ω) p
        standardGaussianInfinitePi ≤ M (min n m) := by
    rcases le_total n m with hnm | hmn
    · have hbase := eLpNorm'_gaussianPartialSum_sub_shift_le v hp hA hnm
      have hneg : (fun ω => gaussianPartialSum v n ω - gaussianPartialSum v m ω) =
          -(fun ω => gaussianPartialSum v m ω - gaussianPartialSum v n ω) := by
        funext ω
        change gaussianPartialSum v n ω - gaussianPartialSum v m ω =
          -(gaussianPartialSum v m ω - gaussianPartialSum v n ω)
        abel
      rw [hneg, eLpNorm'_neg]
      simpa [M, min_eq_left hnm] using hbase
    · have hbase := eLpNorm'_gaussianPartialSum_sub_shift_le v hp hA hmn
      simpa [M, min_eq_right hmn] using hbase
  have hmin : N ≤ min n m := (Nat.le_min).2 ⟨hn, hm⟩
  exact hbound.trans_lt ((hN (min n m) hmin).trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)))

/-- Every finite Gaussian partial sum has every finite moment of order `p ≥ 2`. -/
theorem memLp_gaussianPartialSum {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [OpensMeasurableSpace V]
    (v : ℕ → V) {p : ℝ} (hp : 2 ≤ p) (hA : Summable (fun j => ‖v j‖ ^ 2))
    (n : ℕ) : MemLp (fun ω => gaussianPartialSum v n ω)
      (ENNReal.ofReal p) standardGaussianInfinitePi := by
  have hmeas : Measurable (fun ω => gaussianPartialSum v n ω) := by
    have hcont : Continuous (fun ω : ℕ → ℝ =>
        ∑ j ∈ Finset.range n, ω j • v j) := by
      apply continuous_finsetSum
      intro j hj
      exact (continuous_apply j).smul continuous_const
    simpa [gaussianPartialSum] using hcont.measurable
  have hp0 : ENNReal.ofReal p ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hpTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hbound :
      eLpNorm' (fun ω => gaussianPartialSum v n ω) p standardGaussianInfinitePi ≤
        eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1) *
          ENNReal.ofReal (Real.sqrt (∑' j, ‖v j‖ ^ 2)) := by
    have h := eLpNorm'_gaussianPartialSum_sub_shift_le v hp hA
      (n := 0) (m := n) (Nat.zero_le n)
    simpa [gaussianPartialSum, Nat.zero_add] using h
  have hfinite : eLpNorm' (fun ω => gaussianPartialSum v n ω) p
      standardGaussianInfinitePi < ∞ := by
    apply lt_of_le_of_lt hbound
    apply ENNReal.mul_lt_top
    · exact scalarGaussianLpMoment_lt_top p hp
    · exact ENNReal.ofReal_lt_top
  rw [memLp_iff]
  have heq := eLpNorm_eq_eLpNorm' (μ := standardGaussianInfinitePi)
    hp0 hpTop hmeas.aestronglyMeasurable
  rw [ENNReal.toReal_ofReal (by linarith)] at heq
  rw [heq]
  exact hfinite

local instance gaussianLpExponentFact {p : ℝ} [Fact (2 ≤ p)] :
    Fact (1 ≤ ENNReal.ofReal p) := ⟨by
  have hp : 2 ≤ p := Fact.out
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by linarith)⟩

/-- An `Lᵖ(V)` limit of the Gaussian partial sums exists for every finite real `p ≥ 2`.
It is represented by an element of the complete Bochner `Lᵖ` space. -/
theorem exists_gaussianPartialSum_Lp_limit {p : ℝ} [Fact (2 ≤ p)] {V : Type*}
    [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    (v : ℕ → V) (hA : Summable (fun j => ‖v j‖ ^ 2)) :
    ∃ f : Lp V (ENNReal.ofReal p) standardGaussianInfinitePi,
      Tendsto (fun n =>
        (memLp_gaussianPartialSum v (Fact.out : 2 ≤ p) hA n).toLp
          (fun ω => gaussianPartialSum v n ω)) atTop (𝓝 f) := by
  have hp : 2 ≤ p := Fact.out
  let F : ℕ → Lp V (ENNReal.ofReal p) standardGaussianInfinitePi := fun n =>
    (memLp_gaussianPartialSum v hp hA n).toLp (fun ω => gaussianPartialSum v n ω)
  have hCauchy : CauchySeq F := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := eLpNorm'_gaussianPartialSum_cauchy v hp hA ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [Lp.dist_def]
    have hmem_m := memLp_gaussianPartialSum v hp hA m
    have hmem_n := memLp_gaussianPartialSum v hp hA n
    have hcoe_m := MemLp.coeFn_toLp hmem_m
    have hcoe_n := MemLp.coeFn_toLp hmem_n
    have hae : (fun ω => (F m) ω - (F n) ω) =ᵐ[standardGaussianInfinitePi]
        fun ω => gaussianPartialSum v m ω - gaussianPartialSum v n ω := hcoe_m.sub hcoe_n
    change (eLpNorm (fun ω => (F m) ω - (F n) ω)
      (ENNReal.ofReal p) standardGaussianInfinitePi).toReal < ε
    rw [eLpNorm_congr_ae hae]
    have hp0 : ENNReal.ofReal p ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (by linarith)).ne'
    have hpTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
    have hmeas : Measurable (fun ω =>
        gaussianPartialSum v m ω - gaussianPartialSum v n ω) := by
      have hcont : Continuous (fun ω : ℕ → ℝ =>
          gaussianPartialSum v m ω - gaussianPartialSum v n ω) := by
        exact (show Continuous (fun ω : ℕ → ℝ => gaussianPartialSum v m ω) from by
          have hsum : Continuous (fun ω : ℕ → ℝ =>
              ∑ j ∈ Finset.range m, ω j • v j) := by
            apply continuous_finsetSum
            intro j hj
            exact (continuous_apply j).smul continuous_const
          simpa [gaussianPartialSum] using hsum).sub
          (show Continuous (fun ω : ℕ → ℝ => gaussianPartialSum v n ω) from by
            have hsum : Continuous (fun ω : ℕ → ℝ =>
                ∑ j ∈ Finset.range n, ω j • v j) := by
              apply continuous_finsetSum
              intro j hj
              exact (continuous_apply j).smul continuous_const
            simpa [gaussianPartialSum] using hsum)
      exact hcont.measurable
    have heq := eLpNorm_eq_eLpNorm' (μ := standardGaussianInfinitePi)
      hp0 hpTop hmeas.aestronglyMeasurable
    rw [ENNReal.toReal_ofReal (by linarith)] at heq
    rw [heq]
    exact ENNReal.toReal_lt_of_lt_ofReal (hN m n hm hn)
  obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete hCauchy
  exact ⟨f, by simpa [F] using hf⟩

private lemma gaussianTailEnergy_tendsto_zero {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) :
    Tendsto (fun n => ∑' k, ‖v (n + k)‖ ^ 2) atTop (𝓝 0) := by
  simpa [Function.comp_def] using
    (summable_shift_tsum_tendsto_zero (a := fun j => ‖v j‖ ^ 2) hA)

/-- Tail energies of a square-summable Hilbert family become arbitrarily small. -/
theorem exists_gaussianTailEnergy_small {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (k : ℕ) : ∃ N, ∀ n, N ≤ n → ∑' j, ‖v (n + j)‖ ^ 2 < (1 / 2 : ℝ) ^ (2 * k) := by
  have hε : 0 < (1 / 2 : ℝ) ^ (2 * k) := by positivity
  have hev : ∀ᶠ n : ℕ in atTop, ∑' j, ‖v (n + j)‖ ^ 2 < (1 / 2 : ℝ) ^ (2 * k) :=
    gaussianTailEnergy_tendsto_zero hA |>.eventually (Iio_mem_nhds hε)
  exact Filter.eventually_atTop.mp hev

/-- A truncation threshold after which the remaining Hilbert energy is below the prescribed
geometric scale. -/
noncomputable def gaussianFastThreshold {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (k : ℕ) : ℕ := Classical.choose (exists_gaussianTailEnergy_small hA k)

/-- The selected threshold satisfies its geometric tail estimate. -/
theorem gaussianFastThreshold_spec {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (k n : ℕ) (hn : gaussianFastThreshold hA k ≤ n) :
    ∑' j, ‖v (n + j)‖ ^ 2 < (1 / 2 : ℝ) ^ (2 * k) :=
  (Classical.choose_spec (exists_gaussianTailEnergy_small hA k)) n hn

/-- A fixed increasing subsequence of truncation indices whose remaining Hilbert energy decays
geometrically. -/
noncomputable def gaussianFastIndex {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (k + 1), (gaussianFastThreshold hA i + 1)

theorem gaussianFastIndex_ge_threshold {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (k : ℕ) : gaussianFastThreshold hA k ≤ gaussianFastIndex hA k := by
  have hk : k ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
  have hs := Finset.single_le_sum
    (s := Finset.range (k + 1))
    (f := fun i => gaussianFastThreshold hA i + 1)
    (fun _ _ => Nat.zero_le _) hk
  dsimp [gaussianFastIndex]
  omega

private lemma gaussianFastIndex_succ {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (k : ℕ) : gaussianFastIndex hA (k + 1) =
      gaussianFastIndex hA k + (gaussianFastThreshold hA (k + 1) + 1) := by
  change (∑ i ∈ Finset.range ((k + 1) + 1),
      (gaussianFastThreshold hA i + 1)) = _
  rw [Finset.sum_range_succ]
  rfl

theorem gaussianFastIndex_strictMono {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) :
    StrictMono (gaussianFastIndex hA) := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [gaussianFastIndex_succ]
  omega

theorem gaussianFastIndex_tailEnergy_lt {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (k : ℕ) :
    ∑' j, ‖v (gaussianFastIndex hA k + j)‖ ^ 2 < (1 / 2 : ℝ) ^ (2 * k) := by
  apply gaussianFastThreshold_spec hA k (gaussianFastIndex hA k)
  exact gaussianFastIndex_ge_threshold hA k

/-- The dimension-free Lp tail estimate along the selected fast subsequence. -/
theorem eLpNorm'_gaussianFastPartialSum_sub_le {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) {p : ℝ} (hp : 2 ≤ p)
    (k l : ℕ) (hkl : k ≤ l) :
    eLpNorm' (fun ω => gaussianPartialSum v (gaussianFastIndex hA l) ω -
      gaussianPartialSum v (gaussianFastIndex hA k) ω) p standardGaussianInfinitePi ≤
      eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1) *
        ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
  have hindex : gaussianFastIndex hA k ≤ gaussianFastIndex hA l :=
    (gaussianFastIndex_strictMono hA).monotone hkl
  have htail := eLpNorm'_gaussianPartialSum_sub_le (v := v) hindex hp
  let energy : ℝ := ∑ j ∈ Finset.range (gaussianFastIndex hA l) \
      Finset.range (gaussianFastIndex hA k), ‖v j‖ ^ 2
  have henergy : energy ≤ ∑' j, ‖v (gaussianFastIndex hA k + j)‖ ^ 2 := by
    dsimp [energy]
    exact finiteTail_sum_le_tsum_shift (fun j => sq_nonneg ‖v j‖) hA _ _ hindex
  have henergy_nonneg : 0 ≤ energy := by
    dsimp [energy]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsmall : energy < (1 / 2 : ℝ) ^ (2 * k) :=
    lt_of_le_of_lt henergy (gaussianFastIndex_tailEnergy_lt hA k)
  have hpow : ((1 / 2 : ℝ) ^ k) ^ 2 = (1 / 2 : ℝ) ^ (2 * k) := by
    calc
      ((1 / 2 : ℝ) ^ k) ^ 2 = (1 / 2 : ℝ) ^ (k * 2) := by rw [pow_mul]
      _ = (1 / 2 : ℝ) ^ (2 * k) := by rw [Nat.mul_comm]
  have hroot : Real.sqrt energy ≤ (1 / 2 : ℝ) ^ k := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [hsmall, hpow]
  calc
    _ ≤ eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1) * ENNReal.ofReal (Real.sqrt energy) := htail
    _ ≤ eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1) * ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
      gcongr

/-- The partial sums evaluated along the fixed fast subsequence. -/
noncomputable def gaussianFastPartialSumSequence {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) :
    ℕ → (ℕ → ℝ) → V := fun k ω => gaussianPartialSum v (gaussianFastIndex hA k) ω

private noncomputable def gaussianFastMajorant (p : ℝ) (k : ℕ) : ℝ≥0∞ :=
  eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1) * ENNReal.ofReal ((1 / 2 : ℝ) ^ k) +
    ENNReal.ofReal ((1 / 2 : ℝ) ^ k)

private lemma gaussianFastMajorant_tsum_ne_top (p : ℝ) (hp : 2 ≤ p) :
    ∑' k, gaussianFastMajorant p k ≠ ∞ := by
  let c : ℝ≥0∞ := eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1)
  have hc : c ≠ ∞ := scalarGaussianLpMoment_lt_top p hp |>.ne
  have hgeom : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) := summable_geometric_two
  have hgeom' : ∑' k, ENNReal.ofReal ((1 / 2 : ℝ) ^ k) ≠ ∞ := hgeom.tsum_ofReal_ne_top
  have hsum : ∑' k, gaussianFastMajorant p k =
      c * (∑' k, ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) +
        ∑' k, ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
    simp [gaussianFastMajorant, c, ENNReal.tsum_add, ENNReal.tsum_mul_left]
  rw [hsum]
  exact (ENNReal.add_ne_top).mpr ⟨ENNReal.mul_ne_top hc hgeom', hgeom'⟩

private lemma eLpNorm_gaussianFastPartialSum_sub_le {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [SecondCountableTopology V] [MeasurableSpace V]
    [BorelSpace V] [OpensMeasurableSpace V] {v : ℕ → V}
    (hA : Summable (fun j => ‖v j‖ ^ 2)) {p : ℝ} (hp : 2 ≤ p)
    (k l : ℕ) (hkl : k ≤ l) :
    eLpNorm (gaussianFastPartialSumSequence hA l - gaussianFastPartialSumSequence hA k)
      (ENNReal.ofReal p) standardGaussianInfinitePi ≤
      eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1) * ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
  have hmem_l := memLp_gaussianPartialSum v hp hA (gaussianFastIndex hA l)
  have hmem_k := memLp_gaussianPartialSum v hp hA (gaussianFastIndex hA k)
  have hmem := hmem_l.sub hmem_k
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hpTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have heq := eLpNorm_eq_eLpNorm' hp0 hpTop hmem.aestronglyMeasurable
  rw [ENNReal.toReal_ofReal (by linarith)] at heq
  change eLpNorm ((fun ω => gaussianPartialSum v (gaussianFastIndex hA l) ω) -
      (fun ω => gaussianPartialSum v (gaussianFastIndex hA k) ω))
      (ENNReal.ofReal p) standardGaussianInfinitePi ≤ _
  rw [heq]
  exact eLpNorm'_gaussianFastPartialSum_sub_le hA hp k l hkl

private lemma gaussianFastPartialSum_cauchy {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [SecondCountableTopology V] [MeasurableSpace V]
    [BorelSpace V] [OpensMeasurableSpace V] {v : ℕ → V}
    (hA : Summable (fun j => ‖v j‖ ^ 2)) {p : ℝ} (hp : 2 ≤ p) :
    ∀ N n m, N ≤ n → N ≤ m →
      eLpNorm (gaussianFastPartialSumSequence hA n - gaussianFastPartialSumSequence hA m)
        (ENNReal.ofReal p) standardGaussianInfinitePi < gaussianFastMajorant p N := by
  intro N n m hNn hNm
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hpTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hεN : 0 < (1 / 2 : ℝ) ^ N := pow_pos (by norm_num) _
  have hbase (a b : ℕ) (hab : a ≤ b) :
      eLpNorm (gaussianFastPartialSumSequence hA b - gaussianFastPartialSumSequence hA a)
        (ENNReal.ofReal p) standardGaussianInfinitePi ≤
        eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1) * ENNReal.ofReal ((1 / 2 : ℝ) ^ a) :=
    eLpNorm_gaussianFastPartialSum_sub_le hA hp a b hab
  have hpow (a : ℕ) (hNa : N ≤ a) : (1 / 2 : ℝ) ^ a ≤ (1 / 2 : ℝ) ^ N :=
    pow_le_pow_of_le_one (by positivity) (by norm_num) hNa
  have hmul (a : ℕ) (hNa : N ≤ a) :
      eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1) * ENNReal.ofReal ((1 / 2 : ℝ) ^ a) ≤
        eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1) * ENNReal.ofReal ((1 / 2 : ℝ) ^ N) := by
    exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (hpow a hNa)) _
  by_cases hnm : n ≤ m
  · have hnorm : eLpNorm (gaussianFastPartialSumSequence hA n -
        gaussianFastPartialSumSequence hA m) (ENNReal.ofReal p) standardGaussianInfinitePi =
        eLpNorm (gaussianFastPartialSumSequence hA m -
          gaussianFastPartialSumSequence hA n) (ENNReal.ofReal p) standardGaussianInfinitePi := by
      rw [show gaussianFastPartialSumSequence hA n - gaussianFastPartialSumSequence hA m =
        -(gaussianFastPartialSumSequence hA m - gaussianFastPartialSumSequence hA n) by abel,
        eLpNorm_neg]
    calc
      _ = _ := hnorm
      _ ≤ eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1) *
          ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := hbase n m hnm
      _ ≤ eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1) *
          ENNReal.ofReal ((1 / 2 : ℝ) ^ N) := hmul n hNn
      _ < gaussianFastMajorant p N := by
        dsimp [gaussianFastMajorant]
        have hbaseTop :
            (eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1) *
              ENNReal.ofReal ((1 / 2 : ℝ) ^ N)) ≠ ∞ :=
          ENNReal.mul_ne_top (scalarGaussianLpMoment_lt_top p hp).ne ENNReal.ofReal_ne_top
        have hstrict := ENNReal.add_lt_add_left hbaseTop (ENNReal.ofReal_pos.mpr hεN)
        simpa using hstrict
  · have hmn : m ≤ n := by omega
    calc
      _ ≤ eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1) *
          ENNReal.ofReal ((1 / 2 : ℝ) ^ m) := hbase m n hmn
      _ ≤ eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1) *
          ENNReal.ofReal ((1 / 2 : ℝ) ^ N) := hmul m hNm
      _ < gaussianFastMajorant p N := by
        dsimp [gaussianFastMajorant]
        have hbaseTop :
            (eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1) *
              ENNReal.ofReal ((1 / 2 : ℝ) ^ N)) ≠ ∞ :=
          ENNReal.mul_ne_top (scalarGaussianLpMoment_lt_top p hp).ne ENNReal.ofReal_ne_top
        have hstrict := ENNReal.add_lt_add_left hbaseTop (ENNReal.ofReal_pos.mpr hεN)
        simpa using hstrict

/-- The Hilbert-valued Gaussian series has an almost-everywhere limit along one fixed fast
subsequence of partial sums. -/
theorem exists_gaussianFastPartialSum_ae_limit {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    (v : ℕ → V) (hA : Summable (fun j => ‖v j‖ ^ 2)) :
    ∃ Ψ : (ℕ → ℝ) → V, StronglyMeasurable Ψ ∧
      ∀ᵐ ω ∂standardGaussianInfinitePi,
        Tendsto (fun k => gaussianFastPartialSumSequence hA k ω) atTop (𝓝 (Ψ ω)) := by
  let F : ℕ → (ℕ → ℝ) → V := gaussianFastPartialSumSequence hA
  have hmem (k : ℕ) : MemLp (F k) (ENNReal.ofReal 2) standardGaussianInfinitePi := by
    change MemLp (gaussianPartialSum v (gaussianFastIndex hA k))
      (ENNReal.ofReal 2) standardGaussianInfinitePi
    exact memLp_gaussianPartialSum v (p := 2) (by norm_num) hA (gaussianFastIndex hA k)
  have hB := gaussianFastMajorant_tsum_ne_top 2 (by norm_num)
  have hcau : ∀ N n m, N ≤ n → N ≤ m →
      eLpNorm (F n - F m) (ENNReal.ofReal 2) standardGaussianInfinitePi <
        gaussianFastMajorant 2 N := by
    simpa [F] using gaussianFastPartialSum_cauchy hA (p := 2) (by norm_num)
  have hae := MeasureTheory.Lp.ae_tendsto_of_cauchy_eLpNorm
    (fun k => (hmem k).aestronglyMeasurable)
    (by norm_num : 1 ≤ ENNReal.ofReal 2) hB hcau
  exact exists_stronglyMeasurable_limit_of_tendsto_ae
    (fun k => (hmem k).aestronglyMeasurable) hae

/-- The chosen measurable version of the a.e. limit along the fast Gaussian subsequence. -/
noncomputable def gaussianSeriesLimit {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    (v : ℕ → V) (hA : Summable (fun j => ‖v j‖ ^ 2)) : (ℕ → ℝ) → V :=
  Classical.choose (exists_gaussianFastPartialSum_ae_limit v hA)

/-- The series limit is strongly measurable. -/
theorem stronglyMeasurable_gaussianSeriesLimit {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    (v : ℕ → V) (hA : Summable (fun j => ‖v j‖ ^ 2)) :
    StronglyMeasurable (gaussianSeriesLimit v hA) :=
  (Classical.choose_spec (exists_gaussianFastPartialSum_ae_limit v hA)).1

/-- The selected fast subsequence converges almost everywhere to `gaussianSeriesLimit`. -/
theorem ae_tendsto_gaussianSeriesLimit {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    (v : ℕ → V) (hA : Summable (fun j => ‖v j‖ ^ 2)) :
    ∀ᵐ ω ∂standardGaussianInfinitePi,
      Tendsto (fun k => gaussianFastPartialSumSequence hA k ω) atTop
        (𝓝 (gaussianSeriesLimit v hA ω)) :=
  (Classical.choose_spec (exists_gaussianFastPartialSum_ae_limit v hA)).2

/-- The fixed fast subsequence converges to its a.e. limit in every finite `Lᵖ`, `p ≥ 2`. -/
theorem tendsto_eLpNorm_gaussianFastPartialSum {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    (v : ℕ → V) (hA : Summable (fun j => ‖v j‖ ^ 2)) {p : ℝ} (hp : 2 ≤ p) :
    Tendsto (fun k => eLpNorm
      (gaussianFastPartialSumSequence hA k - gaussianSeriesLimit v hA)
      (ENNReal.ofReal p) standardGaussianInfinitePi) atTop (𝓝 0) := by
  let F : ℕ → (ℕ → ℝ) → V := gaussianFastPartialSumSequence hA
  have hmem (k : ℕ) : MemLp (F k) (ENNReal.ofReal p) standardGaussianInfinitePi := by
    change MemLp (gaussianPartialSum v (gaussianFastIndex hA k))
      (ENNReal.ofReal p) standardGaussianInfinitePi
    exact memLp_gaussianPartialSum v hp hA (gaussianFastIndex hA k)
  have hB := gaussianFastMajorant_tsum_ne_top p hp
  have hcau : ∀ N n m, N ≤ n → N ≤ m →
      eLpNorm (F n - F m) (ENNReal.ofReal p) standardGaussianInfinitePi <
        gaussianFastMajorant p N := by
    simpa [F] using gaussianFastPartialSum_cauchy hA hp
  exact MeasureTheory.Lp.cauchy_tendsto_of_tendsto
    (fun k => (hmem k).aestronglyMeasurable) (gaussianSeriesLimit v hA)
    hB hcau (ae_tendsto_gaussianSeriesLimit v hA)

/-- The a.e. limit of the fast subsequence has every finite moment required by the series theorem. -/
theorem memLp_gaussianSeriesLimit {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    (v : ℕ → V) (hA : Summable (fun j => ‖v j‖ ^ 2)) {p : ℝ} (hp : 2 ≤ p) :
    MemLp (gaussianSeriesLimit v hA) (ENNReal.ofReal p) standardGaussianInfinitePi := by
  have hmem (k : ℕ) : MemLp (gaussianFastPartialSumSequence hA k)
      (ENNReal.ofReal p) standardGaussianInfinitePi := by
    change MemLp (gaussianPartialSum v (gaussianFastIndex hA k))
      (ENNReal.ofReal p) standardGaussianInfinitePi
    exact memLp_gaussianPartialSum v hp hA (gaussianFastIndex hA k)
  have hpENN : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  exact MeasureTheory.Lp.memLp_of_cauchy_tendsto hpENN hmem
    (gaussianSeriesLimit v hA) (tendsto_eLpNorm_gaussianFastPartialSum v hA hp)

/-- The a.e. subsequential limit represents the limit of the full partial-sum sequence in every
finite `Lᵖ`, `p ≥ 2`. -/
theorem ae_eq_gaussianSeriesLimit_of_Lp_limit {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    (v : ℕ → V) (hA : Summable (fun j => ‖v j‖ ^ 2)) {p : ℝ} [Fact (2 ≤ p)]
    (f : Lp V (ENNReal.ofReal p) standardGaussianInfinitePi)
    (hf : Tendsto (fun n => (memLp_gaussianPartialSum v (Fact.out : 2 ≤ p) hA n).toLp
      (fun ω => gaussianPartialSum v n ω)) atTop (𝓝 f)) :
    (fun ω => f ω) =ᵐ[standardGaussianInfinitePi] gaussianSeriesLimit v hA := by
  let hp : 2 ≤ p := Fact.out
  let F : ℕ → Lp V (ENNReal.ofReal p) standardGaussianInfinitePi := fun n =>
    (memLp_gaussianPartialSum v hp hA n).toLp (fun ω => gaussianPartialSum v n ω)
  have hfullCauchy : CauchySeq F := by
    simpa [F] using hf.cauchySeq
  have hΨ : MemLp (gaussianSeriesLimit v hA) (ENNReal.ofReal p) standardGaussianInfinitePi :=
    memLp_gaussianSeriesLimit v hA hp
  have hfastNorm : Tendsto (fun k => eLpNorm
      (gaussianFastPartialSumSequence hA k - gaussianSeriesLimit v hA)
      (ENNReal.ofReal p) standardGaussianInfinitePi) atTop (𝓝 0) :=
    tendsto_eLpNorm_gaussianFastPartialSum v hA hp
  have hcoe (k : ℕ) :
      (fun ω => F (gaussianFastIndex hA k) ω) =ᵐ[standardGaussianInfinitePi]
        gaussianFastPartialSumSequence hA k := by
    change (fun ω => ((memLp_gaussianPartialSum v hp hA (gaussianFastIndex hA k)).toLp
      (fun ω => gaussianPartialSum v (gaussianFastIndex hA k) ω)) ω) =ᵐ[standardGaussianInfinitePi]
        (fun ω => gaussianPartialSum v (gaussianFastIndex hA k) ω)
    exact MemLp.coeFn_toLp (memLp_gaussianPartialSum v hp hA (gaussianFastIndex hA k))
  have hnormEq (k : ℕ) : eLpNorm
      ((fun ω => F (gaussianFastIndex hA k) ω) - gaussianSeriesLimit v hA)
      (ENNReal.ofReal p) standardGaussianInfinitePi =
      eLpNorm (gaussianFastPartialSumSequence hA k - gaussianSeriesLimit v hA)
      (ENNReal.ofReal p) standardGaussianInfinitePi := by
    apply eLpNorm_congr_ae
    filter_upwards [hcoe k] with ω hω
    simp only [Pi.sub_apply, hω]
  have hnorm : Tendsto (fun k => eLpNorm
      ((fun ω => F (gaussianFastIndex hA k) ω) - gaussianSeriesLimit v hA)
      (ENNReal.ofReal p) standardGaussianInfinitePi) atTop (𝓝 0) :=
    hfastNorm.congr (fun k => (hnormEq k).symm)
  have hsub : Tendsto (fun k => F (gaussianFastIndex hA k)) atTop
      (𝓝 ((hΨ).toLp (gaussianSeriesLimit v hA))) :=
    (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm
      (fun k => F (gaussianFastIndex hA k))
      (gaussianSeriesLimit v hA) hΨ).2 hnorm
  have hidx : Tendsto (gaussianFastIndex hA) atTop atTop :=
    (gaussianFastIndex_strictMono hA).tendsto_atTop
  have hwhole : Tendsto F atTop (𝓝 ((hΨ).toLp (gaussianSeriesLimit v hA))) := by
    exact tendsto_nhds_of_cauchySeq_of_subseq hfullCauchy hidx hsub
  have heq : f = (hΨ).toLp (gaussianSeriesLimit v hA) := tendsto_nhds_unique hf hwhole
  rw [heq]
  exact MemLp.coeFn_toLp hΨ

/-- The sum of the norms of successive fast-subsequence increments. -/
noncomputable def gaussianFastVariation {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {v : ℕ → V}
    (hA : Summable (fun j => ‖v j‖ ^ 2)) (ω : ℕ → ℝ) : ℝ :=
  ∑' k, ‖gaussianFastPartialSumSequence hA (k + 1) ω -
    gaussianFastPartialSumSequence hA k ω‖

/-- The fast-subsequence variation has every finite moment of order at least two. -/
theorem memLp_gaussianFastVariation {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [SecondCountableTopology V] [MeasurableSpace V]
    [BorelSpace V] [OpensMeasurableSpace V]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) {p : ℝ} (hp : 2 ≤ p) :
    MemLp (gaussianFastVariation hA) (ENNReal.ofReal p) standardGaussianInfinitePi ∧
      ∀ᵐ ω ∂standardGaussianInfinitePi,
        Summable (fun k => ‖gaussianFastPartialSumSequence hA (k + 1) ω -
          gaussianFastPartialSumSequence hA k ω‖) := by
  let q : ℝ≥0∞ := ENNReal.ofReal p
  let F : ℕ → (ℕ → ℝ) → V := gaussianFastPartialSumSequence hA
  let c : ℝ≥0∞ := eLpNorm' (id : ℝ → ℝ) p (gaussianReal 0 1)
  have hq1 : 1 ≤ q := by
    dsimp [q]
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  letI : Fact (1 ≤ q) := ⟨hq1⟩
  have hc : c ≠ ∞ := scalarGaussianLpMoment_lt_top p hp |>.ne
  have hgeom : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) := summable_geometric_two
  have hgeom' : ∑' k, ENNReal.ofReal ((1 / 2 : ℝ) ^ k) ≠ ∞ :=
    hgeom.tsum_ofReal_ne_top
  have hB : ∑' k, c * ENNReal.ofReal ((1 / 2 : ℝ) ^ k) ≠ ∞ := by
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top hc hgeom'
  have hvecMem (k : ℕ) : MemLp (fun ω => F (k + 1) ω - F k ω) q
      standardGaussianInfinitePi := by
    change MemLp (fun ω => gaussianPartialSum v (gaussianFastIndex hA (k + 1)) ω -
      gaussianPartialSum v (gaussianFastIndex hA k) ω) q standardGaussianInfinitePi
    exact (memLp_gaussianPartialSum v hp hA _).sub
      (memLp_gaussianPartialSum v hp hA _)
  have hbound (k : ℕ) : eLpNorm (fun ω => ‖F (k + 1) ω - F k ω‖) q
      standardGaussianInfinitePi ≤ c * ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
    have hp0 : q ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
    have hpTop : q ≠ ∞ := ENNReal.ofReal_ne_top
    have hprime := eLpNorm'_gaussianFastPartialSum_sub_le hA hp k (k + 1) (by omega)
    have heq := eLpNorm_eq_eLpNorm' hp0 hpTop (hvecMem k).aestronglyMeasurable
    have hqreal : q.toReal = p := by
      dsimp [q]
      exact ENNReal.toReal_ofReal (by linarith)
    rw [eLpNorm_norm (fun ω => F (k + 1) ω - F k ω)
      (hvecMem k).aestronglyMeasurable, heq, hqreal]
    simpa [F, gaussianFastPartialSumSequence, c] using hprime
  let g : ℕ → Lp ℝ q standardGaussianInfinitePi := fun k =>
    (hvecMem k).norm.toLp (fun ω => ‖F (k + 1) ω - F k ω‖)
  have hgn (k : ℕ) : ‖g k‖ₑ ≤ c * ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
    dsimp [g]
    rw [Lp.enorm_toLp]
    exact hbound k
  have hsumNorm : ∑' k, ‖g k‖ₑ ≠ ∞ := by
    apply ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum hgn) (lt_top_iff_ne_top.mpr hB))
  have htermSum : ∑' k,
      eLpNorm (fun ω => ‖F (k + 1) ω - F k ω‖) q standardGaussianInfinitePi ≠ ∞ := by
    apply ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum hbound)
      (lt_top_iff_ne_top.mpr hB))
  have hvariationSummable : ∀ᵐ ω ∂standardGaussianInfinitePi,
      Summable (fun k => ‖F (k + 1) ω - F k ω‖) := by
    have h := MeasureTheory.summable_norm_of_tsum_eLpNorm_ne_top hq1 htermSum
    filter_upwards [h] with ω hω
    simpa only [norm_norm] using hω
  have hEq : (∑' k, g k : Lp ℝ q standardGaussianInfinitePi) =ᵐ[
      standardGaussianInfinitePi] gaussianFastVariation hA := by
    have hTsum := Lp.coeFn_tsum (E := ℝ) (p := q) hsumNorm
    have hCoe (k : ℕ) : (g k : (ℕ → ℝ) → ℝ) =ᵐ[standardGaussianInfinitePi]
        (fun ω => ‖F (k + 1) ω - F k ω‖) := by
      exact MemLp.coeFn_toLp (hvecMem k).norm
    have hCoeAll : ∀ᵐ ω ∂standardGaussianInfinitePi, ∀ k,
        (g k : (ℕ → ℝ) → ℝ) ω = ‖F (k + 1) ω - F k ω‖ := by
      rw [ae_all_iff]
      exact fun k => hCoe k
    filter_upwards [hTsum, hCoeAll] with ω hω hωall
    calc
      (∑' k, g k : Lp ℝ q standardGaussianInfinitePi) ω =
          ∑' k, (g k : (ℕ → ℝ) → ℝ) ω := hω
      _ = ∑' k, ‖F (k + 1) ω - F k ω‖ := tsum_congr hωall
  refine ⟨MemLp.ae_eq hEq (Lp.memLp (∑' k, g k)), ?_⟩
  simpa [F, gaussianFastPartialSumSequence] using hvariationSummable

/-- A random envelope controlling every term of the fast partial-sum subsequence. -/
noncomputable def gaussianFastEnvelope {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {v : ℕ → V}
    (hA : Summable (fun j => ‖v j‖ ^ 2)) (ω : ℕ → ℝ) : ℝ :=
  ‖gaussianFastPartialSumSequence hA 0 ω‖ + gaussianFastVariation hA ω

/-- The pathwise envelope has all finite moments of order at least two. -/
theorem memLp_gaussianFastEnvelope {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [SecondCountableTopology V] [MeasurableSpace V]
    [BorelSpace V] [OpensMeasurableSpace V]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) {p : ℝ} (hp : 2 ≤ p) :
    MemLp (gaussianFastEnvelope hA) (ENNReal.ofReal p) standardGaussianInfinitePi := by
  change MemLp (fun ω => ‖gaussianFastPartialSumSequence hA 0 ω‖ +
    gaussianFastVariation hA ω) (ENNReal.ofReal p) standardGaussianInfinitePi
  exact (memLp_gaussianPartialSum v hp hA (gaussianFastIndex hA 0)).norm.add
    (memLp_gaussianFastVariation hA hp).1

/-- Almost surely, the envelope bounds the norm of every fast partial sum. -/
theorem ae_norm_gaussianFastPartialSum_le_envelope {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) :
    ∀ᵐ ω ∂standardGaussianInfinitePi, ∀ k,
      ‖gaussianFastPartialSumSequence hA k ω‖ ≤ gaussianFastEnvelope hA ω := by
  filter_upwards [(memLp_gaussianFastVariation hA (by norm_num : 2 ≤ (2 : ℝ))).2]
    with ω hvariation
  intro k
  let F : ℕ → (ℕ → ℝ) → V := gaussianFastPartialSumSequence hA
  have htel : F k ω = F 0 ω + ∑ i ∈ Finset.range k, (F (i + 1) ω - F i ω) := by
    have hsum : ∑ i ∈ Finset.range k, (F (i + 1) ω - F i ω) = F k ω - F 0 ω := by
      simpa [F] using Finset.sum_range_sub (fun i => gaussianFastPartialSumSequence hA i ω) k
    rw [hsum]
    abel
  have hnorm := norm_add_le (F 0 ω)
    (∑ i ∈ Finset.range k, (F (i + 1) ω - F i ω))
  calc
    ‖gaussianFastPartialSumSequence hA k ω‖ =
        ‖F 0 ω + ∑ i ∈ Finset.range k, (F (i + 1) ω - F i ω)‖ := by
          change ‖F k ω‖ = _
          rw [htel]
    _ ≤ ‖F 0 ω‖ + ∑ i ∈ Finset.range k, ‖F (i + 1) ω - F i ω‖ := by
      calc
        _ ≤ ‖F 0 ω‖ + ‖∑ i ∈ Finset.range k, (F (i + 1) ω - F i ω)‖ := hnorm
        _ ≤ _ := by gcongr; exact norm_sum_le _ _
    _ ≤ gaussianFastEnvelope hA ω := by
      simpa [F, gaussianFastEnvelope, gaussianFastVariation,
        gaussianFastPartialSumSequence] using
        add_le_add_left (hvariation.sum_le_tsum (Finset.range k)
          (fun i _ => norm_nonneg _)) ‖F 0 ω‖

end ASDExplicitGamma.Gaussian

