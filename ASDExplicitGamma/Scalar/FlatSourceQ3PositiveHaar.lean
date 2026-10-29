module

public import ASDExplicitGamma.Scalar.FlatSourceHaarLimit
public import ASDExplicitGamma.Scalar.FlatSourceQ3FiniteGradient
public import ASDExplicitGamma.Scalar.FlatSourcePoincare
public import ASDExplicitGamma.Scalar.FlatSourceQ3FiniteGradientTrace
public import ASDExplicitGamma.Scalar.FlatSourceQ3LpBridge
public import Homogenization.Sobolev.L2Ambient
public import ASDExplicitGamma.Gaussian.H3Separable

/-! Coordinate transfer from the physical vector L² limit to normalized cell L². -/

@[expose] public section

open MeasureTheory Homogenization Filter
open ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped ENNReal Topology

namespace ASDExplicitGamma.Scalar

theorem primalEnergy_measurable_of_l2_map
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : TriadicCube 2)
    [MeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure Q))]
    [BorelSpace (Lp ℝ 2 (normalizedCubeMeasure Q))]
    [OpensMeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure Q))]
    (u : Ω → Lp ℝ 2 (normalizedCubeMeasure Q))
    (hu : Measurable u) :
    Measurable (fun ω => primalEnergy Q (Real.sqrt 3) (fun x => u ω x)) := by
  classical
  let q : ℝ := Real.sqrt 3
  let a : ℕ → Ω → ℝ := fun n ω =>
    q ^ (n + 1) * ‖cubeIncrementL2CLM Q (n + 1) (u ω)‖ ^ 2
  let S : Ω → ℝ≥0∞ := fun ω => ∑' n, ENNReal.ofReal (a n ω)
  have ha (n : ℕ) : Measurable (a n) := by
    dsimp [a]
    have hnorm : Measurable (fun ω =>
        ‖cubeIncrementL2CLM Q (n + 1) (u ω)‖ ^ 2) :=
      (((cubeIncrementL2CLM Q (n + 1)).continuous.measurable.comp hu).norm.pow_const 2)
    simpa only [mul_comm] using hnorm.const_mul (q ^ (n + 1))
  have ha_nonneg (n : ℕ) (ω : Ω) : 0 ≤ a n ω := by
    dsimp [a]
    positivity
  have hS : Measurable S := by
    dsimp [S]
    exact Measurable.ennreal_tsum fun n => (ha n).ennreal_ofReal
  have htsum (ω : Ω) :
      (∑' n, a n ω) = (S ω).toReal := by
    by_cases htop : S ω = ∞
    · have hnot : ¬ Summable (fun n => a n ω) := by
        intro hs
        have hfinite := hs.tsum_ofReal_ne_top
        have hSfinite : S ω ≠ ∞ := by
          intro hInf
          exact hfinite (by simpa [S] using hInf)
        exact hSfinite htop
      rw [tsum_eq_zero_of_not_summable hnot, htop]
      rfl
    · let b : ℕ → NNReal := fun n => Real.toNNReal (a n ω)
      have hb (n : ℕ) : (b n : ℝ≥0∞) = ENNReal.ofReal (a n ω) := by
        simp [b, ENNReal.ofReal, Real.toNNReal_of_nonneg (ha_nonneg n ω)]
      have hsumB : Summable b := by
        apply (ENNReal.tsum_coe_ne_top_iff_summable).mp
        rw [show (∑' n, (b n : ℝ≥0∞)) = S ω from by
          apply tsum_congr
          intro n
          exact hb n]
        exact htop
      have hsumA : Summable (fun n => a n ω) := by
        have hsumReal : Summable (fun n => (b n : ℝ)) :=
          NNReal.summable_coe.2 hsumB
        have hEq : (fun n => (b n : ℝ)) = fun n => a n ω := by
          funext n
          dsimp [b]
          exact Real.coe_toNNReal _ (ha_nonneg n ω)
        exact hEq ▸ hsumReal
      have hrepr : ENNReal.ofReal (∑' n, a n ω) = S ω := by
        dsimp [S]
        exact ENNReal.ofReal_tsum_of_nonneg (fun n => ha_nonneg n ω) hsumA
      have hsum_nonneg : 0 ≤ (∑' n, a n ω) :=
        tsum_nonneg fun n => ha_nonneg n ω
      calc
        (∑' n, a n ω) = (ENNReal.ofReal (∑' n, a n ω)).toReal := by
          rw [ENNReal.toReal_ofReal hsum_nonneg]
        _ = (S ω).toReal := by rw [hrepr]
  have hbaseEq :
      (fun ω => energy Q (cubeIncrement Q 0 (fun x => u ω x))) =
        fun ω => ‖cubeIncrementL2CLM Q 0 (u ω)‖ ^ 2 := by
    funext ω
    exact energy_cubeIncrement_eq_clm_norm_sq Q 0 (u ω)
  have hbase : Measurable
      (fun ω => energy Q (cubeIncrement Q 0 (fun x => u ω x))) := by
    rw [hbaseEq]
    exact (((cubeIncrementL2CLM Q 0).continuous.measurable.comp hu).norm.pow_const 2)
  have hEq (ω : Ω) :
      primalEnergy Q q (fun x => u ω x) =
        energy Q (cubeIncrement Q 0 (fun x => u ω x)) + (S ω).toReal := by
    rw [primalEnergy]
    have hterm (n : ℕ) :
        q ^ (n + 1) * energy Q
          (cubeIncrement Q (n + 1) (fun x => u ω x)) = a n ω := by
      rw [energy_cubeIncrement_eq_clm_norm_sq]
    rw [tsum_congr hterm, htsum ω]
  have hresult : Measurable
      (fun ω => energy Q (cubeIncrement Q 0 (fun x => u ω x)) + (S ω).toReal) :=
    hbase.add hS.ennreal_toReal
  rw [show (fun ω => primalEnergy Q (Real.sqrt 3) (fun x => u ω x)) =
      fun ω => energy Q (cubeIncrement Q 0 (fun x => u ω x)) + (S ω).toReal from by
        funext ω
        simpa [q] using hEq ω]
  exact hresult

/-- The normalized cell measure is the corresponding scalar multiple of
Lebesgue measure on the open cube. -/
theorem normalizedCubeMeasure_eq_smul_open (Q : TriadicCube 2) :
    normalizedCubeMeasure Q =
      ENNReal.ofReal ((cubeVolume Q)⁻¹) • volumeMeasureOn (openCubeSet Q) := by
  have hraw : volumeMeasureOn (openCubeSet Q) =
      ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q := by
    rw [volumeMeasureOn, ← volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
    rw [normalizedCubeMeasure, cubeMeasure, smul_smul]
    have hcoeff : ENNReal.ofReal (cubeVolume Q) *
        ENNReal.ofReal ((cubeVolume Q)⁻¹) = 1 := by
      rw [← ENNReal.ofReal_mul (cubeVolume_pos Q).le]
      rw [mul_inv_cancel₀ (ne_of_gt (cubeVolume_pos Q)), ENNReal.ofReal_one]
    rw [hcoeff, one_smul]
  rw [hraw, smul_smul]
  have hcoeff : ENNReal.ofReal ((cubeVolume Q)⁻¹) *
      ENNReal.ofReal (cubeVolume Q) = 1 := by
    rw [mul_comm, ← ENNReal.ofReal_mul (cubeVolume_pos Q).le]
    rw [mul_inv_cancel₀ (ne_of_gt (cubeVolume_pos Q)), ENNReal.ofReal_one]
  rw [hcoeff, one_smul]

/-- A Hilbert-vector spatial L² class has a continuous coordinate map into
normalized scalar cell L². -/
noncomputable def hilbertVectorL2_normalizedCoordCLM
    (Q : TriadicCube 2) (i : Fin 2) :
    HilbertVectorL2 (openCubeSet Q) →L[ℝ]
      Lp ℝ 2 (normalizedCubeMeasure Q) := by
  let μ := volumeMeasureOn (openCubeSet Q)
  let c : ℝ≥0∞ := ENNReal.ofReal ((cubeVolume Q)⁻¹)
  have hc : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hdom : normalizedCubeMeasure Q ≤ c • μ := by
    rw [show normalizedCubeMeasure Q = c • μ from normalizedCubeMeasure_eq_smul_open Q]
  let toScalar : Lp (Vec 2) 2 μ →L[ℝ] Lp ℝ 2 μ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).compLpL 2 μ
  let toNormalized : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (normalizedCubeMeasure Q) :=
    Lp.LpToLpOfMeasureLeSMul (p := (2 : ℝ≥0∞))
      (μ := normalizedCubeMeasure Q) (ν := μ) (c := c) hc hdom
  exact toNormalized.comp (toScalar.comp
    (hilbertVectorL2ToVectorL2 (U := openCubeSet Q)))

section FixedProductPositiveHaarMeasurability

end FixedProductPositiveHaarMeasurability

/-- The coordinate map agrees almost everywhere with the expected scalar
coordinate of the physical Hilbert-vector representative. -/
theorem hilbertVectorL2_normalizedCoordCLM_ae
    (Q : TriadicCube 2) (i : Fin 2)
    (F : HilbertVectorL2 (openCubeSet Q)) :
    hilbertVectorL2_normalizedCoordCLM Q i F =ᵐ[normalizedCubeMeasure Q]
      fun x => (hilbertVectorL2ToVectorL2 (U := openCubeSet Q) F x) i := by
  let μ := volumeMeasureOn (openCubeSet Q)
  let c : ℝ≥0∞ := ENNReal.ofReal ((cubeVolume Q)⁻¹)
  have hc : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hdom : normalizedCubeMeasure Q ≤ c • μ := by
    rw [show normalizedCubeMeasure Q = c • μ from normalizedCubeMeasure_eq_smul_open Q]
  have hproj : ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).compLpL 2 μ)
      (hilbertVectorL2ToVectorL2 (U := openCubeSet Q) F) =ᵐ[μ]
        fun x => (hilbertVectorL2ToVectorL2 (U := openCubeSet Q) F x) i :=
    ContinuousLinearMap.coeFn_compLpL
      (p := 2) (μ := μ)
      (L := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i)
      (f := hilbertVectorL2ToVectorL2 (U := openCubeSet Q) F)
  have htransfer := Lp.coeFn_LpToLpOfMeasureLeSMul hc hdom
    (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).compLpL 2 μ)
      (hilbertVectorL2ToVectorL2 (U := openCubeSet Q) F))
  filter_upwards [htransfer,
    hproj.filter_mono (Measure.absolutelyContinuous_of_le_smul hdom).ae_le] with x hx₁ hx₂
  change ((Lp.LpToLpOfMeasureLeSMul (p := (2 : ℝ≥0∞))
      (μ := normalizedCubeMeasure Q) (ν := μ) (c := c) hc hdom)
      (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).compLpL 2 μ)
        (hilbertVectorL2ToVectorL2 (U := openCubeSet Q) F))) x = _
  rw [hx₁, hx₂]

/-- The vector positive-Haar energy is lower semicontinuous under strong
coordinatewise normalized L² convergence when every approximant has a weak
H¹ gradient. The limit field itself needs no gradient. -/
theorem vectorPositiveHaarNorm_sq_le_of_partial_bounds
    (Q : TriadicCube 2) (F : Vec 2 → Fin 2 → ℝ) (C : ℝ)
    (hpartial : ∀ N, ∑ i : Fin 2,
      partialEnergy Q (Real.sqrt 3) N (fun x => F x i) ≤ C) :
    vectorPositiveHaarNorm Q F ^ 2 ≤ C := by
  let q : ℝ := Real.sqrt 3
  let a : ℕ → ℝ := fun k => ∑ i : Fin 2,
    q ^ k * energy Q (cubeIncrement Q k (fun x => F x i))
  have hq : 0 < q := Real.sqrt_pos.2 (by norm_num)
  have ha (k : ℕ) : 0 ≤ a k := by
    dsimp [a]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (pow_nonneg hq.le _) (energy_nonneg Q _)
  have hpartialEq (N : ℕ) :
      (∑ k ∈ Finset.range (N + 1), a k) =
        ∑ i : Fin 2, partialEnergy Q q N (fun x => F x i) := by
    change (∑ k ∈ Finset.range (N + 1), ∑ i : Fin 2,
        q ^ k * energy Q (cubeIncrement Q k (fun x => F x i))) =
      ∑ i : Fin 2, ∑ k ∈ Finset.range (N + 1),
        q ^ k * energy Q (cubeIncrement Q k (fun x => F x i))
    rw [Finset.sum_comm]
  have hsumBound (n : ℕ) : (∑ k ∈ Finset.range n, a k) ≤ C := by
    calc
      (∑ k ∈ Finset.range n, a k) ≤
          ∑ k ∈ Finset.range (n + 1), a k :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ n))
          (by intro k hk hkn; exact ha k)
      _ = ∑ i : Fin 2, partialEnergy Q q n (fun x => F x i) := hpartialEq n
      _ ≤ C := by simpa [q] using hpartial n
  have has : Summable a := summable_of_sum_range_le ha hsumBound
  have htail : Summable (fun k : ℕ => q ^ (k + 1) *
      (∑ i : Fin 2, energy Q (cubeIncrement Q (k + 1) (fun x => F x i)))) := by
    have htail' : Summable (fun k : ℕ => a (k + 1)) :=
      (summable_nat_add_iff 1).2 has
    simpa [a, ← Finset.mul_sum] using htail'
  have htailCoord (i : Fin 2) :
      Summable (fun k : ℕ => q ^ (k + 1) *
        energy Q (cubeIncrement Q (k + 1) (fun x => F x i))) := by
    apply htail.of_nonneg_of_le
    · intro k
      exact mul_nonneg (pow_nonneg hq.le _) (energy_nonneg Q _)
    · intro k
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq.le _)
      exact Finset.single_le_sum
        (fun j _ => energy_nonneg Q (cubeIncrement Q (k + 1) (fun x => F x j)))
        (Finset.mem_univ i)
  have hlim : Tendsto
      (fun N => ∑ i : Fin 2, partialEnergy Q q N (fun x => F x i))
      atTop (𝓝 (vectorPositiveHaarNorm Q F ^ 2)) := by
    have hsum := tendsto_finsetSum Finset.univ fun i _ =>
      partialEnergy_tendsto Q q (fun x => F x i) (htailCoord i)
    have hvalue : (∑ i : Fin 2, primalEnergy Q q (fun x => F x i)) =
        vectorPositiveHaarNorm Q F ^ 2 := by
      rw [vectorPositiveHaarNorm_sq]
      apply Finset.sum_congr rfl
      intro i hi
      rw [positiveHaarNorm, Real.sq_sqrt
        (primalEnergy_nonneg Q q (Real.sqrt_nonneg 3) (fun x => F x i))]
    rw [← hvalue]
    exact hsum
  exact le_of_tendsto_of_tendsto' hlim tendsto_const_nhds hpartial

theorem partialEnergy_congr_ae
    (Q : TriadicCube 2) (q : ℝ) (N : ℕ) {f g : Vec 2 → ℝ}
    (hfg : f =ᵐ[normalizedCubeMeasure Q] g) :
    partialEnergy Q q N f = partialEnergy Q q N g := by
  unfold partialEnergy
  apply Finset.sum_congr rfl
  intro k hk
  rw [cubeIncrement_congr_ae Q k hfg]

theorem vectorPositiveHaarNorm_sq_congr_ae
    (Q : TriadicCube 2) {F G : Vec 2 → Fin 2 → ℝ}
    (hFG : ∀ i, (fun x => F x i) =ᵐ[normalizedCubeMeasure Q]
      (fun x => G x i)) :
    vectorPositiveHaarNorm Q F ^ 2 = vectorPositiveHaarNorm Q G ^ 2 := by
  rw [vectorPositiveHaarNorm_sq Q F, vectorPositiveHaarNorm_sq Q G]
  apply Finset.sum_congr rfl
  intro i hi
  have hE (k : ℕ) : energy Q (cubeIncrement Q k (fun x => F x i)) =
      energy Q (cubeIncrement Q k (fun x => G x i)) :=
    congrArg (energy Q) (cubeIncrement_congr_ae Q k (hFG i))
  have hP : primalEnergy Q (Real.sqrt 3) (fun x => F x i) =
      primalEnergy Q (Real.sqrt 3) (fun x => G x i) := by
    unfold primalEnergy
    rw [hE 0]
    congr 1
    apply tsum_congr
    intro k
    rw [hE (k + 1)]
  simp only [positiveHaarNorm, hP]

theorem vectorPositiveHaarNorm_sq_lsc_of_l2_tendsto_h1
    (Q : TriadicCube 2)
    (fseq : ℕ → Fin 2 → Lp ℝ 2 (normalizedCubeMeasure Q))
    (f : Fin 2 → Lp ℝ 2 (normalizedCubeMeasure Q))
    (rawseq : ℕ → Fin 2 → Vec 2 → ℝ)
    (Gseq : ℕ → Fin 2 → Vec 2 → Vec 2)
    (hseq : ∀ i, Tendsto (fun n => fseq n i) atTop (𝓝 (f i)))
    (hrep : ∀ n i, (fun x => fseq n i x) =ᵐ[normalizedCubeMeasure Q]
      rawseq n i)
    (hG : ∀ n i j, MemLp (fun x => Gseq n i x j) 2 (normalizedCubeMeasure Q))
    (hweak : ∀ n i, HasWeakGradientOn (openCubeSet Q)
      (rawseq n i) (Gseq n i)) :
    ENNReal.ofReal (vectorPositiveHaarNorm Q (fun x i => f i x) ^ 2) ≤
      Filter.liminf
        (fun n => ENNReal.ofReal
          (vectorPositiveHaarNorm Q (fun x i => fseq n i x) ^ 2)) atTop := by
  let q : ℝ := Real.sqrt 3
  let P : ℕ → ℝ := fun N => ∑ i : Fin 2,
    partialEnergy Q q N (fun x => f i x)
  let L : ℝ≥0∞ := Filter.liminf
    (fun n => ENNReal.ofReal
      (vectorPositiveHaarNorm Q (fun x i => fseq n i x) ^ 2)) atTop
  have hpartialTendsto (N : ℕ) :
      Tendsto (fun n => ∑ i : Fin 2,
        partialEnergy Q q N (fun x => fseq n i x)) atTop (𝓝 (P N)) := by
    have hsum := tendsto_finsetSum Finset.univ fun i _ =>
      partialEnergy_tendsto_of_l2_tendsto Q q N
        (fun n => fseq n i) (f i) (hseq i)
    simpa [P] using hsum
  have hpartialBound (N n : ℕ) :
      (∑ i : Fin 2, partialEnergy Q q N (fun x => fseq n i x)) ≤
        vectorPositiveHaarNorm Q (fun x i => fseq n i x) ^ 2 := by
    calc
      (∑ i : Fin 2, partialEnergy Q q N (fun x => fseq n i x)) =
          ∑ i : Fin 2, partialEnergy Q q N (rawseq n i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact partialEnergy_congr_ae Q q N (hrep n i)
      _ ≤ ∑ i : Fin 2, positiveHaarNorm Q (rawseq n i) ^ 2 :=
        Finset.sum_le_sum fun i hi =>
          partialEnergy_le_positiveHaarNorm_sq_of_h1 Q
            (by
              have hraw : MemLp (fun x => fseq n i x) 2 (normalizedCubeMeasure Q) :=
                Lp.memLp (fseq n i)
              exact (memLp_congr_ae (hrep n i)).mp hraw)
            (fun j => hG n i j) (hweak n i) N
      _ = vectorPositiveHaarNorm Q (fun x i => fseq n i x) ^ 2 :=
        (vectorPositiveHaarNorm_sq Q (fun x i => rawseq n i x)).symm.trans
          (@vectorPositiveHaarNorm_sq_congr_ae Q
            (fun x i => rawseq n i x)
            (fun x i => fseq n i x)
            (fun i => (hrep n i).symm))
  have hpartialFatou (N : ℕ) : ENNReal.ofReal (P N) ≤ L := by
    have hENN : Tendsto
        (fun n => ENNReal.ofReal
          (∑ i : Fin 2, partialEnergy Q q N (fun x => fseq n i x))) atTop
        (𝓝 (ENNReal.ofReal (P N))) :=
      (ENNReal.continuous_ofReal.continuousAt.tendsto).comp (hpartialTendsto N)
    have hmono : Filter.liminf
        (fun n => ENNReal.ofReal
          (∑ i : Fin 2, partialEnergy Q q N (fun x => fseq n i x))) atTop ≤ L := by
      dsimp [L]
      exact Filter.liminf_le_liminf
        (Filter.Eventually.of_forall fun n => ENNReal.ofReal_le_ofReal
          (hpartialBound N n))
    calc
      ENNReal.ofReal (P N) = Filter.liminf
          (fun n => ENNReal.ofReal
            (∑ i : Fin 2, partialEnergy Q q N (fun x => fseq n i x))) atTop :=
        hENN.liminf_eq.symm
      _ ≤ L := hmono
  by_cases hL : L = ⊤
  · change ENNReal.ofReal
      (vectorPositiveHaarNorm Q (fun x i => f i x) ^ 2) ≤ L
    rw [hL]
    exact le_top
  · have hLC : ENNReal.ofReal L.toReal = L := ENNReal.ofReal_toReal hL
    have hpartialReal (N : ℕ) : P N ≤ L.toReal := by
      have hle : ENNReal.ofReal (P N) ≤ ENNReal.ofReal L.toReal := by
        simpa only [hLC] using hpartialFatou N
      exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp hle
    have hnorm : vectorPositiveHaarNorm Q (fun x i => f i x) ^ 2 ≤ L.toReal :=
      vectorPositiveHaarNorm_sq_le_of_partial_bounds Q
        (fun x i => f i x) L.toReal hpartialReal
    calc
      ENNReal.ofReal (vectorPositiveHaarNorm Q (fun x i => f i x) ^ 2) ≤
          ENNReal.ofReal L.toReal := ENNReal.ofReal_le_ofReal hnorm
      _ = L := hLC

/-- The finite source product's physical L² coordinate is the coordinate of
its actual finite H¹ product representative. -/
theorem flat_source_q3_finite_product_component_ae
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (e : Vec 2) (N : ℕ) (ω : ℕ → ℝ) (β : ℝ)
    (L : {l : ℝ // 0 < l}) (i : Fin 2) :
    (fun x =>
      ((flatSourceQ3ValueLInf Q hab hcd β L
          (gaussianPartialSum
            (q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis) N ω) •
        flatSourceQ3ProjectedL2 Q hab hcd e β L
          (gaussianPartialSum
            (q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis) N ω)) x).toVec i) =ᵐ[
        volumeMeasureOn (openCubeSet Q)]
      (flatSourceQ3FiniteProductComponent Q β L e N ω i).toFun := by
  classical
  let μ := volumeMeasureOn (openCubeSet Q)
  let dirs := q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis
  have hscalar := flat_source_q3_value_partial_sum_ae
    Q hab hcd N ω β L
  have hscalar' :
      flatSourceQ3ValueLInf Q hab hcd β L (gaussianPartialSum dirs N ω) =ᵐ[μ]
        flatSourceQ3FiniteScalar β L N ω := by
    filter_upwards [hscalar, ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx hxQ
    rw [hx]
    unfold flatSourceQ3FiniteScalar gaussianScalarPartialSum
    apply Finset.sum_congr rfl
    intro n hn
    have hmode :
        q3H3RangeValue a₀ b₀ c₀ d₀ β L (dirs n)
            (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x) =
          flatSourceQ3FiniteValueMode β L n x := by
      let := Encodable.ofCountable whiteBasisIndex
      by_cases henc : n ∈ Set.range (Encodable.encode : whiteBasisIndex → ℕ)
      · obtain ⟨j, rfl⟩ := henc
        dsimp [dirs, q3H3Directions, flatSourceQ3FiniteValueMode]
        rw [enumerated_encode,
          q3H3RangeValue_factor a₀ b₀ c₀ d₀ β hab hcd L]
        rw [lambda8CovarianceClamp_eq_of_mem a₀ b₀ c₀ d₀ hab hcd (hQ hxQ)]
        rw [q3Convolution, enumerated_encode]
      · have hdir : dirs n = 0 := by
          dsimp [dirs, q3H3Directions]
          exact Function.extend_apply' _ _ _ henc
        have hzero : gaussEnumerated whiteBasis n = 0 := by
          dsimp [gaussEnumerated]
          exact Function.extend_apply' _ _ _ henc
        rw [hdir, map_zero]
        simp [flatSourceQ3FiniteValueMode, hzero, q3Convolution]
    have hmode' :
        q3H3RangeValue a₀ b₀ c₀ d₀ β L
            (q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis n)
            (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x) =
          flatSourceQ3FiniteValueMode β L n x := by
      simpa [dirs] using hmode
    change ω n * q3H3RangeValue a₀ b₀ c₀ d₀ β L
        (q3H3Directions a₀ b₀ c₀ d₀ β L whiteBasis n)
        (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x) =
      ω n * flatSourceQ3FiniteValueMode β L n x
    exact congrArg (fun z : ℝ => ω n * z) hmode'
  have hprojected := flat_source_q3_projected_partial_sum_component_ae
    Q hab hcd e N ω β L i
  have hprojectedMode (n : ℕ) :
      (fun x => (flatSourceQ3ProjectedL2 Q hab hcd e β L
        (dirs n) x).toVec i) =ᵐ[μ]
        fun x => flatSourceQ3FiniteProjectedMode Q β L e i n x := by
    simpa [dirs, flatSourceQ3FiniteProjectedMode] using
      flat_source_q3_projected_direction_component_eq_parent_mode_ae
        Q hab hcd hQ e β L n i
  have hprojected' :
      (fun x => (flatSourceQ3ProjectedL2 Q hab hcd e β L
        (gaussianPartialSum dirs N ω) x).toVec i) =ᵐ[μ]
        flatSourceQ3FiniteProjectedComponent Q β L e N ω i := by
    have hmodes : ∀ᵐ x ∂μ, ∀ n,
        (flatSourceQ3ProjectedL2 Q hab hcd e β L (dirs n) x).toVec i =
          flatSourceQ3FiniteProjectedMode Q β L e i n x := by
      rw [ae_all_iff]
      intro n
      exact hprojectedMode n
    filter_upwards [hprojected, hmodes] with x hx hmodes
    rw [hx, flat_source_q3_finite_projected_component_value]
    unfold gaussianScalarPartialSum
    apply Finset.sum_congr rfl
    intro n hn
    exact congrArg (fun z : ℝ => ω n * z) (hmodes n)
  filter_upwards [Lp.coeFn_lpSMul (r := 2)
      (flatSourceQ3ValueLInf Q hab hcd β L (gaussianPartialSum dirs N ω))
      (flatSourceQ3ProjectedL2 Q hab hcd e β L (gaussianPartialSum dirs N ω)),
    hscalar', hprojected'] with x hsmul hval hload
  have hsmul' :
      (flatSourceQ3ValueLInf Q hab hcd β L (gaussianPartialSum dirs N ω) •
        flatSourceQ3ProjectedL2 Q hab hcd e β L (gaussianPartialSum dirs N ω)) x =
        flatSourceQ3ValueLInf Q hab hcd β L (gaussianPartialSum dirs N ω) x •
          flatSourceQ3ProjectedL2 Q hab hcd e β L (gaussianPartialSum dirs N ω) x := by
    simpa only [Pi.smul_apply'] using hsmul
  rw [hsmul']
  change flatSourceQ3ValueLInf Q hab hcd β L (gaussianPartialSum dirs N ω) x *
      (flatSourceQ3ProjectedL2 Q hab hcd e β L
        (gaussianPartialSum dirs N ω) x).toVec i = _
  rw [hval, hload]
  rw [flat_source_q3_finite_product_component_toFun]

end ASDExplicitGamma.Scalar
