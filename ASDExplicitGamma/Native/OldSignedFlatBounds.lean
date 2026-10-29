module

public import ASDExplicitGamma.Native.OldSignedAffineReciprocalBounds
public import ASDExplicitGamma.Native.OldSignedFlatAffine
public import ASDExplicitGamma.Native.OldSignedHodgeFields
public import ASDExplicitGamma.Triadic.DiagEnergyCongr
public import ASDExplicitGamma.Triadic.HaarNormTriangle
public import ASDExplicitGamma.Triadic.VectorHaarSymmetry
public import ASDExplicitGamma.Variational.ForcedSourceFeedback

/-! OLD flat projection bounds for the actual weighted minimizer. -/
@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Response Scalar Triadic Variational
open scoped BigOperators RealInnerProductSpace

noncomputable section

private theorem old_signed_weakHaarNorm_add_le (Q : TriadicCube 2)
    {f g : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    weakHaarNorm Q (fun x => f x + g x) ≤ weakHaarNorm Q f + weakHaarNorm Q g := by
  let w := (Real.sqrt 3)⁻¹
  let c₀ := 1 - w
  let weight (n : ℕ) := c₀ * w ^ n
  let a (n : ℕ) := Real.sqrt (weight n * energy Q (cubeProjection Q n f))
  let b (n : ℕ) := Real.sqrt (weight n * energy Q (cubeProjection Q n g))
  let c (n : ℕ) := Real.sqrt (weight n *
    energy Q (cubeProjection Q n (fun x => f x + g x)))
  have hroot : 1 < Real.sqrt 3 := by
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      Real.sqrt_nonneg (3 : ℝ)]
  have hw : 0 ≤ w := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hc₀ : 0 ≤ c₀ := by
    dsimp [c₀, w]
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hroot.le)
  have hweight (n : ℕ) : 0 ≤ weight n :=
    mul_nonneg hc₀ (pow_nonneg hw n)
  have hsf' : Summable (fun n : ℕ => w ^ n * energy Q (cubeProjection Q n f)) := by
    simpa only [w] using summable_weighted_projections Q hroot hf
  have hsg' : Summable (fun n : ℕ => w ^ n * energy Q (cubeProjection Q n g)) := by
    simpa only [w] using summable_weighted_projections Q hroot hg
  have hsf : Summable (fun n : ℕ => weight n * energy Q (cubeProjection Q n f)) := by
    convert hsf'.mul_left c₀ using 1
    ext n
    simp [weight, mul_assoc]
  have hsg : Summable (fun n : ℕ => weight n * energy Q (cubeProjection Q n g)) := by
    convert hsg'.mul_left c₀ using 1
    ext n
    simp [weight, mul_assoc]
  have hsq (u : Vec 2 → ℝ) (n : ℕ) :
      (Real.sqrt (weight n * energy Q (cubeProjection Q n u))) ^ 2 =
        weight n * energy Q (cubeProjection Q n u) :=
    Real.sq_sqrt (mul_nonneg (hweight n) (energy_nonneg Q _))
  have has : Summable (fun n : ℕ => (a n) ^ 2) := by
    simpa only [a, hsq] using hsf
  have hbs : Summable (fun n : ℕ => (b n) ^ 2) := by
    simpa only [b, hsq] using hsg
  have hpoint (n : ℕ) : c n ≤ a n + b n := by
    have h := hilbertL2Norm_add_le Q (projection_memLp Q n f 2)
      (projection_memLp Q n g 2)
    simp only [hilbertL2Norm, hilbertEnergy_real] at h
    dsimp [a, b, c]
    rw [projection_add Q n hf hg]
    rw [Real.sqrt_mul (hweight n), Real.sqrt_mul (hweight n), Real.sqrt_mul (hweight n)]
    simpa only [mul_add] using mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg (weight n))
  have hseries := sqrt_tsum_sq_le_of_pointwise has hbs
    (fun n => Real.sqrt_nonneg _) hpoint
  have hsc : Summable (fun n : ℕ => weight n *
      energy Q (cubeProjection Q n (fun x => f x + g x))) := by
    simpa only [c, hsq] using hseries.1
  have hsf'' : Summable (fun n : ℕ => w ^ n * energy Q (cubeProjection Q n
      (fun x => f x + g x))) := by
    have hwlt : w < 1 := (inv_lt_one₀ (Real.sqrt_pos.2 (by norm_num))).2 hroot
    have hc₀pos : 0 < c₀ := sub_pos.mpr hwlt
    have htmp := hsc.mul_left c₀⁻¹
    convert htmp using 1
    ext n
    dsimp [weight]
    field_simp [ne_of_gt hc₀pos]
  have hdualF := dualEnergy_eq_weighted_projections Q hroot hf
    (by simpa only [w] using hsf')
  have hdualG := dualEnergy_eq_weighted_projections Q hroot hg
    (by simpa only [w] using hsg')
  have hdualFG : dualEnergy Q (Real.sqrt 3) (fun x => f x + g x) =
      (1 - w) * ∑' n : ℕ, w ^ n * energy Q
        (cubeProjection Q n (fun x => f x + g x)) := by
    exact dualEnergy_eq_weighted_projections Q hroot
      (show MemLp (fun x => f x + g x) 2 (normalizedCubeMeasure Q) from hf.add hg)
      hsf''
  have hsumA : (∑' n : ℕ, (a n) ^ 2) =
      (1 - w) * ∑' n : ℕ, w ^ n * energy Q (cubeProjection Q n f) := by
    calc
      _ = ∑' n : ℕ, c₀ *
          (w ^ n * energy Q (cubeProjection Q n f)) := by
        apply tsum_congr
        intro n
        calc
          (a n) ^ 2 = weight n * energy Q (cubeProjection Q n f) := hsq f n
          _ = c₀ * (w ^ n * energy Q (cubeProjection Q n f)) := by ring
      _ = c₀ * ∑' n : ℕ, w ^ n * energy Q (cubeProjection Q n f) := tsum_mul_left
      _ = _ := by rfl
  have hsumB : (∑' n : ℕ, (b n) ^ 2) =
      (1 - w) * ∑' n : ℕ, w ^ n * energy Q (cubeProjection Q n g) := by
    calc
      _ = ∑' n : ℕ, c₀ *
          (w ^ n * energy Q (cubeProjection Q n g)) := by
        apply tsum_congr
        intro n
        calc
          (b n) ^ 2 = weight n * energy Q (cubeProjection Q n g) := hsq g n
          _ = c₀ * (w ^ n * energy Q (cubeProjection Q n g)) := by ring
      _ = c₀ * ∑' n : ℕ, w ^ n * energy Q (cubeProjection Q n g) := tsum_mul_left
      _ = _ := by rfl
  have hsumC : (∑' n : ℕ, (c n) ^ 2) =
      (1 - w) * ∑' n : ℕ, w ^ n * energy Q
        (cubeProjection Q n (fun x => f x + g x)) := by
    calc
      _ = ∑' n : ℕ, c₀ *
          (w ^ n * energy Q (cubeProjection Q n (fun x => f x + g x))) := by
        apply tsum_congr
        intro n
        calc
          (c n) ^ 2 = weight n *
              energy Q (cubeProjection Q n (fun x => f x + g x)) := hsq (fun x => f x + g x) n
          _ = c₀ * (w ^ n *
              energy Q (cubeProjection Q n (fun x => f x + g x))) := by ring
      _ = c₀ * ∑' n : ℕ, w ^ n * energy Q
          (cubeProjection Q n (fun x => f x + g x)) := tsum_mul_left
      _ = _ := by rfl
  have hrootBound : Real.sqrt (∑' n : ℕ, (c n) ^ 2) ≤
      Real.sqrt (∑' n : ℕ, (a n) ^ 2) + Real.sqrt (∑' n : ℕ, (b n) ^ 2) :=
    hseries.2
  have hnormF : weakHaarNorm Q f = Real.sqrt (∑' n : ℕ, (a n) ^ 2) := by
    unfold weakHaarNorm
    rw [hdualF, ← hsumA]
  have hnormG : weakHaarNorm Q g = Real.sqrt (∑' n : ℕ, (b n) ^ 2) := by
    unfold weakHaarNorm
    rw [hdualG, ← hsumB]
  have hnormFG : weakHaarNorm Q (fun x => f x + g x) =
      Real.sqrt (∑' n : ℕ, (c n) ^ 2) := by
    unfold weakHaarNorm
    rw [hdualFG, ← hsumC]
  rw [hnormFG, hnormF, hnormG]
  exact hrootBound

private theorem old_signed_vectorWeakHaarNorm_add_le (Q : TriadicCube 2)
    {f g : Vec 2 → Vec 2}
    (hf : ∀ i : Fin 2, MemLp (fun x => f x i) 2 (normalizedCubeMeasure Q))
    (hg : ∀ i : Fin 2, MemLp (fun x => g x i) 2 (normalizedCubeMeasure Q)) :
    vectorWeakHaarNorm Q (fun x i => f x i + g x i) ≤
      vectorWeakHaarNorm Q f + vectorWeakHaarNorm Q g := by
  let a (i : Fin 2) := weakHaarNorm Q (fun x => f x i)
  let b (i : Fin 2) := weakHaarNorm Q (fun x => g x i)
  let c (i : Fin 2) := weakHaarNorm Q (fun x => f x i + g x i)
  have hpoint (i : Fin 2) : c i ≤ a i + b i :=
    old_signed_weakHaarNorm_add_le Q (hf i) (hg i)
  have hsum : (∑ i : Fin 2, c i ^ 2) ≤ ∑ i : Fin 2, (a i + b i) ^ 2 :=
    Finset.sum_le_sum fun i hi => pow_le_pow_left₀ (Real.sqrt_nonneg _) (hpoint i) 2
  have h1 := Real.sqrt_le_sqrt hsum
  have h2 := sqrt_finset_sq_add_le Finset.univ a b
  have hfid (u : Vec 2 → Vec 2) :
      vectorWeakHaarNorm Q u =
        Real.sqrt (∑ i : Fin 2, weakHaarNorm Q (fun x => u x i) ^ 2) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp
    change (vectorWeakHaarNorm Q u) ^ 2 = _
    rw [vectorWeakHaarNorm_sq]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i hi => sq_nonneg
      (weakHaarNorm Q (fun x => u x i)))]
  calc
    vectorWeakHaarNorm Q (fun x i => f x i + g x i) = Real.sqrt (∑ i : Fin 2, c i ^ 2) := by
      simpa only [c] using hfid (fun x i => f x i + g x i)
    _ ≤ Real.sqrt (∑ i : Fin 2, (a i + b i) ^ 2) := h1
    _ ≤ Real.sqrt (∑ i : Fin 2, a i ^ 2) + Real.sqrt (∑ i : Fin 2, b i ^ 2) := h2
    _ = vectorWeakHaarNorm Q f + vectorWeakHaarNorm Q g := by rw [← hfid, ← hfid]

private theorem old_signed_vectorWeak_le_positive (Q : TriadicCube 2)
    {f : Vec 2 → Vec 2}
    (hf : ∀ i : Fin 2, MemLp (fun x => f x i) 2 (normalizedCubeMeasure Q))
    (hP : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1) (fun x => f x i)))) :
    vectorWeakHaarNorm Q f ≤ vectorPositiveHaarNorm Q f := by
  have hroot : 1 < Real.sqrt 3 := by
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      Real.sqrt_nonneg (3 : ℝ)]
  have hbase : 0 ≤ (Real.sqrt 3)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hle : (Real.sqrt 3)⁻¹ ≤ Real.sqrt 3 := by
    exact ((inv_le_one₀ (Real.sqrt_pos.2 (by norm_num))).mpr hroot.le).trans hroot.le
  have hcoord (i : Fin 2) : dualEnergy Q (Real.sqrt 3) (fun x => f x i) ≤
      primalEnergy Q (Real.sqrt 3) (fun x => f x i) := by
    unfold dualEnergy primalEnergy
    apply add_le_add_right
    have hsum := summable_dual_increments Q hroot (hf i)
    have hterm (j : ℕ) : (Real.sqrt 3)⁻¹ ^ (j + 1) *
        energy Q (cubeIncrement Q (j + 1) (fun x => f x i)) ≤
      (Real.sqrt 3) ^ (j + 1) *
        energy Q (cubeIncrement Q (j + 1) (fun x => f x i)) := by
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hbase hle (j + 1)) (energy_nonneg Q _)
    exact hsum.tsum_le_tsum hterm (hP i)
  have hE : vectorWeakHaarEnergy Q f ≤ vectorPositiveHaarEnergy Q f := by
    simp only [vectorWeakHaarEnergy, vectorPositiveHaarEnergy]
    exact Finset.sum_le_sum fun i hi => hcoord i
  unfold vectorWeakHaarNorm vectorPositiveHaarNorm
  exact Real.sqrt_le_sqrt hE

private theorem old_signed_affine_reciprocal_corrector_norm
    (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    oldSignedBlockWeakNorm Q (fun x =>
      scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma k)
        (scalarResidualField Q nu sigma hnu hsigma k
          ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P)) x - P) ≤
      Real.sqrt (6 * oldSignedCorrectorHistory Q
        (responseFramePlanarCoefficientField nu sigma k)) *
        Real.sqrt (blockVecDot P P) := by
  have hsq := old_signed_affine_reciprocal_corrector Q nu sigma hnu hsigma k P
  have hT : 0 ≤ oldSignedCorrectorHistory Q
      (responseFramePlanarCoefficientField nu sigma k) := by
    have hα : 0 ≤ Scalar.inverseHistoryDiscount :=
      Scalar.inverse_history_discount_range.1.le
    have hResp : 0 ≤ oldSignedResponseHistory Q
        (responseFramePlanarCoefficientField nu sigma k) := by
      unfold oldSignedResponseHistory
      exact ENNReal.toReal_nonneg
    have hTrace : 0 ≤ (oldSignedTraceHistory Q
        (responseFramePlanarCoefficientField nu sigma k)).toReal := ENNReal.toReal_nonneg
    unfold oldSignedCorrectorHistory
    exact mul_nonneg (mul_nonneg (by linarith) hResp) hTrace
  have hp : 0 ≤ blockVecDot P P := blockVecDot_nonneg P
  have hR : 0 ≤ Real.sqrt (6 * oldSignedCorrectorHistory Q
      (responseFramePlanarCoefficientField nu sigma k)) * Real.sqrt (blockVecDot P P) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hR2 : (Real.sqrt (6 * oldSignedCorrectorHistory Q
      (responseFramePlanarCoefficientField nu sigma k)) * Real.sqrt (blockVecDot P P)) ^ 2 =
        6 * oldSignedCorrectorHistory Q
          (responseFramePlanarCoefficientField nu sigma k) * blockVecDot P P := by
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hp]
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) hR).mp
  rw [hR2]
  exact hsq

private theorem old_signed_block_snd_weak_le (Q : TriadicCube 2)
    (F : Vec 2 → BlockVec 2) :
    vectorWeakHaarNorm Q (fun x => (F x).2) ≤ oldSignedBlockWeakNorm Q F := by
  have htop : 0 ≤ vectorWeakHaarNorm Q (fun x => (F x).1) := Real.sqrt_nonneg _
  have hbot : 0 ≤ vectorWeakHaarNorm Q (fun x => (F x).2) := Real.sqrt_nonneg _
  have hsq : (vectorWeakHaarNorm Q (fun x => (F x).2)) ^ 2 ≤
      (oldSignedBlockWeakNorm Q F) ^ 2 := by
    unfold oldSignedBlockWeakNorm
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact le_add_of_nonneg_left (sq_nonneg (vectorWeakHaarNorm Q (fun x => (F x).1)))
  exact (sq_le_sq₀ hbot (Real.sqrt_nonneg _)).mp hsq

private theorem old_signed_block_snd_positive_le' (Q : TriadicCube 2)
    (F : Vec 2 → BlockVec 2) :
    vectorPositiveHaarNorm Q (fun x => (F x).2) ≤ oldSignedBlockPositiveNorm Q F := by
  have hbot : 0 ≤ vectorPositiveHaarNorm Q (fun x => (F x).2) := Real.sqrt_nonneg _
  have hsq : (vectorPositiveHaarNorm Q (fun x => (F x).2)) ^ 2 ≤
      (oldSignedBlockPositiveNorm Q F) ^ 2 := by
    unfold oldSignedBlockPositiveNorm
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact le_add_of_nonneg_left
      (sq_nonneg (vectorPositiveHaarNorm Q (fun x => (F x).1)))
  exact (sq_le_sq₀ hbot (Real.sqrt_nonneg _)).mp hsq

private theorem old_signed_block_fst_positive_le (Q : TriadicCube 2)
    (F : Vec 2 → BlockVec 2) :
    vectorPositiveHaarNorm Q (fun x => (F x).1) ≤ oldSignedBlockPositiveNorm Q F := by
  have htop : 0 ≤ vectorPositiveHaarNorm Q (fun x => (F x).1) := Real.sqrt_nonneg _
  have hsq : (vectorPositiveHaarNorm Q (fun x => (F x).1)) ^ 2 ≤
      (oldSignedBlockPositiveNorm Q F) ^ 2 := by
    unfold oldSignedBlockPositiveNorm
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact le_add_of_nonneg_right
      (sq_nonneg (vectorPositiveHaarNorm Q (fun x => (F x).2)))
  exact (sq_le_sq₀ htop (Real.sqrt_nonneg _)).mp hsq

private theorem old_signed_vectorWeakHaarNorm_congr_ae (Q : TriadicCube 2)
    {F G : Vec 2 → Vec 2}
    (hFG : F =ᵐ[volumeMeasureOn (openCubeSet Q)] G) :
    vectorWeakHaarNorm Q F = vectorWeakHaarNorm Q G := by
  have hFG' : F =ᵐ[volume.restrict (cubeSet Q)] G := by
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
    exact hFG
  have hcoord (i : Fin 2) :
      (fun x => F x i) =ᵐ[volume.restrict (cubeSet Q)] (fun x => G x i) := by
    filter_upwards [hFG'] with x hx
    exact congrArg (fun v : Vec 2 => v i) hx
  unfold vectorWeakHaarNorm
  congr 1
  unfold vectorWeakHaarEnergy
  apply Finset.sum_congr rfl
  intro i hi
  unfold dualEnergy
  exact diagPrimalEnergy_congr_ae Q ((Real.sqrt 3)⁻¹) (hcoord i)

private theorem old_signed_block_field_mean_split' (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (F : Vec 2 → BlockVec 2) (hF : MemBlockL2 (openCubeSet Q) F) :
    let m := oldSignedBlockMean Q F
    let H := toHilbertBlockL2OfBlockField hF
    let HM := (scalarFrameRealization Q nu sigma hnu hsigma k).constantField m
    let HG := toHilbertBlockL2OfBlockField
      (hF.sub (memLp_const (oldSignedBlockMean Q F)))
    H = HM + HG := by
  dsimp
  let m := oldSignedBlockMean Q F
  let hConst : MemBlockL2 (openCubeSet Q) (fun _ : Vec 2 => m) := memLp_const m
  let hG : MemBlockL2 (openCubeSet Q) (fun x => F x - m) := hF.sub (memLp_const m)
  let HM := (scalarFrameRealization Q nu sigma hnu hsigma k).constantField m
  let HG := toHilbertBlockL2OfBlockField hG
  have hConstRaw : toHilbertBlockL2OfBlockField hConst =
      blockVecToHilbertBlockL2Const m := by
    apply Lp.ext
    filter_upwards [coeFn_toHilbertBlockL2OfBlockField hConst,
      coeFn_blockVecToHilbertBlockL2Const (U := openCubeSet Q) m] with x hx hy
    exact hx.trans hy.symm
  have hSource : toHilbertBlockL2OfBlockField hF = HM + HG := by
    apply Lp.ext
    filter_upwards [coeFn_toHilbertBlockL2OfBlockField hF,
      coeFn_toHilbertBlockL2OfBlockField hConst,
      coeFn_toHilbertBlockL2OfBlockField hG,
      MeasureTheory.Lp.coeFn_add HM HG] with x hF' hConst' hG' hsum
    have hmConst : HM x = HilbertBlockVec.ofBlockVec m := by
      have hpoint := congrArg (fun H : HilbertBlockL2 (openCubeSet Q) => H x) hConstRaw
      exact hpoint.symm.trans hConst'
    have hGpoint : HG x = HilbertBlockVec.ofBlockVec (F x - m) := by
      simpa [HG, hilbertifyBlockField] using hG'
    calc
      toHilbertBlockL2OfBlockField hF x = hilbertifyBlockField F x := hF'
      _ = Function.const (Vec 2) (HilbertBlockVec.ofBlockVec m) x +
          hilbertifyBlockField (fun x => F x - m) x := by
        apply (HilbertBlockVec.continuousLinearEquivBlockVec 2).injective
        change F x = m + (F x - m)
        abel
      _ = HM x + HG x := by
        change HilbertBlockVec.ofBlockVec m +
          HilbertBlockVec.ofBlockVec (F x - m) = HM x + HG x
        rw [← hmConst, ← hGpoint]
      _ = (HM + HG) x := by simpa [Pi.add_apply] using hsum.symm
  exact hSource

private theorem old_signed_block_field_eq_pureSecond_load (Q : TriadicCube 2)
    {G : Vec 2 → BlockVec 2} (hG : MemBlockL2 (openCubeSet Q) G)
    (hGfirst : (fun x => (G x).1) =ᵐ[volumeMeasureOn (openCubeSet Q)] 0) :
    ∃ hGsecond : MemLp (fun x => (G x).2) 2 (normalizedCubeMeasure Q),
      toHilbertBlockL2OfBlockField hG =
        Variational.projectedSourceLoad Q hGsecond := by
  let U := openCubeSet Q
  let Gsecond : Vec 2 → Vec 2 := fun x => (G x).2
  have hGsecondOpen : MemVectorL2 U Gsecond := memVectorL2_snd_of_memBlockL2 hG
  have hGsecondCoord (i : Fin 2) :
      MemLp (fun x => Gsecond x i) 2 (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hGsecondOpen i)
  have hGsecond : MemLp Gsecond 2 (normalizedCubeMeasure Q) :=
    memLp_pi_iff.mpr hGsecondCoord
  let hzero : MemVectorL2 U (0 : Vec 2 → Vec 2) := MemLp.zero
  let hGsecond' : MemVectorL2 U Gsecond :=
    memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hGsecond
  have hGfield : G =ᵐ[volumeMeasureOn U] fun x => (0, Gsecond x) := by
    filter_upwards [hGfirst] with x hx
    exact Prod.ext hx rfl
  have hComponents : toHilbertBlockL2OfBlockField hG =
      toHilbertBlockL2OfComponents hzero hGsecond' := by
    apply Lp.ext
    filter_upwards [coeFn_toHilbertBlockL2OfBlockField hG,
      coeFn_toHilbertBlockL2OfComponents hzero hGsecond', hGfield]
      with x hGval hcomponents hpoint
    calc
      toHilbertBlockL2OfBlockField hG x = hilbertifyBlockField G x := hGval
      _ = hilbertBlockField (fun _ : Vec 2 => 0) Gsecond x := by
        simp [hilbertifyBlockField, hilbertBlockField, hpoint]
      _ = toHilbertBlockL2OfComponents hzero hGsecond' x := hcomponents.symm
  have hLoadBlock : hilbertBlockL2ToBlockL2
      (Variational.projectedSourceLoad Q hGsecond) =
        toBlockL2OfComponents hzero hGsecond' := by
    apply Lp.ext
    filter_upwards [coeFn_hilbertBlockL2ToBlockL2
        (F := Variational.projectedSourceLoad Q hGsecond),
      (ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volumeMeasureOn U)
        (L := hilbertPureSecond.toContinuousLinearMap)
        (f := toHilbertVectorL2OfVecField hGsecond')),
      coeFn_toHilbertVectorL2OfVecField hGsecond',
      coeFn_toBlockL2OfComponents hzero hGsecond'] with x htransport hpure hvec hcomponents
    rw [htransport, hcomponents]
    change (hilbertPureSecondL2 U (toHilbertVectorL2OfVecField hGsecond') x).toBlockVec = _
    have hpure' : hilbertPureSecondL2 U (toHilbertVectorL2OfVecField hGsecond') x =
        hilbertPureSecond.toContinuousLinearMap (hilbertifyVecField Gsecond x) := by
      simpa [hilbertPureSecondL2, hvec] using hpure
    rw [hpure']
    simp [hilbertPureSecond, blockField, HilbertBlockVec.toBlockVec,
      hilbertifyVecField]
  have hLoad : Variational.projectedSourceLoad Q hGsecond =
      toHilbertBlockL2OfComponents hzero hGsecond' := by
    apply (continuousLinearEquivBlockL2 (U := U)).symm.injective
    calc
      hilbertBlockL2ToBlockL2 (Variational.projectedSourceLoad Q hGsecond) =
          toBlockL2OfComponents hzero hGsecond' := hLoadBlock
      _ = hilbertBlockL2ToBlockL2 (toHilbertBlockL2OfComponents hzero hGsecond') := by
        symm
        exact PotentialSolenoidalL2Data.hilbertBlockL2ToBlockL2_toHilbertBlockL2OfComponents
          (U := U) hzero hGsecond'
  exact ⟨hGsecond, hComponents.trans hLoad.symm⟩

private theorem old_signed_block_mean_first_eq_zero (Q : TriadicCube 2)
    {F : Vec 2 → BlockVec 2}
    (hfirst : (fun x => (F x).1) =ᵐ[volumeMeasureOn (openCubeSet Q)] 0) :
    (oldSignedBlockMean Q F).1 = 0 := by
  funext i
  change cubeAverage Q (fun x => (F x).1 i) = 0
  rw [cube_average_eq_volume_average_open Q]
  have hcoord : (fun x => (F x).1 i) =ᵐ[volumeMeasureOn (openCubeSet Q)] 0 := by
    filter_upwards [hfirst] with x hx
    exact congrArg (fun v : Vec 2 => v i) hx
  rw [Variational.forcedSource_volumeAverage_congr_ae hcoord]
  simp [volumeAverage]

private theorem old_signed_isSolenoidalOn_congr_ae {U : Set (Vec 2)}
    {F G : Vec 2 → Vec 2} (hFG : F =ᵐ[volumeMeasureOn U] G)
    (hF : IsSolenoidalOn U F) : IsSolenoidalOn U G := by
  intro φ
  calc
    ∫ x in U, vecDot (G x) (φ.toH1Function.grad x) ∂volume =
        ∫ x in U, vecDot (F x) (φ.toH1Function.grad x) ∂volume := by
          apply MeasureTheory.integral_congr_ae
          exact hFG.symm.mono fun x hx => by simp [hx]
    _ = 0 := hF φ

private theorem old_signed_residual_removed_variation (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    {F : Vec 2 → BlockVec 2} (hF : MemBlockL2 (openCubeSet Q) F) :
    ∃ V : Vec 2 → BlockVec 2, ScalarVariation (openCubeSet Q) V ∧
      (fun x => F x - scalarResidualField Q nu sigma hnu hsigma k
        (toHilbertBlockL2OfBlockField hF) x) =ᵐ[volumeMeasureOn (openCubeSet Q)] V := by
  let U := openCubeSet Q
  let H := toHilbertBlockL2OfBlockField hF
  let ZL := scalarResidualField Q nu sigma hnu hsigma k H
  let Z : Vec 2 → BlockVec 2 := fun x => ZL x
  let hZ : MemBlockL2 U Z := by
    simpa [Z] using (Lp.memLp ZL)
  let hRemoved : MemBlockL2 U (fun x => F x - Z x) := hF.sub hZ
  let R := scalarProjectionResidual Q nu sigma hnu hsigma k H
  have hZclass : toHilbertBlockL2OfBlockField hZ = R := by
    simpa [ZL, Z, R, H, Scalar.scalarResidualField] using
      hilbert_field_rebuild (scalarProjectionResidual Q nu sigma hnu hsigma k H)
  have hRemovedClass : toHilbertBlockL2OfBlockField hRemoved = H - R := by
    apply Lp.ext
    filter_upwards [coeFn_toHilbertBlockL2OfBlockField hRemoved,
      coeFn_toHilbertBlockL2OfBlockField hF,
      coeFn_toHilbertBlockL2OfBlockField hZ,
      MeasureTheory.Lp.coeFn_sub H R] with x hrem hfx hzx hsub
    rw [hrem, hsub]
    change hilbertifyBlockField (fun y => F y - Z y) x =
      toHilbertBlockL2OfBlockField hF x - R x
    rw [hfx]
    have hRpoint : R x = hilbertifyBlockField Z x := by
      have h := congrArg (fun A : HilbertBlockL2 U => A x) hZclass
      rw [hzx] at h
      exact h.symm
    rw [hRpoint]
    apply (HilbertBlockVec.continuousLinearEquivBlockVec 2).injective
    simp [hilbertifyBlockField]
    symm
    simpa using (HilbertBlockVec.continuousLinearEquivBlockVec 2).map_sub
      (HilbertBlockVec.ofBlockVec (F x)) (HilbertBlockVec.ofBlockVec (Z x))
  let recData := Variational.lemmaVRecoveryData (isOpenBoundedConvexDomain_openCubeSet Q)
  let muData := recData.toMuCorrectionSpaceRecoveryData
  have hRemovedMem : H - R ∈
      (scalarFrameRealization Q nu sigma hnu hsigma k).correctionSpace.correctionSpace :=
    scalar_projection_removed_mem Q nu sigma hnu hsigma k H
  have hRemovedMemClass : toHilbertBlockL2OfBlockField hRemoved ∈
      (scalarFrameRealization Q nu sigma hnu hsigma k).correctionSpace.correctionSpace := by
    rw [hRemovedClass]
    exact hRemovedMem
  have hRemovedMem' : toHilbertBlockL2OfBlockField hRemoved ∈ muData.correctionSpace.toSubmodule := by
    change hilbertBlockL2ToBlockL2 (toHilbertBlockL2OfBlockField hRemoved) ∈
      (PotentialSolenoidalL2Data.ofSubmoduleClosures U).blockPotentialZeroTraceSolenoidalZeroNormalTrace
    simpa [muData, recData, Variational.lemmaVRecoveryData,
      Scalar.scalar_frame_correction_space] using hRemovedMemClass
  let remSub : muData.correctionSpace.toSubmodule :=
    ⟨toHilbertBlockL2OfBlockField hRemoved, hRemovedMem'⟩
  let corr := muData.repr remSub
  have hcorr : corr.toHilbertBlockL2 = toHilbertBlockL2OfBlockField hRemoved := by
    simpa [remSub, muData, recData] using muData.repr_eq remSub
  have hcorrPlain : corr.toBlockL2 = toBlockL2 hRemoved := by
    apply (continuousLinearEquivBlockL2 (U := U)).injective
    calc
      blockL2ToHilbertBlockL2 corr.toBlockL2 = corr.toHilbertBlockL2 :=
        corr.blockL2ToHilbertBlockL2_toBlockL2
      _ = toHilbertBlockL2OfBlockField hRemoved := hcorr
      _ = blockL2ToHilbertBlockL2 (toBlockL2 hRemoved) := by
        exact (blockL2ToHilbertBlockL2_toBlockL2 hRemoved).symm
  have hcorrAE : corr.toBlockField =ᵐ[volumeMeasureOn U] fun x => F x - Z x :=
    (toBlockL2_eq_toBlockL2_iff corr.memBlockL2_toBlockField hRemoved).mp hcorrPlain
  refine ⟨corr.toBlockField,
    ⟨corr.memBlockL2_toBlockField, corr.isPotentialZeroTrace,
      corr.isSolenoidalZeroNormalTrace⟩, ?_⟩
  exact hcorrAE.symm

/-- Affine/oscillation projection energy for the actual OLD
weighted minimizer. Positive Haar summability is required only for the
centered source field, exactly as in AN §6.1. -/
theorem old_signed_flat_projection_energy (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (F : Vec 2 → BlockVec 2) (hF : MemBlockL2 (openCubeSet Q) F)
    (hPfst : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1)
        (fun x => (F x).1 i - (oldSignedBlockMean Q F).1 i))))
    (hPsnd : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1)
        (fun x => (F x).2 i - (oldSignedBlockMean Q F).2 i)))) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let Z := scalarResidualField Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hF)
    let m := oldSignedBlockMean Q F
    let O := oldSignedBlockPositiveNorm Q (F - fun _ => m)
    let T := oldSignedCorrectorHistory Q a
    let M := oldSignedResponseHistory Q a
    oldSignedEnergyPairing Q nu sigma k Z Z ≤
      blockVecDot m (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) m) +
        2 * Real.sqrt (6 * T) * Real.sqrt (blockVecDot m m) * O + M * O ^ 2 := by
  dsimp
  have hAffine := old_signed_affine_reciprocal_corrector_norm
    Q nu sigma hnu hsigma k (oldSignedBlockMean Q F)
  exact old_signed_flat_projection_energy_of_affine_reciprocal_corrector
    Q nu sigma hnu hsigma k F hF hPfst hPsnd hAffine

/-- The second-block reciprocal error of the actual OLD minimizer is bounded
by its affine corrector and the centered source oscillation. -/
theorem old_signed_flat_reciprocal_weak (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (F : Vec 2 → BlockVec 2) (hF : MemBlockL2 (openCubeSet Q) F)
    (hPfst : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1)
        (fun x => (F x).1 i - (oldSignedBlockMean Q F).1 i))))
    (hPsnd : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1)
        (fun x => (F x).2 i - (oldSignedBlockMean Q F).2 i)))) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let Z := scalarResidualField Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hF)
    let m := oldSignedBlockMean Q F
    let O := oldSignedBlockPositiveNorm Q (F - fun _ => m)
    let T := oldSignedCorrectorHistory Q a
    let M := oldSignedResponseHistory Q a
    let rZ x := (blockMatVecMul (blockCoeffField a x) (Z x)).2
    vectorWeakHaarNorm Q (fun x => rZ x - (F x).2) ≤
      Real.sqrt (6 * T) * Real.sqrt (blockVecDot m m) + (M + 1) * O := by
  dsimp
  let a := responseFramePlanarCoefficientField nu sigma k
  let m := oldSignedBlockMean Q F
  let G : Vec 2 → BlockVec 2 := fun x => F x - m
  let H := toHilbertBlockL2OfBlockField hF
  let HM := (scalarFrameRealization Q nu sigma hnu hsigma k).constantField m
  let hG : MemBlockL2 (openCubeSet Q) G := hF.sub (memLp_const m)
  let HG := toHilbertBlockL2OfBlockField hG
  let ZF : Vec 2 → BlockVec 2 := scalarResidualField Q nu sigma hnu hsigma k H
  let ZM : Vec 2 → BlockVec 2 := scalarResidualField Q nu sigma hnu hsigma k HM
  let ZG : Vec 2 → BlockVec 2 := scalarResidualField Q nu sigma hnu hsigma k HG
  let JM := scalarCoefficientFlux a ZM
  let JG := scalarCoefficientFlux a ZG
  let O := oldSignedBlockPositiveNorm Q G
  let T := oldSignedCorrectorHistory Q a
  let M := oldSignedResponseHistory Q a
  change vectorWeakHaarNorm Q (fun x => (scalarCoefficientFlux a ZF x).2 - (F x).2) ≤
    Real.sqrt (6 * T) * Real.sqrt (blockVecDot m m) + (M + 1) * O
  have hSource := old_signed_block_field_mean_split' Q nu sigma hnu hsigma k F hF
  have hSource' : H = HM + HG := by simpa [H, HM, HG, hG, G, m] using hSource
  have hZFclass : scalarResidualField Q nu sigma hnu hsigma k H =
      scalarResidualField Q nu sigma hnu hsigma k HM +
        scalarResidualField Q nu sigma hnu hsigma k HG := by
    rw [hSource']
    exact scalar_residual_field_add Q nu sigma hnu hsigma k HM HG
  have hZFae : ZF =ᵐ[volumeMeasureOn (openCubeSet Q)]
      (fun x => ZM x + ZG x) := by
    have hclass := Lp.ext_iff.mp hZFclass
    have hadd := MeasureTheory.Lp.coeFn_add
      (scalarResidualField Q nu sigma hnu hsigma k HM)
      (scalarResidualField Q nu sigma hnu hsigma k HG)
    filter_upwards [hclass, hadd] with x hx haddx
    exact hx.trans haddx
  have hFluxAddAE : scalarCoefficientFlux a ZF =ᵐ[volumeMeasureOn (openCubeSet Q)]
      (fun x => JM x + JG x) := by
    filter_upwards [hZFae] with x hx
    change blockMatVecMul (blockCoeffField a x) (ZF x) =
      blockMatVecMul (blockCoeffField a x) (ZM x) +
        blockMatVecMul (blockCoeffField a x) (ZG x)
    rw [hx, blockMatVecMul_add]
  have hFsplit (x : Vec 2) : F x = m + G x := by
    dsimp [G]
    abel
  have hDiffAE : (fun x => (scalarCoefficientFlux a ZF x).2 - (F x).2) =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      (fun x => ((JM x).2 - m.2) + ((JG x).2 - (G x).2)) := by
    filter_upwards [hFluxAddAE] with x hx
    rw [hx, hFsplit x]
    change (JM x).2 + (JG x).2 - (m.2 + (G x).2) = _
    abel
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  have hGM : MemBlockL2 (openCubeSet Q) G := hG
  have hJM : MemBlockL2 (openCubeSet Q) JM := by
    have hZM : MemBlockL2 (openCubeSet Q)
        (scalarResidualField Q nu sigma hnu hsigma k HM) := Lp.memLp _
    apply scalar_coefficient_flux_memL2 Q a hEll
    simpa [ZM] using hZM
  have hJG : MemBlockL2 (openCubeSet Q) JG := by
    have hZG : MemBlockL2 (openCubeSet Q)
        (scalarResidualField Q nu sigma hnu hsigma k HG) := Lp.memLp _
    apply scalar_coefficient_flux_memL2 Q a hEll
    simpa [ZG] using hZG
  have hJMcoord (i : Fin 2) : MemLp (fun x => (JM x).2 i) 2
      (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hJM) i)
  have hJGcoord (i : Fin 2) : MemLp (fun x => (JG x).2 i) 2
      (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hJG) i)
  have hGcoord (i : Fin 2) : MemLp (fun x => (G x).2 i) 2
      (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hGM) i)
  have hAffine := old_signed_affine_reciprocal_corrector_norm
    Q nu sigma hnu hsigma k m
  have hAffine2 (i : Fin 2) : MemLp (fun x => (JM x).2 i - m.2 i) 2
      (normalizedCubeMeasure Q) := (hJMcoord i).sub (memLp_const (m.2 i))
  have hAffineWeak : vectorWeakHaarNorm Q (fun x => (JM x).2 - m.2) ≤
      Real.sqrt (6 * T) * Real.sqrt (blockVecDot m m) := by
    have hle := old_signed_block_snd_weak_le Q (fun x => JM x - m)
    have hle' : vectorWeakHaarNorm Q (fun x => (JM x).2 - m.2) ≤
        oldSignedBlockWeakNorm Q (fun x => JM x - m) := by
      simpa using hle
    have hrec := hle'.trans hAffine
    simpa [T, a, JM, ZM, HM] using hrec
  have hSourceEnergy : oldSignedEnergyPairing Q nu sigma k ZG ZG ≤ M * O ^ 2 := by
    have h := old_signed_flat_source_energy Q nu sigma hnu hsigma k G hGM
      (by simpa [G, m] using hPfst) (by simpa [G, m] using hPsnd)
    simpa [M, O, a, G, HG, ZG] using h
  have hFluxWeak : oldSignedBlockWeakNorm Q JG ^ 2 ≤
      M * oldSignedEnergyPairing Q nu sigma k ZG ZG := by
    have h := old_signed_flux_weak_history_bound Q nu sigma hnu hsigma k HG
    have hAvg : cubeAverage Q (fun x => blockVecDot (ZG x) (JG x)) =
        oldSignedEnergyPairing Q nu sigma k ZG ZG := by
      unfold oldSignedEnergyPairing
      exact cube_average_eq_volume_average_open Q _
    change oldSignedBlockWeakNorm Q JG ^ 2 ≤
      oldSignedResponseHistory Q a * cubeAverage Q
        (fun x => blockVecDot (ZG x) (JG x)) at h
    rw [hAvg] at h
    simpa [M, a] using h
  have hM : 0 ≤ M := by
    dsimp [M, oldSignedResponseHistory]
    exact ENNReal.toReal_nonneg
  have hFluxBound : oldSignedBlockWeakNorm Q JG ≤ M * O := by
    have hsq : (oldSignedBlockWeakNorm Q JG) ^ 2 ≤ (M * O) ^ 2 := by
      calc
        _ ≤ M * (M * O ^ 2) := by
          exact (hFluxWeak.trans (mul_le_mul_of_nonneg_left hSourceEnergy hM))
        _ = (M * O) ^ 2 := by ring
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hM (Real.sqrt_nonneg _))).mp hsq
  have hJGWeak : vectorWeakHaarNorm Q (fun x => (JG x).2) ≤ M * O :=
    (old_signed_block_snd_weak_le Q JG).trans hFluxBound
  have hO : 0 ≤ O := Real.sqrt_nonneg _
  have hGsourceP (i : Fin 2) : Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1) (fun x => (G x).2 i))) := by
    simpa [G, m] using hPsnd i
  have hGsourceWeak : vectorWeakHaarNorm Q (fun x => (G x).2) ≤ O := by
    calc
      vectorWeakHaarNorm Q (fun x => (G x).2) ≤
          vectorPositiveHaarNorm Q (fun x => (G x).2) :=
        old_signed_vectorWeak_le_positive Q hGcoord hGsourceP
      _ ≤ oldSignedBlockPositiveNorm Q G := old_signed_block_snd_positive_le' Q G
      _ = O := rfl
  have hNeg : vectorWeakHaarNorm Q (fun x i => -(G x).2 i) =
      vectorWeakHaarNorm Q (fun x => (G x).2) := by
    unfold vectorWeakHaarNorm vectorWeakHaarEnergy
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    change dualEnergy Q (Real.sqrt 3) (fun x => -(G x).2 i) =
      dualEnergy Q (Real.sqrt 3) (fun x => (G x).2 i)
    unfold dualEnergy
    exact primalEnergy_neg Q ((Real.sqrt 3)⁻¹) (fun x => (G x).2 i)
  have hCenterDiff : vectorWeakHaarNorm Q (fun x => (JG x).2 - (G x).2) ≤
      vectorWeakHaarNorm Q (fun x => (JG x).2) +
        vectorWeakHaarNorm Q (fun x => (G x).2) := by
    have h := old_signed_vectorWeakHaarNorm_add_le Q hJGcoord
      (fun i => (hGcoord i).neg)
    calc
      vectorWeakHaarNorm Q (fun x => (JG x).2 - (G x).2) =
          vectorWeakHaarNorm Q (fun x i => (JG x).2 i + -(G x).2 i) := by
        congr 1
      _ ≤ vectorWeakHaarNorm Q (fun x => (JG x).2) +
          vectorWeakHaarNorm Q (fun x i => -(G x).2 i) := by
        simpa only [Pi.add_apply, Pi.neg_apply] using h
      _ = vectorWeakHaarNorm Q (fun x => (JG x).2) +
          vectorWeakHaarNorm Q (fun x => (G x).2) := by rw [hNeg]
  have hCenterBound : vectorWeakHaarNorm Q (fun x => (JG x).2 - (G x).2) ≤
      (M + 1) * O := by
    calc
      _ ≤ vectorWeakHaarNorm Q (fun x => (JG x).2) +
          vectorWeakHaarNorm Q (fun x => (G x).2) := hCenterDiff
      _ ≤ M * O + O := add_le_add hJGWeak hGsourceWeak
      _ = (M + 1) * O := by ring
  have hsum : vectorWeakHaarNorm Q
      (fun x => ((JM x).2 - m.2) + ((JG x).2 - (G x).2)) ≤
      vectorWeakHaarNorm Q (fun x => (JM x).2 - m.2) +
        vectorWeakHaarNorm Q (fun x => (JG x).2 - (G x).2) :=
    old_signed_vectorWeakHaarNorm_add_le Q hAffine2
      (fun i => (hJGcoord i).sub (hGcoord i))
  have hDiffNorm := old_signed_vectorWeakHaarNorm_congr_ae Q hDiffAE
  rw [hDiffNorm]
  calc
    _ ≤ vectorWeakHaarNorm Q (fun x => (JM x).2 - m.2) +
        vectorWeakHaarNorm Q (fun x => (JG x).2 - (G x).2) := hsum
    _ ≤ Real.sqrt (6 * T) * Real.sqrt (blockVecDot m m) +
        (M + 1) * O := add_le_add hAffineWeak hCenterBound

/-- For a pure-second source, the actual first reciprocal component consists
of its affine corrector and the centered pure-source feedback. -/
theorem old_signed_flat_pure_second_first_weak (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (F : Vec 2 → BlockVec 2) (hF : MemBlockL2 (openCubeSet Q) F)
    (hPfst : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1)
        (fun x => (F x).1 i - (oldSignedBlockMean Q F).1 i))))
    (hPsnd : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1)
        (fun x => (F x).2 i - (oldSignedBlockMean Q F).2 i))))
    (hfirst : (fun x => (F x).1) =ᵐ[volumeMeasureOn (openCubeSet Q)] 0) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let Z := scalarResidualField Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hF)
    let m := oldSignedBlockMean Q F
    let O := oldSignedBlockPositiveNorm Q (F - fun _ => m)
    let T := oldSignedCorrectorHistory Q a
    let B := oldSignedInverseHistory Q a
    vectorWeakHaarNorm Q (fun x => (Z x).1) ≤
      Real.sqrt T * Real.sqrt (blockVecDot m m) +
        (1 + Scalar.inverseHistoryDiscount) * B * O := by
  let a := responseFramePlanarCoefficientField nu sigma k
  let m := oldSignedBlockMean Q F
  let G : Vec 2 → BlockVec 2 := fun x => F x - m
  let Z : Vec 2 → BlockVec 2 := scalarResidualField Q nu sigma hnu hsigma k
    (toHilbertBlockL2OfBlockField hF)
  let H := toHilbertBlockL2OfBlockField hF
  let HM := (scalarFrameRealization Q nu sigma hnu hsigma k).constantField m
  let hG : MemBlockL2 (openCubeSet Q) G := hF.sub (memLp_const m)
  let HG := toHilbertBlockL2OfBlockField hG
  let ZF : Vec 2 → BlockVec 2 := scalarResidualField Q nu sigma hnu hsigma k H
  let ZM : Vec 2 → BlockVec 2 := scalarResidualField Q nu sigma hnu hsigma k HM
  let ZG : Vec 2 → BlockVec 2 := scalarResidualField Q nu sigma hnu hsigma k HG
  let O := oldSignedBlockPositiveNorm Q G
  let T := oldSignedCorrectorHistory Q a
  let B := oldSignedInverseHistory Q a
  let α := Scalar.inverseHistoryDiscount
  change vectorWeakHaarNorm Q (fun x => (Z x).1) ≤
    Real.sqrt T * Real.sqrt (blockVecDot m m) + (1 + α) * B * O
  have hmFirst : m.1 = 0 := by
    simpa [m] using old_signed_block_mean_first_eq_zero Q hfirst
  have hGfirst : (fun x => (G x).1) =ᵐ[volumeMeasureOn (openCubeSet Q)] 0 := by
    filter_upwards [hfirst] with x hx
    change (F x).1 - m.1 = 0
    rw [hx, hmFirst]
    simp
  have _hGfirstPositive (i : Fin 2) : Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1) (fun x => (G x).1 i))) := by
    simpa [G, m] using hPfst i
  have hSource := old_signed_block_field_mean_split' Q nu sigma hnu hsigma k F hF
  have hSource' : H = HM + HG := by simpa [H, HM, HG, hG, G, m] using hSource
  have hZFclass : scalarResidualField Q nu sigma hnu hsigma k H =
      scalarResidualField Q nu sigma hnu hsigma k HM +
        scalarResidualField Q nu sigma hnu hsigma k HG := by
    rw [hSource']
    exact scalar_residual_field_add Q nu sigma hnu hsigma k HM HG
  have hZFae : ZF =ᵐ[volumeMeasureOn (openCubeSet Q)] fun x => ZM x + ZG x := by
    have hclass := Lp.ext_iff.mp hZFclass
    have hadd := MeasureTheory.Lp.coeFn_add
      (scalarResidualField Q nu sigma hnu hsigma k HM)
      (scalarResidualField Q nu sigma hnu hsigma k HG)
    filter_upwards [hclass, hadd] with x hx haddx
    exact hx.trans haddx
  have hZFfirst : (fun x => (ZF x).1) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      (fun x => (ZM x).1 + (ZG x).1) := by
    filter_upwards [hZFae] with x hx
    simpa using congrArg Prod.fst hx
  have hZMmem : MemBlockL2 (openCubeSet Q) (fun x => ZM x) := by
    exact Lp.memLp (scalarResidualField Q nu sigma hnu hsigma k HM)
  have hZGmem : MemBlockL2 (openCubeSet Q) (fun x => ZG x) := by
    exact Lp.memLp (scalarResidualField Q nu sigma hnu hsigma k HG)
  have hZMcoord (i : Fin 2) : MemLp (fun x => (ZM x).1 i) 2
      (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hZMmem) i)
  have hZGcoord (i : Fin 2) : MemLp (fun x => (ZG x).1 i) 2
      (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hZGmem) i)
  have hAffineSq :
      (vectorWeakHaarNorm Q (fun x => (ZM x).1 - m.1)) ^ 2 ≤ T * blockVecDot m m := by
    simpa [T, ZM, HM, a] using old_signed_affine_first_corrector Q nu sigma hnu hsigma k m
  have hα : 0 ≤ α := Scalar.inverse_history_discount_range.1.le
  have hM : 0 ≤ oldSignedResponseHistory Q a := by
    unfold oldSignedResponseHistory
    exact ENNReal.toReal_nonneg
  have htrace : 0 ≤ (oldSignedTraceHistory Q a).toReal := ENNReal.toReal_nonneg
  have hT : 0 ≤ T := by
    dsimp [T, oldSignedCorrectorHistory]
    exact mul_nonneg (mul_nonneg (by linarith) hM) htrace
  have hmSq : 0 ≤ blockVecDot m m := blockVecDot_nonneg m
  have hAffineRoot : 0 ≤ Real.sqrt T * Real.sqrt (blockVecDot m m) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hAffineRootSq :
      (Real.sqrt T * Real.sqrt (blockVecDot m m)) ^ 2 = T * blockVecDot m m := by
    rw [mul_pow, Real.sq_sqrt hT, Real.sq_sqrt hmSq]
  have hAffineSub : vectorWeakHaarNorm Q (fun x => (ZM x).1 - m.1) ≤
      Real.sqrt T * Real.sqrt (blockVecDot m m) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hAffineRoot).mp
    rw [hAffineRootSq]
    exact hAffineSq
  have hAffine : vectorWeakHaarNorm Q (fun x => (ZM x).1) ≤
      Real.sqrt T * Real.sqrt (blockVecDot m m) := by
    simpa [hmFirst] using hAffineSub
  obtain ⟨hGsecond, hGload⟩ :=
    old_signed_block_field_eq_pureSecond_load Q hG hGfirst
  have hGsecondPos (i : Fin 2) : Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1) (fun x => (G x).2 i))) := by
    simpa [G, m] using hPsnd i
  obtain ⟨v, hv⟩ := Variational.projectedSource_firstPotential_exists
    Q nu sigma hnu hsigma k hGsecond
  have hFeedback := Variational.projectedSource_forced_feedback_bound
    Q nu sigma hnu hsigma k hGsecond hGsecondPos v hv
  have hZGload : scalarResidualField Q nu sigma hnu hsigma k HG =
      Variational.projectedSourceField Q nu sigma hnu hsigma k hGsecond := by
    simpa [HG, Variational.projectedSourceField] using
      congrArg (fun X : HilbertBlockL2 (openCubeSet Q) =>
        scalarResidualField Q nu sigma hnu hsigma k X) hGload
  have hZGfield : ZG =ᵐ[volumeMeasureOn (openCubeSet Q)]
      Variational.projectedSourceField Q nu sigma hnu hsigma k hGsecond :=
    Lp.ext_iff.mp hZGload
  have hZGfirstAE : (fun x => (ZG x).1) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      (fun x => (Variational.projectedSourceField Q nu sigma hnu hsigma k hGsecond x).1) := by
    filter_upwards [hZGfield] with x hx
    exact congrArg Prod.fst hx
  have hZGgrad : (fun x => (ZG x).1) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      v.toH1Function.grad := hZGfirstAE.trans hv
  have hFeedbackNorm := old_signed_vectorWeakHaarNorm_congr_ae Q hZGgrad
  have hB : 0 ≤ B := by
    dsimp [B, oldSignedInverseHistory, a]
    exact lemmaVInverseHistory_nonneg Q (responseFramePlanarCoefficientField nu sigma k)
      (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hαeq : α = (3 : ℝ) ^ (-(1 / 4 : ℝ)) := by
    change Scalar.inverseHistoryDiscount = (3 : ℝ) ^ (-(1 / 4 : ℝ))
    rw [Scalar.inverse_history_discount_eq,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  have hCenteredPos : vectorPositiveHaarNorm Q (fun x => (G x).2) ≤ O :=
    old_signed_block_snd_positive_le' Q G
  have hO : 0 ≤ O := Real.sqrt_nonneg _
  have hCenter : vectorWeakHaarNorm Q (fun x => (ZG x).1) ≤ (1 / 2 + α) * B * O := by
    calc
      vectorWeakHaarNorm Q (fun x => (ZG x).1) =
          vectorWeakHaarNorm Q v.toH1Function.grad := hFeedbackNorm
      _ = Real.sqrt (vectorWeakHaarEnergy Q v.toH1Function.grad) := rfl
      _ ≤ (1 / 2 + α) * B * vectorPositiveHaarNorm Q (fun x => (G x).2) := by
        simpa [hαeq, a, B, oldSignedInverseHistory, vectorWeakHaarNorm,
          vectorWeakHaarEnergy, vectorPositiveHaarNorm,
          vectorPositiveHaarEnergy] using hFeedback
      _ ≤ (1 / 2 + α) * B * O :=
        mul_le_mul_of_nonneg_left hCenteredPos (mul_nonneg (by linarith) hB)
  have hCenterCoeff : (1 / 2 + α) * B ≤ (1 + α) * B :=
    mul_le_mul_of_nonneg_right (by linarith) hB
  have hCenterFinal : vectorWeakHaarNorm Q (fun x => (ZG x).1) ≤ (1 + α) * B * O := by
    calc
      _ ≤ (1 / 2 + α) * B * O := hCenter
      _ ≤ (1 + α) * B * O := mul_le_mul_of_nonneg_right hCenterCoeff hO
  have hsum := old_signed_vectorWeakHaarNorm_add_le Q hZMcoord hZGcoord
  have hZFnorm := old_signed_vectorWeakHaarNorm_congr_ae Q hZFfirst
  rw [hZFnorm]
  calc
    vectorWeakHaarNorm Q (fun x => (ZM x).1 + (ZG x).1) ≤
        vectorWeakHaarNorm Q (fun x => (ZM x).1) + vectorWeakHaarNorm Q (fun x => (ZG x).1) := hsum
    _ ≤ Real.sqrt T * Real.sqrt (blockVecDot m m) + (1 + α) * B * O :=
      add_le_add hAffine hCenterFinal

/-- Removing the projection correction preserves the true scalar compatibility
of a centered source. The witness is recovered from the closed correction
space, so compatibility is established for the actual projection residual. -/
private theorem old_signed_centered_residual_compatible (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    {G : Vec 2 → BlockVec 2} (hG : ScalarCompatible (openCubeSet Q) G) :
    ScalarCompatible (openCubeSet Q)
      (scalarResidualField Q nu sigma hnu hsigma k
        (toHilbertBlockL2OfBlockField hG.1)) := by
  let U := openCubeSet Q
  let HG := toHilbertBlockL2OfBlockField hG.1
  let ZG := scalarResidualField Q nu sigma hnu hsigma k HG
  change ScalarCompatible U ZG
  obtain ⟨V, hV, hRemoved⟩ :=
    old_signed_residual_removed_variation Q nu sigma hnu hsigma k hG.1
  have hZGmem : MemBlockL2 U ZG := Lp.memLp ZG
  have hZGfirstAE : (fun x => (ZG x).1) =ᵐ[volumeMeasureOn U]
      ((fun x => (G x).1) + (-1 : ℝ) • fun x => (V x).1) := by
    filter_upwards [hRemoved] with x hx
    have hi := congrArg (fun X : BlockVec 2 => X.1) hx
    ext i
    have hii := congrArg (fun v : Vec 2 => v i) hi
    simp at hii ⊢
    linarith
  have hZGsecondAE : (fun x => (ZG x).2) =ᵐ[volumeMeasureOn U]
      ((fun x => (G x).2) + (-1 : ℝ) • fun x => (V x).2) := by
    filter_upwards [hRemoved] with x hx
    have hi := congrArg (fun X : BlockVec 2 => X.2) hx
    ext i
    have hii := congrArg (fun v : Vec 2 => v i) hi
    simp at hii ⊢
    linarith
  have hZGpot : IsPotentialOn U (fun x => (ZG x).1) := by
    exact old_signed_isPotentialOn_congr_ae
      (isPotentialOn_add hG.2.1
        (isPotentialOn_smul hV.2.1.isPotentialOn (-1))) hZGfirstAE.symm
  have hZGsolAdd : IsSolenoidalOn U
      ((fun x => (G x).2) + (-1 : ℝ) • fun x => (V x).2) :=
    isSolenoidalOn_add_of_memVectorL2
      (memVectorL2_snd_of_memBlockL2 hG.1)
      ((memVectorL2_snd_of_memBlockL2 hV.1).const_smul (-1 : ℝ))
      hG.2.2 (isSolenoidalOn_smul hV.2.2.isSolenoidalOn (-1 : ℝ))
  have hZGsol : IsSolenoidalOn U (fun x => (ZG x).2) :=
    old_signed_isSolenoidalOn_congr_ae hZGsecondAE.symm hZGsolAdd
  exact ⟨hZGmem, hZGpot, hZGsol⟩

/-- Compatible coercivity controls the centered first block of the actual OLD
projection. The source-energy input is the proved positive-Haar estimate. -/
private theorem old_signed_compatible_coercivity_bound (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    {Z : Vec 2 → BlockVec 2} (hZ : ScalarCompatible (openCubeSet Q) Z) :
    vectorWeakHaarEnergy Q (fun x i => (Z x).1 i) ≤
      lemmaVInverseHistory Q (responseFramePlanarCoefficientField nu sigma k)
        (Real.sqrt 3) * oldSignedEnergyPairing Q nu sigma k Z Z := by
  let U := openCubeSet Q
  let a := responseFramePlanarCoefficientField nu sigma k
  let W : BlockState 2 := ⟨fun x => (Z x).1, fun x => (Z x).2⟩
  have hWfield : W.eval = Z := by
    funext x
    exact Prod.eta _
  have hWmem : MemBlockL2 U W.eval := by
    rw [hWfield]
    exact hZ.1
  have hWpot : IsBlockPotentialOn U W := by
    change IsPotentialOn U (fun x => (W.eval x).1)
    simpa [W, BlockState.eval] using hZ.2.1
  have hWsol : IsBlockSolenoidalOn U W := by
    change IsSolenoidalOn U (fun x => (W.eval x).2)
    simpa [W, BlockState.eval] using hZ.2.2
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  have hcoercive := Variational.compatible_coercivity hEll W hWpot hWsol hWmem
  have hPair : blockPairingAverage U a W W = oldSignedEnergyPairing Q nu sigma k Z Z := by
    change volumeAverage U (fun x => blockVecDot (Z x)
      (blockMatVecMul (blockCoeffField a x) (Z x))) = _
    rfl
  calc
    _ ≤ lemmaVInverseHistory Q a (Real.sqrt 3) * blockPairingAverage U a W W := by
      simpa [Variational.compatibleInverseHistory, W, BlockState.eval, a] using hcoercive
    _ = lemmaVInverseHistory Q a (Real.sqrt 3) * oldSignedEnergyPairing Q nu sigma k Z Z := by
      rw [hPair]

private theorem old_signed_centered_energy_bound (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (ZG : Vec 2 → BlockVec 2)
    (O : ℝ)
    (hcoercive : vectorWeakHaarEnergy Q (fun x i => (ZG x).1 i) ≤
      lemmaVInverseHistory Q (responseFramePlanarCoefficientField nu sigma k)
        (Real.sqrt 3) * oldSignedEnergyPairing Q nu sigma k ZG ZG)
    (hSourceEnergy : oldSignedEnergyPairing Q nu sigma k ZG ZG ≤
      oldSignedResponseHistory Q (responseFramePlanarCoefficientField nu sigma k) * O ^ 2) :
    vectorWeakHaarEnergy Q (fun x i => (ZG x).1 i) ≤
      oldSignedInverseHistory Q (responseFramePlanarCoefficientField nu sigma k) *
        oldSignedResponseHistory Q (responseFramePlanarCoefficientField nu sigma k) * O ^ 2 := by
  let a := responseFramePlanarCoefficientField nu sigma k
  let B0 := lemmaVInverseHistory Q a (Real.sqrt 3)
  let B := oldSignedInverseHistory Q a
  let M := oldSignedResponseHistory Q a
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  have hroot : 1 < Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  have hquarter : 1 < (3 : ℝ) ^ (1 / 4 : ℝ) :=
    Real.one_lt_rpow (by norm_num) (by norm_num)
  have hquarterLe : (3 : ℝ) ^ (1 / 4 : ℝ) ≤ Real.sqrt 3 := by
    calc
      (3 : ℝ) ^ (1 / 4 : ℝ) ≤ (3 : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = Real.sqrt 3 := (Real.sqrt_eq_rpow 3).symm
  have hInvLe : (Real.sqrt 3)⁻¹ ≤ ((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹ :=
    (inv_le_inv₀ (Real.sqrt_pos.2 (by norm_num)) (by positivity)).2 hquarterLe
  have hHistory : B0 ≤ B := by
    simpa [B0, B, oldSignedInverseHistory, a] using
      lemmaVInverseHistory_le_of_inverse_discount Q hEll hroot hquarter hInvLe
  have hB0 : 0 ≤ B0 := lemmaVInverseHistory_nonneg Q a hroot
  have hM : 0 ≤ M := by
    dsimp [M, oldSignedResponseHistory]
    exact ENNReal.toReal_nonneg
  calc
    _ ≤ B0 * oldSignedEnergyPairing Q nu sigma k ZG ZG := hcoercive
    _ ≤ B0 * (M * O ^ 2) := mul_le_mul_of_nonneg_left hSourceEnergy hB0
    _ ≤ B * (M * O ^ 2) :=
      mul_le_mul_of_nonneg_right hHistory (mul_nonneg hM (sq_nonneg O))
    _ = B * M * O ^ 2 := by ring

private theorem old_signed_centered_compatible_first_bound
    (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    {G : Vec 2 → BlockVec 2} (hG : ScalarCompatible (openCubeSet Q) G)
    (hPfst : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1) (fun x => (G x).1 i))))
    (hPsnd : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1) (fun x => (G x).2 i)))) :
    vectorWeakHaarNorm Q (fun x =>
      (scalarResidualField Q nu sigma hnu hsigma k
        (toHilbertBlockL2OfBlockField hG.1) x).1) ≤
      Real.sqrt (oldSignedInverseHistory Q
        (responseFramePlanarCoefficientField nu sigma k) *
          oldSignedResponseHistory Q (responseFramePlanarCoefficientField nu sigma k)) *
        oldSignedBlockPositiveNorm Q G := by
  let U := openCubeSet Q
  let a := responseFramePlanarCoefficientField nu sigma k
  let HG := toHilbertBlockL2OfBlockField hG.1
  let ZG := scalarResidualField Q nu sigma hnu hsigma k HG
  let O := oldSignedBlockPositiveNorm Q G
  let B := oldSignedInverseHistory Q a
  let M := oldSignedResponseHistory Q a
  change vectorWeakHaarNorm Q (fun x => (ZG x).1) ≤ Real.sqrt (B * M) * O
  have hZGcompat : ScalarCompatible U ZG := by
    simpa [ZG, HG] using
      old_signed_centered_residual_compatible Q nu sigma hnu hsigma k hG
  have hSourceEnergy : oldSignedEnergyPairing Q nu sigma k ZG ZG ≤ M * O ^ 2 := by
    have h := old_signed_flat_source_energy Q nu sigma hnu hsigma k G hG.1 hPfst hPsnd
    simpa [M, O, a, HG, ZG] using h
  have hcoercive := old_signed_compatible_coercivity_bound Q nu sigma hnu hsigma k hZGcompat
  have hEnergy : vectorWeakHaarEnergy Q (fun x i => (ZG x).1 i) ≤ B * M * O ^ 2 := by
    simpa [B, M, a] using old_signed_centered_energy_bound Q nu sigma hnu hsigma k ZG O
      hcoercive hSourceEnergy
  have hB : 0 ≤ B := by
    dsimp [B, oldSignedInverseHistory, a]
    exact lemmaVInverseHistory_nonneg Q (responseFramePlanarCoefficientField nu sigma k)
      (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hM : 0 ≤ M := by
    dsimp [M, oldSignedResponseHistory]
    exact ENNReal.toReal_nonneg
  have hO : 0 ≤ O := Real.sqrt_nonneg _
  have hRootEq : Real.sqrt (B * M * O ^ 2) = Real.sqrt (B * M) * O := by
    rw [show B * M * O ^ 2 = (B * M) * O ^ 2 by ring,
      Real.sqrt_mul (mul_nonneg hB hM), Real.sqrt_sq_eq_abs, abs_of_nonneg hO]
  change Real.sqrt (vectorWeakHaarEnergy Q (fun x i => (ZG x).1 i)) ≤
    Real.sqrt (B * M) * O
  calc
    _ ≤ Real.sqrt (B * M * O ^ 2) := Real.sqrt_le_sqrt hEnergy
    _ = Real.sqrt (B * M) * O := hRootEq

private theorem old_signed_centered_source_compatible' (Q : TriadicCube 2)
    {F : Vec 2 → BlockVec 2} (hF : MemBlockL2 (openCubeSet Q) F)
    (hcompat : ScalarCompatible (openCubeSet Q) F) :
    ScalarCompatible (openCubeSet Q)
      (fun x => F x - oldSignedBlockMean Q F) := by
  let U := openCubeSet Q
  let m := oldSignedBlockMean Q F
  let G : Vec 2 → BlockVec 2 := fun x => F x - m
  have hG : MemBlockL2 U G := hF.sub (memLp_const m)
  have hU : IsOpenBoundedConvexDomain U := isOpenBoundedConvexDomain_openCubeSet Q
  have hvol : (volume U).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]
    exact (cubeVolume_pos Q).ne'
  have hConstPot : IsPotentialOn U (fun _ : Vec 2 => m.1) := by
    exact (H1Function.affineOnIsSobolevRegularDomain hU.isSobolevRegularDomain m.1).isPotentialOn
  have hConstSol : IsSolenoidalOn U (fun _ : Vec 2 => m.2) :=
    IsSolenoidalOn.const_isSolenoidalOn_of_isSobolevRegularDomain
      hU.isSobolevRegularDomain hvol m.2
  have hGpotSum : IsPotentialOn U
      ((fun x => (F x).1) + (-1 : ℝ) • fun _ : Vec 2 => m.1) :=
    isPotentialOn_add hcompat.2.1 (isPotentialOn_smul hConstPot (-1 : ℝ))
  have hGpotAE : ((fun x => (F x).1) + (-1 : ℝ) • fun _ : Vec 2 => m.1) =ᵐ[
      volumeMeasureOn U] (fun x => (G x).1) := by
    filter_upwards with x
    ext i
    simp [G]
    ring
  have hGpot : IsPotentialOn U (fun x => (G x).1) :=
    old_signed_isPotentialOn_congr_ae hGpotSum hGpotAE
  have hGsecondAdd : IsSolenoidalOn U
      ((fun x => (F x).2) + (-1 : ℝ) • fun _ : Vec 2 => m.2) :=
    isSolenoidalOn_add_of_memVectorL2
      (memVectorL2_snd_of_memBlockL2 hF) ((memVectorL2_const m.2).const_smul (-1 : ℝ))
      hcompat.2.2 (isSolenoidalOn_smul hConstSol (-1 : ℝ))
  have hGsol : IsSolenoidalOn U (fun x => (G x).2) := by
    apply old_signed_isSolenoidalOn_congr_ae ?_ hGsecondAdd
    filter_upwards with x
    ext i
    simp [G]
    ring
  exact ⟨hG, hGpot, hGsol⟩

private theorem old_signed_centered_input_first_bound (Q : TriadicCube 2)
    {G : Vec 2 → BlockVec 2} (hG : MemBlockL2 (openCubeSet Q) G)
    (hPfst : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1) (fun x => (G x).1 i)))) :
    vectorWeakHaarNorm Q (fun x => (G x).1) ≤ oldSignedBlockPositiveNorm Q G := by
  have hCoord (i : Fin 2) : MemLp (fun x => (G x).1 i) 2
      (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hG) i)
  have hSeries (i : Fin 2) : Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1) (fun x => (G x).1 i))) := hPfst i
  calc
    vectorWeakHaarNorm Q (fun x => (G x).1) ≤
        vectorPositiveHaarNorm Q (fun x => (G x).1) :=
      old_signed_vectorWeak_le_positive Q hCoord hSeries
    _ ≤ oldSignedBlockPositiveNorm Q G := old_signed_block_fst_positive_le Q G

private theorem old_signed_affine_first_residual_bound (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (m : BlockVec 2) :
    vectorWeakHaarNorm Q (fun x =>
      (scalarResidualField Q nu sigma hnu hsigma k
        ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField m) x).1 - m.1) ≤
      Real.sqrt (oldSignedCorrectorHistory Q
        (responseFramePlanarCoefficientField nu sigma k)) *
          Real.sqrt (blockVecDot m m) := by
  let a := responseFramePlanarCoefficientField nu sigma k
  let ZM := scalarResidualField Q nu sigma hnu hsigma k
    ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField m)
  let T := oldSignedCorrectorHistory Q a
  change vectorWeakHaarNorm Q (fun x => (ZM x).1 - m.1) ≤
    Real.sqrt T * Real.sqrt (blockVecDot m m)
  have hSq : (vectorWeakHaarNorm Q (fun x => (ZM x).1 - m.1)) ^ 2 ≤
      T * blockVecDot m m := by
    simpa [T, ZM, a] using old_signed_affine_first_corrector Q nu sigma hnu hsigma k m
  have hα : 0 ≤ Scalar.inverseHistoryDiscount := Scalar.inverse_history_discount_range.1.le
  have hM : 0 ≤ oldSignedResponseHistory Q a := by
    unfold oldSignedResponseHistory
    exact ENNReal.toReal_nonneg
  have hTrace : 0 ≤ (oldSignedTraceHistory Q a).toReal := ENNReal.toReal_nonneg
  have hT : 0 ≤ T := by
    dsimp [T, oldSignedCorrectorHistory]
    exact mul_nonneg (mul_nonneg (by linarith) hM) hTrace
  have hmSq : 0 ≤ blockVecDot m m := blockVecDot_nonneg m
  have hRootNonneg : 0 ≤ Real.sqrt T * Real.sqrt (blockVecDot m m) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hRootSq : (Real.sqrt T * Real.sqrt (blockVecDot m m)) ^ 2 =
      T * blockVecDot m m := by
    rw [mul_pow, Real.sq_sqrt hT, Real.sq_sqrt hmSq]
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) hRootNonneg).mp
  rw [hRootSq]
  exact hSq

private theorem old_signed_scalar_residual_first_add (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    {H H₁ H₂ : HilbertBlockL2 (openCubeSet Q)} (hH : H = H₁ + H₂) :
    (fun x => (scalarResidualField Q nu sigma hnu hsigma k H x).1) =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      (fun x => (scalarResidualField Q nu sigma hnu hsigma k H₁ x).1 +
        (scalarResidualField Q nu sigma hnu hsigma k H₂ x).1) := by
  have hclass : scalarResidualField Q nu sigma hnu hsigma k H =
      scalarResidualField Q nu sigma hnu hsigma k H₁ +
        scalarResidualField Q nu sigma hnu hsigma k H₂ := by
    rw [hH]
    exact scalar_residual_field_add Q nu sigma hnu hsigma k H₁ H₂
  have hae := Lp.ext_iff.mp hclass
  have hadd := MeasureTheory.Lp.coeFn_add
    (scalarResidualField Q nu sigma hnu hsigma k H₁)
    (scalarResidualField Q nu sigma hnu hsigma k H₂)
  have hfields : (fun x => (scalarResidualField Q nu sigma hnu hsigma k H x)) =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      (fun x => scalarResidualField Q nu sigma hnu hsigma k H₁ x +
        scalarResidualField Q nu sigma hnu hsigma k H₂ x) := by
    filter_upwards [hae, hadd] with x hx haddx
    exact hx.trans haddx
  filter_upwards [hfields] with x hx
  exact congrArg Prod.fst hx

private theorem old_signed_first_projection_split_bound (Q : TriadicCube 2)
    (m : BlockVec 2) (A C : ℝ)
    {F G : Vec 2 → BlockVec 2} {ZF ZM ZG : Vec 2 → BlockVec 2}
    (hFsplit : ∀ x, F x = m + G x)
    (hZsplit : (fun x => (ZF x).1) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      (fun x => (ZM x).1 + (ZG x).1))
    (hZM : MemBlockL2 (openCubeSet Q) ZM)
    (hZG : MemBlockL2 (openCubeSet Q) ZG)
    (hG : MemBlockL2 (openCubeSet Q) G)
    (hAffine : vectorWeakHaarNorm Q (fun x => (ZM x).1 - m.1) ≤ A)
    (hCenter : vectorWeakHaarNorm Q (fun x => (ZG x).1 - (G x).1) ≤ C) :
    vectorWeakHaarNorm Q (fun x => (ZF x).1 - (F x).1) ≤ A + C := by
  have hDiffAE : (fun x => (ZF x).1 - (F x).1) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      (fun x => ((ZM x).1 - m.1) + ((ZG x).1 - (G x).1)) := by
    filter_upwards [hZsplit] with x hx
    rw [hx, hFsplit x]
    ext i
    simp
    ring
  have hAffineCoord (i : Fin 2) : MemLp (fun x => (ZM x).1 i - m.1 i) 2
      (normalizedCubeMeasure Q) :=
    (memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2
        (memVectorL2_fst_of_memBlockL2 hZM) i)).sub (memLp_const (m.1 i))
  have hCenterCoord (i : Fin 2) : MemLp (fun x => (ZG x).1 i - (G x).1 i) 2
      (normalizedCubeMeasure Q) :=
    (memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2
        (memVectorL2_fst_of_memBlockL2 hZG) i)).sub
      (memLp_normalized_of_memL2On
        (memScalarL2_coord_of_memVectorL2
          (memVectorL2_fst_of_memBlockL2 hG) i))
  have hSumNorm := old_signed_vectorWeakHaarNorm_add_le Q hAffineCoord hCenterCoord
  have hDiffNorm := old_signed_vectorWeakHaarNorm_congr_ae Q hDiffAE
  rw [hDiffNorm]
  calc
    vectorWeakHaarNorm Q (fun x i => (ZM x).1 i - m.1 i + ((ZG x).1 i - (G x).1 i)) ≤
        vectorWeakHaarNorm Q (fun x => (ZM x).1 - m.1) +
          vectorWeakHaarNorm Q (fun x => (ZG x).1 - (G x).1) := hSumNorm
    _ ≤ A + C := add_le_add hAffine hCenter

private theorem old_signed_vectorWeakHaarNorm_sub_le (Q : TriadicCube 2)
    {f g : Vec 2 → Vec 2}
    (hf : ∀ i : Fin 2, MemLp (fun x => f x i) 2 (normalizedCubeMeasure Q))
    (hg : ∀ i : Fin 2, MemLp (fun x => g x i) 2 (normalizedCubeMeasure Q)) :
    vectorWeakHaarNorm Q (fun x => f x - g x) ≤
      vectorWeakHaarNorm Q f + vectorWeakHaarNorm Q g := by
  have hsum := old_signed_vectorWeakHaarNorm_add_le Q hf (fun i => (hg i).neg)
  have hNeg : vectorWeakHaarNorm Q (fun x i => -g x i) = vectorWeakHaarNorm Q g := by
    unfold vectorWeakHaarNorm vectorWeakHaarEnergy
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    unfold dualEnergy
    exact primalEnergy_neg Q ((Real.sqrt 3)⁻¹) (fun x => g x i)
  calc
    vectorWeakHaarNorm Q (fun x => f x - g x) =
        vectorWeakHaarNorm Q (fun x i => f x i + -(g x i)) := by
      congr 1
    _ ≤ vectorWeakHaarNorm Q f + vectorWeakHaarNorm Q (fun x i => -(g x i)) := by
      simpa only [Pi.add_apply, Pi.neg_apply] using hsum
    _ = vectorWeakHaarNorm Q f + vectorWeakHaarNorm Q g := by rw [hNeg]

private theorem old_signed_centered_projection_error_bound (Q : TriadicCube 2)
    (nu sigma : ℝ) (k : ResponseCoefficient (openCubeSet Q))
    {G ZG : Vec 2 → BlockVec 2}
    (hZG : MemBlockL2 (openCubeSet Q) ZG)
    (hG : MemBlockL2 (openCubeSet Q) G)
    (hOutput : vectorWeakHaarNorm Q (fun x => (ZG x).1) ≤
      Real.sqrt (oldSignedInverseHistory Q (responseFramePlanarCoefficientField nu sigma k) *
        oldSignedResponseHistory Q (responseFramePlanarCoefficientField nu sigma k)) *
          oldSignedBlockPositiveNorm Q G)
    (hInput : vectorWeakHaarNorm Q (fun x => (G x).1) ≤ oldSignedBlockPositiveNorm Q G) :
    vectorWeakHaarNorm Q (fun x => (ZG x).1 - (G x).1) ≤
      (Real.sqrt (oldSignedInverseHistory Q (responseFramePlanarCoefficientField nu sigma k) *
        oldSignedResponseHistory Q (responseFramePlanarCoefficientField nu sigma k)) + 1) *
          oldSignedBlockPositiveNorm Q G := by
  have hZGcoord (i : Fin 2) : MemLp (fun x => (ZG x).1 i) 2
      (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hZG) i)
  have hGcoord (i : Fin 2) : MemLp (fun x => (G x).1 i) 2
      (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hG) i)
  calc
    _ ≤ vectorWeakHaarNorm Q (fun x => (ZG x).1) +
        vectorWeakHaarNorm Q (fun x => (G x).1) :=
      old_signed_vectorWeakHaarNorm_sub_le Q hZGcoord hGcoord
    _ ≤ Real.sqrt (oldSignedInverseHistory Q (responseFramePlanarCoefficientField nu sigma k) *
          oldSignedResponseHistory Q (responseFramePlanarCoefficientField nu sigma k)) *
          oldSignedBlockPositiveNorm Q G + oldSignedBlockPositiveNorm Q G :=
      add_le_add hOutput hInput
    _ = (Real.sqrt (oldSignedInverseHistory Q (responseFramePlanarCoefficientField nu sigma k) *
          oldSignedResponseHistory Q (responseFramePlanarCoefficientField nu sigma k)) + 1) *
          oldSignedBlockPositiveNorm Q G := by ring

private theorem old_signed_centered_positive_series (Q : TriadicCube 2)
    (F : Vec 2 → BlockVec 2)
    (hPfst : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1)
        (fun x => (F x).1 i - (oldSignedBlockMean Q F).1 i))))
    (hPsnd : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1)
        (fun x => (F x).2 i - (oldSignedBlockMean Q F).2 i)))) :
    let m := oldSignedBlockMean Q F
    let G : Vec 2 → BlockVec 2 := fun x => F x - m
    (∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1) (fun x => (G x).1 i)))) ∧
    (∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1) (fun x => (G x).2 i)))) := by
  let m := oldSignedBlockMean Q F
  let G : Vec 2 → BlockVec 2 := fun x => F x - m
  constructor
  · intro i
    simpa [G, m] using hPfst i
  · intro i
    simpa [G, m] using hPsnd i

private theorem old_signed_centered_projection_estimates (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (F : Vec 2 → BlockVec 2) (hF : MemBlockL2 (openCubeSet Q) F)
    (hPfst : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1)
        (fun x => (F x - oldSignedBlockMean Q F).1 i))))
    (hPsnd : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1)
        (fun x => (F x - oldSignedBlockMean Q F).2 i))))
    (hcompat : ScalarCompatible (openCubeSet Q) F) :
    let U := openCubeSet Q
    let m := oldSignedBlockMean Q F
    let G : Vec 2 → BlockVec 2 := fun x => F x - m
    let hG : MemBlockL2 U G := hF.sub (memLp_const m)
    let HG := toHilbertBlockL2OfBlockField hG
    let ZG := scalarResidualField Q nu sigma hnu hsigma k HG
    let O := oldSignedBlockPositiveNorm Q G
    let a := responseFramePlanarCoefficientField nu sigma k
    let B := oldSignedInverseHistory Q a
    let M := oldSignedResponseHistory Q a
    ScalarCompatible U G ∧ ScalarCompatible U ZG ∧
      vectorWeakHaarNorm Q (fun x => (ZG x).1) ≤ Real.sqrt (B * M) * O ∧
      vectorWeakHaarNorm Q (fun x => (G x).1) ≤ O ∧
      vectorWeakHaarNorm Q (fun x => (ZG x).1 - (G x).1) ≤
        (Real.sqrt (B * M) + 1) * O := by
  let U := openCubeSet Q
  let m := oldSignedBlockMean Q F
  let G : Vec 2 → BlockVec 2 := fun x => F x - m
  let hG : MemBlockL2 U G := hF.sub (memLp_const m)
  let HG := toHilbertBlockL2OfBlockField hG
  let ZG := scalarResidualField Q nu sigma hnu hsigma k HG
  let O := oldSignedBlockPositiveNorm Q G
  let a := responseFramePlanarCoefficientField nu sigma k
  let B := oldSignedInverseHistory Q a
  let M := oldSignedResponseHistory Q a
  have hGcompat : ScalarCompatible U G := by
    change ScalarCompatible U (fun x => F x - oldSignedBlockMean Q F)
    exact old_signed_centered_source_compatible' Q hF hcompat
  have hZGcompat : ScalarCompatible U ZG := by
    change ScalarCompatible U
      (scalarResidualField Q nu sigma hnu hsigma k
        (toHilbertBlockL2OfBlockField hG))
    exact old_signed_centered_residual_compatible Q nu sigma hnu hsigma k hGcompat
  have hOutput : vectorWeakHaarNorm Q (fun x => (ZG x).1) ≤ Real.sqrt (B * M) * O := by
    change vectorWeakHaarNorm Q
        (fun x => (scalarResidualField Q nu sigma hnu hsigma k
          (toHilbertBlockL2OfBlockField hG) x).1) ≤
      Real.sqrt (oldSignedInverseHistory Q a * oldSignedResponseHistory Q a) *
        oldSignedBlockPositiveNorm Q G
    exact old_signed_centered_compatible_first_bound Q nu sigma hnu hsigma k hGcompat
      hPfst hPsnd
  have hInput : vectorWeakHaarNorm Q (fun x => (G x).1) ≤ O := by
    change vectorWeakHaarNorm Q (fun x => (G x).1) ≤ oldSignedBlockPositiveNorm Q G
    exact old_signed_centered_input_first_bound Q hG hPfst
  have hCenter : vectorWeakHaarNorm Q (fun x => (ZG x).1 - (G x).1) ≤
      (Real.sqrt (B * M) + 1) * O := by
    change vectorWeakHaarNorm Q (fun x => (ZG x).1 - (G x).1) ≤
      (Real.sqrt (oldSignedInverseHistory Q a * oldSignedResponseHistory Q a) + 1) *
        oldSignedBlockPositiveNorm Q G
    exact old_signed_centered_projection_error_bound Q nu sigma k hZGcompat.1 hG
      hOutput hInput
  exact ⟨hGcompat, hZGcompat, hOutput, hInput, hCenter⟩

private theorem old_signed_affine_centered_split (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (F : Vec 2 → BlockVec 2)
    (m : BlockVec 2) (G : Vec 2 → BlockVec 2)
    (hG : MemBlockL2 (openCubeSet Q) G)
    (H HM HG : HilbertBlockL2 (openCubeSet Q))
    (hHM : HM = (scalarFrameRealization Q nu sigma hnu hsigma k).constantField m)
    (hMeanSplit : H = HM + HG)
    (hFsplit : ∀ x, F x = m + G x)
    (hCenter : vectorWeakHaarNorm Q
      (fun x => (scalarResidualField Q nu sigma hnu hsigma k HG x).1 - (G x).1) ≤
      (Real.sqrt (oldSignedInverseHistory Q (responseFramePlanarCoefficientField nu sigma k) *
        oldSignedResponseHistory Q (responseFramePlanarCoefficientField nu sigma k)) + 1) *
          oldSignedBlockPositiveNorm Q G) :
    vectorWeakHaarNorm Q
      (fun x => (scalarResidualField Q nu sigma hnu hsigma k H x).1 - (F x).1) ≤
      Real.sqrt (oldSignedCorrectorHistory Q
        (responseFramePlanarCoefficientField nu sigma k)) * Real.sqrt (blockVecDot m m) +
        (Real.sqrt (oldSignedInverseHistory Q (responseFramePlanarCoefficientField nu sigma k) *
          oldSignedResponseHistory Q (responseFramePlanarCoefficientField nu sigma k)) + 1) *
            oldSignedBlockPositiveNorm Q G := by
  have hZFfirst := old_signed_scalar_residual_first_add Q nu sigma hnu hsigma k hMeanSplit
  have hAffine₀ := old_signed_affine_first_residual_bound Q nu sigma hnu hsigma k m
  have hAffine : vectorWeakHaarNorm Q
      (fun x => (scalarResidualField Q nu sigma hnu hsigma k HM x).1 - m.1) ≤
      Real.sqrt (oldSignedCorrectorHistory Q
        (responseFramePlanarCoefficientField nu sigma k)) * Real.sqrt (blockVecDot m m) := by
    rw [hHM]
    exact hAffine₀
  have hZMmem : MemBlockL2 (openCubeSet Q)
      (fun x => scalarResidualField Q nu sigma hnu hsigma k HM x) :=
    Lp.memLp (scalarResidualField Q nu sigma hnu hsigma k HM)
  exact old_signed_first_projection_split_bound Q m
    (Real.sqrt (oldSignedCorrectorHistory Q
      (responseFramePlanarCoefficientField nu sigma k)) * Real.sqrt (blockVecDot m m))
    ((Real.sqrt (oldSignedInverseHistory Q (responseFramePlanarCoefficientField nu sigma k) *
      oldSignedResponseHistory Q (responseFramePlanarCoefficientField nu sigma k)) + 1) *
        oldSignedBlockPositiveNorm Q G)
    (F := F) (G := G)
    (ZF := fun x => scalarResidualField Q nu sigma hnu hsigma k H x)
    (ZM := fun x => scalarResidualField Q nu sigma hnu hsigma k HM x)
    (ZG := fun x => scalarResidualField Q nu sigma hnu hsigma k HG x)
    hFsplit hZFfirst hZMmem
    (Lp.memLp (scalarResidualField Q nu sigma hnu hsigma k HG)) hG hAffine hCenter

/-- For a compatible source, the first block of the centered actual OLD
projection is controlled by compatible coercivity and the source-energy
bound; the affine mean is handled by the exact affine corrector. -/
theorem old_signed_flat_compatible_first_corrector (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (F : Vec 2 → BlockVec 2) (hF : MemBlockL2 (openCubeSet Q) F)
    (hPfst : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1)
        (fun x => (F x).1 i - (oldSignedBlockMean Q F).1 i))))
    (hPsnd : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1)
        (fun x => (F x).2 i - (oldSignedBlockMean Q F).2 i))))
    (hcompat : ScalarCompatible (openCubeSet Q) F) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let Z := scalarResidualField Q nu sigma hnu hsigma k
      (toHilbertBlockL2OfBlockField hF)
    let m := oldSignedBlockMean Q F
    let O := oldSignedBlockPositiveNorm Q (F - fun _ => m)
    let T := oldSignedCorrectorHistory Q a
    let B := oldSignedInverseHistory Q a
    let M := oldSignedResponseHistory Q a
    vectorWeakHaarNorm Q (fun x => (Z x).1 - (F x).1) ≤
      Real.sqrt T * Real.sqrt (blockVecDot m m) + (Real.sqrt (B * M) + 1) * O := by
  let U := openCubeSet Q
  let a := responseFramePlanarCoefficientField nu sigma k
  let m := oldSignedBlockMean Q F
  let G : Vec 2 → BlockVec 2 := fun x => F x - m
  let H := toHilbertBlockL2OfBlockField hF
  let HM := (scalarFrameRealization Q nu sigma hnu hsigma k).constantField m
  let hG : MemBlockL2 U G := hF.sub (memLp_const m)
  let HG := toHilbertBlockL2OfBlockField hG
  let ZF : Vec 2 → BlockVec 2 := scalarResidualField Q nu sigma hnu hsigma k H
  let ZM : Vec 2 → BlockVec 2 := scalarResidualField Q nu sigma hnu hsigma k HM
  let ZG : Vec 2 → BlockVec 2 := scalarResidualField Q nu sigma hnu hsigma k HG
  let O := oldSignedBlockPositiveNorm Q G
  let T := oldSignedCorrectorHistory Q a
  let B := oldSignedInverseHistory Q a
  let M := oldSignedResponseHistory Q a
  change vectorWeakHaarNorm Q (fun x => (ZF x).1 - (F x).1) ≤
    Real.sqrt T * Real.sqrt (blockVecDot m m) + (Real.sqrt (B * M) + 1) * O
  have hPositive := old_signed_centered_positive_series Q F hPfst hPsnd
  have hPfstCentered : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1) (fun x => (G x).1 i))) := hPositive.1
  have hPsndCentered : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1) (fun x => (G x).2 i))) := hPositive.2
  have hCentered := old_signed_centered_projection_estimates Q nu sigma hnu hsigma k
    F hF hPfstCentered hPsndCentered hcompat
  rcases hCentered with ⟨_, _, _, _, hCenter⟩
  have hSource := old_signed_block_field_mean_split' Q nu sigma hnu hsigma k F hF
  have hMeanSplit : H = HM + HG := by
    simpa [H, HM, HG, hG, G, m] using hSource
  have hFsplit (x : Vec 2) : F x = m + G x := by
    dsimp [G]
    abel
  exact old_signed_affine_centered_split Q nu sigma hnu hsigma k F
    m G hG H HM HG rfl hMeanSplit hFsplit hCenter
end
end ASDExplicitGamma.Native
