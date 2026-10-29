/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.SmoothFeedbackJointPaired
public import ASDExplicitGamma.Scalar.SmoothFeedbackResponse
public import ASDExplicitGamma.Scalar.OldCutoffCoefficient
public import ASDExplicitGamma.Scalar.SmoothFeedbackGapSourceForce
public import ASDExplicitGamma.Native.OldSignedAffineResidualSplit
public import ASDExplicitGamma.Native.OldSignedWeakPositiveComparison
public import ASDExplicitGamma.Native.OldSignedWeakTriangle
public import ASDExplicitGamma.Native.OldSignedHaarCongr

/-! Cellwise joint smooth-feedback estimate for the actual OLD cell response:
affine part (directional Gram) plus centered part (paired history charge)
plus the centered source oscillation. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native
open Algsuperdiff.Section3
open scoped BigOperators

noncomputable section

/-- Euclidean triangle inequality in the plane, on nonnegative coordinates. -/
theorem joint_plane_triangle {x₁ x₂ y₁ y₂ : ℝ}
    (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) :
    Real.sqrt ((x₁ + x₂) ^ 2 + (y₁ + y₂) ^ 2) ≤
      Real.sqrt (x₁ ^ 2 + y₁ ^ 2) + Real.sqrt (x₂ ^ 2 + y₂ ^ 2) := by
  have h := sqrt_finset_sq_add_le (Finset.univ : Finset (Fin 2))
    (fun i => if i = 0 then x₁ else y₁) (fun i => if i = 0 then x₂ else y₂)
  simpa [Fin.sum_univ_two] using h

/-- Weak-Haar triangle for a pair (first block, reciprocal block), at the
level of energies. -/
theorem joint_pair_weak_triangle (R : TriadicCube 2)
    {a₁ a₂ b₁ b₂ : Vec 2 → Vec 2}
    (ha₁ : ∀ i : Fin 2, MemLp (fun x => a₁ x i) 2 (normalizedCubeMeasure R))
    (ha₂ : ∀ i : Fin 2, MemLp (fun x => a₂ x i) 2 (normalizedCubeMeasure R))
    (hb₁ : ∀ i : Fin 2, MemLp (fun x => b₁ x i) 2 (normalizedCubeMeasure R))
    (hb₂ : ∀ i : Fin 2, MemLp (fun x => b₂ x i) 2 (normalizedCubeMeasure R)) :
    Real.sqrt (vectorWeakHaarEnergy R (fun x => a₁ x + a₂ x) +
        vectorWeakHaarEnergy R (fun x => b₁ x + b₂ x)) ≤
      Real.sqrt (vectorWeakHaarEnergy R a₁ + vectorWeakHaarEnergy R b₁) +
      Real.sqrt (vectorWeakHaarEnergy R a₂ + vectorWeakHaarEnergy R b₂) := by
  have ha := old_signed_vector_weak_triangle R ha₁ ha₂
  have hb := old_signed_vector_weak_triangle R hb₁ hb₂
  have hsq (F : Vec 2 → Vec 2) : vectorWeakHaarEnergy R F = vectorWeakHaarNorm R F ^ 2 := by
    unfold vectorWeakHaarNorm
    rw [Real.sq_sqrt (vectorWeakHaarEnergy_nonneg R F)]
  rw [hsq, hsq, hsq a₁, hsq a₂, hsq b₁, hsq b₂]
  have n0 (F : Vec 2 → Vec 2) : 0 ≤ vectorWeakHaarNorm R F := Real.sqrt_nonneg _
  calc
    _ ≤ Real.sqrt ((vectorWeakHaarNorm R a₁ + vectorWeakHaarNorm R a₂) ^ 2 +
        (vectorWeakHaarNorm R b₁ + vectorWeakHaarNorm R b₂) ^ 2) := by
      apply Real.sqrt_le_sqrt
      have h1 := pow_le_pow_left₀ (n0 _) ha 2
      have h2 := pow_le_pow_left₀ (n0 _) hb 2
      linarith
    _ ≤ _ := joint_plane_triangle (n0 _) (n0 _) (n0 _) (n0 _)

/-- The cell estimate: for an actual H10 gradient source on the parent, the
joint weak charge of `(p_w - w, g_w)` on a child cell is bounded by the
affine directional pair at the child mean, the paired history charge of the
centered residual, and the centered quarter-order source oscillation. -/
theorem smooth_feedback_cell_joint_feedback
    (Q R : TriadicCube 2) (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (u : H10Function (openCubeSet Q))
    (hQ : ScalarQuarterHaarAdmissible R (fun x i =>
      u.toH1Function.grad x i - cubeAverage R (fun y => u.toH1Function.grad y i))) :
    let f : Vec 2 → Vec 2 := u.toH1Function.grad
    let mean : Vec 2 := fun j => cubeAverage R (fun x => f x j)
    let F : Vec 2 → BlockVec 2 := fun x => (f x, 0)
    let hF : MemBlockL2 (openCubeSet Q) F :=
      memBlockL2_blockField u.toH1Function.grad_memVectorL2 MemLp.zero
    let kR := oldSignedCellCoefficient Q R hRQ k
    let aR := responseFramePlanarCoefficientField nu sigma kR
    let Y := oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k F hF
    let ZM := scalarResidualField R nu sigma hnu hsigma kR
      ((scalarFrameRealization R nu sigma hnu hsigma kR).constantField (mean, 0))
    let C : Vec 2 → BlockVec 2 := fun x => (fun j => f x j - mean j, 0)
    let hC : MemBlockL2 (openCubeSet Q) C := by
      have hsub : MemLp (fun x => F x - (mean, 0)) 2
          (volumeMeasureOn (openCubeSet Q)) := hF.sub (memLp_const (mean, 0))
      convert hsub using 1
      ext x j
      · simp [C, F, f]
      · change (0 : Vec 2) j = (0 - 0 : Vec 2) j
        simp
    let YC := oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k C hC
    Real.sqrt (vectorWeakHaarEnergy R (fun x j => (Y x).1 j - f x j) +
        vectorWeakHaarEnergy R (fun x => (scalarCoefficientFlux aR Y x).2)) ≤
      Real.sqrt (vectorWeakHaarEnergy R (fun x j => (ZM x).1 j - mean j) +
        vectorWeakHaarEnergy R (fun x => (scalarCoefficientFlux aR ZM x).2)) +
      Real.sqrt (lemmaVInverseHistory R aR ((3 : ℝ) ^ (1 / 4 : ℝ)) *
        oldSignedEnergyPairing R nu sigma kR YC YC) +
      Real.sqrt (vectorPositiveHaarEnergy R (fun x j => f x j - mean j)) := by
  classical
  intro f mean F hF kR aR Y ZM C hC YC
  have hFR : MemBlockL2 (openCubeSet R) F :=
    hF.mono_measure (Measure.restrict_mono_set volume hRQ)
  have hCR : MemBlockL2 (openCubeSet R) C :=
    hC.mono_measure (Measure.restrict_mono_set volume hRQ)
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet R) nu sigma hnu hsigma kR
  have hm : oldSignedBlockMean R F = (mean, 0) := by
    apply Prod.ext
    · rfl
    · funext i
      change cubeAverage R (fun x => (F x).2 i) = 0
      simp [F, cubeAverage]
  have hY : Y = scalarResidualField R nu sigma hnu hsigma kR
      (toHilbertBlockL2OfBlockField hFR) := rfl
  have hsplit := old_signed_residual_mean_split_ae R nu sigma hnu hsigma kR F hFR
  dsimp only at hsplit
  have hGC : (fun x => F x - oldSignedBlockMean R F) = C := by
    funext x
    rw [hm]
    ext i <;> simp [F, C, f]
  have hZG : scalarResidualField R nu sigma hnu hsigma kR
      (toHilbertBlockL2OfBlockField (hFR.sub (memLp_const (oldSignedBlockMean R F)))) =
      YC := by
    have key : ∀ (G G' : Vec 2 → BlockVec 2) (h : G = G')
        (hG : MemBlockL2 (openCubeSet R) G) (hG' : MemBlockL2 (openCubeSet R) G'),
        toHilbertBlockL2OfBlockField hG = toHilbertBlockL2OfBlockField hG' := by
      intro G G' h hG hG'
      subst h
      rfl
    change _ = scalarResidualField R nu sigma hnu hsigma kR
      (toHilbertBlockL2OfBlockField hCR)
    congr 1
    exact key _ _ hGC _ _
  have hsplit' : (fun x => Y x) =ᵐ[volumeMeasureOn (openCubeSet R)]
      (fun x => ZM x + YC x) := by
    have := hsplit
    rw [hZG, hm] at this
    exact this
  have hZMmem : MemBlockL2 (openCubeSet R) ZM := Lp.memLp ZM
  have hYCmem : MemBlockL2 (openCubeSet R) YC := Lp.memLp YC
  have hfluxZM : MemBlockL2 (openCubeSet R) (scalarCoefficientFlux aR ZM) :=
    scalar_coefficient_flux_memL2 R aR hEll hZMmem
  have hfluxYC : MemBlockL2 (openCubeSet R) (scalarCoefficientFlux aR YC) :=
    scalar_coefficient_flux_memL2 R aR hEll hYCmem
  have toLp (V : Vec 2 → Vec 2) (hV : MemVectorL2 (openCubeSet R) V) (i : Fin 2) :
      MemLp (fun x => V x i) 2 (normalizedCubeMeasure R) :=
    memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hV i)
  let a₁ : Vec 2 → Vec 2 := fun x j => (ZM x).1 j - mean j
  let a₂ : Vec 2 → Vec 2 := fun x j => (YC x).1 j - (C x).1 j
  let b₁ : Vec 2 → Vec 2 := fun x => (scalarCoefficientFlux aR ZM x).2
  let b₂ : Vec 2 → Vec 2 := fun x => (scalarCoefficientFlux aR YC x).2
  have ha₁ := toLp a₁ ((memVectorL2_fst_of_memBlockL2 hZMmem).sub (memVectorL2_const mean))
  have ha₂ := toLp a₂ ((memVectorL2_fst_of_memBlockL2 hYCmem).sub
    (memVectorL2_fst_of_memBlockL2 hCR))
  have hb₁ := toLp b₁ (memVectorL2_snd_of_memBlockL2 hfluxZM)
  have hb₂ := toLp b₂ (memVectorL2_snd_of_memBlockL2 hfluxYC)
  have hfirst : (fun x j => (Y x).1 j - f x j) =ᵐ[volumeMeasureOn (openCubeSet R)]
      (fun x => a₁ x + a₂ x) := by
    filter_upwards [hsplit'] with x hx
    have hh := congrArg Prod.fst hx
    change (Y x).1 = (ZM x).1 + (YC x).1 at hh
    funext j
    have hj := congrFun hh j
    simp only [a₁, a₂, Pi.add_apply, C, f, hj]
    ring
  have hsecond : (fun x => (scalarCoefficientFlux aR Y x).2) =ᵐ[
      volumeMeasureOn (openCubeSet R)] (fun x => b₁ x + b₂ x) := by
    filter_upwards [hsplit'] with x hx
    have h2 : scalarCoefficientFlux aR Y x =
        scalarCoefficientFlux aR ZM x + scalarCoefficientFlux aR YC x := by
      unfold scalarCoefficientFlux
      rw [hx, blockMatVecMul_add]
    have := congrArg Prod.snd h2
    simpa [b₁, b₂] using this
  rw [smooth_feedback_vector_weak_energy_congr_ae R hfirst,
    smooth_feedback_vector_weak_energy_congr_ae R hsecond]
  refine (joint_pair_weak_triangle R ha₁ ha₂ hb₁ hb₂).trans ?_
  let c : Vec 2 → Vec 2 := fun x j => f x j - mean j
  have hc_eq : ∀ x, (C x).1 = c x := fun x => rfl
  have hCcompat : ScalarCompatible (openCubeSet Q) C :=
    smooth_feedback_centered_h10_source_compatible Q R u
  have hpaired :=
    smooth_feedback_old_cell_residual_paired_weak_energy_of_compatible
      Q R hRQ nu sigma hnu hsigma k C hC hCcompat
  dsimp only at hpaired
  have hYC1 := toLp (fun x => (YC x).1) (memVectorL2_fst_of_memBlockL2 hYCmem)
  have hcm := toLp c (memVectorL2_fst_of_memBlockL2 hCR)
  have hcneg : ∀ i : Fin 2, MemLp (fun x => (-c x) i) 2 (normalizedCubeMeasure R) :=
    fun i => (hcm i).neg
  have ha₂eq : a₂ = fun x => (YC x).1 + -c x := by
    funext x j
    simp [a₂, hc_eq, sub_eq_add_neg]
  have hnorm : vectorWeakHaarNorm R a₂ ≤
      vectorWeakHaarNorm R (fun x => (YC x).1) + vectorWeakHaarNorm R c := by
    rw [ha₂eq]
    refine (old_signed_vector_weak_triangle R hYC1 hcneg).trans ?_
    rw [old_signed_vector_weak_neg]
  have hcpos : vectorWeakHaarNorm R c ≤ Real.sqrt (vectorPositiveHaarEnergy R c) := by
    have := old_signed_vector_weak_le_positive R hcm hQ.increments
    exact this
  have hn0 (F : Vec 2 → Vec 2) : 0 ≤ vectorWeakHaarNorm R F := Real.sqrt_nonneg _
  have hsq (F : Vec 2 → Vec 2) : vectorWeakHaarEnergy R F = vectorWeakHaarNorm R F ^ 2 := by
    unfold vectorWeakHaarNorm
    rw [Real.sq_sqrt (vectorWeakHaarEnergy_nonneg R F)]
  have hcent : Real.sqrt (vectorWeakHaarEnergy R a₂ + vectorWeakHaarEnergy R b₂) ≤
      Real.sqrt (lemmaVInverseHistory R aR ((3 : ℝ) ^ (1 / 4 : ℝ)) *
        oldSignedEnergyPairing R nu sigma kR YC YC) +
      Real.sqrt (vectorPositiveHaarEnergy R c) := by
    have h1 : Real.sqrt (vectorWeakHaarEnergy R a₂ + vectorWeakHaarEnergy R b₂) ≤
        Real.sqrt ((vectorWeakHaarNorm R (fun x => (YC x).1) +
          vectorWeakHaarNorm R c) ^ 2 + vectorWeakHaarNorm R b₂ ^ 2) := by
      apply Real.sqrt_le_sqrt
      rw [hsq a₂, hsq b₂]
      have := pow_le_pow_left₀ (hn0 _) hnorm 2
      linarith
    have h2 := joint_plane_triangle (hn0 (fun x => (YC x).1)) (hn0 c)
      (hn0 b₂) (le_refl (0 : ℝ))
    have h3 : Real.sqrt (vectorWeakHaarNorm R c ^ 2 + 0 ^ 2) = vectorWeakHaarNorm R c := by
      rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, Real.sqrt_sq (hn0 c)]
    rw [h3] at h2
    have h4 : Real.sqrt (vectorWeakHaarNorm R (fun x => (YC x).1) ^ 2 +
        vectorWeakHaarNorm R b₂ ^ 2) ≤
        Real.sqrt (lemmaVInverseHistory R aR ((3 : ℝ) ^ (1 / 4 : ℝ)) *
          oldSignedEnergyPairing R nu sigma kR YC YC) := by
      apply Real.sqrt_le_sqrt
      rw [← hsq, ← hsq]
      exact hpaired
    rw [add_zero] at h2
    linarith
  linarith

/-- The restriction of the parent OLD skew coefficient to a child cell is the
OLD skew coefficient of that child. -/
theorem smooth_feedback_cell_coefficient_restrict (m : ℤ)
    (Q R : TriadicCube 2) (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (ω : Cutoff.CutoffSample 2) :
    oldSignedCellCoefficient Q R hRQ (oldCutoffSkewCoefficient m Q ω) =
      oldCutoffSkewCoefficient m R ω := by
  apply BoundedContinuousFunction.ext
  intro x
  rfl

/-- The affine pair of the actual cell response to the child mean is the
directional Gram of that child at the mean. -/
theorem smooth_feedback_cell_affine_pair_eq_gamma
    (M : ABKModel 2) (m : ℤ) (Q R : TriadicCube 2)
    (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (ω : Cutoff.CutoffSample 2) (mean : Vec 2) :
    let σ : ℝ := Annealed.sigmaBar M m
    let k : ResponseCoefficient (openCubeSet Q) := oldCutoffSkewCoefficient m Q ω
    let kR := oldSignedCellCoefficient Q R hRQ k
    let aR := responseFramePlanarCoefficientField M.nu σ kR
    let ZM := scalarResidualField R M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).property kR
      ((scalarFrameRealization R M.nu σ M.nu_pos
        (Annealed.sigmaBar M m).property kR).constantField (mean, 0))
    vectorWeakHaarEnergy R (fun x j => (ZM x).1 j - mean j) +
        vectorWeakHaarEnergy R (fun x => (scalarCoefficientFlux aR ZM x).2) =
      smoothFeedbackCellDirectionalGamma M m R mean ω := by
  intro σ k kR aR ZM
  have hk : kR = oldCutoffSkewCoefficient m R ω :=
    smooth_feedback_cell_coefficient_restrict m Q R hRQ ω
  have hae := smooth_feedback_affine_projection_ae M m R mean ω
  have hZM : (fun x => ZM x) =ᵐ[volumeMeasureOn (openCubeSet R)]
      smoothFeedbackCellAffineResidual M m R mean ω := by
    have : ZM = scalarResidualField R M.nu (Annealed.sigmaBar M m : ℝ)
      M.nu_pos (Annealed.sigmaBar M m).property (oldCutoffSkewCoefficient m R ω)
      ((scalarFrameRealization R M.nu (Annealed.sigmaBar M m : ℝ)
        M.nu_pos (Annealed.sigmaBar M m).property (oldCutoffSkewCoefficient m R ω)).constantField
        (mean, 0)) := by
      simp only [ZM]
      rw [hk]
    rw [this]
    exact hae
  unfold smoothFeedbackCellDirectionalGamma
    smoothFeedbackCellAffineTopDefect smoothFeedbackCellAffineReciprocalGradient
  congr 1
  · apply smooth_feedback_vector_weak_energy_congr_ae
    filter_upwards [hZM] with x hx
    funext j
    simp [hx]
  · apply smooth_feedback_vector_weak_energy_congr_ae
    filter_upwards [hZM] with x hx
    have haR : aR = responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
        (oldCutoffSkewCoefficient m R ω) := by
      simp only [aR]
      rw [hk]
    simp only [scalarCoefficientFlux, haR, hx]

/-- Euclidean aggregation of three cellwise bounds over a finite family and a
finite cell index, with a common nonnegative weight. -/
theorem joint_weighted_three_minkowski
    {ι κ : Type*} [Fintype κ] (S : Finset ι) (c : ℝ) (hc : 0 ≤ c)
    (s g r d : ι → κ → ℝ)
    (hs : ∀ i U, 0 ≤ s i U) (hg : ∀ i U, 0 ≤ g i U) (hr : ∀ i U, 0 ≤ r i U)
    (hd : ∀ i U, 0 ≤ d i U) (h : ∀ i U, s i U ≤ g i U + r i U + d i U) :
    Real.sqrt (∑ i ∈ S, c * ∑ U, s i U ^ 2) ≤
      Real.sqrt (∑ i ∈ S, c * ∑ U, g i U ^ 2) +
      Real.sqrt (∑ i ∈ S, c * ∑ U, r i U ^ 2) +
      Real.sqrt (∑ i ∈ S, c * ∑ U, d i U ^ 2) := by
  classical
  have hsc := Real.sqrt_nonneg c
  let T : Finset (ι × κ) := S ×ˢ Finset.univ
  let a : ι × κ → ℝ := fun x => Real.sqrt c * g x.1 x.2
  let b : ι × κ → ℝ := fun x => Real.sqrt c * r x.1 x.2
  let e : ι × κ → ℝ := fun x => Real.sqrt c * d x.1 x.2
  let s' : ι × κ → ℝ := fun x => Real.sqrt c * s x.1 x.2
  have hconv (q : ι → κ → ℝ) :
      (∑ i ∈ S, c * ∑ U, q i U ^ 2) =
        ∑ x ∈ T, (Real.sqrt c * q x.1 x.2) ^ 2 := by
    simp only [T, Finset.sum_product, mul_pow, Real.sq_sqrt hc, Finset.mul_sum]
  rw [hconv s, hconv g, hconv r, hconv d]
  have hle : (∑ x ∈ T, (Real.sqrt c * s x.1 x.2) ^ 2) ≤
      ∑ x ∈ T, ((a x + b x) + e x) ^ 2 := by
    apply Finset.sum_le_sum
    intro x _
    apply pow_le_pow_left₀ (mul_nonneg hsc (hs _ _))
    have := mul_le_mul_of_nonneg_left (h x.1 x.2) hsc
    simp only [a, b, e]
    linarith
  calc
    _ ≤ Real.sqrt (∑ x ∈ T, ((a x + b x) + e x) ^ 2) := Real.sqrt_le_sqrt hle
    _ ≤ Real.sqrt (∑ x ∈ T, (a x + b x) ^ 2) + Real.sqrt (∑ x ∈ T, e x ^ 2) :=
      sqrt_finset_sq_add_le T (fun x => a x + b x) e
    _ ≤ (Real.sqrt (∑ x ∈ T, a x ^ 2) + Real.sqrt (∑ x ∈ T, b x ^ 2)) +
        Real.sqrt (∑ x ∈ T, e x ^ 2) := by
      have := sqrt_finset_sq_add_le T a b
      linarith

end

end ASDExplicitGamma.Scalar
