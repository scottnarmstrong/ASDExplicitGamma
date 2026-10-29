module

public import ASDExplicitGamma.Scalar.SmoothFeedbackResponse
public import ASDExplicitGamma.Scalar.DefectEnergyHilbert

/-! A matrix representation of the actual cellwise directional affine Gram.
The matrix entries are obtained by polarizing the weak-Haar energies of the
actual affine-top defect and reciprocal gradient. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization ASDExplicitGamma.Response Triadic
open Algsuperdiff.Section3
open scoped BigOperators

noncomputable section

private theorem smooth_feedback_weak_scalar_pairing_summable
    (Q : TriadicCube 2) {f g : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    Summable (fun k : ℕ => |weakHaarRho ^ k *
      pairing Q (cubeProjection Q k f) (cubeProjection Q k g)|) := by
  have hq : 1 < Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg (3 : ℝ),
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  let A : ℕ → ℝ := fun k => weakHaarRho ^ k *
    energy Q (cubeProjection Q k f)
  let B : ℕ → ℝ := fun k => weakHaarRho ^ k *
    energy Q (cubeProjection Q k g)
  have hA : Summable A := by
    simpa [A, weakHaarRho] using summable_weighted_projections Q hq hf
  have hB : Summable B := by
    simpa [B, weakHaarRho] using summable_weighted_projections Q hq hg
  have hA0 (k : ℕ) : 0 ≤ energy Q (cubeProjection Q k f) := energy_nonneg Q _
  have hB0 (k : ℕ) : 0 ≤ energy Q (cubeProjection Q k g) := energy_nonneg Q _
  have hrho : 0 ≤ weakHaarRho := by
    unfold weakHaarRho
    positivity
  have hbound (k : ℕ) : |weakHaarRho ^ k *
      pairing Q (cubeProjection Q k f) (cubeProjection Q k g)| ≤ A k + B k := by
    have hfk : MemLp (cubeProjection Q k f) 2 (normalizedCubeMeasure Q) :=
      projection_memLp Q k f 2
    have hgk : MemLp (cubeProjection Q k g) 2 (normalizedCubeMeasure Q) :=
      projection_memLp Q k g 2
    have hpair := abs_pairing_le Q hfk hgk
    have hpair' : |pairing Q (cubeProjection Q k f) (cubeProjection Q k g)| ≤
        Real.sqrt (energy Q (cubeProjection Q k f)) *
          Real.sqrt (energy Q (cubeProjection Q k g)) := by
      simpa [l2Norm] using hpair
    have ham : Real.sqrt (energy Q (cubeProjection Q k f)) *
        Real.sqrt (energy Q (cubeProjection Q k g)) ≤
        (energy Q (cubeProjection Q k f) +
          energy Q (cubeProjection Q k g)) / 2 := by
      have hsF := Real.sq_sqrt (hA0 k)
      have hsG := Real.sq_sqrt (hB0 k)
      nlinarith [sq_nonneg (Real.sqrt (energy Q (cubeProjection Q k f)) -
        Real.sqrt (energy Q (cubeProjection Q k g)))]
    have hrhok : 0 ≤ weakHaarRho ^ k := pow_nonneg hrho _
    have hmul : |weakHaarRho ^ k *
          pairing Q (cubeProjection Q k f) (cubeProjection Q k g)| =
        weakHaarRho ^ k *
          |pairing Q (cubeProjection Q k f) (cubeProjection Q k g)| := by
      rw [abs_mul, abs_of_nonneg hrhok]
    rw [hmul]
    dsimp [A, B]
    calc
      _ ≤ weakHaarRho ^ k *
          (Real.sqrt (energy Q (cubeProjection Q k f)) *
            Real.sqrt (energy Q (cubeProjection Q k g))) :=
        mul_le_mul_of_nonneg_left hpair' hrhok
      _ ≤ weakHaarRho ^ k *
          ((energy Q (cubeProjection Q k f) +
            energy Q (cubeProjection Q k g)) / 2) :=
        mul_le_mul_of_nonneg_left ham hrhok
      _ ≤ weakHaarRho ^ k *
          (energy Q (cubeProjection Q k f) +
            energy Q (cubeProjection Q k g)) := by
        nlinarith [hrhok, hA0 k, hB0 k]
      _ = weakHaarRho ^ k * energy Q (cubeProjection Q k f) +
          weakHaarRho ^ k * energy Q (cubeProjection Q k g) := by ring
  exact Summable.of_nonneg_of_le (fun k => abs_nonneg _) hbound (hA.add hB)

private theorem smooth_feedback_weak_scalar_pairing_congr_ae
    (Q : TriadicCube 2) {f f' g g' : Vec 2 → ℝ}
    (hf : f =ᵐ[volumeMeasureOn (openCubeSet Q)] f')
    (hg : g =ᵐ[volumeMeasureOn (openCubeSet Q)] g') :
    weakScalarPairing Q f g = weakScalarPairing Q f' g' := by
  have hfp (k : ℕ) : cubeProjection Q k f = cubeProjection Q k f' :=
    Cold.square_scalar_projection_congr_ae Q k hf
  have hgp (k : ℕ) : cubeProjection Q k g = cubeProjection Q k g' :=
    Cold.square_scalar_projection_congr_ae Q k hg
  unfold weakScalarPairing
  congr 1
  apply tsum_congr
  intro k
  rw [hfp k, hgp k]

private theorem smooth_feedback_weak_scalar_pairing_self
    (Q : TriadicCube 2) {f : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    weakScalarPairing Q f f = dualEnergy Q (Real.sqrt 3) f := by
  have hq : 1 < Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg (3 : ℝ),
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have hs := summable_weighted_projections Q hq hf
  rw [weakScalarPairing,
    dualEnergy_eq_weighted_projections Q hq hf hs]
  rfl

private theorem smooth_feedback_weak_scalar_pairing_symm
    (Q : TriadicCube 2) {f g : Vec 2 → ℝ}
    (_hf : MemLp f 2 (normalizedCubeMeasure Q))
    (_hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    weakScalarPairing Q f g = weakScalarPairing Q g f := by
  unfold weakScalarPairing
  congr 1
  apply tsum_congr
  intro k
  rw [pairing_comm]

private theorem smooth_feedback_weak_scalar_pairing_add_left
    (Q : TriadicCube 2) {f g h : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q))
    (hh : MemLp h 2 (normalizedCubeMeasure Q)) :
    weakScalarPairing Q (fun x => f x + g x) h =
      weakScalarPairing Q f h + weakScalarPairing Q g h := by
  have hfh := smooth_feedback_weak_scalar_pairing_summable Q hf hh
  have hgh := smooth_feedback_weak_scalar_pairing_summable Q hg hh
  have hfh' : Summable (fun k => weakHaarRho ^ k *
      pairing Q (cubeProjection Q k f) (cubeProjection Q k h)) := by
    apply Summable.of_norm
    simpa [Real.norm_eq_abs] using hfh
  have hgh' : Summable (fun k => weakHaarRho ^ k *
      pairing Q (cubeProjection Q k g) (cubeProjection Q k h)) := by
    apply Summable.of_norm
    simpa [Real.norm_eq_abs] using hgh
  have hp (k : ℕ) :
      pairing Q (fun x => cubeProjection Q k f x + cubeProjection Q k g x)
        (cubeProjection Q k h) =
      pairing Q (cubeProjection Q k f) (cubeProjection Q k h) +
        pairing Q (cubeProjection Q k g) (cubeProjection Q k h) := by
    unfold pairing
    rw [cubeAverage_eq_integral_normalizedCubeMeasure,
      cubeAverage_eq_integral_normalizedCubeMeasure,
      cubeAverage_eq_integral_normalizedCubeMeasure]
    calc
      (∫ x, (cubeProjection Q k f x + cubeProjection Q k g x) *
          cubeProjection Q k h x ∂normalizedCubeMeasure Q) =
        ∫ x, cubeProjection Q k f x * cubeProjection Q k h x +
          cubeProjection Q k g x * cubeProjection Q k h x
          ∂normalizedCubeMeasure Q := by
            apply integral_congr_ae
            filter_upwards [] with x
            ring
      _ = _ := integral_add
        ((projection_memLp Q k f 2).integrable_mul
          (projection_memLp Q k h 2))
        ((projection_memLp Q k g 2).integrable_mul
          (projection_memLp Q k h 2))
  simp only [weakScalarPairing]
  rw [← mul_add, ← hfh'.tsum_add hgh']
  congr 1
  apply tsum_congr
  intro k
  rw [projection_add Q k hf hg, hp]
  ring

private theorem smooth_feedback_weak_scalar_pairing_smul_left
    (Q : TriadicCube 2) {f h : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hh : MemLp h 2 (normalizedCubeMeasure Q)) (c : ℝ) :
    weakScalarPairing Q (fun x => c * f x) h =
      c * weakScalarPairing Q f h := by
  have hfh := smooth_feedback_weak_scalar_pairing_summable Q hf hh
  have hcfh := smooth_feedback_weak_scalar_pairing_summable Q
    (hf.const_mul c) hh
  have hp (k : ℕ) :
      pairing Q (fun x => c * cubeProjection Q k f x)
        (cubeProjection Q k h) =
      c * pairing Q (cubeProjection Q k f) (cubeProjection Q k h) := by
    unfold pairing
    rw [cubeAverage_eq_integral_normalizedCubeMeasure,
      cubeAverage_eq_integral_normalizedCubeMeasure]
    calc
      (∫ x, (c * cubeProjection Q k f x) * cubeProjection Q k h x
          ∂normalizedCubeMeasure Q) =
        ∫ x, c * (cubeProjection Q k f x * cubeProjection Q k h x)
          ∂normalizedCubeMeasure Q := by
            apply integral_congr_ae
            filter_upwards [] with x
            ring
      _ = c * ∫ x, cubeProjection Q k f x * cubeProjection Q k h x
          ∂normalizedCubeMeasure Q := by rw [integral_const_mul]
  have hsum :
      (∑' k, weakHaarRho ^ k *
        pairing Q (cubeProjection Q k (fun x => c * f x))
          (cubeProjection Q k h)) =
      c * (∑' k, weakHaarRho ^ k *
        pairing Q (cubeProjection Q k f) (cubeProjection Q k h)) := by
    calc
      _ = ∑' k, c * (weakHaarRho ^ k *
          pairing Q (cubeProjection Q k f) (cubeProjection Q k h)) := by
        apply tsum_congr
        intro k
        rw [projection_smul, hp]
        ring
      _ = _ := tsum_mul_left
  simp only [weakScalarPairing]
  rw [hsum]
  ring

private theorem smooth_feedback_weak_vector_pairing_self
    (Q : TriadicCube 2) {F : Vec 2 → Vec 2}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q)) :
    weakVectorPairing Q F F = vectorWeakHaarEnergy Q F := by
  unfold weakVectorPairing vectorWeakHaarEnergy
  apply Finset.sum_congr rfl
  intro i hi
  exact smooth_feedback_weak_scalar_pairing_self Q (hF i)

private theorem smooth_feedback_weak_vector_pairing_symm
    (Q : TriadicCube 2) {F G : Vec 2 → Vec 2}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) :
    weakVectorPairing Q F G = weakVectorPairing Q G F := by
  unfold weakVectorPairing
  apply Finset.sum_congr rfl
  intro i hi
  exact smooth_feedback_weak_scalar_pairing_symm Q (hF i) (hG i)

private theorem smooth_feedback_weak_vector_pairing_add_left
    (Q : TriadicCube 2) {F G H : Vec 2 → Vec 2}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (hH : ∀ i, MemLp (fun x => H x i) 2 (normalizedCubeMeasure Q)) :
    weakVectorPairing Q (fun x => F x + G x) H =
      weakVectorPairing Q F H + weakVectorPairing Q G H := by
  unfold weakVectorPairing
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact smooth_feedback_weak_scalar_pairing_add_left Q
    (hF i) (hG i) (hH i)

private theorem smooth_feedback_weak_vector_pairing_smul_left
    (Q : TriadicCube 2) {F H : Vec 2 → Vec 2}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hH : ∀ i, MemLp (fun x => H x i) 2 (normalizedCubeMeasure Q)) (c : ℝ) :
    weakVectorPairing Q (fun x => c • F x) H =
      c * weakVectorPairing Q F H := by
  unfold weakVectorPairing
  calc
    ∑ i : Fin 2, weakScalarPairing Q (fun x => c * F x i)
        (fun x => H x i) =
      ∑ i : Fin 2, c * weakScalarPairing Q (fun x => F x i)
        (fun x => H x i) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact smooth_feedback_weak_scalar_pairing_smul_left Q
            (hF i) (hH i) c
    _ = _ := by rw [Finset.mul_sum]

private theorem smooth_feedback_weak_vector_pairing_congr_ae
    (Q : TriadicCube 2) {F F' G G' : Vec 2 → Vec 2}
    (hF : F =ᵐ[volumeMeasureOn (openCubeSet Q)] F')
    (hG : G =ᵐ[volumeMeasureOn (openCubeSet Q)] G') :
    weakVectorPairing Q F G = weakVectorPairing Q F' G' := by
  unfold weakVectorPairing
  apply Finset.sum_congr rfl
  intro i hi
  apply smooth_feedback_weak_scalar_pairing_congr_ae Q
  · filter_upwards [hF] with x hx
    exact congrFun hx i
  · filter_upwards [hG] with x hx
    exact congrFun hx i

private theorem smooth_feedback_cell_affine_fields_memLp
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (e : Vec 2) (ω : Cutoff.CutoffSample 2) :
    (∀ i, MemLp (fun x => smoothFeedbackCellAffineTopDefect
      M m Q e ω x i) 2 (normalizedCubeMeasure Q)) ∧
    (∀ i, MemLp (fun x => smoothFeedbackCellAffineReciprocalGradient
      M m Q e ω x i) 2 (normalizedCubeMeasure Q)) := by
  let k := oldCutoffSkewCoefficient m Q ω
  let a := responseFramePlanarCoefficientField M.nu
    (Annealed.sigmaBar M m : ℝ) k
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu (Annealed.sigmaBar M m : ℝ)
    M.nu_pos (Annealed.sigmaBar M m).property k
  have hAffine : MemBlockL2 (openCubeSet Q)
      (smoothFeedbackCellAffineResidual M m Q e ω) := by
    simpa [smoothFeedbackCellAffineResidual, a, hEll, k] using
      scalar_cell_response_test_memL2 Q a hEll (e, 0)
  have hTopVec : MemVectorL2 (openCubeSet Q)
      (smoothFeedbackCellAffineTopDefect M m Q e ω) := by
    exact (memVectorL2_fst_of_memBlockL2 hAffine).sub (memLp_const e)
  have hFlux : MemBlockL2 (openCubeSet Q)
      (scalarCoefficientFlux a (smoothFeedbackCellAffineResidual M m Q e ω)) :=
    scalar_coefficient_flux_memL2 Q a hEll hAffine
  have hGradVec : MemVectorL2 (openCubeSet Q)
      (smoothFeedbackCellAffineReciprocalGradient M m Q e ω) := by
    change MemVectorL2 (openCubeSet Q)
      (fun x => (scalarCoefficientFlux a
        (smoothFeedbackCellAffineResidual M m Q e ω) x).2)
    exact memVectorL2_snd_of_memBlockL2 hFlux
  constructor
  · intro i
    exact memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 hTopVec i)
  · intro i
    exact memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 hGradVec i)

private noncomputable def smoothFeedbackCellGammaPair
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) (e f : Vec 2) : ℝ :=
  weakVectorPairing Q
      (smoothFeedbackCellAffineTopDefect M m Q e ω)
      (smoothFeedbackCellAffineTopDefect M m Q f ω) +
    weakVectorPairing Q
      (smoothFeedbackCellAffineReciprocalGradient M m Q e ω)
      (smoothFeedbackCellAffineReciprocalGradient M m Q f ω)

private theorem smooth_feedback_cell_gamma_pair_self
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) (e : Vec 2) :
    smoothFeedbackCellGammaPair M m Q ω e e =
      smoothFeedbackCellDirectionalGamma M m Q e ω := by
  have hF := smooth_feedback_cell_affine_fields_memLp M m Q e ω
  unfold smoothFeedbackCellGammaPair smoothFeedbackCellDirectionalGamma
  rw [smooth_feedback_weak_vector_pairing_self Q hF.1,
    smooth_feedback_weak_vector_pairing_self Q hF.2]

private theorem smooth_feedback_cell_gamma_pair_symm
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) (e f : Vec 2) :
    smoothFeedbackCellGammaPair M m Q ω e f =
      smoothFeedbackCellGammaPair M m Q ω f e := by
  have hE := smooth_feedback_cell_affine_fields_memLp M m Q e ω
  have hF := smooth_feedback_cell_affine_fields_memLp M m Q f ω
  unfold smoothFeedbackCellGammaPair
  rw [smooth_feedback_weak_vector_pairing_symm Q hE.1 hF.1,
    smooth_feedback_weak_vector_pairing_symm Q hE.2 hF.2]

private theorem smooth_feedback_cell_gamma_pair_add_left
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) (e f g : Vec 2) :
    smoothFeedbackCellGammaPair M m Q ω (e + f) g =
      smoothFeedbackCellGammaPair M m Q ω e g +
        smoothFeedbackCellGammaPair M m Q ω f g := by
  have hE := smooth_feedback_cell_affine_fields_memLp M m Q e ω
  have hF := smooth_feedback_cell_affine_fields_memLp M m Q f ω
  have hG := smooth_feedback_cell_affine_fields_memLp M m Q g ω
  have htop := smooth_feedback_affine_top_defect_add_ae M m Q e f ω
  have hrecip := smooth_feedback_affine_reciprocal_gradient_add_ae M m Q e f ω
  unfold smoothFeedbackCellGammaPair
  rw [smooth_feedback_weak_vector_pairing_congr_ae Q htop (Filter.EventuallyEq.rfl),
    smooth_feedback_weak_vector_pairing_congr_ae Q hrecip (Filter.EventuallyEq.rfl),
    smooth_feedback_weak_vector_pairing_add_left Q hE.1 hF.1 hG.1,
    smooth_feedback_weak_vector_pairing_add_left Q hE.2 hF.2 hG.2]
  ac_rfl

private theorem smooth_feedback_cell_gamma_pair_add_right
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) (e f g : Vec 2) :
    smoothFeedbackCellGammaPair M m Q ω e (f + g) =
      smoothFeedbackCellGammaPair M m Q ω e f +
        smoothFeedbackCellGammaPair M m Q ω e g := by
  rw [smooth_feedback_cell_gamma_pair_symm M m Q ω e (f + g),
    smooth_feedback_cell_gamma_pair_add_left M m Q ω f g e,
    smooth_feedback_cell_gamma_pair_symm M m Q ω e f,
    smooth_feedback_cell_gamma_pair_symm M m Q ω e g]

private theorem smooth_feedback_cell_gamma_pair_smul_left
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) (c : ℝ) (e f : Vec 2) :
    smoothFeedbackCellGammaPair M m Q ω (c • e) f =
      c * smoothFeedbackCellGammaPair M m Q ω e f := by
  have hE := smooth_feedback_cell_affine_fields_memLp M m Q e ω
  have hF := smooth_feedback_cell_affine_fields_memLp M m Q f ω
  have htop := smooth_feedback_affine_top_defect_smul_ae M m Q c e ω
  have hrecip := smooth_feedback_affine_reciprocal_gradient_smul_ae M m Q c e ω
  unfold smoothFeedbackCellGammaPair
  rw [smooth_feedback_weak_vector_pairing_congr_ae Q htop (Filter.EventuallyEq.rfl),
    smooth_feedback_weak_vector_pairing_congr_ae Q hrecip (Filter.EventuallyEq.rfl),
    smooth_feedback_weak_vector_pairing_smul_left Q hE.1 hF.1 c,
    smooth_feedback_weak_vector_pairing_smul_left Q hE.2 hF.2 c]
  ring

private theorem smooth_feedback_cell_gamma_pair_smul_right
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) (c : ℝ) (e f : Vec 2) :
    smoothFeedbackCellGammaPair M m Q ω e (c • f) =
      c * smoothFeedbackCellGammaPair M m Q ω e f := by
  rw [smooth_feedback_cell_gamma_pair_symm M m Q ω e (c • f),
    smooth_feedback_cell_gamma_pair_smul_left M m Q ω c f e,
    smooth_feedback_cell_gamma_pair_symm M m Q ω e f]

private theorem smooth_feedback_cell_gamma_pair_add_expansion
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) (e f : Vec 2) :
    smoothFeedbackCellDirectionalGamma M m Q (e + f) ω =
      smoothFeedbackCellDirectionalGamma M m Q e ω +
        2 * smoothFeedbackCellGammaPair M m Q ω e f +
        smoothFeedbackCellDirectionalGamma M m Q f ω := by
  have hsum := smooth_feedback_cell_gamma_pair_self M m Q ω (e + f)
  have he := smooth_feedback_cell_gamma_pair_self M m Q ω e
  have hf := smooth_feedback_cell_gamma_pair_self M m Q ω f
  calc
    _ = smoothFeedbackCellGammaPair M m Q ω (e + f) (e + f) := hsum.symm
    _ = smoothFeedbackCellGammaPair M m Q ω e e +
        smoothFeedbackCellGammaPair M m Q ω e f +
        smoothFeedbackCellGammaPair M m Q ω f e +
        smoothFeedbackCellGammaPair M m Q ω f f := by
      rw [smooth_feedback_cell_gamma_pair_add_left,
        smooth_feedback_cell_gamma_pair_add_right,
        smooth_feedback_cell_gamma_pair_add_right]
      ac_rfl
    _ = _ := by rw [he, hf, smooth_feedback_cell_gamma_pair_symm]; ring

private theorem smooth_feedback_cell_gamma_polar_eq_pair
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) (e f : Vec 2) :
    (smoothFeedbackCellDirectionalGamma M m Q (e + f) ω -
      smoothFeedbackCellDirectionalGamma M m Q e ω -
      smoothFeedbackCellDirectionalGamma M m Q f ω) / 2 =
      smoothFeedbackCellGammaPair M m Q ω e f := by
  rw [smooth_feedback_cell_gamma_pair_add_expansion]
  ring

/-- The polarization matrix of the actual OLD-law directional affine Gram. -/
noncomputable def smoothFeedbackCellGammaMatrix
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) : Mat 2 :=
  fun i j =>
    (smoothFeedbackCellDirectionalGamma M m Q (basisVec i + basisVec j) ω -
      smoothFeedbackCellDirectionalGamma M m Q (basisVec i) ω -
      smoothFeedbackCellDirectionalGamma M m Q (basisVec j) ω) / 2

private theorem smooth_feedback_cell_gamma_matrix_apply
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) (i j : Fin 2) :
    smoothFeedbackCellGammaMatrix M m Q ω i j =
      smoothFeedbackCellGammaPair M m Q ω (basisVec i) (basisVec j) := by
  exact smooth_feedback_cell_gamma_polar_eq_pair M m Q ω
    (basisVec i) (basisVec j)

private theorem smooth_feedback_cell_gamma_pair_basis_expansion
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) (e f : Vec 2) :
    smoothFeedbackCellGammaPair M m Q ω e f =
      ∑ i : Fin 2, ∑ j : Fin 2,
        e i * f j * smoothFeedbackCellGammaPair M m Q ω
          (basisVec i) (basisVec j) := by
  have he : e = e 0 • basisVec 0 + e 1 • basisVec 1 := by
    ext i
    fin_cases i <;> simp [basisVec]
  have hf : f = f 0 • basisVec 0 + f 1 • basisVec 1 := by
    ext i
    fin_cases i <;> simp [basisVec]
  rw [he, hf]
  have hExpand :
      smoothFeedbackCellGammaPair M m Q ω
          (e 0 • basisVec 0 + e 1 • basisVec 1)
          (f 0 • basisVec 0 + f 1 • basisVec 1) =
        (e 0 * f 0) * smoothFeedbackCellGammaPair M m Q ω
            (basisVec 0) (basisVec 0) +
        (e 0 * f 1) * smoothFeedbackCellGammaPair M m Q ω
            (basisVec 0) (basisVec 1) +
        (e 1 * f 0) * smoothFeedbackCellGammaPair M m Q ω
            (basisVec 1) (basisVec 0) +
        (e 1 * f 1) * smoothFeedbackCellGammaPair M m Q ω
            (basisVec 1) (basisVec 1) := by
    rw [smooth_feedback_cell_gamma_pair_add_right,
      smooth_feedback_cell_gamma_pair_add_left,
      smooth_feedback_cell_gamma_pair_add_left,
      smooth_feedback_cell_gamma_pair_smul_left,
      smooth_feedback_cell_gamma_pair_smul_right,
      smooth_feedback_cell_gamma_pair_smul_left,
      smooth_feedback_cell_gamma_pair_smul_right,
      smooth_feedback_cell_gamma_pair_smul_left,
      smooth_feedback_cell_gamma_pair_smul_right,
      smooth_feedback_cell_gamma_pair_smul_left,
      smooth_feedback_cell_gamma_pair_smul_right]
    ring
  rw [hExpand]
  simp [Fin.sum_univ_two]
  ring

theorem smooth_feedback_cell_gamma_matrix_quadratic_form
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) (e : Vec 2) :
    vecDot e (matVecMul (smoothFeedbackCellGammaMatrix M m Q ω) e) =
      smoothFeedbackCellDirectionalGamma M m Q e ω := by
  have hmatrix : vecDot e (matVecMul (smoothFeedbackCellGammaMatrix M m Q ω) e) =
      ∑ i : Fin 2, ∑ j : Fin 2,
        e i * e j * smoothFeedbackCellGammaPair M m Q ω
          (basisVec i) (basisVec j) := by
    simp [vecDot, matVecMul, smooth_feedback_cell_gamma_matrix_apply,
      Fin.sum_univ_two, mul_assoc, mul_comm, mul_left_comm]
    ring
  have hexpand := smooth_feedback_cell_gamma_pair_basis_expansion
    M m Q ω e e
  have hself := smooth_feedback_cell_gamma_pair_self M m Q ω e
  rw [hmatrix, ← hexpand, hself]

theorem smooth_feedback_cell_gamma_matrix_posSemidef
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) :
    (smoothFeedbackCellGammaMatrix M m Q ω).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, ?_⟩
  · rw [Matrix.isHermitian_iff_isSymm]
    ext i j
    change smoothFeedbackCellGammaMatrix M m Q ω j i =
      smoothFeedbackCellGammaMatrix M m Q ω i j
    rw [smooth_feedback_cell_gamma_matrix_apply,
      smooth_feedback_cell_gamma_matrix_apply]
    exact smooth_feedback_cell_gamma_pair_symm M m Q ω
      (basisVec j) (basisVec i)
  · intro e
    have hnonneg := smooth_feedback_cell_directional_gamma_nonneg M m Q e ω
    have hform := smooth_feedback_cell_gamma_matrix_quadratic_form M m Q ω e
    have hform_nonneg :
        0 ≤ vecDot e (matVecMul (smoothFeedbackCellGammaMatrix M m Q ω) e) := by
      rw [hform]
      exact hnonneg
    simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul, star_trivial] using
      hform_nonneg

end

end ASDExplicitGamma.Scalar
