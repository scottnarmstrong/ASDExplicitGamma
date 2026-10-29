module

public import ASDExplicitGamma.Native.SupportOverlap
public import ASDExplicitGamma.Native.VanishingBracket
public import ASDExplicitGamma.Main.CubeRestriction
public import ASDExplicitGamma.Variational.LemmaVTrace
public import ASDExplicitGamma.Gaussian.SupMeanKernelCovariance
public import ASDExplicitGamma.Triadic.PlanarDirectionSmooth
public import ASDExplicitGamma.Variational.LemmaVH2RemainderKernel

/-! # Localized white-noise observations of the frozen variational trace -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Set ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Response ASDExplicitGamma.Variational ASDExplicitGamma.Main
open ASDExplicitGamma.Triadic ASDExplicitGamma.Model
open scoped RealInnerProductSpace

noncomputable section

/-- Every physical q3 white-noise convolution has its actual global C²
representative, obtained from the first-jet convolution identity twice. -/
theorem q3Convolution_contDiff_two (β : ℝ) (L : {l : ℝ // 0 < l})
    (u : WhiteNoise) :
    ContDiff ℝ 2 (q3Convolution β L h3Zero u) := by
  let a₀ := h3Next h3Zero 0 (by norm_num [h3Zero])
  let a₁ := h3Next h3Zero 1 (by norm_num [h3Zero])
  have ha₀ : a₀.1.1.val + a₀.1.2.val ≤ 2 := by norm_num [a₀, h3Next, h3Zero]
  have ha₁ : a₁.1.1.val + a₁.1.2.val ≤ 2 := by norm_num [a₁, h3Next, h3Zero]
  have h₀ := q3Convolution_contDiff_one β L a₀ ha₀ u
  have h₁ := q3Convolution_contDiff_one β L a₁ ha₁ u
  let D : Vec 2 → Vec 2 →L[ℝ] ℝ := fun x =>
    q3Convolution β L a₀ u x • ContinuousLinearMap.proj 0 +
      q3Convolution β L a₁ u x • ContinuousLinearMap.proj 1
  have hD : ContDiff ℝ 1 D := by
    change ContDiff ℝ 1 (fun x =>
      q3Convolution β L a₀ u x • ContinuousLinearMap.proj 0 +
        q3Convolution β L a₁ u x • ContinuousLinearMap.proj 1)
    exact (h₀.smul contDiff_const).add (h₁.smul contDiff_const)
  refine (contDiff_succ_iff_hasFDerivAt (n := 1)).2 ⟨D, hD, ?_⟩
  intro x
  simpa [D, a₀, a₁, h3Zero] using
    q3Convolution_hasFDerivAt β L h3Zero (by norm_num [h3Zero]) u x

/-- The centered physical q3 field, realized as a genuine planar W²,∞
direction on the exact origin cube. -/
noncomputable def mainCubeQ3PhysicalDirection (m : ℤ) (β : ℝ)
    (L : {l : ℝ // 0 < l})
    (x₀ : closedRectangle (-mainCubeHalfSide m) (mainCubeHalfSide m)
      (-mainCubeHalfSide m) (mainCubeHalfSide m)) (u : WhiteNoise) :
    PlanarW2Infinity (originCube 2 m) :=
  PlanarW2Infinity.ofContDiff (originCube 2 m)
    (fun x => q3Convolution β L h3Zero u x -
      q3Convolution β L h3Zero u x₀.1)
    ((q3Convolution_contDiff_two β L u).sub contDiff_const)

/-- The same centered q3 field on the physical closed-square carrier used by
the response adapter. -/
noncomputable def mainCubeQ3PhysicalField (m : ℤ) (β : ℝ)
    (L : {l : ℝ // 0 < l})
    (x₀ : closedRectangle (-mainCubeHalfSide m) (mainCubeHalfSide m)
      (-mainCubeHalfSide m) (mainCubeHalfSide m)) (u : WhiteNoise) :
    C(closedRectangle (-mainCubeHalfSide m) (mainCubeHalfSide m)
      (-mainCubeHalfSide m) (mainCubeHalfSide m), ℝ) :=
  ⟨fun x => q3Convolution β L h3Zero u x.1 -
      q3Convolution β L h3Zero u x₀.1,
    ((q3Convolution_continuous β L h3Zero u).comp continuous_subtype_val).sub
      continuous_const⟩

private theorem smoothCoordinateDerivative_eq_supMeanCoordinateDerivative
    {f : Vec 2 → ℝ} (hf : Differentiable ℝ f) (i : Fin 2) (x : Vec 2) :
    smoothCoordinateDerivative f i x = supMeanCoordinateDerivative i f x := by
  have hline : HasDerivAt (fun t : ℝ => x+t • basisVec i) (basisVec i) 0 := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id (0:ℝ)).smul_const (basisVec i)).const_add x
  have hd := (hf (x + (0:ℝ) • basisVec i)).hasFDerivAt.comp_hasDerivAt 0 hline
  simp only [zero_smul, add_zero, Function.comp_def] at hd
  simpa only [smoothCoordinateDerivative, supMeanCoordinateDerivative] using hd.deriv.symm

/-- The value, first jet, and Hessian of each planar direction are exactly
the corresponding white-noise q3 kernel observations, centered only in value. -/
theorem mainCubeQ3PhysicalDirection_jet (m : ℤ) (β : ℝ)
    (L : {l : ℝ // 0 < l})
    (x₀ : closedRectangle (-mainCubeHalfSide m) (mainCubeHalfSide m)
      (-mainCubeHalfSide m) (mainCubeHalfSide m))
    (u : WhiteNoise) (o : Q3SpatialJet) (x : Vec 2) :
    q3DirectionJet (mainCubeQ3PhysicalDirection m β L x₀ u) o x =
      ⟪u, q3Section β L (supMeanKernelJetIndex o) x -
        (if o = .value then q3Section β L h3Zero x₀.1 else 0)⟫ := by
  let f : Vec 2 → ℝ := fun z => q3Convolution β L h3Zero u z -
    q3Convolution β L h3Zero u x₀.1
  have hf : ContDiff ℝ 2 f := by
    exact (q3Convolution_contDiff_two β L u).sub contDiff_const
  cases o with
  | value =>
      change (PlanarW2Infinity.ofContDiff (originCube 2 m) f hf).value.toFun x = _
      rw [PlanarW2Infinity.ofContDiff_value]
      simp [f, q3Convolution, supMeanKernelJetIndex, Q3SpatialJet.count, h3Zero]
      rw [inner_sub_right]
  | first i =>
      change (PlanarW2Infinity.ofContDiff (originCube 2 m) f hf).value.grad x i = _
      rw [PlanarW2Infinity.ofContDiff_grad]
      have hshift : smoothCoordinateDerivative f i x =
          smoothCoordinateDerivative (q3Convolution β L h3Zero u) i x := by
        simp [smoothCoordinateDerivative, f, fderiv_sub_const]
      rw [hshift, smoothCoordinateDerivative_eq_supMeanCoordinateDerivative
        (q3Convolution_contDiff_two β L u |>.differentiable (by norm_num))]
      rw [supMean_kernel_coordinate_derivative β L h3Zero
        (by norm_num [h3Zero]) u x i]
      rw [show supMeanKernelJetIndex (.first i) =
          h3Next h3Zero i (by norm_num [h3Zero]) by
        fin_cases i <;> rfl]
      have hvalue : Q3SpatialJet.first i ≠ Q3SpatialJet.value := by
        intro h
        cases h
      simp [q3Convolution, hvalue]
  | second i j =>
      change planarW1Derivative
        (PlanarW2Infinity.ofContDiff (originCube 2 m) f hf).gradient x i j = _
      rw [PlanarW2Infinity.ofContDiff_hessian]
      have hfun : (fun z => smoothCoordinateDerivative f i z) =
          q3Convolution β L
            (h3Next h3Zero i (by norm_num [h3Zero])) u := by
        funext z
        have hshift : smoothCoordinateDerivative f i z =
            smoothCoordinateDerivative (q3Convolution β L h3Zero u) i z := by
          simp [smoothCoordinateDerivative, f, fderiv_sub_const]
        rw [hshift, smoothCoordinateDerivative_eq_supMeanCoordinateDerivative
          (q3Convolution_contDiff_two β L u |>.differentiable (by norm_num))]
        exact supMean_kernel_coordinate_derivative β L h3Zero
          (by norm_num [h3Zero]) u z i
      change smoothCoordinateDerivative (fun z => smoothCoordinateDerivative f i z) j x = _
      rw [hfun]
      rw [smoothCoordinateDerivative_eq_supMeanCoordinateDerivative
        (q3Convolution_contDiff_one β L
          (h3Next h3Zero i (by norm_num [h3Zero]))
          (by fin_cases i <;> norm_num [h3Next, h3Zero]) u |>.differentiable (by norm_num))]
      rw [supMean_kernel_coordinate_derivative β L
        (h3Next h3Zero i (by norm_num [h3Zero]))
        (by fin_cases i <;> norm_num [h3Next, h3Zero]) u x j]
      rw [show supMeanKernelJetIndex (.second i j) =
          h3Next (h3Next h3Zero i (by norm_num [h3Zero])) j
            (by fin_cases i <;> norm_num [h3Next, h3Zero]) by
        fin_cases i <;> fin_cases j <;> rfl]
      have hvalue : Q3SpatialJet.second i j ≠ Q3SpatialJet.value := by
        intro h
        cases h
      simp [q3Convolution, hvalue]

@[simp] private theorem supMeanKernelJetIndex_value :
    supMeanKernelJetIndex Q3SpatialJet.value = h3Zero := by
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    rfl
  · apply Fin.ext
    rfl

/-- White-noise section representing the centered value or an uncentered
first/second derivative at a spatial point. -/
noncomputable def mainCubeQ3RemainderJetKernel (m : ℤ) (β : ℝ)
    (L : {l : ℝ // 0 < l})
    (x₀ : closedRectangle (-mainCubeHalfSide m) (mainCubeHalfSide m)
      (-mainCubeHalfSide m) (mainCubeHalfSide m))
    (o : Q3SpatialJet) (x : Vec 2) : WhiteNoise :=
  q3Section β L (supMeanKernelJetIndex o) x -
    (if o = .value then q3Section β L h3Zero x₀.1 else 0)

theorem mainCubeQ3RemainderJetKernel_covariance (m : ℤ) (β : ℝ)
    (L : {l : ℝ // 0 < l})
    (x₀ : closedRectangle (-mainCubeHalfSide m) (mainCubeHalfSide m)
      (-mainCubeHalfSide m) (mainCubeHalfSide m))
    (o p : Q3SpatialJet) (x y : Vec 2) :
    ⟪mainCubeQ3RemainderJetKernel m β L x₀ o x,
      mainCubeQ3RemainderJetKernel m β L x₀ p y⟫ =
        q3RemainderJetCovariance (β^2) L.1 x₀.1 o p x y := by
  cases o <;> cases p <;>
    (simp [mainCubeQ3RemainderJetKernel, q3RemainderJetCovariance,
      inner_sub_left, inner_sub_right] <;>
      simp only [← supMeanKernelJetIndex_value, ← real_inner_self_eq_norm_sq,
        supMean_kernel_jet_covariance, q3ScaledJetCovariance_value_diagonal] <;> ring)

/-- Enumerate the actual full white-noise Hilbert basis, with zero padding if
the general basis index type is not presented as `ℕ`. -/
noncomputable def mainCubeQ3WhiteNoiseSequence : ℕ → WhiteNoise :=
  gaussEnumerated whiteBasis

/-- The standard full white-noise basis gives an honest `RepresentsQ3Remainder`
family, including all cross-point and cross-jet covariance rows. -/
theorem mainCubeQ3PhysicalDirections_represent (m : ℤ) (β : ℝ)
    (L : {l : ℝ // 0 < l})
    (x₀ : closedRectangle (-mainCubeHalfSide m) (mainCubeHalfSide m)
      (-mainCubeHalfSide m) (mainCubeHalfSide m)) :
    RepresentsQ3Remainder
      (fun l => mainCubeQ3PhysicalDirection m β L x₀ (mainCubeQ3WhiteNoiseSequence l))
      (β^2) L.1 x₀.1 := by
  intro o p x y
  classical
  letI : Encodable whiteBasisIndex := Encodable.ofCountable whiteBasisIndex
  let X := mainCubeQ3RemainderJetKernel m β L x₀ o x
  let Y := mainCubeQ3RemainderJetKernel m β L x₀ p y
  let coeff : whiteBasisIndex → ℝ :=
    fun i => ⟪X, whiteBasis i⟫ * ⟪whiteBasis i, Y⟫
  have hsIndex : Summable coeff := by
    exact whiteBasis.summable_inner_mul_inner X Y
  have hseq : (fun n : ℕ =>
      ⟪X, mainCubeQ3WhiteNoiseSequence n⟫ *
        ⟪mainCubeQ3WhiteNoiseSequence n, Y⟫) = gaussEnumerated coeff := by
    funext n
    by_cases hn : n ∈ Set.range (Encodable.encode : whiteBasisIndex → ℕ)
    · obtain ⟨i, rfl⟩ := hn
      simp [mainCubeQ3WhiteNoiseSequence, coeff, enumerated_encode]
    · simp [mainCubeQ3WhiteNoiseSequence, coeff, gaussEnumerated,
        Function.extend_apply' _ _ _ hn]
  have hs : Summable (fun n : ℕ =>
      ⟪X, mainCubeQ3WhiteNoiseSequence n⟫ *
        ⟪mainCubeQ3WhiteNoiseSequence n, Y⟫) := by
    rw [hseq, gaussEnumerated]
    exact (summable_extend_zero Encodable.encode_injective).mpr hsIndex
  have ht : (∑' n : ℕ,
      ⟪X, mainCubeQ3WhiteNoiseSequence n⟫ *
        ⟪mainCubeQ3WhiteNoiseSequence n, Y⟫) = ⟪X, Y⟫ := by
    rw [hseq, gaussEnumerated, tsum_extend_zero Encodable.encode_injective]
    exact whiteBasis.tsum_inner_mul_inner X Y
  have hterm (n : ℕ) :
      q3DirectionJet
          (mainCubeQ3PhysicalDirection m β L x₀ (mainCubeQ3WhiteNoiseSequence n)) o x *
        q3DirectionJet
          (mainCubeQ3PhysicalDirection m β L x₀ (mainCubeQ3WhiteNoiseSequence n)) p y =
        ⟪X, mainCubeQ3WhiteNoiseSequence n⟫ *
          ⟪mainCubeQ3WhiteNoiseSequence n, Y⟫ := by
    rw [mainCubeQ3PhysicalDirection_jet, mainCubeQ3PhysicalDirection_jet]
    change ⟪mainCubeQ3WhiteNoiseSequence n, X⟫ *
        ⟪mainCubeQ3WhiteNoiseSequence n, Y⟫ =
      ⟪X, mainCubeQ3WhiteNoiseSequence n⟫ *
        ⟪mainCubeQ3WhiteNoiseSequence n, Y⟫
    rw [real_inner_comm (mainCubeQ3WhiteNoiseSequence n) X]
  constructor
  · exact hs.congr (fun n => (hterm n).symm)
  · calc
      (∑' l : ℕ, q3DirectionJet
          (mainCubeQ3PhysicalDirection m β L x₀ (mainCubeQ3WhiteNoiseSequence l)) o x *
          q3DirectionJet
            (mainCubeQ3PhysicalDirection m β L x₀ (mainCubeQ3WhiteNoiseSequence l)) p y) =
          ∑' l : ℕ,
            ⟪X, mainCubeQ3WhiteNoiseSequence l⟫ *
              ⟪mainCubeQ3WhiteNoiseSequence l, Y⟫ := by
            apply tsum_congr
            intro l
            simpa only [Function.comp_apply] using hterm l
      _ = ⟪X, Y⟫ := ht
      _ = q3RemainderJetCovariance (β^2) L.1 x₀.1 o p x y := by
        exact mainCubeQ3RemainderJetKernel_covariance m β L x₀ o p x y

/-- Restrict a continuous field on the physical closed square to the closed
response domain used by the variational trace. -/
noncomputable def mainCubeResponseAdapter (m : ℤ) :
    C(closedRectangle (-mainCubeHalfSide m) (mainCubeHalfSide m)
      (-mainCubeHalfSide m) (mainCubeHalfSide m), ℝ) →L[ℝ]
        ResponseCoefficient (openCubeSet (originCube 2 m)) := by
  let U := openCubeSet (originCube 2 m)
  let K := closedRectangle (-mainCubeHalfSide m) (mainCubeHalfSide m)
    (-mainCubeHalfSide m) (mainCubeHalfSide m)
  letI : CompactSpace (closure U) :=
    isCompact_iff_compactSpace.mp (isBounded_openCubeSet (originCube 2 m)).isCompact_closure
  have hK : closure (cubeSet (originCube 2 m)) = K := by
    simpa [K, mainCubeHalfSide, neg_div] using main_origin_cube_closure_rectangle m
  have hsub : closure U ⊆ K := by
    rw [← hK]
    exact closure_mono (openCubeSet_subset_cubeSet (originCube 2 m))
  let restrict : C(K, ℝ) →L[ℝ] C(closure U, ℝ) :=
    ContinuousMap.compCLM ℝ ℝ
      ⟨fun x => ⟨x.1, hsub x.2⟩, continuous_subtype_val.subtype_mk _⟩
  exact (ContinuousMap.linearIsometryBoundedOfCompact (closure U) ℝ ℝ).toLinearIsometry
    |>.toContinuousLinearMap.comp restrict

theorem mainCubeResponseAdapter_apply (m : ℤ)
    (f : C(closedRectangle (-mainCubeHalfSide m) (mainCubeHalfSide m)
      (-mainCubeHalfSide m) (mainCubeHalfSide m), ℝ))
    {x : Vec 2} (hx : x ∈ openCubeSet (originCube 2 m)) :
    mainCubeResponseAdapter m f ⟨x, subset_closure hx⟩ =
      f ⟨x, by
        have hK : closure (cubeSet (originCube 2 m)) =
            closedRectangle (-mainCubeHalfSide m) (mainCubeHalfSide m)
              (-mainCubeHalfSide m) (mainCubeHalfSide m) := by
          simpa only [mainCubeHalfSide, neg_div] using main_origin_cube_closure_rectangle m
        rw [← hK]
        exact subset_closure (openCubeSet_subset_cubeSet (originCube 2 m) hx)⟩ := by
  simp [mainCubeResponseAdapter, ContinuousMap.compCLM_apply]

/-- The response-coefficient direction whose source normalization is
`H = σ η`, as required by the frozen variational trace. -/
noncomputable def mainCubeQ3ResponseDirection (m : ℤ) (σ β : ℝ)
    (L : {l : ℝ // 0 < l})
    (x₀ : closedRectangle (-mainCubeHalfSide m) (mainCubeHalfSide m)
      (-mainCubeHalfSide m) (mainCubeHalfSide m)) (u : WhiteNoise) :
    ResponseCoefficient (openCubeSet (originCube 2 m)) :=
  σ • mainCubeResponseAdapter m (mainCubeQ3PhysicalField m β L x₀ u)

/-- The physical PlanarW2Infinity value is exactly the response-adapted field
after dividing the response coefficient by the true frame. -/
theorem mainCubeQ3PhysicalDirection_response_link (m : ℤ) (σ β : ℝ)
    (hσ : 0 < σ) (L : {l : ℝ // 0 < l})
    (x₀ : closedRectangle (-mainCubeHalfSide m) (mainCubeHalfSide m)
      (-mainCubeHalfSide m) (mainCubeHalfSide m)) (u : WhiteNoise) :
    (mainCubeQ3PhysicalDirection m β L x₀ u).value.toFun =ᵐ[
      volume.restrict (openCubeSet (originCube 2 m))]
      fun x => responseCoefficientExtension
        (mainCubeQ3ResponseDirection m σ β L x₀ u) x / σ := by
  apply ae_restrict_of_forall_mem
    (measurableSet_openCubeSet (originCube 2 m))
  intro x hx
  have hfield : (mainCubeQ3PhysicalDirection m β L x₀ u).value.toFun x =
      q3Convolution β L h3Zero u x -
        q3Convolution β L h3Zero u x₀.1 := by
    change (PlanarW2Infinity.ofContDiff (originCube 2 m)
      (fun z => q3Convolution β L h3Zero u z -
        q3Convolution β L h3Zero u x₀.1) _).value.toFun x = _
    rw [PlanarW2Infinity.ofContDiff_value]
  rw [hfield]
  change q3Convolution β L h3Zero u x -
      q3Convolution β L h3Zero u x₀.1 =
    responseCoefficientExtension
      (σ • mainCubeResponseAdapter m (mainCubeQ3PhysicalField m β L x₀ u)) x / σ
  rw [responseCoefficientExtension_smul_on σ _ hx,
    responseCoefficientExtension_eq _ hx,
    mainCubeResponseAdapter_apply m (mainCubeQ3PhysicalField m β L x₀ u) hx]
  change q3Convolution β L h3Zero u x -
      q3Convolution β L h3Zero u x₀.1 =
    (σ * (q3Convolution β L h3Zero u x -
      q3Convolution β L h3Zero u x₀.1)) / σ
  field_simp [ne_of_gt hσ]

/-- On the physical closed square, the realized field is the exact centered
value factor used by the localized white-noise support theorem. -/
theorem mainCubeQ3PhysicalField_eq_remainderValueFactor (m : ℤ) (β : ℝ)
    (L : {l : ℝ // 0 < l})
    (x₀ : closedRectangle (-mainCubeHalfSide m) (mainCubeHalfSide m)
      (-mainCubeHalfSide m) (mainCubeHalfSide m)) (u : WhiteNoise) :
    mainCubeQ3PhysicalField m β L x₀ u =
      q3RemainderValueFactor (-mainCubeHalfSide m) (mainCubeHalfSide m)
        (-mainCubeHalfSide m) (mainCubeHalfSide m) β L x₀ u := by
  have hside : 0 < mainCubeHalfSide m := by
    dsimp [mainCubeHalfSide, cubeScaleFactor]
    positivity
  apply ContinuousMap.ext
  intro x
  simp only [mainCubeQ3PhysicalField, q3RemainderValueFactor,
    ContinuousLinearMap.comp_apply, centeringMap_apply]
  rw [q3H3RangeValue_factor (-mainCubeHalfSide m) (mainCubeHalfSide m)
      (-mainCubeHalfSide m) (mainCubeHalfSide m) β (by linarith) (by linarith)
      L u x,
    q3H3RangeValue_factor (-mainCubeHalfSide m) (mainCubeHalfSide m)
      (-mainCubeHalfSide m) (mainCubeHalfSide m) β (by linarith) (by linarith)
      L u x₀]
  simp [q3Convolution]

/- The physical center point on the square carrier. -/
noncomputable def mainCubeRectangleCenter (m : ℤ) :
    closedRectangle (-mainCubeHalfSide m) (mainCubeHalfSide m)
      (-mainCubeHalfSide m) (mainCubeHalfSide m) := by
  have hc : cubeCenter (originCube 2 m) = 0 := by
    ext i
    simp [cubeCenter, originCube]
  have hs : 0 < mainCubeHalfSide m := by
    dsimp [mainCubeHalfSide, cubeScaleFactor]
    positivity
  refine ⟨cubeCenter (originCube 2 m), ?_⟩
  rw [hc]
  constructor <;> constructor <;> simp only [Pi.zero_apply] <;> linarith

/-- Lemma V's actual remainder-family adapter, with its covariance
representation and source-normalized response directions constructed from the
full white-noise basis. -/
theorem mainCubeQ3TraceRemainderBracket (m : ℤ) (j : ℕ) (ν σ β : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ) (L : {l : ℝ // 0 < l})
    (k : ResponseCoefficient (openCubeSet (originCube 2 m))) :
    let Q := originCube 2 m
    let H := fun l => mainCubeQ3ResponseDirection m σ β L (mainCubeRectangleCenter m)
      (mainCubeQ3WhiteNoiseSequence l)
    let κ := Real.sqrt (β ^ 2) *
      lemmaVH2Bn (cubeScaleFactor Q / L.1) (diagMeshRadius Q j / L.1)
    (∀ (s : Finset ℕ) (c : ℕ → ℝ), (∑ l ∈ s, c l ^ 2) ≤ 1 →
      |fderiv ℝ (lemmaVTrace m ν σ) k (∑ l ∈ s, c l • H l)| ≤
        2 * κ * lemmaVTileHistory Q j (responseFramePlanarCoefficientField ν σ k) *
          Real.sqrt (lemmaVTrace m ν σ k * (lemmaVTrace m ν σ k + 4)) *
            Real.sqrt (∑ l ∈ s, c l ^ 2)) ∧
    Summable (fun l : ℕ => (fderiv ℝ (lemmaVTrace m ν σ) k (H l)) ^ 2) ∧
    (∑' l : ℕ, (fderiv ℝ (lemmaVTrace m ν σ) k (H l)) ^ 2) ≤
      4 * κ ^ 2 * (lemmaVTileHistory Q j (responseFramePlanarCoefficientField ν σ k)) ^ 2 *
        lemmaVTrace m ν σ k * (lemmaVTrace m ν σ k + 4) := by
  exact nativeRemainderTraceBracket m j ν σ hν hσ k
    (fun l => mainCubeQ3ResponseDirection m σ β L (mainCubeRectangleCenter m)
      (mainCubeQ3WhiteNoiseSequence l))
    (fun l => mainCubeQ3PhysicalDirection m β L (mainCubeRectangleCenter m)
      (mainCubeQ3WhiteNoiseSequence l))
    (β ^ 2) L.1 (mainCubeQ3PhysicalDirections_represent m β L
      (mainCubeRectangleCenter m))
    (sq_nonneg β) L.2
    (fun l => mainCubeQ3PhysicalDirection_response_link m σ β hσ L
      (mainCubeRectangleCenter m) (mainCubeQ3WhiteNoiseSequence l))

/-- The exact derivative of the source four-load trace, transported from the
physical closed square to its response coefficient carrier. -/
noncomputable def mainCubeTraceDerivativeObservation (m : ℤ) (ν σ : ℝ)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m))) :
    C(closedRectangle (-mainCubeHalfSide m) (mainCubeHalfSide m)
      (-mainCubeHalfSide m) (mainCubeHalfSide m), ℝ) →L[ℝ] ℝ :=
  (fderiv ℝ (lemmaVTrace m ν σ) k).comp
    ((σ • (ContinuousLinearMap.id ℝ _)).comp (mainCubeResponseAdapter m))

theorem mainCubeTraceDerivativeObservation_apply (m : ℤ) (ν σ : ℝ)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m)))
    (f : C(closedRectangle (-mainCubeHalfSide m) (mainCubeHalfSide m)
      (-mainCubeHalfSide m) (mainCubeHalfSide m), ℝ)) :
    mainCubeTraceDerivativeObservation m ν σ k f =
      fderiv ℝ (lemmaVTrace m ν σ) k (σ • mainCubeResponseAdapter m f) := rfl

/-- Along each actual q3 noise direction, the source trace derivative is the
white-noise pairing with its localized Riesz gradient. -/
theorem mainCubeTraceDerivative_whiteNoise_pairing (m : ℤ) (ν σ β : ℝ)
    (L : {l : ℝ // 0 < l})
    (x₀ : closedRectangle (-mainCubeHalfSide m) (mainCubeHalfSide m)
      (-mainCubeHalfSide m) (mainCubeHalfSide m))
    (k : ResponseCoefficient (openCubeSet (originCube 2 m))) (u : WhiteNoise) :
    fderiv ℝ (lemmaVTrace m ν σ) k
        (mainCubeQ3ResponseDirection m σ β L x₀ u) =
      ⟪(InnerProductSpace.toDual ℝ WhiteNoise).symm
          ((mainCubeTraceDerivativeObservation m ν σ k).comp
            (q3RemainderValueFactor
              (-mainCubeHalfSide m) (mainCubeHalfSide m)
              (-mainCubeHalfSide m) (mainCubeHalfSide m) β L x₀)), u⟫ := by
  let O := mainCubeTraceDerivativeObservation m ν σ k
  let F := q3RemainderValueFactor
    (-mainCubeHalfSide m) (mainCubeHalfSide m)
    (-mainCubeHalfSide m) (mainCubeHalfSide m) β L x₀
  calc
    fderiv ℝ (lemmaVTrace m ν σ) k
        (mainCubeQ3ResponseDirection m σ β L x₀ u) =
        O (mainCubeQ3PhysicalField m β L x₀ u) := by
          exact (mainCubeTraceDerivativeObservation_apply m ν σ k
            (mainCubeQ3PhysicalField m β L x₀ u)).symm
    _ = O (F u) := by
      exact congrArg O (mainCubeQ3PhysicalField_eq_remainderValueFactor
        m β L x₀ u)
    _ = (O.comp F) u := rfl
    _ = ⟪(InnerProductSpace.toDual ℝ WhiteNoise).symm (O.comp F), u⟫ := by
      exact (congrArg (fun A : WhiteNoise →L[ℝ] ℝ => A u)
        ((InnerProductSpace.toDual ℝ WhiteNoise).apply_symm_apply (O.comp F))).symm

/-- Parseval identifies the complete sequence of trace derivatives along the
physical q3 basis directions with the squared norm of its actual Riesz
gradient. -/
theorem mainCubeTraceDerivative_basis_sq_eq_riesz_norm_sq (m : ℤ) (ν σ β : ℝ)
    (L : {l : ℝ // 0 < l})
    (x₀ : closedRectangle (-mainCubeHalfSide m) (mainCubeHalfSide m)
      (-mainCubeHalfSide m) (mainCubeHalfSide m))
    (k : ResponseCoefficient (openCubeSet (originCube 2 m))):
    (∑' n : ℕ, (fderiv ℝ (lemmaVTrace m ν σ) k
      (mainCubeQ3ResponseDirection m σ β L x₀
        (mainCubeQ3WhiteNoiseSequence n))) ^ 2) =
      ‖(InnerProductSpace.toDual ℝ WhiteNoise).symm
        ((mainCubeTraceDerivativeObservation m ν σ k).comp
          (q3RemainderValueFactor
            (-mainCubeHalfSide m) (mainCubeHalfSide m)
            (-mainCubeHalfSide m) (mainCubeHalfSide m) β L x₀))‖ ^ 2 := by
  classical
  letI : Encodable whiteBasisIndex := Encodable.ofCountable whiteBasisIndex
  let O := mainCubeTraceDerivativeObservation m ν σ k
  let F := q3RemainderValueFactor
    (-mainCubeHalfSide m) (mainCubeHalfSide m)
    (-mainCubeHalfSide m) (mainCubeHalfSide m) β L x₀
  let A : WhiteNoise →L[ℝ] ℝ := O.comp F
  let r : WhiteNoise := (InnerProductSpace.toDual ℝ WhiteNoise).symm A
  have hdual (u : WhiteNoise) : A u = ⟪r, u⟫ := by
    exact (congrArg (fun T : WhiteNoise →L[ℝ] ℝ => T u)
      ((InnerProductSpace.toDual ℝ WhiteNoise).apply_symm_apply A)).symm
  have hterm (n : ℕ) :
      fderiv ℝ (lemmaVTrace m ν σ) k
          (mainCubeQ3ResponseDirection m σ β L x₀
            (mainCubeQ3WhiteNoiseSequence n)) =
        A (mainCubeQ3WhiteNoiseSequence n) := by
    dsimp [A, O, F]
    exact (mainCubeTraceDerivative_whiteNoise_pairing m ν σ β L x₀ k
      (mainCubeQ3WhiteNoiseSequence n)).trans
        (hdual (mainCubeQ3WhiteNoiseSequence n)).symm
  calc
    _ = ∑' n : ℕ, (A (mainCubeQ3WhiteNoiseSequence n)) ^ 2 := by
      apply tsum_congr
      intro n
      rw [hterm n]
    _ = ∑' i : whiteBasisIndex, (A (whiteBasis i)) ^ 2 := by
      simpa [A, mainCubeQ3WhiteNoiseSequence] using
        (enumerated_tsum_apply whiteBasis (fun u => (A u) ^ 2) (by simp))
    _ = ‖r‖ ^ 2 := by
      simpa [r, A] using hilbertBasis_variance whiteBasis A

/-- The actual Riesz gradient of the frozen trace in the q3 remainder field
obeys the vanishing Lemma V bound. -/
theorem mainCubeTraceDerivativeRiesz_norm_sq_le (m : ℤ) (j : ℕ)
    (ν σ β : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (L : {l : ℝ // 0 < l})
    (k : ResponseCoefficient (openCubeSet (originCube 2 m))) :
    ‖(InnerProductSpace.toDual ℝ WhiteNoise).symm
        ((mainCubeTraceDerivativeObservation m ν σ k).comp
          (q3RemainderValueFactor
            (-mainCubeHalfSide m) (mainCubeHalfSide m)
            (-mainCubeHalfSide m) (mainCubeHalfSide m) β L
            (mainCubeRectangleCenter m)))‖ ^ 2 ≤
      4 * (Real.sqrt (β ^ 2) * lemmaVH2Bn
        (cubeScaleFactor (originCube 2 m) / L.1)
        (diagMeshRadius (originCube 2 m) j / L.1)) ^ 2 *
        (lemmaVTileHistory (originCube 2 m) j
          (responseFramePlanarCoefficientField ν σ k)) ^ 2 *
        lemmaVTrace m ν σ k * (lemmaVTrace m ν σ k + 4) := by
  have hV := mainCubeQ3TraceRemainderBracket m j ν σ β hν hσ L k
  rcases hV with ⟨_, _, hsum⟩
  have hparse := mainCubeTraceDerivative_basis_sq_eq_riesz_norm_sq m ν σ β L
    (mainCubeRectangleCenter m) k
  simpa [mainCubeQ3ResponseDirection] using hparse.symm.trans_le hsum

/-- Actual q3 remainder Riesz gradients obey the finite support-overlap
averaging inequality on any finite family of physical rectangles. The only
geometric input is the pointwise multiplicity of the explicitly enlarged
q3 supports. -/
theorem q3RemainderRiesz_average_sq_le_support_overlap
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (a b c d β : ι → ℝ) (L : ι → {l : ℝ // 0 < l})
    (x₀ : ∀ i, closedRectangle (a i) (b i) (c i) (d i))
    (O : ∀ i, C(closedRectangle (a i) (b i) (c i) (d i), ℝ) →L[ℝ] ℝ)
    (hab : ∀ i ∈ S, a i < b i) (hcd : ∀ i ∈ S, c i < d i)
    (M : ℝ) (hM : 0 ≤ M) (hN : 0 < (S.card : ℝ))
    (U : Vec 2 → Finset ι)
    (hactive : ∀ x i, i ∈ U x ↔
      x ∈ q3ExpandedRectangle (a i) (b i) (c i) (d i) (L i))
    (hoverlap : ∀ x : Vec 2, ((S ∩ U x).card : ℝ) ≤ M) :
    ‖((S.card : ℝ)⁻¹) • ∑ i ∈ S,
        (InnerProductSpace.toDual ℝ WhiteNoise).symm
          ((O i).comp (q3RemainderValueFactor
            (a i) (b i) (c i) (d i) (β i) (L i) (x₀ i)))‖ ^ 2 ≤
      M * ((S.card : ℝ)⁻¹) ^ 2 * ∑ i ∈ S,
        ‖(InnerProductSpace.toDual ℝ WhiteNoise).symm
          ((O i).comp (q3RemainderValueFactor
            (a i) (b i) (c i) (d i) (β i) (L i) (x₀ i)))‖ ^ 2 := by
  let A : ι → Set (Vec 2) := fun i =>
    q3ExpandedRectangle (a i) (b i) (c i) (d i) (L i)
  let X : ι → WhiteNoise := fun i =>
    (InnerProductSpace.toDual ℝ WhiteNoise).symm
      ((O i).comp (q3RemainderValueFactor
        (a i) (b i) (c i) (d i) (β i) (L i) (x₀ i)))
  have hzero (i : ι) (hi : i ∈ S) :
      ∀ᵐ x : Vec 2 ∂(volume : Measure (Vec 2)), x ∉ A i → X i x = 0 := by
    simpa [X, A] using q3RemainderObservation_riesz_support
      (a i) (b i) (c i) (d i) (β i) (hab i hi) (hcd i hi)
      (L i) (x₀ i) (O i)
  exact whiteNoise_average_sq_le_supportOverlap S X A U M hM hN hactive hzero
    (Filter.Eventually.of_forall hoverlap)

end
end ASDExplicitGamma.Native
