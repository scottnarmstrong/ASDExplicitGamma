module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorQ3Map
public import ASDExplicitGamma.Inverse.PureFluxGeneratorOpenBridge
public import ASDExplicitGamma.Inverse.PureFluxGeneratorTraceLimit
public import ASDExplicitGamma.Gaussian.GeneratorBounds

/-! The actual physical q3 directions and their common white-noise enumeration. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization MeasureTheory ASDExplicitGamma.Inverse ASDExplicitGamma.Main
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Model
  ASDExplicitGamma.Variational
noncomputable section

theorem main_q3_responseCoefficient_eq_restriction
    (n : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l}) (j : ℕ) :
    pureFluxMainCubeQ3ResponseCoefficient n b L j =
      pureFluxOpenResponseRestriction n (pureFluxMainCubeQ3Directions n b L j) := by
  ext x
  rfl

/-- Restricting the actual compact q3 directions preserves square summability. -/
theorem main_q3_responseCoefficient_summable
    (n : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l}) :
    Summable (fun j => ‖pureFluxMainCubeQ3ResponseCoefficient n b L j‖^2) := by
  have hH : Summable (fun j => ‖pureFluxMainCubeQ3Directions n b L j‖^2) :=
    @summable_sq_bounded_image ℕ (MainCubeH3 n b L)
      C(closure (cubeSet (originCube 2 n)), ℝ)
      inferInstance (mainCubeH3InnerProductSpace n b L).toNormedSpace
      inferInstance inferInstance (mainCubeQ3Directions n b L)
      (mainCubeQ3Directions_summable n b L) (mainCubeH3Value n b L)
  have hr := summable_sq_bounded_image (pureFluxMainCubeQ3Directions n b L)
    hH (pureFluxOpenResponseRestriction n)
  simpa only [← main_q3_responseCoefficient_eq_restriction] using hr

theorem main_q3_directions_tsum_apply (n : ℤ) (b : ℝ)
    (L : {l : ℝ // 0 < l})
    (f : ResponseCoefficient (openCubeSet (originCube 2 n)) → ℝ) (hf : f 0 = 0) :
    (∑' j, f (pureFluxMainCubeQ3ResponseCoefficient n b L j)) =
      ∑' l : whiteBasisIndex, f (pureFluxMainCubeQ3ResponseCoefficient n b L
        (@Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex) l)) := by
  classical
  let enc := @Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex)
  let v := fun l : whiteBasisIndex => pureFluxMainCubeQ3ResponseCoefficient n b L (enc l)
  have hz (j : ℕ) (hj : j ∉ Set.range enc) :
      pureFluxMainCubeQ3ResponseCoefficient n b L j = 0 := by
    rw [main_q3_responseCoefficient_eq_restriction]
    have hdir : pureFluxMainCubeQ3Directions n b L j = 0 := by
      unfold pureFluxMainCubeQ3Directions mainCubeQ3Directions q3H3Directions
      rw [gaussEnumerated, Function.extend_apply' _ _ _ hj]
      exact map_zero _
    rw [hdir, map_zero]
  have heq (j : ℕ) : pureFluxMainCubeQ3ResponseCoefficient n b L j = gaussEnumerated v j := by
    by_cases hj : j ∈ Set.range enc
    · obtain ⟨l, rfl⟩ := hj
      rw [enumerated_encode]
    · rw [hz j hj, gaussEnumerated, Function.extend_apply' _ _ _ hj]
      rfl
  simp_rw [heq]
  simpa only [enumerated_encode] using enumerated_tsum_apply v f hf

/-- Zero padding preserves summability for a scalar expression that vanishes
at the zero vector. -/
theorem enumerated_summable_apply {ι V : Type*} [Countable ι] [Zero V]
    (v : ι → V) (f : V → ℝ) (hf : f 0 = 0)
    (hs : Summable (fun i => f (v i))) :
    Summable (fun n => f (gaussEnumerated v n)) := by
  classical
  let := Encodable.ofCountable ι
  have he : (fun n => f (gaussEnumerated v n)) =
      Function.extend Encodable.encode (fun i => f (v i)) 0 := by
    funext n
    by_cases hn : n ∈ Set.range (Encodable.encode : ι → ℕ)
    · obtain ⟨i, rfl⟩ := hn
      rw [enumerated_encode, Function.Injective.extend_apply Encodable.encode_injective]
    · rw [gaussEnumerated, Function.extend_apply' _ _ _ hn, Function.extend_apply' _ _ _ hn]
      exact hf
  rw [he]
  exact (summable_extend_zero Encodable.encode_injective).mpr hs

/-- The actual enumerated q3 directions retain every cross-point and
cross-jet covariance used by the closed Lemma V band estimate. -/
theorem main_shell_enumerated_representation (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) :
    RepresentsQ3Band
      (fun n => mainQ3DirectionW2 Q b L (gaussEnumerated whiteBasis n))
      {()} (fun _ => b ^ 2) (fun _ => L.1) := by
  intro o p x y
  let f : WhiteNoise → ℝ := fun u =>
    q3Convolution b L (supMeanKernelJetIndex o) u x *
      q3Convolution b L (supMeanKernelJetIndex p) u y
  have hf : f 0 = 0 := by simp [f, q3Convolution]
  have hcov := main_q3_direction_covariance whiteBasis b L
    (supMeanKernelJetIndex o) (supMeanKernelJetIndex p) x y
  rw [supMean_kernel_jet_covariance] at hcov
  have hs := enumerated_summable_apply whiteBasis f hf hcov.summable
  have ht := enumerated_tsum_apply whiteBasis f hf
  rw [hcov.tsum_eq] at ht
  have hidx (q : Q3SpatialJet) : mainQ3JetIndex q = supMeanKernelJetIndex q := by
    cases q <;> rfl
  constructor
  · simpa only [mainQ3DirectionW2_jet, hidx, f] using hs
  · simpa [mainQ3DirectionW2_jet, hidx, f, q3BandJetCovariance,
      q3ScaledJetCovariance, q3BandMoment] using ht

/-- Dividing the physical shell amplitude divides its actual convolution
coordinate by the deterministic frame. -/
theorem q3_convolution_div_frame (b σ : ℝ) (L : {l : ℝ // 0 < l})
    (a : H3Index) (u : WhiteNoise) (x : Vec 2) :
    q3Convolution (b / σ) L a u x = q3Convolution b L a u x / σ := by
  rw [q3Convolution_eq_integral, q3Convolution_eq_integral]
  have he : (fun y => q3SectionFunction (b / σ) L a x y * u y) =
      fun y => σ⁻¹ * (q3SectionFunction b L a x y * u y) := by
    funext y
    unfold q3SectionFunction
    ring
  rw [he, integral_const_mul]
  ring

end
end ASDExplicitGamma.Gaussian
