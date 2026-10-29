module

public import ASDExplicitGamma.Scalar.PairWeakParent
public import ASDExplicitGamma.Scalar.SmoothFeedbackGapMeasurable
public import ASDExplicitGamma.Native.OldSignedEnergyPairingAlgebra

/-! Uniqueness of the physical block minimizer in a variation class, and the block field of a
pair-space (two-slot) solution. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Native
open scoped InnerProduct InnerProductSpace

noncomputable section

/-- A block field of zero physical energy vanishes almost everywhere. -/
theorem energy_zero_ae (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) {D : Vec 2 → BlockVec 2}
    (hD : MemBlockL2 (openCubeSet Q) D)
    (h0 : oldSignedEnergyPairing Q ν σ k D D = 0) :
    ∀ᵐ x ∂(volumeMeasureOn (openCubeSet Q)), D x = 0 := by
  have hE := (scalarFieldEnergy_eq_pairing Q ν σ hν hσ k D).trans h0
  have hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q
  unfold scalarFieldEnergy volumeAverage at hE
  have hI : ∫ x in openCubeSet Q, responseFrameEnergyDensity ν σ
      (responseCoefficientExtension k x) (D x) ∂volume = 0 := by
    rcases mul_eq_zero.1 hE with h | h
    · exact absurd h (inv_ne_zero hvol.ne')
    · exact h
  have hint := scalar_field_density_integrable Q ν σ hν hσ k hD
  have hnn : 0 ≤ᵐ[volumeMeasureOn (openCubeSet Q)] fun x => responseFrameEnergyDensity ν σ
      (responseCoefficientExtension k x) (D x) := Filter.Eventually.of_forall fun x => by
    unfold responseFrameEnergyDensity
    exact add_nonneg (mul_nonneg (div_pos hν hσ).le (vecNormSq_nonneg _))
      (mul_nonneg (div_pos hσ hν).le (vecNormSq_nonneg _))
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 hI
  filter_upwards [hz] with x hx
  have hx' : (ν / σ) * vecNormSq (D x).1 + (σ / ν) * vecNormSq ((D x).2 -
      (responseCoefficientExtension k x / σ) • matVecMul responsePlanarJ (D x).1) = 0 := hx
  have h1 : 0 ≤ (ν / σ) * vecNormSq (D x).1 := mul_nonneg (div_pos hν hσ).le (vecNormSq_nonneg _)
  have h2 : 0 ≤ (σ / ν) * vecNormSq ((D x).2 -
      (responseCoefficientExtension k x / σ) • matVecMul responsePlanarJ (D x).1) :=
    mul_nonneg (div_pos hσ hν).le (vecNormSq_nonneg _)
  have e1 : (ν / σ) * vecNormSq (D x).1 = 0 := by linarith
  have e2 : (σ / ν) * vecNormSq ((D x).2 -
      (responseCoefficientExtension k x / σ) • matVecMul responsePlanarJ (D x).1) = 0 := by
    linarith
  have hp : (D x).1 = 0 := vecNormSq_eq_zero
    ((mul_eq_zero.1 e1).resolve_left (div_pos hν hσ).ne')
  have hq := vecNormSq_eq_zero ((mul_eq_zero.1 e2).resolve_left (div_pos hσ hν).ne')
  rw [hp] at hq
  have hq' : (D x).2 = 0 := by
    have : matVecMul responsePlanarJ (0 : Vec 2) = 0 := by
      ext i; simp [matVecMul]
    simpa [this] using hq
  exact Prod.ext hp hq'

/-- Two block fields that differ from the same affine datum by variations and have the same
Euler pairing against every variation agree almost everywhere. -/
theorem block_unique (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) {Z Z' P : Vec 2 → BlockVec 2}
    (hP : MemBlockL2 (openCubeSet Q) P)
    (hV : ScalarVariation (openCubeSet Q) (fun x => Z x - P x))
    (hV' : ScalarVariation (openCubeSet Q) (fun x => Z' x - P x))
    (hE : ∀ Y : Vec 2 → BlockVec 2, ScalarVariation (openCubeSet Q) Y →
      oldSignedEnergyPairing Q ν σ k Z Y = oldSignedEnergyPairing Q ν σ k Z' Y) :
    ∀ᵐ x ∂(volumeMeasureOn (openCubeSet Q)), Z x = Z' x := by
  have hD : ScalarVariation (openCubeSet Q) (fun x => Z x - Z' x) := by
    have hfun : (fun x => Z x - Z' x) = (fun x => Z x - P x) +
        (-1 : ℝ) • (fun x => Z' x - P x) := by
      funext x
      simp only [Pi.add_apply, Pi.smul_apply]
      ext j <;> simp
    rw [hfun]
    exact scalar_variation_add hV (scalar_variation_smul hV' _)
  have hZ : MemBlockL2 (openCubeSet Q) Z := by
    have h := hV.1.add hP
    convert h using 1
    funext x; simp
  have hZ' : MemBlockL2 (openCubeSet Q) Z' := by
    have h := hV'.1.add hP
    convert h using 1
    funext x; simp
  have hsub := old_signed_energy_pairing_sub_left Q ν σ hν hσ k hZ hZ' hD.1
  have h0 : oldSignedEnergyPairing Q ν σ k (fun x => Z x - Z' x) (fun x => Z x - Z' x) = 0 := by
    have h1 : oldSignedEnergyPairing Q ν σ k (Z - Z') (fun x => Z x - Z' x) =
        oldSignedEnergyPairing Q ν σ k Z (fun x => Z x - Z' x) -
          oldSignedEnergyPairing Q ν σ k Z' (fun x => Z x - Z' x) := hsub
    have h2 := hE _ hD
    change oldSignedEnergyPairing Q ν σ k (Z - Z') (fun x => Z x - Z' x) = 0
    rw [h1, h2, sub_self]
  filter_upwards [energy_zero_ae Q ν σ hν hσ k hD.1 h0] with x hx
  exact sub_eq_zero.1 hx

/-- The pair-space response `B_old (e, 0)` of the flat flux load is the canonical block field
of the load `(0, e)`: its potential `x₀` is the first component and its flux `y₀` is the
reflected first component `(a S)₂`, both almost everywhere. -/
theorem pair_flat_eq_canonical (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) :
    ∃ (φ : H10Function (openCubeSet Q)) (η : H1Function (openCubeSet Q)),
      φ.toH1Function.gradToHilbertVectorL2 =
          (twoSlotX Q hν hσ k (physicalConstantLoad Q e) 0 :
            HilbertVectorL2 (openCubeSet Q)) ∧
      η.gradToHilbertVectorL2 = twoSlotY Q hν hσ k (physicalConstantLoad Q e) 0 ∧
      (∀ᵐ x ∂(volumeMeasureOn (openCubeSet Q)),
        φ.toH1Function.grad x = (oldSignedFrameCanonicalField Q ν σ hν hσ k ((0, e) : BlockVec 2) x).1) ∧
      (∀ᵐ x ∂(volumeMeasureOn (openCubeSet Q)),
        η.grad x = (oldSignedDualReflection Q ν σ k
          (oldSignedFrameCanonicalField Q ν σ hν hσ k ((0, e) : BlockVec 2)) x).1) := by
  classical
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hF : MemVectorL2 (openCubeSet Q) (fun _ : Vec 2 => e) := memVectorL2_const e
  have hG := zeroField_memL2 (openCubeSet Q)
  have hs1 := physicalConstantLoad_mem_fluxSpace Q e
  have hs1' : ∀ w ∈ (physicalFluxSpace Q).toSubmodule,
      ⟪physicalConstantLoad Q e, w⟫_ℝ = ⟪toHilbertVectorL2OfVecField hF, w⟫_ℝ :=
    fun w _ => rfl
  have hs2' : ∀ w : (physicalPotentialSpace Q).toSubmodule,
      ⟪((0 : (physicalPotentialSpace Q).toSubmodule) : HilbertVectorL2 (openCubeSet Q)),
        (w : HilbertVectorL2 (openCubeSet Q))⟫_ℝ =
        ⟪toHilbertVectorL2OfVecField hG, (w : HilbertVectorL2 (openCubeSet Q))⟫_ℝ := by
    intro w
    rw [inner_zeroField]
    simp
  obtain ⟨φ, η, hc, hd, -, -, -, hxφ, hyη, hcz⟩ := two_slot_parent_core_links Q hν hσ k hF hG
    (physicalConstantLoad Q e) (twoSlotY Q hν hσ k (physicalConstantLoad Q e) 0) 0
    (twoSlotX Q hν hσ k (physicalConstantLoad Q e) 0) hs1 hs1' hs2'
    (twoSlot_eq1 Q hν hσ k _ _) (twoSlot_eq2 Q hν hσ k _ _)
  refine ⟨φ, η, hxφ, hyη, ?_⟩
  let a := responseFramePlanarCoefficientField ν σ k
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) ν σ hν hσ k
  let W := twoSlotState ν σ k φ.toH1Function.grad η.grad
  let S := oldSignedFrameCanonicalField Q ν σ hν hσ k ((0, e) : BlockVec 2)
  let P : Vec 2 → BlockVec 2 := fun _ => ((0, e) : BlockVec 2)
  have hx : MemVectorL2 (openCubeSet Q) φ.toH1Function.grad := φ.toH1Function.grad_memVectorL2
  have hy : MemVectorL2 (openCubeSet Q) η.grad := η.grad_memVectorL2
  have hflux : MemVectorL2 (openCubeSet Q) W.flux :=
    (hy.const_smul (ν / σ)).add (shear_memL2 hν hσ k hx)
  have hWmem : MemBlockL2 (openCubeSet Q) W.eval := memBlockL2_blockField hx hflux
  have hPmem : MemBlockL2 (openCubeSet Q) P := memBlockL2_blockField (memVectorL2_const 0) (memVectorL2_const e)
  have hVZ : ScalarVariation (openCubeSet Q) (fun x => W.eval x - P x) := by
    refine ⟨?_, ?_, ?_⟩
    · have h := hWmem.sub hPmem
      exact h
    · refine ⟨φ, ?_⟩
      funext x
      simp [W, P, BlockState.eval, twoSlotState]
    · have h := hcz
      have hfun : (fun x => (W.eval x - P x).2) = (fun z =>
          (ν / σ) • η.grad z + shear' σ k z (φ.toH1Function.grad z) - (fun _ : Vec 2 => e) z) := by
        funext z
        simp [W, P, BlockState.eval, twoSlotState]
      rw [hfun]
      exact h
  have hVS : ScalarVariation (openCubeSet Q) (fun x => S x - P x) :=
    old_signed_canonical_error_variation Q a hEll ((0, e) : BlockVec 2)
  have hforced := two_slot_hforced hν hσ k φ η hG hd
  have hEuler : ∀ Y : Vec 2 → BlockVec 2, ScalarVariation (openCubeSet Q) Y →
      oldSignedEnergyPairing Q ν σ k W.eval Y = oldSignedEnergyPairing Q ν σ k S Y := by
    intro Y hY
    have h0 := old_signed_canonical_variation_pairing Q ν σ hν hσ k ((0, e) : BlockVec 2) hY
    have hT := hforced ⟨fun x => (Y x).1, fun x => (Y x).2⟩ (by
      have : (BlockState.eval ⟨fun x => (Y x).1, fun x => (Y x).2⟩ : Vec 2 → BlockVec 2) = Y := by
        funext x; rfl
      rw [this]; exact hY)
    rw [old_signed_energy_pairing_symm, h0]
    have hsym : oldSignedEnergyPairing Q ν σ k Y W.eval =
        volumeAverage (openCubeSet Q) (blockPairingIntegrand a
          ⟨fun x => (Y x).1, fun x => (Y x).2⟩ W) := rfl
    rw [hsym, hT]
    simp [zeroField, volumeAverage, vecDot]
  have hae := block_unique Q ν σ hν hσ k hPmem hVZ hVS hEuler
  constructor
  · filter_upwards [hae] with x hx
    have := congrArg Prod.fst hx
    simpa [W, BlockState.eval, twoSlotState] using this
  · filter_upwards [hae] with x hx
    have h1 := twoSlot_lower hν hσ k φ.toH1Function.grad η.grad x
    have h2 := congrArg (fun z : BlockVec 2 =>
      (blockMatVecMul (blockCoeffField a x) z).2) hx
    have h3 : (oldSignedDualReflection Q ν σ k S x).1 =
        (blockMatVecMul (blockCoeffField a x) (S x)).2 := rfl
    rw [h3, ← h2]
    exact h1.symm

end

end ASDExplicitGamma.Scalar
