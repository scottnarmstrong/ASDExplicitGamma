module

public import ASDExplicitGamma.Model.BflatGaussianModes
public import Algsuperdiff.Section3.Provider.Diffusivity.Corrector.CorrectorMeasurableForcing

/-! # Actual L² source fields for the B-flat projection -/

@[expose] public section

open MeasureTheory Homogenization
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open scoped Topology RealInnerProductSpace

namespace ASDExplicitGamma.Model

abbrev bflatSquareObservationDomain := openCubeSet bflatUnitSquare

noncomputable def bflatClampReal (x : ℝ) : ℝ := max (-1/2) (min x (1/2))

theorem bflatClampReal_mem (x : ℝ) : bflatClampReal x ∈ Set.Icc (-1/2) (1/2) := by
  constructor
  · exact le_max_left _ _
  · exact max_le_iff.mpr ⟨by norm_num, (min_le_right _ _).trans (by norm_num)⟩

/-- Clamp a point to the closed observation square. On the open square this
agrees with the identity, while making every source observation globally
continuous. -/
noncomputable def bflatClampVec (x : Vec 2) : Vec 2 := fun i => bflatClampReal (x i)

theorem bflatClampVec_mem (x : Vec 2) :
    bflatClampVec x ∈ ASDExplicitGamma.Gaussian.closedRectangle (-1/2) (1/2) (-1/2) (1/2) := by
  change bflatClampReal (x 0) ∈ Set.Icc (-1/2) (1/2) ∧
    bflatClampReal (x 1) ∈ Set.Icc (-1/2) (1/2)
  exact ⟨bflatClampReal_mem _, bflatClampReal_mem _⟩

theorem bflatClampVec_continuous : Continuous bflatClampVec := by
  change Continuous (fun x : Vec 2 => fun i => max (-1 / 2) (min (x i) (1 / 2)))
  exact continuous_pi fun i =>
    continuous_const.max ((continuous_apply i).min continuous_const)

noncomputable def bflatClamp (x : Vec 2) : bflatClosedRectangle :=
  ⟨bflatClampVec x, bflatClampVec_mem x⟩

theorem bflatClamp_continuous : Continuous bflatClamp := by
  exact Continuous.subtype_mk
    bflatClampVec_continuous bflatClampVec_mem

/-- The columns of the planar quarter-turn used by the two source fields. -/
def bflatJEntry (i k : Fin 2) : ℝ :=
  if i = 0 then if k = 1 then 1 else 0 else if k = 0 then -1 else 0

theorem bflatJEntry_abs_le_one (i k : Fin 2) : |bflatJEntry i k| ≤ 1 := by
  fin_cases i <;> fin_cases k <;> norm_num [bflatJEntry]

/-- The global continuous representative of `f J eᵢ` on the observation square. -/
noncomputable def bflatSourceField (i : Fin 2) (f : C(bflatClosedRectangle, ℝ))
    (x : Vec 2) : Vec 2 := fun k => f (bflatClamp x) * bflatJEntry i k

private theorem bflatSourceField_component_continuous (i k : Fin 2)
    (f : C(bflatClosedRectangle, ℝ)) :
    Continuous (fun x : Vec 2 => bflatSourceField i f x k) := by
  exact (f.continuous.comp bflatClamp_continuous).mul continuous_const

theorem bflatSquare_finiteMeasure :
    IsFiniteMeasure (volumeMeasureOn bflatSquareObservationDomain) :=
  (isOpenBoundedConvexDomain_openCubeSet bflatUnitSquare).isFiniteMeasure_restrict_volume

noncomputable instance instBflatSquareObservationFinite :
    IsFiniteMeasure (volumeMeasureOn bflatSquareObservationDomain) :=
  bflatSquare_finiteMeasure

theorem bflatSourceField_memL2 (i : Fin 2) (f : C(bflatClosedRectangle, ℝ)) :
    MemVectorL2 bflatSquareObservationDomain (bflatSourceField i f) := by
  rw [Homogenization.MemVectorL2, Homogenization.volumeMeasureOn, memLp_pi_iff]
  intro k
  apply MemLp.of_bound (bflatSourceField_component_continuous i k f).aestronglyMeasurable ‖f‖
  filter_upwards with x
  change |bflatSourceField i f x k| ≤ ‖f‖
  simp only [bflatSourceField]
  rw [abs_mul]
  calc
    |f (bflatClamp x)| * |bflatJEntry i k| ≤ ‖f‖ * 1 :=
      mul_le_mul (by simpa only [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm f _)
        (bflatJEntry_abs_le_one i k)
        (abs_nonneg _) (norm_nonneg _)
    _ = ‖f‖ := mul_one _

/-- The actual Hilbert-valued L² field associated with `f J eᵢ`. -/
noncomputable def bflatSourceFieldClassLinear (i : Fin 2) :
    C(bflatClosedRectangle, ℝ) →ₗ[ℝ] HilbertVectorL2 bflatSquareObservationDomain where
  toFun f := toHilbertVectorL2OfVecField (bflatSourceField_memL2 i f)
  map_add' f g := by
    have hfield : bflatSourceField i (f + g) = bflatSourceField i f + bflatSourceField i g := by
      funext x
      ext k
      simp [bflatSourceField]
      ring
    calc
      _ = toHilbertVectorL2OfVecField
          ((bflatSourceField_memL2 i f).add (bflatSourceField_memL2 i g)) :=
            toHilbertVectorL2OfVecField_congr _ _ hfield
      _ = _ := toHilbertVectorL2OfVecField_add _ _
  map_smul' c f := by
    have hfield : bflatSourceField i (c • f) = c • bflatSourceField i f := by
      funext x
      ext k
      simp [bflatSourceField]
      ring
    calc
      _ = toHilbertVectorL2OfVecField
          ((bflatSourceField_memL2 i f).const_smul c) :=
            toHilbertVectorL2OfVecField_congr _ _ hfield
      _ = c • toHilbertVectorL2OfVecField (bflatSourceField_memL2 i f) := by
            change toHilbertVectorL2
                (memHilbertVectorL2_hilbertifyVecField
                  ((bflatSourceField_memL2 i f).const_smul c)) = _
            exact MeasureTheory.MemLp.toLp_const_smul c
              (memHilbertVectorL2_hilbertifyVecField (bflatSourceField_memL2 i f))

/-- Continuous linear realization of the two actual square vector sources. -/
noncomputable def bflatSourceFieldClass (i : Fin 2) :
    C(bflatClosedRectangle, ℝ) →L[ℝ] HilbertVectorL2 bflatSquareObservationDomain := by
  let T := bflatSourceFieldClassLinear i
  let C : ℝ := 2 * ((volumeMeasureOn bflatSquareObservationDomain Set.univ).toReal) ^ ((2 : ℝ)⁻¹)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine T.mkContinuous C ?_
  intro f
  have hU : MeasurableSet bflatSquareObservationDomain :=
    (isOpen_openCubeSet bflatUnitSquare).measurableSet
  have hbound : ∀ x ∈ bflatSquareObservationDomain, ‖bflatSourceField i f x‖ ≤ ‖f‖ := by
    intro x hx
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg f)).2
    intro k
    change ‖bflatSourceField i f x k‖ ≤ ‖f‖
    simp only [bflatSourceField, Real.norm_eq_abs]
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (bflatJEntry_abs_le_one i k)
      (abs_nonneg (f (bflatClamp x)))).trans (by
        simpa only [mul_one, Real.norm_eq_abs] using
          ContinuousMap.norm_coe_le_norm f (bflatClamp x))
  have hnorm := norm_toHilbertVectorL2OfVecField_le_of_bound_on hU (bflatSourceField_memL2 i f)
      (norm_nonneg f) hbound
  change ‖T f‖ ≤ _ at hnorm
  calc
    ‖T f‖ ≤ (volumeMeasureOn bflatSquareObservationDomain Set.univ).toReal ^ ((2 : ℝ)⁻¹) *
        (2 * ‖f‖) := hnorm
    _ = C * ‖f‖ := by dsimp [C]; ring

end ASDExplicitGamma.Model
