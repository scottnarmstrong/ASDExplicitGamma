module

public import ASDExplicitGamma.Triadic.SensitivityProduct
public import ASDExplicitGamma.Triadic.SensitivityResponsePair
public import ASDExplicitGamma.Variational.LemmaVMinimizer
public import ASDExplicitGamma.Variational.LemmaVH1
public import Algsuperdiff.Frozen.Section24.CoarseMatrixDerivativeCharacterization
public import Homogenization.Book.Ch04.CoeffFamily
public import Homogenization.Internal.Ch02.DoubledResponse.ScalarMaximizers
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! The source coefficient and skew-matrix direction used in the explicit
coarse-sensitivity derivative estimate. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Variational
open Homogenization.Book.Ch02 Homogenization.Book.Ch04

noncomputable section

/-- The source coefficient `ν I + k J`, with the actual bounded continuous
extension of its scalar skew amplitude. -/
def sensitivityBaseRegField {Q₀ : TriadicCube 2} (ν : ℝ)
    (k : ResponseCoefficient (openCubeSet Q₀)) :
    RegCoeffField 2 where
  toFun := responseFramePlanarCoefficientField ν 1 k
  entry_measurable i j := by
    fin_cases i <;> fin_cases j <;>
      simp [responseFramePlanarCoefficientField, responsePlanarCoefficient,
        responsePlanarJ] <;> fun_prop
  entry_locInt i j := by
    apply Continuous.locallyIntegrable
    fin_cases i <;> fin_cases j <;>
      simp [responseFramePlanarCoefficientField, responsePlanarCoefficient,
        responsePlanarJ] <;> fun_prop

/-- Qualitative ellipticity of the source coefficient is uniform on every
triadic cube; the upper ellipticity bound depends only on `ν` and `‖k‖`. -/
theorem sensitivityBaseRegField_aelocal {Q₀ : TriadicCube 2} (ν : ℝ)
    (hν : 0 < ν) (k : ResponseCoefficient (openCubeSet Q₀)) :
    AELocallyUniformlyEllipticField (sensitivityBaseRegField ν k) := by
  intro R
  refine ⟨ν, (ν ^ 2 + ‖k‖ ^ 2) / ν, hν, ?_, ?_⟩
  · apply (le_div_iff₀ hν).mpr
    nlinarith [sq_nonneg ‖k‖]
  · have hEllR : IsEllipticFieldOn ν ((ν ^ 2 + ‖k‖ ^ 2) / ν)
        (openCubeSet R) (sensitivityBaseRegField ν k).toFun := by
      refine ⟨?_, ?_⟩
      · apply measurable_pi_iff.2
        intro i
        apply measurable_pi_iff.2
        intro j
        exact Measurable.ite (measurableSet_openCubeSet R)
          ((sensitivityBaseRegField ν k).entry_measurable i j) measurable_const
      · intro x hx
        have hkx : |responseCoefficientExtension k x| ≤ ‖k‖ := by
          calc
            |responseCoefficientExtension k x| =
                ‖responseCoefficientExtension k x‖ := by simp
            _ ≤ ‖responseCoefficientExtension k‖ :=
              (responseCoefficientExtension k).norm_coe_le_norm x
            _ = ‖k‖ := responseCoefficientExtension_norm k
        have hpoint := responsePlanarCoefficient_isElliptic ν ‖k‖
          (responseCoefficientExtension k x) hν hkx
        simpa [sensitivityBaseRegField, responseFramePlanarCoefficientField,
          responsePlanarCoefficientField, div_one] using hpoint
    exact IsAEEllipticFieldOn.of_isEllipticFieldOn hEllR

/-- The compatible source coefficient family for `ν I + k J`. -/
noncomputable def sensitivityCoefficientFamily {Q : TriadicCube 2} (ν : ℝ) (hν : 0 < ν)
    (k : ResponseCoefficient (openCubeSet Q)) : TriadicCoeffFamily 2 :=
  triadicCoeffFamilyOfAELocallyUniformlyEllipticField
    (sensitivityBaseRegField (Q₀ := Q) ν k)
    (sensitivityBaseRegField_aelocal (Q₀ := Q) ν hν k)

/-- The Chapter 2 coefficient on the observation cube, with the literal source
field as its representative. -/
noncomputable def sensitivityBookCoeffOn (Q : TriadicCube 2) (ν : ℝ)
    (hν : 0 < ν) (k : ResponseCoefficient (openCubeSet Q)) :
    Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q) := by
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) ν 1 hν one_pos k
  have hEll' : IsEllipticFieldOn ν ((ν ^ 2 + ‖k‖ ^ 2) / ν)
      (openCubeSet Q) (responseFramePlanarCoefficientField ν 1 k) := by
    simpa [div_one] using hEll
  refine ⟨responseFramePlanarCoefficientField ν 1 k, ν,
    (ν ^ 2 + ‖k‖ ^ 2) / ν, hν, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ hν).mpr
    nlinarith [sq_nonneg ‖k‖]
  · intro i j
    have h := ((measurable_pi_iff.mp (measurable_pi_iff.mp hEll'.1 i)) j)
    apply (h.aestronglyMeasurable (μ := volumeMeasureOn (openCubeSet Q))).congr
    exact Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ openCubeSet Q <;> simp [restrictCoeffField, hx]
  · filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    exact hEll'.2 x hx

/-- The actual skew matrix field `H(x)=h(x)J` attached to a scalar planar
`W^{2,∞}` direction. -/
def sensitivityMatrixDirection {Q : TriadicCube 2} (h : PlanarW2Infinity Q) :
    Algsuperdiff.Frozen.Section24.LInfMatrixFieldOn (Book.Ch02.cubeDomain Q) := by
  refine ⟨fun x => h.value.toFun x • responsePlanarJ, ?_⟩
  intro i j
  have hm := h.value_memLp_top.const_mul (responsePlanarJ i j)
  convert hm using 1 <;> ext x <;> simp [Book.Ch02.cubeDomain_coe,
    volumeMeasureOn, Matrix.smul_apply, mul_comm]

end

end ASDExplicitGamma.Triadic
