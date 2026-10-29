module

public import ASDExplicitGamma.Scalar.DualFenchel
public import Homogenization.Sobolev.PotentialSolenoidalL2Recovery
public import Homogenization.Sobolev.W1p.ZeroExtensionGraph

/-! The actual variation and compatible field spaces used by scalar convex duality. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory

/-- The source variation space V = grad H10 times solenoidal fields with zero normal trace. -/
def ScalarVariation (U : Set (Vec 2)) (F : Vec 2 → BlockVec 2) : Prop :=
  MemBlockL2 U F ∧ IsPotentialZeroTraceOn U (fun x => (F x).1) ∧
    IsSolenoidalZeroNormalTraceOn U (fun x => (F x).2)

/-- The source compatible space C = grad H1 times solenoidal fields. -/
def ScalarCompatible (U : Set (Vec 2)) (F : Vec 2 → BlockVec 2) : Prop :=
  MemBlockL2 U F ∧ IsPotentialOn U (fun x => (F x).1) ∧ IsSolenoidalOn U (fun x => (F x).2)

/-- Every genuine variation is compatible. -/
theorem scalar_variation_compatible {U : Set (Vec 2)} {F : Vec 2 → BlockVec 2}
    (hF : ScalarVariation U F) : ScalarCompatible U F :=
  ⟨hF.1,hF.2.1.isPotentialOn,fun φ => hF.2.2 φ.toH1Function⟩

/-- The actual variation space is stable under scalar multiplication. -/
theorem scalar_variation_smul {U : Set (Vec 2)} {F : Vec 2 → BlockVec 2}
    (hF : ScalarVariation U F) (t : ℝ) : ScalarVariation U (t • F) := by
  refine ⟨hF.1.const_smul t,?_,?_⟩
  · exact isPotentialZeroTraceOn_smul hF.2.1 t
  · exact isSolenoidalZeroNormalTraceOn_smul hF.2.2 t

/-- Finite sums of genuine variations are genuine variations. -/
theorem scalar_variation_add {U : Set (Vec 2)} {F G : Vec 2 → BlockVec 2}
    (hF : ScalarVariation U F) (hG : ScalarVariation U G) : ScalarVariation U (F+G) := by
  refine ⟨hF.1.add hG.1,isPotentialZeroTraceOn_add hF.2.1 hG.2.1,?_⟩
  exact isSolenoidalZeroNormalTraceOn_add hF.2.2 hG.2.2
    (fun φ => integrableOn_vecDot_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hF.1) φ.grad_memVectorL2)
    (fun φ => integrableOn_vecDot_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hG.1) φ.grad_memVectorL2)

/-- The zero field belongs to the genuine variation space. -/
theorem scalar_variation_zero (U : Set (Vec 2)) : ScalarVariation U (0 : Vec 2 → BlockVec 2) :=
  ⟨MemLp.zero,isPotentialZeroTraceOn_zero,isSolenoidalZeroNormalTraceOn_zero⟩

/-- The div-curl pairings give the source orthogonality C = R V-perp in the direction needed here. -/
theorem scalar_compatible_exchange_pairing_zero {U : Set (Vec 2)}
    {X Z : Vec 2 → BlockVec 2} (hX : ScalarCompatible U X) (hZ : ScalarVariation U Z) :
    (∫ x in U,blockVecDot (scalarBlockExchange (X x)) (Z x) ∂volume)=0 := by
  obtain ⟨u,hu⟩ := hX.2.1
  obtain ⟨v,hv⟩ := hZ.2.1
  have h1 : (∫ x in U,vecDot (X x).2 (Z x).1 ∂volume)=0 := by
    simpa only [hv] using hX.2.2 v
  have h2 : (∫ x in U,vecDot (X x).1 (Z x).2 ∂volume)=0 := by
    have h := hZ.2.2 u
    simpa only [hu,vecDot_comm] using h
  have hi1 := integrableOn_vecDot_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hX.1)
    (memVectorL2_fst_of_memBlockL2 hZ.1)
  have hi2 := integrableOn_vecDot_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hX.1)
    (memVectorL2_snd_of_memBlockL2 hZ.1)
  change (∫ x in U,vecDot (X x).2 (Z x).1+vecDot (X x).1 (Z x).2 ∂volume)=0
  rw [integral_add hi1 hi2,h1,h2,add_zero]

/-- Zero extension of a source variation on any open cell is a global source variation. -/
theorem scalar_variation_zero_extension {U V : Set (Vec 2)} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ⊆ V) {F : Vec 2 → BlockVec 2} (hF : ScalarVariation U F) :
    ScalarVariation V (U.indicator F) := by
  classical
  have hm : MemBlockL2 V (U.indicator F) :=
    ((memLp_indicator_iff_restrict hU.measurableSet).mpr hF.1).mono_measure Measure.restrict_le_self
  refine ⟨hm,?_,?_⟩
  · obtain ⟨u,hu⟩ := hF.2.1
    refine ⟨u.extendByZeroToOpenSuperset hU.measurableSet hV hUV,?_⟩
    rw [H10Function.extendByZeroToOpenSuperset_grad]
    funext x
    by_cases hx : x ∈ U <;> simp [H10Function.zeroExtensionGrad,hx,hu]
  · intro φ
    have h := hF.2.2 (φ.restrict hU hUV)
    have he : (fun x => vecDot ((U.indicator F) x).2 (φ.grad x))=
        U.indicator (fun x => vecDot (F x).2 (φ.grad x)) := by
      funext x
      by_cases hx : x ∈ U <;> simp [hx,vecDot]
    rw [he,integral_indicator hU.measurableSet]
    rw [Measure.restrict_restrict hU.measurableSet,Set.inter_eq_left.mpr hUV]
    exact h

end ASDExplicitGamma.Scalar
