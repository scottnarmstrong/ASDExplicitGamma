module

public import ASDExplicitGamma.Gaussian.Q3ConvolutionRegularity
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Ordinary Lebesgue integrals on the source rectangles -/

@[expose] public section

open MeasureTheory Homogenization Set
open scoped Topology

namespace ASDExplicitGamma.Gaussian

def openRectangle (a b c d : ℝ) : Set (Vec 2) :=
  {x | x 0 ∈ Ioo a b ∧ x 1 ∈ Ioo c d}

def closedRectangle (a b c d : ℝ) : Set (Vec 2) :=
  {x | x 0 ∈ Icc a b ∧ x 1 ∈ Icc c d}

theorem openRectangle_isOpen (a b c d : ℝ) : IsOpen (openRectangle a b c d) :=
  (isOpen_Ioo.preimage (continuous_apply 0)).inter (isOpen_Ioo.preimage (continuous_apply 1))

theorem closedRectangle_isCompact (a b c d : ℝ) : IsCompact (closedRectangle a b c d) := by
  exact (Homeomorph.finTwoArrow (X := ℝ)).isClosedEmbedding.isCompact_preimage
    (isCompact_Icc.prod isCompact_Icc)

instance instRectangleFiniteMeasure (a b c d : ℝ) :
    IsFiniteMeasure (volume.restrict (openRectangle a b c d)) := by
  apply isFiniteMeasure_restrict.mpr
  apply ne_of_lt
  have hsub : openRectangle a b c d ⊆ closedRectangle a b c d := fun x hx =>
    ⟨Ioo_subset_Icc_self hx.1, Ioo_subset_Icc_self hx.2⟩
  exact lt_of_le_of_lt (measure_mono hsub)
    (closedRectangle_isCompact a b c d).measure_lt_top

instance instRectangleCompactSpace (a b c d : ℝ) : CompactSpace (closedRectangle a b c d) :=
  isCompact_iff_compactSpace.mp (closedRectangle_isCompact a b c d)

/-- The boundary has zero Lebesgue measure, so the Sobolev domain is the open square. -/
theorem rectangle_restrict_eq (a b c d : ℝ) :
    volume.restrict (openRectangle a b c d) = volume.restrict (closedRectangle a b c d) := by
  apply Measure.restrict_congr_set
  have hz (i : Fin 2) (v : ℝ) : ∀ᵐ x : Vec 2, x i ≠ v := by
    rw [ae_iff]
    simp only [not_not]
    rw [show (volume : Measure (Vec 2)) = Measure.pi (fun _ : Fin 2 => (volume : Measure ℝ)) from volume_pi]
    exact Measure.pi_hyperplane (fun _ : Fin 2 => (volume : Measure ℝ)) i v
  filter_upwards [hz 0 a, hz 0 b, hz 1 c, hz 1 d] with x ha hb hc hd
  simp only [openRectangle, closedRectangle, mem_ofPred_eq, mem_Ioo, mem_Icc]
  apply propext
  constructor
  · exact fun h => ⟨⟨h.1.1.le, h.1.2.le⟩, ⟨h.2.1.le, h.2.2.le⟩⟩
  · exact fun h => ⟨⟨lt_of_le_of_ne h.1.1 ha.symm, lt_of_le_of_ne h.1.2 hb⟩,
      ⟨lt_of_le_of_ne h.2.1 hc.symm, lt_of_le_of_ne h.2.2 hd⟩⟩

/-- Fubini on the closed rectangle, with the same ordinary normalization as the weak H³ norm. -/
theorem rectangle_integral_eq (a b c d : ℝ) (f : Vec 2 → ℝ) (hf : Continuous f) :
    (∫ x in openRectangle a b c d, f x) =
      ∫ s in Icc a b, ∫ t in Icc c d, f ![s, t] := by
  rw [rectangle_restrict_eq]
  have hp := (volume_preserving_finTwoArrow ℝ).setIntegral_preimage_emb
    MeasurableEquiv.finTwoArrow.measurableEmbedding
    (fun p : ℝ × ℝ => f ![p.1, p.2]) ((Icc a b) ×ˢ (Icc c d))
  have he : (fun x : Vec 2 => f ![x 0, x 1]) = f := by
    funext x
    congr 1
    ext i
    fin_cases i <;> rfl
  change (∫ x in closedRectangle a b c d, f ![x 0, x 1]) = _ at hp
  rw [he] at hp
  rw [hp]
  apply setIntegral_prod
  exact (hf.comp (Homeomorph.finTwoArrow (X := ℝ)).symm.continuous).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)

end ASDExplicitGamma.Gaussian
