module

public import ASDExplicitGamma.Inverse.HybridActiveSum

/-! Weighted scalar form of the actual planar active-gradient charge. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Provider Algsuperdiff.Section3.Provider.Whitney
open scoped ENNReal
noncomputable section

/-- Continuous spatial wave payments preserve integrability of every actual
geometric density square on a deterministic root layer. -/
theorem assembly_density_square_mul_continuous_integrable (M : ABKModel 2)
    (Q : TriadicCube 2) (H : ℕ) (hH : 333 ≤ H) (τ η : ℝ)
    (n : ℕ) (e : Fin 3) (ω : Cutoff.CutoffSample 2) (F : Vec 2 → ℝ) (hF : Continuous F) :
    IntegrableOn (fun x => (layerResolutionDiameter M Q H τ η n e ω x)^2*F x)
      (rootLayerCarrier Q H n) := by
  have hZ : IntegrableOn (fun x => (layerResolutionDiameter M Q H τ η n e ω x)^2)
      (rootLayerCarrier Q H n) := by
    by_cases hn : n=0
    · subst n
      simp only [root_layer_carrier_zero,integrableOn_empty]
    · have hn1 : 1 ≤ n := by omega
      simpa only [Nat.add_zero,Nat.sub_add_cancel hn1] using
        layer_resolution_square_integrableOn M Q H hH (0,n-1) τ η e ω
  obtain ⟨B,hB⟩ := (isCompact_closedBall (cubeCenter Q) (cubeRadius Q)).exists_bound_of_continuousOn
    hF.continuousOn
  apply hZ.mul_bdd hF.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (root_layer_carrier_measurable Q H n)] with x hx
  exact hB x (cubeSet_subset_closedBall Q
    (openCubeSet_subset_cubeSet Q (root_layer_carrier_subset_open Q H n hx)))

/-- An arbitrary nonnegative spatial payment can multiply the actual active
slope charge before disjoint cells are enlarged to deterministic layers. -/
theorem assembly_weighted_active_charge (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (hH : 333 ≤ H) (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ j, H ≤ j → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-j) τ η) j (rootBlockStart Q j))
    (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
    (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)
    (hfinite : ∀ j ≤ Q.scale-(H:ℤ), ∀ z, diameterField (q3PlanarMarks M j τ η) ω z ≠ ∞)
    (C : HybridCell Q H S → Mat 2)
    (hC : ∀ i, ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), x ∈ (hybridDomain i:Set (Vec 2)) →
      stoppedKuhnGradient M Q H hH τ η ω hgood S hS hbad x=C i)
    (F : ℕ → Vec 2 → ℝ) (hF0 : ∀ n x, 0 ≤ F n x)
    (hFZ : ∀ n e, IntegrableOn (fun x =>
      (layerResolutionDiameter M Q H τ η n e ω x)^2*F n x) (rootLayerCarrier Q H n))
    (A : HybridActiveCell Q H S → ℝ)
    (hA : ∀ i, ∀ᵐ x ∂volumeMeasureOn (hybridDomain (.inr i):Set (Vec 2)),
      A i ≤ ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (C (.inr i))‖^2*F i.1.val.1 x)
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) :
    (∑' i : HybridActiveCell Q H S, ENNReal.ofReal
      (w i.1.val.1*(volume (hybridDomain (.inr i):Set (Vec 2))).toReal/
        (volume (cubeSet Q)).toReal*A i)) ≤
      ∑' n : ℕ, ENNReal.ofReal (w n*(planarGradientCharge 40+1)/
        (volume (cubeSet Q)).toReal*
          ∑ e : Fin 3, ∫ x in rootLayerCarrier Q H n,
            (layerResolutionDiameter M Q H τ η n e ω x)^2*F n x) := by
  classical
  let Z := fun n (e : Fin 3) x => (layerResolutionDiameter M Q H τ η n e ω x)^2*F n x
  let f := fun n x => (w n/(volume (cubeSet Q)).toReal*(planarGradientCharge 40+1))*
    ∑ e : Fin 3, Z n e x
  have hS0 : 0 ≤ planarGradientCharge 40+1 := by unfold planarGradientCharge; positivity
  have hf (n : ℕ) : IntegrableOn (f n) (rootLayerCarrier Q H n) :=
    (integrable_finsetSum Finset.univ (fun e _ => hFZ n e)).const_mul _
  have hf0 (n : ℕ) (x : Vec 2) : 0 ≤ f n x :=
    mul_nonneg (mul_nonneg (div_nonneg (hw n) ENNReal.toReal_nonneg) hS0)
      (Finset.sum_nonneg fun e _ => mul_nonneg (sq_nonneg _) (hF0 n x))
  have hsub (i : HybridActiveCell Q H S) :
      (hybridDomain (.inr i):Set (Vec 2)) ⊆ rootLayerCarrier Q H i.1.val.1 := by
    intro x hx
    exact Set.mem_iUnion₂.mpr ⟨i.1.val.2.val,i.1.val.2.property,
      openCubeSet_subset_cubeSet _ (hybrid_domain_subset_parent (.inr i) hx)⟩
  have hgroup := grouped_disjoint_cell_integrals_le volume
    (fun i : HybridActiveCell Q H S => (hybridDomain (.inr i):Set (Vec 2)))
    (rootLayerCarrier Q H) (fun i => i.1.val.1) (fun i => (hybridDomain (.inr i)).measurableSet)
    (root_layer_carrier_measurable Q H)
    (fun i j hne => hybrid_domains_disjoint Q H S (fun he => hne (Sum.inr_injective he)))
    hsub f hf0 hf
  have hcharge := stopped_kuhn_gradient_ae_active_charge M Q H hH τ η ω hgood S hS hbad hfinite
  have hcell (i : HybridActiveCell Q H S) : ENNReal.ofReal
      (w i.1.val.1*(volume (hybridDomain (.inr i):Set (Vec 2))).toReal/
        (volume (cubeSet Q)).toReal*A i) ≤
        ENNReal.ofReal (∫ x in (hybridDomain (.inr i):Set (Vec 2)), f i.1.val.1 x) := by
    let V := hybridDomain (.inr i)
    let n := i.1.val.1
    let P := i.1.val.2.val
    have hactive : ∃ D ∈ S, CubeTouch P D := by
      simpa only [not_forall,not_imp,not_not,exists_prop,P] using i.1.property
    have hineq : ∀ᵐ x ∂volumeMeasureOn (V:Set (Vec 2)),
        w n/(volume (cubeSet Q)).toReal*A i ≤ f n x := by
      filter_upwards [hA i,
        ae_restrict_of_ae_restrict_of_subset (hybrid_domain_subset_root (.inr i)) hcharge,
        ae_restrict_of_ae_restrict_of_subset (hybrid_domain_subset_root (.inr i)) (hC (.inr i)),
        ae_restrict_mem V.measurableSet] with x hxA hxcharge hxC hxV
      have hc := hxcharge n P i.1.val.2.property hactive (hybrid_domain_subset_parent (.inr i) hxV)
      rw [hxC hxV] at hc
      have hh := hxA.trans (mul_le_mul_of_nonneg_right hc (hF0 n x))
      have hh' := mul_le_mul_of_nonneg_left hh
        (div_nonneg (hw n) (ENNReal.toReal_nonneg (a := volume (cubeSet Q))))
      dsimp only [f,Z]
      rw [← Finset.sum_mul]
      convert hh' using 1
      ring
    have hleft : IntegrableOn (fun _ : Vec 2 => w n/(volume (cubeSet Q)).toReal*A i) (V:Set (Vec 2)) :=
      integrableOn_const V.isDomain.2.1.volume_lt_top.ne
    have hh := integral_mono_ae hleft ((hf n).mono_set (hsub i)) hineq
    rw [integral_const,Measure.real_def,smul_eq_mul,Measure.restrict_apply_univ] at hh
    apply ENNReal.ofReal_le_ofReal
    convert hh using 1
    ring

  apply (ENNReal.tsum_le_tsum hcell).trans hgroup |>.trans_eq
  apply tsum_congr
  intro n
  rw [show (∫ x in rootLayerCarrier Q H n, f n x)=
      (w n/(volume (cubeSet Q)).toReal*(planarGradientCharge 40+1))*
        ∑ e : Fin 3, ∫ x in rootLayerCarrier Q H n, Z n e x by
    rw [integral_const_mul,integral_finsetSum Finset.univ (fun e _ => hFZ n e)]]
  congr 1
  ring

end
end ASDExplicitGamma.Inverse
