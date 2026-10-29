module

public import ASDExplicitGamma.Native.BoundaryChargePanelDegree
public import ASDExplicitGamma.Numerics.Native.PanelEndpoint

/-! Integral and return continuation for the exact OLD boundary-fixed panel,
keeping the fixed endpoint reserve separate from proportional source inputs. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory ASDExplicitGamma.Numerics.Native
noncomputable section

/-- The exact panel formula is integrable on the whole source time interval,
from its already-checked nonnegative monotonicity certificate. -/
theorem native_boundary_panel_integrable (fields : List ℝ) (hlen : fields.length=17)
    (hfields : ∀ x ∈ fields, 0 ≤ x) :
    IntervalIntegrable (nativePanelValue fields) volume 0 1 := by
  apply MonotoneOn.intervalIntegrable
  apply (nativePanel_monotone fields hlen hfields).mono
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)]
  intro t ht
  exact ht.1

end
end ASDExplicitGamma.Native
