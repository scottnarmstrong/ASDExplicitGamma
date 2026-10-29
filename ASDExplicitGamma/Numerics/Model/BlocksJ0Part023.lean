module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B23 : ModeBlockData :=
  ⟨⟨23, 24, (3537638004311564503/5000000000000000000000 : ℚ), (3527826655524801791/5000000000000000000000 : ℚ)⟩, [
    (23, modeDataJ0M24)], (1415055201724625801/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b23 : entryChecks 0 bflatBlockJ0B23.entries = true := by
  simp only [entryChecks,bflatBlockJ0B23,List.all_cons,List.all_nil,
    mode_checked_j0_m24,Bool.and_self]
theorem block_mass_checked_j0_b23 : blockMassCheck bflatBlockJ0B23 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
