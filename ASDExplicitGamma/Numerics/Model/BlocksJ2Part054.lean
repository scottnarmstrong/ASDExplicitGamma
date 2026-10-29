module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B54 : ModeBlockData :=
  ⟨⟨54, 55, (153707734387703067/1000000000000000000000 : ℚ), (702777911050892791/5000000000000000000000 : ℚ)⟩, [
    (54, modeDataJ2M55)], (1537077343877030669/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b54 : entryChecks 2 bflatBlockJ2B54.entries = true := by
  simp only [entryChecks,bflatBlockJ2B54,List.all_cons,List.all_nil,
    mode_checked_j2_m55,Bool.and_self]
theorem block_mass_checked_j2_b54 : blockMassCheck bflatBlockJ2B54 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
