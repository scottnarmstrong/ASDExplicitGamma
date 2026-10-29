module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B59 : ModeBlockData :=
  ⟨⟨59, 60, (1224088170058574589/10000000000000000000000 : ℚ), (58531908456985451/500000000000000000000 : ℚ)⟩, [
    (59, modeDataJ2M60)], (306022042514643647/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b59 : entryChecks 2 bflatBlockJ2B59.entries = true := by
  simp only [entryChecks,bflatBlockJ2B59,List.all_cons,List.all_nil,
    mode_checked_j2_m60,Bool.and_self]
theorem block_mass_checked_j2_b59 : blockMassCheck bflatBlockJ2B59 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
