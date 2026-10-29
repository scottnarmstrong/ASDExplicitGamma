module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B8 : ModeBlockData :=
  ⟨⟨8, 9, (25999913251160481471/500000000000000000000 : ℚ), (24238661117491341451/10000000000000000000000 : ℚ)⟩, [
    (8, modeDataJ2M9)], (519998265023209629419/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b8 : entryChecks 2 bflatBlockJ2B8.entries = true := by
  simp only [entryChecks,bflatBlockJ2B8,List.all_cons,List.all_nil,
    mode_checked_j2_m9,Bool.and_self]
theorem block_mass_checked_j2_b8 : blockMassCheck bflatBlockJ2B8 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
