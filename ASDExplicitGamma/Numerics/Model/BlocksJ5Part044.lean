module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B44 : ModeBlockData :=
  ⟨⟨44, 45, (4996917344874492583/2000000000000000000000 : ℚ), (39279954058352559/10000000000000000000000 : ℚ)⟩, [
    (44, modeDataJ5M45)], (12492293362186231457/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b44 : entryChecks 5 bflatBlockJ5B44.entries = true := by
  simp only [entryChecks,bflatBlockJ5B44,List.all_cons,List.all_nil,
    mode_checked_j5_m45,Bool.and_self]
theorem block_mass_checked_j5_b44 : blockMassCheck bflatBlockJ5B44 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
