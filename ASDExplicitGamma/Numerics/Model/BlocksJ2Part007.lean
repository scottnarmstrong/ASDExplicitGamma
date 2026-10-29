module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B7 : ModeBlockData :=
  ⟨⟨7, 8, (275271910631996628987/5000000000000000000000 : ℚ), (25126458121702541301/10000000000000000000000 : ℚ)⟩, [
    (7, modeDataJ2M8)], (550543821263993257973/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b7 : entryChecks 2 bflatBlockJ2B7.entries = true := by
  simp only [entryChecks,bflatBlockJ2B7,List.all_cons,List.all_nil,
    mode_checked_j2_m8,Bool.and_self]
theorem block_mass_checked_j2_b7 : blockMassCheck bflatBlockJ2B7 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
