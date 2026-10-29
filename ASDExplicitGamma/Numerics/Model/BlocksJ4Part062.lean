module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B62 : ModeBlockData :=
  ⟨⟨62, 63, (16012595446740130157/2500000000000000000000 : ℚ), (320245734196286537/10000000000000000000000 : ℚ)⟩, [
    (62, modeDataJ4M63)], (64050381786960520627/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b62 : entryChecks 4 bflatBlockJ4B62.entries = true := by
  simp only [entryChecks,bflatBlockJ4B62,List.all_cons,List.all_nil,
    mode_checked_j4_m63,Bool.and_self]
theorem block_mass_checked_j4_b62 : blockMassCheck bflatBlockJ4B62 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
