module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B38 : ModeBlockData :=
  ⟨⟨38, 39, (71002886020494169769/10000000000000000000000 : ℚ), (341589871329816753/10000000000000000000000 : ℚ)⟩, [
    (38, modeDataJ4M39)], (8875360752561771221/1250000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b38 : entryChecks 4 bflatBlockJ4B38.entries = true := by
  simp only [entryChecks,bflatBlockJ4B38,List.all_cons,List.all_nil,
    mode_checked_j4_m39,Bool.and_self]
theorem block_mass_checked_j4_b38 : blockMassCheck bflatBlockJ4B38 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
