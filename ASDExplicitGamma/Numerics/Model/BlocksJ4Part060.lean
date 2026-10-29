module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B60 : ModeBlockData :=
  ⟨⟨60, 61, (8090676207117576723/1250000000000000000000 : ℚ), (322339552413219011/10000000000000000000000 : ℚ)⟩, [
    (60, modeDataJ4M61)], (64725409656940613783/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b60 : entryChecks 4 bflatBlockJ4B60.entries = true := by
  simp only [entryChecks,bflatBlockJ4B60,List.all_cons,List.all_nil,
    mode_checked_j4_m61,Bool.and_self]
theorem block_mass_checked_j4_b60 : blockMassCheck bflatBlockJ4B60 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
