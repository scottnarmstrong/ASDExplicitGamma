module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B43 : ModeBlockData :=
  ⟨⟨43, 44, (69777977784491408813/10000000000000000000000 : ℚ), (13514549779885077/400000000000000000000 : ℚ)⟩, [
    (43, modeDataJ4M44)], (17444494446122852203/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b43 : entryChecks 4 bflatBlockJ4B43.entries = true := by
  simp only [entryChecks,bflatBlockJ4B43,List.all_cons,List.all_nil,
    mode_checked_j4_m44,Bool.and_self]
theorem block_mass_checked_j4_b43 : blockMassCheck bflatBlockJ4B43 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
