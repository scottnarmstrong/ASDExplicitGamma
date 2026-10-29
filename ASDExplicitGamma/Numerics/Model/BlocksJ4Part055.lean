module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B55 : ModeBlockData :=
  ⟨⟨55, 56, (66343399698699887121/10000000000000000000000 : ℚ), (327338835226993127/10000000000000000000000 : ℚ)⟩, [
    (55, modeDataJ4M56)], (829292496233748589/125000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b55 : entryChecks 4 bflatBlockJ4B55.entries = true := by
  simp only [entryChecks,bflatBlockJ4B55,List.all_cons,List.all_nil,
    mode_checked_j4_m56,Bool.and_self]
theorem block_mass_checked_j4_b55 : blockMassCheck bflatBlockJ4B55 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
