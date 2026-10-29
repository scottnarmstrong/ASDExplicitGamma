module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B24 : ModeBlockData :=
  ⟨⟨24, 25, (73714482849905739661/10000000000000000000000 : ℚ), (174894778101523309/5000000000000000000000 : ℚ)⟩, [
    (24, modeDataJ4M25)], (3685724142495286983/500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b24 : entryChecks 4 bflatBlockJ4B24.entries = true := by
  simp only [entryChecks,bflatBlockJ4B24,List.all_cons,List.all_nil,
    mode_checked_j4_m25,Bool.and_self]
theorem block_mass_checked_j4_b24 : blockMassCheck bflatBlockJ4B24 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
