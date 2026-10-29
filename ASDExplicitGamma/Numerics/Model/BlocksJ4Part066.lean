module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part004

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B66 : ModeBlockData :=
  ⟨⟨72, 76, (29946406930055709381/1250000000000000000000 : ℚ), (307238145802732031/2500000000000000000000 : ℚ)⟩, [
    (72, modeDataJ4M73),
    (73, modeDataJ4M74),
    (74, modeDataJ4M75),
    (75, modeDataJ4M76)], (59892813860111418761/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b66 : entryChecks 4 bflatBlockJ4B66.entries = true := by
  simp only [entryChecks,bflatBlockJ4B66,List.all_cons,List.all_nil,
    mode_checked_j4_m73,
    mode_checked_j4_m74,
    mode_checked_j4_m75,
    mode_checked_j4_m76,Bool.and_self]
theorem block_mass_checked_j4_b66 : blockMassCheck bflatBlockJ4B66 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
