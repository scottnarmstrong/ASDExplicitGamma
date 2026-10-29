module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B8 : ModeBlockData :=
  ⟨⟨8, 9, (4712902863480644581/625000000000000000000 : ℚ), (177436518788456279/5000000000000000000000 : ℚ)⟩, [
    (8, modeDataJ4M9)], (15081289163138062659/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b8 : entryChecks 4 bflatBlockJ4B8.entries = true := by
  simp only [entryChecks,bflatBlockJ4B8,List.all_cons,List.all_nil,
    mode_checked_j4_m9,Bool.and_self]
theorem block_mass_checked_j4_b8 : blockMassCheck bflatBlockJ4B8 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
