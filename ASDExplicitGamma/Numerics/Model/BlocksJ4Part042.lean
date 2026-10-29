module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B42 : ModeBlockData :=
  ⟨⟨42, 43, (35016580874534946177/5000000000000000000000 : ℚ), (10582536450674147/312500000000000000000 : ℚ)⟩, [
    (42, modeDataJ4M43)], (70033161749069892353/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b42 : entryChecks 4 bflatBlockJ4B42.entries = true := by
  simp only [entryChecks,bflatBlockJ4B42,List.all_cons,List.all_nil,
    mode_checked_j4_m43,Bool.and_self]
theorem block_mass_checked_j4_b42 : blockMassCheck bflatBlockJ4B42 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
