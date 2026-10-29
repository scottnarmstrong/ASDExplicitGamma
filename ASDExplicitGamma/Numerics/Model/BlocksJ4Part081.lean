module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part010

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B81 : ModeBlockData :=
  ⟨⟨161, 170, (202148657561808498629/10000000000000000000000 : ℚ), (795478094975696929/5000000000000000000000 : ℚ)⟩, [
    (161, modeDataJ4M162),
    (162, modeDataJ4M163),
    (163, modeDataJ4M164),
    (164, modeDataJ4M165),
    (165, modeDataJ4M166),
    (166, modeDataJ4M167),
    (167, modeDataJ4M168),
    (168, modeDataJ4M169),
    (169, modeDataJ4M170)], (10107432878090424931/500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b81 : entryChecks 4 bflatBlockJ4B81.entries = true := by
  simp only [entryChecks,bflatBlockJ4B81,List.all_cons,List.all_nil,
    mode_checked_j4_m162,
    mode_checked_j4_m163,
    mode_checked_j4_m164,
    mode_checked_j4_m165,
    mode_checked_j4_m166,
    mode_checked_j4_m167,
    mode_checked_j4_m168,
    mode_checked_j4_m169,
    mode_checked_j4_m170,Bool.and_self]
theorem block_mass_checked_j4_b81 : blockMassCheck bflatBlockJ4B81 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
