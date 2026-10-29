module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part009
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part010

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B73 : ModeBlockData :=
  ⟨⟨159, 176, (375811672222783851563/10000000000000000000000 : ℚ), (618271194716972353/10000000000000000000000 : ℚ)⟩, [
    (159, modeDataJ5M160),
    (160, modeDataJ5M161),
    (161, modeDataJ5M162),
    (162, modeDataJ5M163),
    (163, modeDataJ5M164),
    (164, modeDataJ5M165),
    (165, modeDataJ5M166),
    (166, modeDataJ5M167),
    (167, modeDataJ5M168),
    (168, modeDataJ5M169),
    (169, modeDataJ5M170),
    (170, modeDataJ5M171),
    (171, modeDataJ5M172),
    (172, modeDataJ5M173),
    (173, modeDataJ5M174),
    (174, modeDataJ5M175),
    (175, modeDataJ5M176)], (187905836111391925773/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b73 : entryChecks 5 bflatBlockJ5B73.entries = true := by
  simp only [entryChecks,bflatBlockJ5B73,List.all_cons,List.all_nil,
    mode_checked_j5_m160,
    mode_checked_j5_m161,
    mode_checked_j5_m162,
    mode_checked_j5_m163,
    mode_checked_j5_m164,
    mode_checked_j5_m165,
    mode_checked_j5_m166,
    mode_checked_j5_m167,
    mode_checked_j5_m168,
    mode_checked_j5_m169,
    mode_checked_j5_m170,
    mode_checked_j5_m171,
    mode_checked_j5_m172,
    mode_checked_j5_m173,
    mode_checked_j5_m174,
    mode_checked_j5_m175,
    mode_checked_j5_m176,Bool.and_self]
theorem block_mass_checked_j5_b73 : blockMassCheck bflatBlockJ5B73 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
