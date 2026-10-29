module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part022
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part023
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part024

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B97 : ModeBlockData :=
  ⟨⟨367, 386, (210693488685147601/2500000000000000000000 : ℚ), (7405255310878173/125000000000000000000 : ℚ)⟩, [
    (367, modeDataJ4M368),
    (368, modeDataJ4M369),
    (369, modeDataJ4M370),
    (370, modeDataJ4M371),
    (371, modeDataJ4M372),
    (372, modeDataJ4M373),
    (373, modeDataJ4M374),
    (374, modeDataJ4M375),
    (375, modeDataJ4M376),
    (376, modeDataJ4M377),
    (377, modeDataJ4M378),
    (378, modeDataJ4M379),
    (379, modeDataJ4M380),
    (380, modeDataJ4M381),
    (381, modeDataJ4M382),
    (382, modeDataJ4M383),
    (383, modeDataJ4M384),
    (384, modeDataJ4M385),
    (385, modeDataJ4M386)], (168554790948118077/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b97 : entryChecks 4 bflatBlockJ4B97.entries = true := by
  simp only [entryChecks,bflatBlockJ4B97,List.all_cons,List.all_nil,
    mode_checked_j4_m368,
    mode_checked_j4_m369,
    mode_checked_j4_m370,
    mode_checked_j4_m371,
    mode_checked_j4_m372,
    mode_checked_j4_m373,
    mode_checked_j4_m374,
    mode_checked_j4_m375,
    mode_checked_j4_m376,
    mode_checked_j4_m377,
    mode_checked_j4_m378,
    mode_checked_j4_m379,
    mode_checked_j4_m380,
    mode_checked_j4_m381,
    mode_checked_j4_m382,
    mode_checked_j4_m383,
    mode_checked_j4_m384,
    mode_checked_j4_m385,
    mode_checked_j4_m386,Bool.and_self]
theorem block_mass_checked_j4_b97 : blockMassCheck bflatBlockJ4B97 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
