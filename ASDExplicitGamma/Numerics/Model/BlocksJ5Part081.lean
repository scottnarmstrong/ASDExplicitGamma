module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part021
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part022
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part023

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B81 : ModeBlockData :=
  ⟨⟨348, 383, (1818373445517833657/39062500000000000000 : ℚ), (187894504639193877/2000000000000000000000 : ℚ)⟩, [
    (348, modeDataJ5M349),
    (349, modeDataJ5M350),
    (350, modeDataJ5M351),
    (351, modeDataJ5M352),
    (352, modeDataJ5M353),
    (353, modeDataJ5M354),
    (354, modeDataJ5M355),
    (355, modeDataJ5M356),
    (356, modeDataJ5M357),
    (357, modeDataJ5M358),
    (358, modeDataJ5M359),
    (359, modeDataJ5M360),
    (360, modeDataJ5M361),
    (361, modeDataJ5M362),
    (362, modeDataJ5M363),
    (363, modeDataJ5M364),
    (364, modeDataJ5M365),
    (365, modeDataJ5M366),
    (366, modeDataJ5M367),
    (367, modeDataJ5M368),
    (368, modeDataJ5M369),
    (369, modeDataJ5M370),
    (370, modeDataJ5M371),
    (371, modeDataJ5M372),
    (372, modeDataJ5M373),
    (373, modeDataJ5M374),
    (374, modeDataJ5M375),
    (375, modeDataJ5M376),
    (376, modeDataJ5M377),
    (377, modeDataJ5M378),
    (378, modeDataJ5M379),
    (379, modeDataJ5M380),
    (380, modeDataJ5M381),
    (381, modeDataJ5M382),
    (382, modeDataJ5M383)], (465503602052565416157/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b81 : entryChecks 5 bflatBlockJ5B81.entries = true := by
  simp only [entryChecks,bflatBlockJ5B81,List.all_cons,List.all_nil,
    mode_checked_j5_m349,
    mode_checked_j5_m350,
    mode_checked_j5_m351,
    mode_checked_j5_m352,
    mode_checked_j5_m353,
    mode_checked_j5_m354,
    mode_checked_j5_m355,
    mode_checked_j5_m356,
    mode_checked_j5_m357,
    mode_checked_j5_m358,
    mode_checked_j5_m359,
    mode_checked_j5_m360,
    mode_checked_j5_m361,
    mode_checked_j5_m362,
    mode_checked_j5_m363,
    mode_checked_j5_m364,
    mode_checked_j5_m365,
    mode_checked_j5_m366,
    mode_checked_j5_m367,
    mode_checked_j5_m368,
    mode_checked_j5_m369,
    mode_checked_j5_m370,
    mode_checked_j5_m371,
    mode_checked_j5_m372,
    mode_checked_j5_m373,
    mode_checked_j5_m374,
    mode_checked_j5_m375,
    mode_checked_j5_m376,
    mode_checked_j5_m377,
    mode_checked_j5_m378,
    mode_checked_j5_m379,
    mode_checked_j5_m380,
    mode_checked_j5_m381,
    mode_checked_j5_m382,
    mode_checked_j5_m383,Bool.and_self]
theorem block_mass_checked_j5_b81 : blockMassCheck bflatBlockJ5B81 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
