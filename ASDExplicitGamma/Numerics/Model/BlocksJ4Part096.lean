module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part021
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part022

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B96 : ModeBlockData :=
  ⟨⟨349, 367, (758238864723977899/10000000000000000000000 : ℚ), (2458851907138179/39062500000000000000 : ℚ)⟩, [
    (349, modeDataJ4M350),
    (350, modeDataJ4M351),
    (351, modeDataJ4M352),
    (352, modeDataJ4M353),
    (353, modeDataJ4M354),
    (354, modeDataJ4M355),
    (355, modeDataJ4M356),
    (356, modeDataJ4M357),
    (357, modeDataJ4M358),
    (358, modeDataJ4M359),
    (359, modeDataJ4M360),
    (360, modeDataJ4M361),
    (361, modeDataJ4M362),
    (362, modeDataJ4M363),
    (363, modeDataJ4M364),
    (364, modeDataJ4M365),
    (365, modeDataJ4M366),
    (366, modeDataJ4M367)], (758238864723977881/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b96 : entryChecks 4 bflatBlockJ4B96.entries = true := by
  simp only [entryChecks,bflatBlockJ4B96,List.all_cons,List.all_nil,
    mode_checked_j4_m350,
    mode_checked_j4_m351,
    mode_checked_j4_m352,
    mode_checked_j4_m353,
    mode_checked_j4_m354,
    mode_checked_j4_m355,
    mode_checked_j4_m356,
    mode_checked_j4_m357,
    mode_checked_j4_m358,
    mode_checked_j4_m359,
    mode_checked_j4_m360,
    mode_checked_j4_m361,
    mode_checked_j4_m362,
    mode_checked_j4_m363,
    mode_checked_j4_m364,
    mode_checked_j4_m365,
    mode_checked_j4_m366,
    mode_checked_j4_m367,Bool.and_self]
theorem block_mass_checked_j4_b96 : blockMassCheck bflatBlockJ4B96 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
