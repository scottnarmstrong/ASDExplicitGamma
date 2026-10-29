module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part017
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part018

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B92 : ModeBlockData :=
  ⟨⟨285, 300, (314150571726826809/250000000000000000000 : ℚ), (856356886397781753/10000000000000000000000 : ℚ)⟩, [
    (285, modeDataJ4M286),
    (286, modeDataJ4M287),
    (287, modeDataJ4M288),
    (288, modeDataJ4M289),
    (289, modeDataJ4M290),
    (290, modeDataJ4M291),
    (291, modeDataJ4M292),
    (292, modeDataJ4M293),
    (293, modeDataJ4M294),
    (294, modeDataJ4M295),
    (295, modeDataJ4M296),
    (296, modeDataJ4M297),
    (297, modeDataJ4M298),
    (298, modeDataJ4M299),
    (299, modeDataJ4M300)], (2513204573814614469/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b92 : entryChecks 4 bflatBlockJ4B92.entries = true := by
  simp only [entryChecks,bflatBlockJ4B92,List.all_cons,List.all_nil,
    mode_checked_j4_m286,
    mode_checked_j4_m287,
    mode_checked_j4_m288,
    mode_checked_j4_m289,
    mode_checked_j4_m290,
    mode_checked_j4_m291,
    mode_checked_j4_m292,
    mode_checked_j4_m293,
    mode_checked_j4_m294,
    mode_checked_j4_m295,
    mode_checked_j4_m296,
    mode_checked_j4_m297,
    mode_checked_j4_m298,
    mode_checked_j4_m299,
    mode_checked_j4_m300,Bool.and_self]
theorem block_mass_checked_j4_b92 : blockMassCheck bflatBlockJ4B92 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
