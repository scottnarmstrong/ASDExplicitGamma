module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part017
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part018
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part019

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B79 : ModeBlockData :=
  ⟨⟨287, 316, (237518895864978753479/5000000000000000000000 : ℚ), (878860128914842639/10000000000000000000000 : ℚ)⟩, [
    (287, modeDataJ5M288),
    (288, modeDataJ5M289),
    (289, modeDataJ5M290),
    (290, modeDataJ5M291),
    (291, modeDataJ5M292),
    (292, modeDataJ5M293),
    (293, modeDataJ5M294),
    (294, modeDataJ5M295),
    (295, modeDataJ5M296),
    (296, modeDataJ5M297),
    (297, modeDataJ5M298),
    (298, modeDataJ5M299),
    (299, modeDataJ5M300),
    (300, modeDataJ5M301),
    (301, modeDataJ5M302),
    (302, modeDataJ5M303),
    (303, modeDataJ5M304),
    (304, modeDataJ5M305),
    (305, modeDataJ5M306),
    (306, modeDataJ5M307),
    (307, modeDataJ5M308),
    (308, modeDataJ5M309),
    (309, modeDataJ5M310),
    (310, modeDataJ5M311),
    (311, modeDataJ5M312),
    (312, modeDataJ5M313),
    (313, modeDataJ5M314),
    (314, modeDataJ5M315),
    (315, modeDataJ5M316)], (475037791729957506929/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b79 : entryChecks 5 bflatBlockJ5B79.entries = true := by
  simp only [entryChecks,bflatBlockJ5B79,List.all_cons,List.all_nil,
    mode_checked_j5_m288,
    mode_checked_j5_m289,
    mode_checked_j5_m290,
    mode_checked_j5_m291,
    mode_checked_j5_m292,
    mode_checked_j5_m293,
    mode_checked_j5_m294,
    mode_checked_j5_m295,
    mode_checked_j5_m296,
    mode_checked_j5_m297,
    mode_checked_j5_m298,
    mode_checked_j5_m299,
    mode_checked_j5_m300,
    mode_checked_j5_m301,
    mode_checked_j5_m302,
    mode_checked_j5_m303,
    mode_checked_j5_m304,
    mode_checked_j5_m305,
    mode_checked_j5_m306,
    mode_checked_j5_m307,
    mode_checked_j5_m308,
    mode_checked_j5_m309,
    mode_checked_j5_m310,
    mode_checked_j5_m311,
    mode_checked_j5_m312,
    mode_checked_j5_m313,
    mode_checked_j5_m314,
    mode_checked_j5_m315,
    mode_checked_j5_m316,Bool.and_self]
theorem block_mass_checked_j5_b79 : blockMassCheck bflatBlockJ5B79 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
