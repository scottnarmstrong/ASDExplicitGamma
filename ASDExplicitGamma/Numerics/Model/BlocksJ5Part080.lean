module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part019
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part020
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part021

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B80 : ModeBlockData :=
  ⟨⟨316, 348, (238624089485832860929/5000000000000000000000 : ℚ), (917696604022098737/10000000000000000000000 : ℚ)⟩, [
    (316, modeDataJ5M317),
    (317, modeDataJ5M318),
    (318, modeDataJ5M319),
    (319, modeDataJ5M320),
    (320, modeDataJ5M321),
    (321, modeDataJ5M322),
    (322, modeDataJ5M323),
    (323, modeDataJ5M324),
    (324, modeDataJ5M325),
    (325, modeDataJ5M326),
    (326, modeDataJ5M327),
    (327, modeDataJ5M328),
    (328, modeDataJ5M329),
    (329, modeDataJ5M330),
    (330, modeDataJ5M331),
    (331, modeDataJ5M332),
    (332, modeDataJ5M333),
    (333, modeDataJ5M334),
    (334, modeDataJ5M335),
    (335, modeDataJ5M336),
    (336, modeDataJ5M337),
    (337, modeDataJ5M338),
    (338, modeDataJ5M339),
    (339, modeDataJ5M340),
    (340, modeDataJ5M341),
    (341, modeDataJ5M342),
    (342, modeDataJ5M343),
    (343, modeDataJ5M344),
    (344, modeDataJ5M345),
    (345, modeDataJ5M346),
    (346, modeDataJ5M347),
    (347, modeDataJ5M348)], (238624089485832860913/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b80 : entryChecks 5 bflatBlockJ5B80.entries = true := by
  simp only [entryChecks,bflatBlockJ5B80,List.all_cons,List.all_nil,
    mode_checked_j5_m317,
    mode_checked_j5_m318,
    mode_checked_j5_m319,
    mode_checked_j5_m320,
    mode_checked_j5_m321,
    mode_checked_j5_m322,
    mode_checked_j5_m323,
    mode_checked_j5_m324,
    mode_checked_j5_m325,
    mode_checked_j5_m326,
    mode_checked_j5_m327,
    mode_checked_j5_m328,
    mode_checked_j5_m329,
    mode_checked_j5_m330,
    mode_checked_j5_m331,
    mode_checked_j5_m332,
    mode_checked_j5_m333,
    mode_checked_j5_m334,
    mode_checked_j5_m335,
    mode_checked_j5_m336,
    mode_checked_j5_m337,
    mode_checked_j5_m338,
    mode_checked_j5_m339,
    mode_checked_j5_m340,
    mode_checked_j5_m341,
    mode_checked_j5_m342,
    mode_checked_j5_m343,
    mode_checked_j5_m344,
    mode_checked_j5_m345,
    mode_checked_j5_m346,
    mode_checked_j5_m347,
    mode_checked_j5_m348,Bool.and_self]
theorem block_mass_checked_j5_b80 : blockMassCheck bflatBlockJ5B80 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
