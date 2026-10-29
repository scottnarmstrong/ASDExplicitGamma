module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part018
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part019

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B93 : ModeBlockData :=
  ⟨⟨300, 316, (3372223851613098681/5000000000000000000000 : ℚ), (803598647786683663/10000000000000000000000 : ℚ)⟩, [
    (300, modeDataJ4M301),
    (301, modeDataJ4M302),
    (302, modeDataJ4M303),
    (303, modeDataJ4M304),
    (304, modeDataJ4M305),
    (305, modeDataJ4M306),
    (306, modeDataJ4M307),
    (307, modeDataJ4M308),
    (308, modeDataJ4M309),
    (309, modeDataJ4M310),
    (310, modeDataJ4M311),
    (311, modeDataJ4M312),
    (312, modeDataJ4M313),
    (313, modeDataJ4M314),
    (314, modeDataJ4M315),
    (315, modeDataJ4M316)], (3372223851613098673/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b93 : entryChecks 4 bflatBlockJ4B93.entries = true := by
  simp only [entryChecks,bflatBlockJ4B93,List.all_cons,List.all_nil,
    mode_checked_j4_m301,
    mode_checked_j4_m302,
    mode_checked_j4_m303,
    mode_checked_j4_m304,
    mode_checked_j4_m305,
    mode_checked_j4_m306,
    mode_checked_j4_m307,
    mode_checked_j4_m308,
    mode_checked_j4_m309,
    mode_checked_j4_m310,
    mode_checked_j4_m311,
    mode_checked_j4_m312,
    mode_checked_j4_m313,
    mode_checked_j4_m314,
    mode_checked_j4_m315,
    mode_checked_j4_m316,Bool.and_self]
theorem block_mass_checked_j4_b93 : blockMassCheck bflatBlockJ4B93 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
