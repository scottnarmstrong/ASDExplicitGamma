module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part020
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part021

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B95 : ModeBlockData :=
  ⟨⟨332, 349, (1311967664353330673/10000000000000000000000 : ℚ), (167172369525740079/2500000000000000000000 : ℚ)⟩, [
    (332, modeDataJ4M333),
    (333, modeDataJ4M334),
    (334, modeDataJ4M335),
    (335, modeDataJ4M336),
    (336, modeDataJ4M337),
    (337, modeDataJ4M338),
    (338, modeDataJ4M339),
    (339, modeDataJ4M340),
    (340, modeDataJ4M341),
    (341, modeDataJ4M342),
    (342, modeDataJ4M343),
    (343, modeDataJ4M344),
    (344, modeDataJ4M345),
    (345, modeDataJ4M346),
    (346, modeDataJ4M347),
    (347, modeDataJ4M348),
    (348, modeDataJ4M349)], (40998989511041583/312500000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b95 : entryChecks 4 bflatBlockJ4B95.entries = true := by
  simp only [entryChecks,bflatBlockJ4B95,List.all_cons,List.all_nil,
    mode_checked_j4_m333,
    mode_checked_j4_m334,
    mode_checked_j4_m335,
    mode_checked_j4_m336,
    mode_checked_j4_m337,
    mode_checked_j4_m338,
    mode_checked_j4_m339,
    mode_checked_j4_m340,
    mode_checked_j4_m341,
    mode_checked_j4_m342,
    mode_checked_j4_m343,
    mode_checked_j4_m344,
    mode_checked_j4_m345,
    mode_checked_j4_m346,
    mode_checked_j4_m347,
    mode_checked_j4_m348,
    mode_checked_j4_m349,Bool.and_self]
theorem block_mass_checked_j4_b95 : blockMassCheck bflatBlockJ4B95 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
