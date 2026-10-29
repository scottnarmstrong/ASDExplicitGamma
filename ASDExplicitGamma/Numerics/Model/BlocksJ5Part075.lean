module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part012
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part013

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B75 : ModeBlockData :=
  ⟨⟨194, 214, (103677408464249027243/2500000000000000000000 : ℚ), (682678577010723/9765625000000000000 : ℚ)⟩, [
    (194, modeDataJ5M195),
    (195, modeDataJ5M196),
    (196, modeDataJ5M197),
    (197, modeDataJ5M198),
    (198, modeDataJ5M199),
    (199, modeDataJ5M200),
    (200, modeDataJ5M201),
    (201, modeDataJ5M202),
    (202, modeDataJ5M203),
    (203, modeDataJ5M204),
    (204, modeDataJ5M205),
    (205, modeDataJ5M206),
    (206, modeDataJ5M207),
    (207, modeDataJ5M208),
    (208, modeDataJ5M209),
    (209, modeDataJ5M210),
    (210, modeDataJ5M211),
    (211, modeDataJ5M212),
    (212, modeDataJ5M213),
    (213, modeDataJ5M214)], (51838704232124513619/1250000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b75 : entryChecks 5 bflatBlockJ5B75.entries = true := by
  simp only [entryChecks,bflatBlockJ5B75,List.all_cons,List.all_nil,
    mode_checked_j5_m195,
    mode_checked_j5_m196,
    mode_checked_j5_m197,
    mode_checked_j5_m198,
    mode_checked_j5_m199,
    mode_checked_j5_m200,
    mode_checked_j5_m201,
    mode_checked_j5_m202,
    mode_checked_j5_m203,
    mode_checked_j5_m204,
    mode_checked_j5_m205,
    mode_checked_j5_m206,
    mode_checked_j5_m207,
    mode_checked_j5_m208,
    mode_checked_j5_m209,
    mode_checked_j5_m210,
    mode_checked_j5_m211,
    mode_checked_j5_m212,
    mode_checked_j5_m213,
    mode_checked_j5_m214,Bool.and_self]
theorem block_mass_checked_j5_b75 : blockMassCheck bflatBlockJ5B75 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
