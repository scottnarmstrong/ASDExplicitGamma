module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part012
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part013

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B85 : ModeBlockData :=
  ⟨⟨199, 210, (122357009359844685047/10000000000000000000000 : ℚ), (139546214163760587/1000000000000000000000 : ℚ)⟩, [
    (199, modeDataJ4M200),
    (200, modeDataJ4M201),
    (201, modeDataJ4M202),
    (202, modeDataJ4M203),
    (203, modeDataJ4M204),
    (204, modeDataJ4M205),
    (205, modeDataJ4M206),
    (206, modeDataJ4M207),
    (207, modeDataJ4M208),
    (208, modeDataJ4M209),
    (209, modeDataJ4M210)], (30589252339961171259/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b85 : entryChecks 4 bflatBlockJ4B85.entries = true := by
  simp only [entryChecks,bflatBlockJ4B85,List.all_cons,List.all_nil,
    mode_checked_j4_m200,
    mode_checked_j4_m201,
    mode_checked_j4_m202,
    mode_checked_j4_m203,
    mode_checked_j4_m204,
    mode_checked_j4_m205,
    mode_checked_j4_m206,
    mode_checked_j4_m207,
    mode_checked_j4_m208,
    mode_checked_j4_m209,
    mode_checked_j4_m210,Bool.and_self]
theorem block_mass_checked_j4_b85 : blockMassCheck bflatBlockJ4B85 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
