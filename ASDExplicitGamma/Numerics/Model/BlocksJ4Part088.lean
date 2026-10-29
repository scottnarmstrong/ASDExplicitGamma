module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part014
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part015

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B88 : ModeBlockData :=
  ⟨⟨233, 245, (74102771348664707/12500000000000000000 : ℚ), (27724981577882679/250000000000000000000 : ℚ)⟩, [
    (233, modeDataJ4M234),
    (234, modeDataJ4M235),
    (235, modeDataJ4M236),
    (236, modeDataJ4M237),
    (237, modeDataJ4M238),
    (238, modeDataJ4M239),
    (239, modeDataJ4M240),
    (240, modeDataJ4M241),
    (241, modeDataJ4M242),
    (242, modeDataJ4M243),
    (243, modeDataJ4M244),
    (244, modeDataJ4M245)], (14820554269732941397/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b88 : entryChecks 4 bflatBlockJ4B88.entries = true := by
  simp only [entryChecks,bflatBlockJ4B88,List.all_cons,List.all_nil,
    mode_checked_j4_m234,
    mode_checked_j4_m235,
    mode_checked_j4_m236,
    mode_checked_j4_m237,
    mode_checked_j4_m238,
    mode_checked_j4_m239,
    mode_checked_j4_m240,
    mode_checked_j4_m241,
    mode_checked_j4_m242,
    mode_checked_j4_m243,
    mode_checked_j4_m244,
    mode_checked_j4_m245,Bool.and_self]
theorem block_mass_checked_j4_b88 : blockMassCheck bflatBlockJ4B88 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
