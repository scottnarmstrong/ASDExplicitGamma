module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part016

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B90 : ModeBlockData :=
  ⟨⟨258, 271, (15167568485851580407/5000000000000000000000 : ℚ), (474929539869336963/5000000000000000000000 : ℚ)⟩, [
    (258, modeDataJ4M259),
    (259, modeDataJ4M260),
    (260, modeDataJ4M261),
    (261, modeDataJ4M262),
    (262, modeDataJ4M263),
    (263, modeDataJ4M264),
    (264, modeDataJ4M265),
    (265, modeDataJ4M266),
    (266, modeDataJ4M267),
    (267, modeDataJ4M268),
    (268, modeDataJ4M269),
    (269, modeDataJ4M270),
    (270, modeDataJ4M271)], (30335136971703160801/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b90 : entryChecks 4 bflatBlockJ4B90.entries = true := by
  simp only [entryChecks,bflatBlockJ4B90,List.all_cons,List.all_nil,
    mode_checked_j4_m259,
    mode_checked_j4_m260,
    mode_checked_j4_m261,
    mode_checked_j4_m262,
    mode_checked_j4_m263,
    mode_checked_j4_m264,
    mode_checked_j4_m265,
    mode_checked_j4_m266,
    mode_checked_j4_m267,
    mode_checked_j4_m268,
    mode_checked_j4_m269,
    mode_checked_j4_m270,
    mode_checked_j4_m271,Bool.and_self]
theorem block_mass_checked_j4_b90 : blockMassCheck bflatBlockJ4B90 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
