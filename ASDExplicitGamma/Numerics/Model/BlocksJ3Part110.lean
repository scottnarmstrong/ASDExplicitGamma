module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part012

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B110 : ModeBlockData :=
  ⟨⟨195, 199, (468401126894436839/10000000000000000000000 : ℚ), (214539940196017403/5000000000000000000000 : ℚ)⟩, [
    (195, modeDataJ3M196),
    (196, modeDataJ3M197),
    (197, modeDataJ3M198),
    (198, modeDataJ3M199)], (93680225378887367/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b110 : entryChecks 3 bflatBlockJ3B110.entries = true := by
  simp only [entryChecks,bflatBlockJ3B110,List.all_cons,List.all_nil,
    mode_checked_j3_m196,
    mode_checked_j3_m197,
    mode_checked_j3_m198,
    mode_checked_j3_m199,Bool.and_self]
theorem block_mass_checked_j3_b110 : blockMassCheck bflatBlockJ3B110 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
