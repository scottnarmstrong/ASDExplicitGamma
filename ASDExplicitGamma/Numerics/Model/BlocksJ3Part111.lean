module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part012

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B111 : ModeBlockData :=
  ⟨⟨199, 204, (560752852635249511/10000000000000000000000 : ℚ), (511995970873575877/10000000000000000000000 : ℚ)⟩, [
    (199, modeDataJ3M200),
    (200, modeDataJ3M201),
    (201, modeDataJ3M202),
    (202, modeDataJ3M203),
    (203, modeDataJ3M204)], (280376426317624753/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b111 : entryChecks 3 bflatBlockJ3B111.entries = true := by
  simp only [entryChecks,bflatBlockJ3B111,List.all_cons,List.all_nil,
    mode_checked_j3_m200,
    mode_checked_j3_m201,
    mode_checked_j3_m202,
    mode_checked_j3_m203,
    mode_checked_j3_m204,Bool.and_self]
theorem block_mass_checked_j3_b111 : blockMassCheck bflatBlockJ3B111 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
