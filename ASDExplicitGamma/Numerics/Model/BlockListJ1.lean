module
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part000
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part001
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part002
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part003
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part004
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part005
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part006
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part007
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part008
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part009
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part010
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part011
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part012
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part013
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part014
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part015
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part016
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part017
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part018
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part019
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part020
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part021
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part022
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part023
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part024
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part025
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part026
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part027
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part028
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part029
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part030
public import ASDExplicitGamma.Numerics.Model.BlocksJ1Part031

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlocksJ1 : List ModeBlockData := [
  bflatBlockJ1B0,
  bflatBlockJ1B1,
  bflatBlockJ1B2,
  bflatBlockJ1B3,
  bflatBlockJ1B4,
  bflatBlockJ1B5,
  bflatBlockJ1B6,
  bflatBlockJ1B7,
  bflatBlockJ1B8,
  bflatBlockJ1B9,
  bflatBlockJ1B10,
  bflatBlockJ1B11,
  bflatBlockJ1B12,
  bflatBlockJ1B13,
  bflatBlockJ1B14,
  bflatBlockJ1B15,
  bflatBlockJ1B16,
  bflatBlockJ1B17,
  bflatBlockJ1B18,
  bflatBlockJ1B19,
  bflatBlockJ1B20,
  bflatBlockJ1B21,
  bflatBlockJ1B22,
  bflatBlockJ1B23,
  bflatBlockJ1B24,
  bflatBlockJ1B25,
  bflatBlockJ1B26,
  bflatBlockJ1B27,
  bflatBlockJ1B28,
  bflatBlockJ1B29,
  bflatBlockJ1B30,
  bflatBlockJ1B31]
theorem block_cover_j1 : (bflatBlocksJ1.map ModeBlockData.bound).flatMap blockModes = List.range 32 := by
  decide +kernel
theorem all_blocks_entries_j1 : bflatBlocksJ1.all (fun b => entryChecks 1 b.entries) = true := by
  simp only [bflatBlocksJ1,List.all_cons,List.all_nil,
    block_entries_checked_j1_b0,
    block_entries_checked_j1_b1,
    block_entries_checked_j1_b2,
    block_entries_checked_j1_b3,
    block_entries_checked_j1_b4,
    block_entries_checked_j1_b5,
    block_entries_checked_j1_b6,
    block_entries_checked_j1_b7,
    block_entries_checked_j1_b8,
    block_entries_checked_j1_b9,
    block_entries_checked_j1_b10,
    block_entries_checked_j1_b11,
    block_entries_checked_j1_b12,
    block_entries_checked_j1_b13,
    block_entries_checked_j1_b14,
    block_entries_checked_j1_b15,
    block_entries_checked_j1_b16,
    block_entries_checked_j1_b17,
    block_entries_checked_j1_b18,
    block_entries_checked_j1_b19,
    block_entries_checked_j1_b20,
    block_entries_checked_j1_b21,
    block_entries_checked_j1_b22,
    block_entries_checked_j1_b23,
    block_entries_checked_j1_b24,
    block_entries_checked_j1_b25,
    block_entries_checked_j1_b26,
    block_entries_checked_j1_b27,
    block_entries_checked_j1_b28,
    block_entries_checked_j1_b29,
    block_entries_checked_j1_b30,
    block_entries_checked_j1_b31,Bool.and_self]
theorem all_blocks_mass_j1 : bflatBlocksJ1.all (blockMassCheck) = true := by
  simp only [bflatBlocksJ1,List.all_cons,List.all_nil,
    block_mass_checked_j1_b0,
    block_mass_checked_j1_b1,
    block_mass_checked_j1_b2,
    block_mass_checked_j1_b3,
    block_mass_checked_j1_b4,
    block_mass_checked_j1_b5,
    block_mass_checked_j1_b6,
    block_mass_checked_j1_b7,
    block_mass_checked_j1_b8,
    block_mass_checked_j1_b9,
    block_mass_checked_j1_b10,
    block_mass_checked_j1_b11,
    block_mass_checked_j1_b12,
    block_mass_checked_j1_b13,
    block_mass_checked_j1_b14,
    block_mass_checked_j1_b15,
    block_mass_checked_j1_b16,
    block_mass_checked_j1_b17,
    block_mass_checked_j1_b18,
    block_mass_checked_j1_b19,
    block_mass_checked_j1_b20,
    block_mass_checked_j1_b21,
    block_mass_checked_j1_b22,
    block_mass_checked_j1_b23,
    block_mass_checked_j1_b24,
    block_mass_checked_j1_b25,
    block_mass_checked_j1_b26,
    block_mass_checked_j1_b27,
    block_mass_checked_j1_b28,
    block_mass_checked_j1_b29,
    block_mass_checked_j1_b30,
    block_mass_checked_j1_b31,Bool.and_self]
end ASDExplicitGamma.Numerics.Model
