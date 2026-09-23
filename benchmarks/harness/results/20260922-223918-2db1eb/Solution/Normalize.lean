import Solution.Data
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0
namespace Quantum.Circuit.Harness
open Instr
theorem local_cancel : ([H 2, H 2, CX 1 2, Tdg 2, CX 0 2, T 2, CX 1 2, Tdg 2, CX 0 2, T 1, T 2, H 2, CX 0 1, T 0, Tdg 1, CX 0 1, H 2] : Circuit 3) ≡ᵤ [CX 1 2, Tdg 2, CX 0 2, T 2, CX 1 2, Tdg 2, CX 0 2, T 1, T 2, CX 0 1, T 0, Tdg 1, CX 0 1] := by
  circuit_simp
theorem cancel0_0 : ac0_0 ≡ᵤ dc0_0 :=
  Equivalent.of_rename (wires₃ (a := 15) (b := 17) (c := 32) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_1 : ac0_1 ≡ᵤ dc0_1 :=
  Equivalent.of_rename (wires₃ (a := 14) (b := 18) (c := 32) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_2 : ac0_2 ≡ᵤ dc0_2 :=
  Equivalent.of_rename (wires₃ (a := 13) (b := 19) (c := 32) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_3 : ac0_3 ≡ᵤ dc0_3 :=
  Equivalent.of_rename (wires₃ (a := 12) (b := 20) (c := 32) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_4 : ac0_4 ≡ᵤ dc0_4 :=
  Equivalent.of_rename (wires₃ (a := 11) (b := 21) (c := 32) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_5 : ac0_5 ≡ᵤ dc0_5 :=
  Equivalent.of_rename (wires₃ (a := 10) (b := 22) (c := 32) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_6 : ac0_6 ≡ᵤ dc0_6 :=
  Equivalent.of_rename (wires₃ (a := 9) (b := 23) (c := 32) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_7 : ac0_7 ≡ᵤ dc0_7 :=
  Equivalent.of_rename (wires₃ (a := 8) (b := 24) (c := 32) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_8 : ac0_8 ≡ᵤ dc0_8 :=
  Equivalent.of_rename (wires₃ (a := 7) (b := 25) (c := 32) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_9 : ac0_9 ≡ᵤ dc0_9 :=
  Equivalent.of_rename (wires₃ (a := 6) (b := 26) (c := 32) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_10 : ac0_10 ≡ᵤ dc0_10 :=
  Equivalent.of_rename (wires₃ (a := 5) (b := 27) (c := 32) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_11 : ac0_11 ≡ᵤ dc0_11 :=
  Equivalent.of_rename (wires₃ (a := 4) (b := 28) (c := 32) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_12 : ac0_12 ≡ᵤ dc0_12 :=
  Equivalent.of_rename (wires₃ (a := 3) (b := 29) (c := 32) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_13 : ac0_13 ≡ᵤ dc0_13 :=
  Equivalent.of_rename (wires₃ (a := 2) (b := 30) (c := 32) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_14 : ac0_14 ≡ᵤ dc0_14 :=
  Equivalent.of_rename (wires₃ (a := 1) (b := 31) (c := 32) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_15 : ac0_15 ≡ᵤ dc0_15 :=
  Equivalent.of_rename (wires₃ (a := 15) (b := 18) (c := 33) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_16 : ac0_16 ≡ᵤ dc0_16 :=
  Equivalent.of_rename (wires₃ (a := 14) (b := 19) (c := 33) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_17 : ac0_17 ≡ᵤ dc0_17 :=
  Equivalent.of_rename (wires₃ (a := 13) (b := 20) (c := 33) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_18 : ac0_18 ≡ᵤ dc0_18 :=
  Equivalent.of_rename (wires₃ (a := 12) (b := 21) (c := 33) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_19 : ac0_19 ≡ᵤ dc0_19 :=
  Equivalent.of_rename (wires₃ (a := 11) (b := 22) (c := 33) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_20 : ac0_20 ≡ᵤ dc0_20 :=
  Equivalent.of_rename (wires₃ (a := 10) (b := 23) (c := 33) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_21 : ac0_21 ≡ᵤ dc0_21 :=
  Equivalent.of_rename (wires₃ (a := 9) (b := 24) (c := 33) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_22 : ac0_22 ≡ᵤ dc0_22 :=
  Equivalent.of_rename (wires₃ (a := 8) (b := 25) (c := 33) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_23 : ac0_23 ≡ᵤ dc0_23 :=
  Equivalent.of_rename (wires₃ (a := 7) (b := 26) (c := 33) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_24 : ac0_24 ≡ᵤ dc0_24 :=
  Equivalent.of_rename (wires₃ (a := 6) (b := 27) (c := 33) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_25 : ac0_25 ≡ᵤ dc0_25 :=
  Equivalent.of_rename (wires₃ (a := 5) (b := 28) (c := 33) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_26 : ac0_26 ≡ᵤ dc0_26 :=
  Equivalent.of_rename (wires₃ (a := 4) (b := 29) (c := 33) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_27 : ac0_27 ≡ᵤ dc0_27 :=
  Equivalent.of_rename (wires₃ (a := 3) (b := 30) (c := 33) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_28 : ac0_28 ≡ᵤ dc0_28 :=
  Equivalent.of_rename (wires₃ (a := 2) (b := 31) (c := 33) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_29 : ac0_29 ≡ᵤ dc0_29 :=
  Equivalent.of_rename (wires₃ (a := 15) (b := 19) (c := 34) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_30 : ac0_30 ≡ᵤ dc0_30 :=
  Equivalent.of_rename (wires₃ (a := 14) (b := 20) (c := 34) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_31 : ac0_31 ≡ᵤ dc0_31 :=
  Equivalent.of_rename (wires₃ (a := 13) (b := 21) (c := 34) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_32 : ac0_32 ≡ᵤ dc0_32 :=
  Equivalent.of_rename (wires₃ (a := 12) (b := 22) (c := 34) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_33 : ac0_33 ≡ᵤ dc0_33 :=
  Equivalent.of_rename (wires₃ (a := 11) (b := 23) (c := 34) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_34 : ac0_34 ≡ᵤ dc0_34 :=
  Equivalent.of_rename (wires₃ (a := 10) (b := 24) (c := 34) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_35 : ac0_35 ≡ᵤ dc0_35 :=
  Equivalent.of_rename (wires₃ (a := 9) (b := 25) (c := 34) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_36 : ac0_36 ≡ᵤ dc0_36 :=
  Equivalent.of_rename (wires₃ (a := 8) (b := 26) (c := 34) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_37 : ac0_37 ≡ᵤ dc0_37 :=
  Equivalent.of_rename (wires₃ (a := 7) (b := 27) (c := 34) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_38 : ac0_38 ≡ᵤ dc0_38 :=
  Equivalent.of_rename (wires₃ (a := 6) (b := 28) (c := 34) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_39 : ac0_39 ≡ᵤ dc0_39 :=
  Equivalent.of_rename (wires₃ (a := 5) (b := 29) (c := 34) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_40 : ac0_40 ≡ᵤ dc0_40 :=
  Equivalent.of_rename (wires₃ (a := 4) (b := 30) (c := 34) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_41 : ac0_41 ≡ᵤ dc0_41 :=
  Equivalent.of_rename (wires₃ (a := 3) (b := 31) (c := 34) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_42 : ac0_42 ≡ᵤ dc0_42 :=
  Equivalent.of_rename (wires₃ (a := 15) (b := 20) (c := 35) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_43 : ac0_43 ≡ᵤ dc0_43 :=
  Equivalent.of_rename (wires₃ (a := 14) (b := 21) (c := 35) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_44 : ac0_44 ≡ᵤ dc0_44 :=
  Equivalent.of_rename (wires₃ (a := 13) (b := 22) (c := 35) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_45 : ac0_45 ≡ᵤ dc0_45 :=
  Equivalent.of_rename (wires₃ (a := 12) (b := 23) (c := 35) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_46 : ac0_46 ≡ᵤ dc0_46 :=
  Equivalent.of_rename (wires₃ (a := 11) (b := 24) (c := 35) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_47 : ac0_47 ≡ᵤ dc0_47 :=
  Equivalent.of_rename (wires₃ (a := 10) (b := 25) (c := 35) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_48 : ac0_48 ≡ᵤ dc0_48 :=
  Equivalent.of_rename (wires₃ (a := 9) (b := 26) (c := 35) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_49 : ac0_49 ≡ᵤ dc0_49 :=
  Equivalent.of_rename (wires₃ (a := 8) (b := 27) (c := 35) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_50 : ac0_50 ≡ᵤ dc0_50 :=
  Equivalent.of_rename (wires₃ (a := 7) (b := 28) (c := 35) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_51 : ac0_51 ≡ᵤ dc0_51 :=
  Equivalent.of_rename (wires₃ (a := 6) (b := 29) (c := 35) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_52 : ac0_52 ≡ᵤ dc0_52 :=
  Equivalent.of_rename (wires₃ (a := 5) (b := 30) (c := 35) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_53 : ac0_53 ≡ᵤ dc0_53 :=
  Equivalent.of_rename (wires₃ (a := 4) (b := 31) (c := 35) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_54 : ac0_54 ≡ᵤ dc0_54 :=
  Equivalent.of_rename (wires₃ (a := 15) (b := 21) (c := 36) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_55 : ac0_55 ≡ᵤ dc0_55 :=
  Equivalent.of_rename (wires₃ (a := 14) (b := 22) (c := 36) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_56 : ac0_56 ≡ᵤ dc0_56 :=
  Equivalent.of_rename (wires₃ (a := 13) (b := 23) (c := 36) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_57 : ac0_57 ≡ᵤ dc0_57 :=
  Equivalent.of_rename (wires₃ (a := 12) (b := 24) (c := 36) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_58 : ac0_58 ≡ᵤ dc0_58 :=
  Equivalent.of_rename (wires₃ (a := 11) (b := 25) (c := 36) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_59 : ac0_59 ≡ᵤ dc0_59 :=
  Equivalent.of_rename (wires₃ (a := 10) (b := 26) (c := 36) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_60 : ac0_60 ≡ᵤ dc0_60 :=
  Equivalent.of_rename (wires₃ (a := 9) (b := 27) (c := 36) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_61 : ac0_61 ≡ᵤ dc0_61 :=
  Equivalent.of_rename (wires₃ (a := 8) (b := 28) (c := 36) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_62 : ac0_62 ≡ᵤ dc0_62 :=
  Equivalent.of_rename (wires₃ (a := 7) (b := 29) (c := 36) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_63 : ac0_63 ≡ᵤ dc0_63 :=
  Equivalent.of_rename (wires₃ (a := 6) (b := 30) (c := 36) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_64 : ac0_64 ≡ᵤ dc0_64 :=
  Equivalent.of_rename (wires₃ (a := 5) (b := 31) (c := 36) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_65 : ac0_65 ≡ᵤ dc0_65 :=
  Equivalent.of_rename (wires₃ (a := 15) (b := 22) (c := 37) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_66 : ac0_66 ≡ᵤ dc0_66 :=
  Equivalent.of_rename (wires₃ (a := 14) (b := 23) (c := 37) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_67 : ac0_67 ≡ᵤ dc0_67 :=
  Equivalent.of_rename (wires₃ (a := 13) (b := 24) (c := 37) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_68 : ac0_68 ≡ᵤ dc0_68 :=
  Equivalent.of_rename (wires₃ (a := 12) (b := 25) (c := 37) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_69 : ac0_69 ≡ᵤ dc0_69 :=
  Equivalent.of_rename (wires₃ (a := 11) (b := 26) (c := 37) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_70 : ac0_70 ≡ᵤ dc0_70 :=
  Equivalent.of_rename (wires₃ (a := 10) (b := 27) (c := 37) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_71 : ac0_71 ≡ᵤ dc0_71 :=
  Equivalent.of_rename (wires₃ (a := 9) (b := 28) (c := 37) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_72 : ac0_72 ≡ᵤ dc0_72 :=
  Equivalent.of_rename (wires₃ (a := 8) (b := 29) (c := 37) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_73 : ac0_73 ≡ᵤ dc0_73 :=
  Equivalent.of_rename (wires₃ (a := 7) (b := 30) (c := 37) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_74 : ac0_74 ≡ᵤ dc0_74 :=
  Equivalent.of_rename (wires₃ (a := 6) (b := 31) (c := 37) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_75 : ac0_75 ≡ᵤ dc0_75 :=
  Equivalent.of_rename (wires₃ (a := 15) (b := 23) (c := 38) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_76 : ac0_76 ≡ᵤ dc0_76 :=
  Equivalent.of_rename (wires₃ (a := 14) (b := 24) (c := 38) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_77 : ac0_77 ≡ᵤ dc0_77 :=
  Equivalent.of_rename (wires₃ (a := 13) (b := 25) (c := 38) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_78 : ac0_78 ≡ᵤ dc0_78 :=
  Equivalent.of_rename (wires₃ (a := 12) (b := 26) (c := 38) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_79 : ac0_79 ≡ᵤ dc0_79 :=
  Equivalent.of_rename (wires₃ (a := 11) (b := 27) (c := 38) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_80 : ac0_80 ≡ᵤ dc0_80 :=
  Equivalent.of_rename (wires₃ (a := 10) (b := 28) (c := 38) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_81 : ac0_81 ≡ᵤ dc0_81 :=
  Equivalent.of_rename (wires₃ (a := 9) (b := 29) (c := 38) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_82 : ac0_82 ≡ᵤ dc0_82 :=
  Equivalent.of_rename (wires₃ (a := 8) (b := 30) (c := 38) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_83 : ac0_83 ≡ᵤ dc0_83 :=
  Equivalent.of_rename (wires₃ (a := 7) (b := 31) (c := 38) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_84 : ac0_84 ≡ᵤ dc0_84 :=
  Equivalent.of_rename (wires₃ (a := 15) (b := 24) (c := 39) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_85 : ac0_85 ≡ᵤ dc0_85 :=
  Equivalent.of_rename (wires₃ (a := 14) (b := 25) (c := 39) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_86 : ac0_86 ≡ᵤ dc0_86 :=
  Equivalent.of_rename (wires₃ (a := 13) (b := 26) (c := 39) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_87 : ac0_87 ≡ᵤ dc0_87 :=
  Equivalent.of_rename (wires₃ (a := 12) (b := 27) (c := 39) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_88 : ac0_88 ≡ᵤ dc0_88 :=
  Equivalent.of_rename (wires₃ (a := 11) (b := 28) (c := 39) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_89 : ac0_89 ≡ᵤ dc0_89 :=
  Equivalent.of_rename (wires₃ (a := 10) (b := 29) (c := 39) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_90 : ac0_90 ≡ᵤ dc0_90 :=
  Equivalent.of_rename (wires₃ (a := 9) (b := 30) (c := 39) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_91 : ac0_91 ≡ᵤ dc0_91 :=
  Equivalent.of_rename (wires₃ (a := 8) (b := 31) (c := 39) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_92 : ac0_92 ≡ᵤ dc0_92 :=
  Equivalent.of_rename (wires₃ (a := 15) (b := 25) (c := 40) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_93 : ac0_93 ≡ᵤ dc0_93 :=
  Equivalent.of_rename (wires₃ (a := 14) (b := 26) (c := 40) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_94 : ac0_94 ≡ᵤ dc0_94 :=
  Equivalent.of_rename (wires₃ (a := 13) (b := 27) (c := 40) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_95 : ac0_95 ≡ᵤ dc0_95 :=
  Equivalent.of_rename (wires₃ (a := 12) (b := 28) (c := 40) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_96 : ac0_96 ≡ᵤ dc0_96 :=
  Equivalent.of_rename (wires₃ (a := 11) (b := 29) (c := 40) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_97 : ac0_97 ≡ᵤ dc0_97 :=
  Equivalent.of_rename (wires₃ (a := 10) (b := 30) (c := 40) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_98 : ac0_98 ≡ᵤ dc0_98 :=
  Equivalent.of_rename (wires₃ (a := 9) (b := 31) (c := 40) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_99 : ac0_99 ≡ᵤ dc0_99 :=
  Equivalent.of_rename (wires₃ (a := 15) (b := 26) (c := 41) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_100 : ac0_100 ≡ᵤ dc0_100 :=
  Equivalent.of_rename (wires₃ (a := 14) (b := 27) (c := 41) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_101 : ac0_101 ≡ᵤ dc0_101 :=
  Equivalent.of_rename (wires₃ (a := 13) (b := 28) (c := 41) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_102 : ac0_102 ≡ᵤ dc0_102 :=
  Equivalent.of_rename (wires₃ (a := 12) (b := 29) (c := 41) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_103 : ac0_103 ≡ᵤ dc0_103 :=
  Equivalent.of_rename (wires₃ (a := 11) (b := 30) (c := 41) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_104 : ac0_104 ≡ᵤ dc0_104 :=
  Equivalent.of_rename (wires₃ (a := 10) (b := 31) (c := 41) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_105 : ac0_105 ≡ᵤ dc0_105 :=
  Equivalent.of_rename (wires₃ (a := 15) (b := 27) (c := 42) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_106 : ac0_106 ≡ᵤ dc0_106 :=
  Equivalent.of_rename (wires₃ (a := 14) (b := 28) (c := 42) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_107 : ac0_107 ≡ᵤ dc0_107 :=
  Equivalent.of_rename (wires₃ (a := 13) (b := 29) (c := 42) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_108 : ac0_108 ≡ᵤ dc0_108 :=
  Equivalent.of_rename (wires₃ (a := 12) (b := 30) (c := 42) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_109 : ac0_109 ≡ᵤ dc0_109 :=
  Equivalent.of_rename (wires₃ (a := 11) (b := 31) (c := 42) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_110 : ac0_110 ≡ᵤ dc0_110 :=
  Equivalent.of_rename (wires₃ (a := 15) (b := 28) (c := 43) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_111 : ac0_111 ≡ᵤ dc0_111 :=
  Equivalent.of_rename (wires₃ (a := 14) (b := 29) (c := 43) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_112 : ac0_112 ≡ᵤ dc0_112 :=
  Equivalent.of_rename (wires₃ (a := 13) (b := 30) (c := 43) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_113 : ac0_113 ≡ᵤ dc0_113 :=
  Equivalent.of_rename (wires₃ (a := 12) (b := 31) (c := 43) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_114 : ac0_114 ≡ᵤ dc0_114 :=
  Equivalent.of_rename (wires₃ (a := 15) (b := 29) (c := 44) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_115 : ac0_115 ≡ᵤ dc0_115 :=
  Equivalent.of_rename (wires₃ (a := 14) (b := 30) (c := 44) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_116 : ac0_116 ≡ᵤ dc0_116 :=
  Equivalent.of_rename (wires₃ (a := 13) (b := 31) (c := 44) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_117 : ac0_117 ≡ᵤ dc0_117 :=
  Equivalent.of_rename (wires₃ (a := 15) (b := 30) (c := 45) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_118 : ac0_118 ≡ᵤ dc0_118 :=
  Equivalent.of_rename (wires₃ (a := 14) (b := 31) (c := 45) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel0_119 : ac0_119 ≡ᵤ dc0_119 :=
  Equivalent.of_rename (wires₃ (a := 15) (b := 31) (c := 46) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem normalize0 : a0 ≡ᵤ d0 := by
  exact ((((((cancel0_0).append ((cancel0_1).append (cancel0_2))).append (((cancel0_3).append (cancel0_4)).append ((cancel0_5).append (cancel0_6)))).append ((((cancel0_7).append (cancel0_8)).append ((cancel0_9).append (cancel0_10))).append (((cancel0_11).append (cancel0_12)).append ((cancel0_13).append (cancel0_14))))).append ((((cancel0_15).append ((cancel0_16).append (cancel0_17))).append (((cancel0_18).append (cancel0_19)).append ((cancel0_20).append (cancel0_21)))).append ((((cancel0_22).append (cancel0_23)).append ((cancel0_24).append (cancel0_25))).append (((cancel0_26).append (cancel0_27)).append ((cancel0_28).append (cancel0_29)))))).append (((((cancel0_30).append ((cancel0_31).append (cancel0_32))).append (((cancel0_33).append (cancel0_34)).append ((cancel0_35).append (cancel0_36)))).append ((((cancel0_37).append (cancel0_38)).append ((cancel0_39).append (cancel0_40))).append (((cancel0_41).append (cancel0_42)).append ((cancel0_43).append (cancel0_44))))).append ((((cancel0_45).append ((cancel0_46).append (cancel0_47))).append (((cancel0_48).append (cancel0_49)).append ((cancel0_50).append (cancel0_51)))).append ((((cancel0_52).append (cancel0_53)).append ((cancel0_54).append (cancel0_55))).append (((cancel0_56).append (cancel0_57)).append ((cancel0_58).append (cancel0_59))))))).append ((((((cancel0_60).append ((cancel0_61).append (cancel0_62))).append (((cancel0_63).append (cancel0_64)).append ((cancel0_65).append (cancel0_66)))).append ((((cancel0_67).append (cancel0_68)).append ((cancel0_69).append (cancel0_70))).append (((cancel0_71).append (cancel0_72)).append ((cancel0_73).append (cancel0_74))))).append ((((cancel0_75).append ((cancel0_76).append (cancel0_77))).append (((cancel0_78).append (cancel0_79)).append ((cancel0_80).append (cancel0_81)))).append ((((cancel0_82).append (cancel0_83)).append ((cancel0_84).append (cancel0_85))).append (((cancel0_86).append (cancel0_87)).append ((cancel0_88).append (cancel0_89)))))).append (((((cancel0_90).append ((cancel0_91).append (cancel0_92))).append (((cancel0_93).append (cancel0_94)).append ((cancel0_95).append (cancel0_96)))).append ((((cancel0_97).append (cancel0_98)).append ((cancel0_99).append (cancel0_100))).append (((cancel0_101).append (cancel0_102)).append ((cancel0_103).append (cancel0_104))))).append ((((cancel0_105).append ((cancel0_106).append (cancel0_107))).append (((cancel0_108).append (cancel0_109)).append ((cancel0_110).append (cancel0_111)))).append ((((cancel0_112).append (cancel0_113)).append ((cancel0_114).append (cancel0_115))).append (((cancel0_116).append (cancel0_117)).append ((cancel0_118).append (cancel0_119)))))))
theorem cancel1_0 : ac1_0 ≡ᵤ dc1_0 :=
  Equivalent.of_rename (wires₃ (a := 15) (b := 16) (c := 47) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_1 : ac1_1 ≡ᵤ dc1_1 :=
  Equivalent.of_rename (wires₃ (a := 14) (b := 17) (c := 47) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_2 : ac1_2 ≡ᵤ dc1_2 :=
  Equivalent.of_rename (wires₃ (a := 13) (b := 18) (c := 47) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_3 : ac1_3 ≡ᵤ dc1_3 :=
  Equivalent.of_rename (wires₃ (a := 12) (b := 19) (c := 47) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_4 : ac1_4 ≡ᵤ dc1_4 :=
  Equivalent.of_rename (wires₃ (a := 11) (b := 20) (c := 47) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_5 : ac1_5 ≡ᵤ dc1_5 :=
  Equivalent.of_rename (wires₃ (a := 10) (b := 21) (c := 47) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_6 : ac1_6 ≡ᵤ dc1_6 :=
  Equivalent.of_rename (wires₃ (a := 9) (b := 22) (c := 47) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_7 : ac1_7 ≡ᵤ dc1_7 :=
  Equivalent.of_rename (wires₃ (a := 8) (b := 23) (c := 47) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_8 : ac1_8 ≡ᵤ dc1_8 :=
  Equivalent.of_rename (wires₃ (a := 7) (b := 24) (c := 47) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_9 : ac1_9 ≡ᵤ dc1_9 :=
  Equivalent.of_rename (wires₃ (a := 6) (b := 25) (c := 47) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_10 : ac1_10 ≡ᵤ dc1_10 :=
  Equivalent.of_rename (wires₃ (a := 5) (b := 26) (c := 47) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_11 : ac1_11 ≡ᵤ dc1_11 :=
  Equivalent.of_rename (wires₃ (a := 4) (b := 27) (c := 47) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_12 : ac1_12 ≡ᵤ dc1_12 :=
  Equivalent.of_rename (wires₃ (a := 3) (b := 28) (c := 47) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_13 : ac1_13 ≡ᵤ dc1_13 :=
  Equivalent.of_rename (wires₃ (a := 2) (b := 29) (c := 47) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_14 : ac1_14 ≡ᵤ dc1_14 :=
  Equivalent.of_rename (wires₃ (a := 1) (b := 30) (c := 47) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_15 : ac1_15 ≡ᵤ dc1_15 :=
  Equivalent.of_rename (wires₃ (a := 0) (b := 31) (c := 47) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_16 : ac1_16 ≡ᵤ dc1_16 :=
  Equivalent.of_rename (wires₃ (a := 14) (b := 16) (c := 46) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_17 : ac1_17 ≡ᵤ dc1_17 :=
  Equivalent.of_rename (wires₃ (a := 13) (b := 17) (c := 46) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_18 : ac1_18 ≡ᵤ dc1_18 :=
  Equivalent.of_rename (wires₃ (a := 12) (b := 18) (c := 46) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_19 : ac1_19 ≡ᵤ dc1_19 :=
  Equivalent.of_rename (wires₃ (a := 11) (b := 19) (c := 46) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_20 : ac1_20 ≡ᵤ dc1_20 :=
  Equivalent.of_rename (wires₃ (a := 10) (b := 20) (c := 46) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_21 : ac1_21 ≡ᵤ dc1_21 :=
  Equivalent.of_rename (wires₃ (a := 9) (b := 21) (c := 46) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_22 : ac1_22 ≡ᵤ dc1_22 :=
  Equivalent.of_rename (wires₃ (a := 8) (b := 22) (c := 46) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_23 : ac1_23 ≡ᵤ dc1_23 :=
  Equivalent.of_rename (wires₃ (a := 7) (b := 23) (c := 46) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_24 : ac1_24 ≡ᵤ dc1_24 :=
  Equivalent.of_rename (wires₃ (a := 6) (b := 24) (c := 46) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_25 : ac1_25 ≡ᵤ dc1_25 :=
  Equivalent.of_rename (wires₃ (a := 5) (b := 25) (c := 46) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_26 : ac1_26 ≡ᵤ dc1_26 :=
  Equivalent.of_rename (wires₃ (a := 4) (b := 26) (c := 46) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_27 : ac1_27 ≡ᵤ dc1_27 :=
  Equivalent.of_rename (wires₃ (a := 3) (b := 27) (c := 46) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_28 : ac1_28 ≡ᵤ dc1_28 :=
  Equivalent.of_rename (wires₃ (a := 2) (b := 28) (c := 46) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_29 : ac1_29 ≡ᵤ dc1_29 :=
  Equivalent.of_rename (wires₃ (a := 1) (b := 29) (c := 46) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_30 : ac1_30 ≡ᵤ dc1_30 :=
  Equivalent.of_rename (wires₃ (a := 0) (b := 30) (c := 46) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_31 : ac1_31 ≡ᵤ dc1_31 :=
  Equivalent.of_rename (wires₃ (a := 13) (b := 16) (c := 45) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_32 : ac1_32 ≡ᵤ dc1_32 :=
  Equivalent.of_rename (wires₃ (a := 12) (b := 17) (c := 45) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_33 : ac1_33 ≡ᵤ dc1_33 :=
  Equivalent.of_rename (wires₃ (a := 11) (b := 18) (c := 45) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_34 : ac1_34 ≡ᵤ dc1_34 :=
  Equivalent.of_rename (wires₃ (a := 10) (b := 19) (c := 45) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_35 : ac1_35 ≡ᵤ dc1_35 :=
  Equivalent.of_rename (wires₃ (a := 9) (b := 20) (c := 45) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_36 : ac1_36 ≡ᵤ dc1_36 :=
  Equivalent.of_rename (wires₃ (a := 8) (b := 21) (c := 45) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_37 : ac1_37 ≡ᵤ dc1_37 :=
  Equivalent.of_rename (wires₃ (a := 7) (b := 22) (c := 45) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_38 : ac1_38 ≡ᵤ dc1_38 :=
  Equivalent.of_rename (wires₃ (a := 6) (b := 23) (c := 45) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_39 : ac1_39 ≡ᵤ dc1_39 :=
  Equivalent.of_rename (wires₃ (a := 5) (b := 24) (c := 45) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_40 : ac1_40 ≡ᵤ dc1_40 :=
  Equivalent.of_rename (wires₃ (a := 4) (b := 25) (c := 45) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_41 : ac1_41 ≡ᵤ dc1_41 :=
  Equivalent.of_rename (wires₃ (a := 3) (b := 26) (c := 45) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_42 : ac1_42 ≡ᵤ dc1_42 :=
  Equivalent.of_rename (wires₃ (a := 2) (b := 27) (c := 45) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_43 : ac1_43 ≡ᵤ dc1_43 :=
  Equivalent.of_rename (wires₃ (a := 1) (b := 28) (c := 45) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_44 : ac1_44 ≡ᵤ dc1_44 :=
  Equivalent.of_rename (wires₃ (a := 0) (b := 29) (c := 45) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_45 : ac1_45 ≡ᵤ dc1_45 :=
  Equivalent.of_rename (wires₃ (a := 12) (b := 16) (c := 44) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_46 : ac1_46 ≡ᵤ dc1_46 :=
  Equivalent.of_rename (wires₃ (a := 11) (b := 17) (c := 44) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_47 : ac1_47 ≡ᵤ dc1_47 :=
  Equivalent.of_rename (wires₃ (a := 10) (b := 18) (c := 44) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_48 : ac1_48 ≡ᵤ dc1_48 :=
  Equivalent.of_rename (wires₃ (a := 9) (b := 19) (c := 44) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_49 : ac1_49 ≡ᵤ dc1_49 :=
  Equivalent.of_rename (wires₃ (a := 8) (b := 20) (c := 44) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_50 : ac1_50 ≡ᵤ dc1_50 :=
  Equivalent.of_rename (wires₃ (a := 7) (b := 21) (c := 44) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_51 : ac1_51 ≡ᵤ dc1_51 :=
  Equivalent.of_rename (wires₃ (a := 6) (b := 22) (c := 44) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_52 : ac1_52 ≡ᵤ dc1_52 :=
  Equivalent.of_rename (wires₃ (a := 5) (b := 23) (c := 44) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_53 : ac1_53 ≡ᵤ dc1_53 :=
  Equivalent.of_rename (wires₃ (a := 4) (b := 24) (c := 44) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_54 : ac1_54 ≡ᵤ dc1_54 :=
  Equivalent.of_rename (wires₃ (a := 3) (b := 25) (c := 44) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_55 : ac1_55 ≡ᵤ dc1_55 :=
  Equivalent.of_rename (wires₃ (a := 2) (b := 26) (c := 44) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_56 : ac1_56 ≡ᵤ dc1_56 :=
  Equivalent.of_rename (wires₃ (a := 1) (b := 27) (c := 44) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_57 : ac1_57 ≡ᵤ dc1_57 :=
  Equivalent.of_rename (wires₃ (a := 0) (b := 28) (c := 44) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_58 : ac1_58 ≡ᵤ dc1_58 :=
  Equivalent.of_rename (wires₃ (a := 11) (b := 16) (c := 43) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_59 : ac1_59 ≡ᵤ dc1_59 :=
  Equivalent.of_rename (wires₃ (a := 10) (b := 17) (c := 43) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_60 : ac1_60 ≡ᵤ dc1_60 :=
  Equivalent.of_rename (wires₃ (a := 9) (b := 18) (c := 43) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_61 : ac1_61 ≡ᵤ dc1_61 :=
  Equivalent.of_rename (wires₃ (a := 8) (b := 19) (c := 43) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_62 : ac1_62 ≡ᵤ dc1_62 :=
  Equivalent.of_rename (wires₃ (a := 7) (b := 20) (c := 43) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_63 : ac1_63 ≡ᵤ dc1_63 :=
  Equivalent.of_rename (wires₃ (a := 6) (b := 21) (c := 43) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_64 : ac1_64 ≡ᵤ dc1_64 :=
  Equivalent.of_rename (wires₃ (a := 5) (b := 22) (c := 43) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_65 : ac1_65 ≡ᵤ dc1_65 :=
  Equivalent.of_rename (wires₃ (a := 4) (b := 23) (c := 43) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_66 : ac1_66 ≡ᵤ dc1_66 :=
  Equivalent.of_rename (wires₃ (a := 3) (b := 24) (c := 43) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_67 : ac1_67 ≡ᵤ dc1_67 :=
  Equivalent.of_rename (wires₃ (a := 2) (b := 25) (c := 43) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_68 : ac1_68 ≡ᵤ dc1_68 :=
  Equivalent.of_rename (wires₃ (a := 1) (b := 26) (c := 43) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_69 : ac1_69 ≡ᵤ dc1_69 :=
  Equivalent.of_rename (wires₃ (a := 0) (b := 27) (c := 43) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_70 : ac1_70 ≡ᵤ dc1_70 :=
  Equivalent.of_rename (wires₃ (a := 10) (b := 16) (c := 42) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_71 : ac1_71 ≡ᵤ dc1_71 :=
  Equivalent.of_rename (wires₃ (a := 9) (b := 17) (c := 42) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_72 : ac1_72 ≡ᵤ dc1_72 :=
  Equivalent.of_rename (wires₃ (a := 8) (b := 18) (c := 42) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_73 : ac1_73 ≡ᵤ dc1_73 :=
  Equivalent.of_rename (wires₃ (a := 7) (b := 19) (c := 42) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_74 : ac1_74 ≡ᵤ dc1_74 :=
  Equivalent.of_rename (wires₃ (a := 6) (b := 20) (c := 42) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_75 : ac1_75 ≡ᵤ dc1_75 :=
  Equivalent.of_rename (wires₃ (a := 5) (b := 21) (c := 42) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_76 : ac1_76 ≡ᵤ dc1_76 :=
  Equivalent.of_rename (wires₃ (a := 4) (b := 22) (c := 42) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_77 : ac1_77 ≡ᵤ dc1_77 :=
  Equivalent.of_rename (wires₃ (a := 3) (b := 23) (c := 42) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_78 : ac1_78 ≡ᵤ dc1_78 :=
  Equivalent.of_rename (wires₃ (a := 2) (b := 24) (c := 42) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_79 : ac1_79 ≡ᵤ dc1_79 :=
  Equivalent.of_rename (wires₃ (a := 1) (b := 25) (c := 42) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_80 : ac1_80 ≡ᵤ dc1_80 :=
  Equivalent.of_rename (wires₃ (a := 0) (b := 26) (c := 42) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_81 : ac1_81 ≡ᵤ dc1_81 :=
  Equivalent.of_rename (wires₃ (a := 9) (b := 16) (c := 41) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_82 : ac1_82 ≡ᵤ dc1_82 :=
  Equivalent.of_rename (wires₃ (a := 8) (b := 17) (c := 41) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_83 : ac1_83 ≡ᵤ dc1_83 :=
  Equivalent.of_rename (wires₃ (a := 7) (b := 18) (c := 41) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_84 : ac1_84 ≡ᵤ dc1_84 :=
  Equivalent.of_rename (wires₃ (a := 6) (b := 19) (c := 41) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_85 : ac1_85 ≡ᵤ dc1_85 :=
  Equivalent.of_rename (wires₃ (a := 5) (b := 20) (c := 41) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_86 : ac1_86 ≡ᵤ dc1_86 :=
  Equivalent.of_rename (wires₃ (a := 4) (b := 21) (c := 41) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_87 : ac1_87 ≡ᵤ dc1_87 :=
  Equivalent.of_rename (wires₃ (a := 3) (b := 22) (c := 41) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_88 : ac1_88 ≡ᵤ dc1_88 :=
  Equivalent.of_rename (wires₃ (a := 2) (b := 23) (c := 41) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_89 : ac1_89 ≡ᵤ dc1_89 :=
  Equivalent.of_rename (wires₃ (a := 1) (b := 24) (c := 41) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_90 : ac1_90 ≡ᵤ dc1_90 :=
  Equivalent.of_rename (wires₃ (a := 0) (b := 25) (c := 41) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_91 : ac1_91 ≡ᵤ dc1_91 :=
  Equivalent.of_rename (wires₃ (a := 8) (b := 16) (c := 40) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_92 : ac1_92 ≡ᵤ dc1_92 :=
  Equivalent.of_rename (wires₃ (a := 7) (b := 17) (c := 40) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_93 : ac1_93 ≡ᵤ dc1_93 :=
  Equivalent.of_rename (wires₃ (a := 6) (b := 18) (c := 40) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_94 : ac1_94 ≡ᵤ dc1_94 :=
  Equivalent.of_rename (wires₃ (a := 5) (b := 19) (c := 40) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_95 : ac1_95 ≡ᵤ dc1_95 :=
  Equivalent.of_rename (wires₃ (a := 4) (b := 20) (c := 40) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_96 : ac1_96 ≡ᵤ dc1_96 :=
  Equivalent.of_rename (wires₃ (a := 3) (b := 21) (c := 40) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_97 : ac1_97 ≡ᵤ dc1_97 :=
  Equivalent.of_rename (wires₃ (a := 2) (b := 22) (c := 40) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_98 : ac1_98 ≡ᵤ dc1_98 :=
  Equivalent.of_rename (wires₃ (a := 1) (b := 23) (c := 40) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_99 : ac1_99 ≡ᵤ dc1_99 :=
  Equivalent.of_rename (wires₃ (a := 0) (b := 24) (c := 40) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_100 : ac1_100 ≡ᵤ dc1_100 :=
  Equivalent.of_rename (wires₃ (a := 7) (b := 16) (c := 39) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_101 : ac1_101 ≡ᵤ dc1_101 :=
  Equivalent.of_rename (wires₃ (a := 6) (b := 17) (c := 39) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_102 : ac1_102 ≡ᵤ dc1_102 :=
  Equivalent.of_rename (wires₃ (a := 5) (b := 18) (c := 39) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_103 : ac1_103 ≡ᵤ dc1_103 :=
  Equivalent.of_rename (wires₃ (a := 4) (b := 19) (c := 39) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_104 : ac1_104 ≡ᵤ dc1_104 :=
  Equivalent.of_rename (wires₃ (a := 3) (b := 20) (c := 39) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_105 : ac1_105 ≡ᵤ dc1_105 :=
  Equivalent.of_rename (wires₃ (a := 2) (b := 21) (c := 39) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_106 : ac1_106 ≡ᵤ dc1_106 :=
  Equivalent.of_rename (wires₃ (a := 1) (b := 22) (c := 39) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_107 : ac1_107 ≡ᵤ dc1_107 :=
  Equivalent.of_rename (wires₃ (a := 0) (b := 23) (c := 39) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_108 : ac1_108 ≡ᵤ dc1_108 :=
  Equivalent.of_rename (wires₃ (a := 6) (b := 16) (c := 38) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_109 : ac1_109 ≡ᵤ dc1_109 :=
  Equivalent.of_rename (wires₃ (a := 5) (b := 17) (c := 38) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_110 : ac1_110 ≡ᵤ dc1_110 :=
  Equivalent.of_rename (wires₃ (a := 4) (b := 18) (c := 38) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_111 : ac1_111 ≡ᵤ dc1_111 :=
  Equivalent.of_rename (wires₃ (a := 3) (b := 19) (c := 38) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_112 : ac1_112 ≡ᵤ dc1_112 :=
  Equivalent.of_rename (wires₃ (a := 2) (b := 20) (c := 38) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_113 : ac1_113 ≡ᵤ dc1_113 :=
  Equivalent.of_rename (wires₃ (a := 1) (b := 21) (c := 38) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_114 : ac1_114 ≡ᵤ dc1_114 :=
  Equivalent.of_rename (wires₃ (a := 0) (b := 22) (c := 38) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_115 : ac1_115 ≡ᵤ dc1_115 :=
  Equivalent.of_rename (wires₃ (a := 5) (b := 16) (c := 37) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_116 : ac1_116 ≡ᵤ dc1_116 :=
  Equivalent.of_rename (wires₃ (a := 4) (b := 17) (c := 37) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_117 : ac1_117 ≡ᵤ dc1_117 :=
  Equivalent.of_rename (wires₃ (a := 3) (b := 18) (c := 37) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_118 : ac1_118 ≡ᵤ dc1_118 :=
  Equivalent.of_rename (wires₃ (a := 2) (b := 19) (c := 37) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_119 : ac1_119 ≡ᵤ dc1_119 :=
  Equivalent.of_rename (wires₃ (a := 1) (b := 20) (c := 37) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_120 : ac1_120 ≡ᵤ dc1_120 :=
  Equivalent.of_rename (wires₃ (a := 0) (b := 21) (c := 37) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_121 : ac1_121 ≡ᵤ dc1_121 :=
  Equivalent.of_rename (wires₃ (a := 4) (b := 16) (c := 36) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_122 : ac1_122 ≡ᵤ dc1_122 :=
  Equivalent.of_rename (wires₃ (a := 3) (b := 17) (c := 36) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_123 : ac1_123 ≡ᵤ dc1_123 :=
  Equivalent.of_rename (wires₃ (a := 2) (b := 18) (c := 36) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_124 : ac1_124 ≡ᵤ dc1_124 :=
  Equivalent.of_rename (wires₃ (a := 1) (b := 19) (c := 36) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_125 : ac1_125 ≡ᵤ dc1_125 :=
  Equivalent.of_rename (wires₃ (a := 0) (b := 20) (c := 36) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_126 : ac1_126 ≡ᵤ dc1_126 :=
  Equivalent.of_rename (wires₃ (a := 3) (b := 16) (c := 35) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_127 : ac1_127 ≡ᵤ dc1_127 :=
  Equivalent.of_rename (wires₃ (a := 2) (b := 17) (c := 35) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_128 : ac1_128 ≡ᵤ dc1_128 :=
  Equivalent.of_rename (wires₃ (a := 1) (b := 18) (c := 35) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_129 : ac1_129 ≡ᵤ dc1_129 :=
  Equivalent.of_rename (wires₃ (a := 0) (b := 19) (c := 35) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_130 : ac1_130 ≡ᵤ dc1_130 :=
  Equivalent.of_rename (wires₃ (a := 2) (b := 16) (c := 34) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_131 : ac1_131 ≡ᵤ dc1_131 :=
  Equivalent.of_rename (wires₃ (a := 1) (b := 17) (c := 34) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_132 : ac1_132 ≡ᵤ dc1_132 :=
  Equivalent.of_rename (wires₃ (a := 0) (b := 18) (c := 34) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_133 : ac1_133 ≡ᵤ dc1_133 :=
  Equivalent.of_rename (wires₃ (a := 1) (b := 16) (c := 33) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_134 : ac1_134 ≡ᵤ dc1_134 :=
  Equivalent.of_rename (wires₃ (a := 0) (b := 17) (c := 33) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem cancel1_135 : ac1_135 ≡ᵤ dc1_135 :=
  Equivalent.of_rename (wires₃ (a := 0) (b := 16) (c := 32) (by decide) (by decide) (by decide)) local_cancel rfl rfl
theorem normalize1 : a1 ≡ᵤ d1 := by
  exact (((((((cancel1_0).append (cancel1_1)).append ((cancel1_2).append (cancel1_3))).append (((cancel1_4).append (cancel1_5)).append ((cancel1_6).append (cancel1_7)))).append ((((cancel1_8).append (cancel1_9)).append ((cancel1_10).append (cancel1_11))).append (((cancel1_12).append (cancel1_13)).append ((cancel1_14).append ((cancel1_15).append (cancel1_16)))))).append (((((cancel1_17).append (cancel1_18)).append ((cancel1_19).append (cancel1_20))).append (((cancel1_21).append (cancel1_22)).append ((cancel1_23).append (cancel1_24)))).append ((((cancel1_25).append (cancel1_26)).append ((cancel1_27).append (cancel1_28))).append (((cancel1_29).append (cancel1_30)).append ((cancel1_31).append ((cancel1_32).append (cancel1_33))))))).append ((((((cancel1_34).append (cancel1_35)).append ((cancel1_36).append (cancel1_37))).append (((cancel1_38).append (cancel1_39)).append ((cancel1_40).append (cancel1_41)))).append ((((cancel1_42).append (cancel1_43)).append ((cancel1_44).append (cancel1_45))).append (((cancel1_46).append (cancel1_47)).append ((cancel1_48).append ((cancel1_49).append (cancel1_50)))))).append (((((cancel1_51).append (cancel1_52)).append ((cancel1_53).append (cancel1_54))).append (((cancel1_55).append (cancel1_56)).append ((cancel1_57).append (cancel1_58)))).append ((((cancel1_59).append (cancel1_60)).append ((cancel1_61).append (cancel1_62))).append (((cancel1_63).append (cancel1_64)).append ((cancel1_65).append ((cancel1_66).append (cancel1_67)))))))).append (((((((cancel1_68).append (cancel1_69)).append ((cancel1_70).append (cancel1_71))).append (((cancel1_72).append (cancel1_73)).append ((cancel1_74).append (cancel1_75)))).append ((((cancel1_76).append (cancel1_77)).append ((cancel1_78).append (cancel1_79))).append (((cancel1_80).append (cancel1_81)).append ((cancel1_82).append ((cancel1_83).append (cancel1_84)))))).append (((((cancel1_85).append (cancel1_86)).append ((cancel1_87).append (cancel1_88))).append (((cancel1_89).append (cancel1_90)).append ((cancel1_91).append (cancel1_92)))).append ((((cancel1_93).append (cancel1_94)).append ((cancel1_95).append (cancel1_96))).append (((cancel1_97).append (cancel1_98)).append ((cancel1_99).append ((cancel1_100).append (cancel1_101))))))).append ((((((cancel1_102).append (cancel1_103)).append ((cancel1_104).append (cancel1_105))).append (((cancel1_106).append (cancel1_107)).append ((cancel1_108).append (cancel1_109)))).append ((((cancel1_110).append (cancel1_111)).append ((cancel1_112).append (cancel1_113))).append (((cancel1_114).append (cancel1_115)).append ((cancel1_116).append ((cancel1_117).append (cancel1_118)))))).append (((((cancel1_119).append (cancel1_120)).append ((cancel1_121).append (cancel1_122))).append (((cancel1_123).append (cancel1_124)).append ((cancel1_125).append (cancel1_126)))).append ((((cancel1_127).append (cancel1_128)).append ((cancel1_129).append (cancel1_130))).append (((cancel1_131).append (cancel1_132)).append ((cancel1_133).append ((cancel1_134).append (cancel1_135))))))))
end Quantum.Circuit.Harness
