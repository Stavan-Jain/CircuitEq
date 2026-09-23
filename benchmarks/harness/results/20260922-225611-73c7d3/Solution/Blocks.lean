import Solution.Data
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Quantum.Circuit.Harness
open Instr

theorem motifs_checked (t : Fin 192) (ps : List (Fin 192 × Fin 192))
 (h : ps.all (fun p => decide (p.1 ≠ p.2 ∧ p.1 ≠ t ∧ p.2 ≠ t)) = true) :
 (ps.flatMap fun p => rawMotif p.1 p.2 t) ≡ᵤ
 (ps.flatMap fun p => diagMotif p.1 p.2 t) :=
 motifs_sound t ps (by
  intro p hp
  exact of_decide_eq_true ((List.all_eq_true.mp h) p hp))


theorem raw_sound0 : raw0 ≡ᵤ diag0 := motifs_checked 128 ps0 (by decide +kernel)

theorem phase_sound0 : res0 ++ diag0 ≡ᵤ opt0 ++ res1 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step0 : res0 ++ (H 128 :: diag0) ≡ᵤ (H 128 :: opt0) ++ res1 :=
 with_head _ _ _ _ 128 phase_sound0 (by decide +kernel)

theorem raw_sound1 : raw1 ≡ᵤ diag1 := motifs_checked 129 ps1 (by decide +kernel)

theorem phase_sound1 : res1 ++ diag1 ≡ᵤ opt1 ++ res2 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step1 : res1 ++ (H 129 :: diag1) ≡ᵤ (H 129 :: opt1) ++ res2 :=
 with_head _ _ _ _ 129 phase_sound1 (by decide +kernel)

theorem raw_sound2 : raw2 ≡ᵤ diag2 := motifs_checked 130 ps2 (by decide +kernel)

theorem phase_sound2 : res2 ++ diag2 ≡ᵤ opt2 ++ res3 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step2 : res2 ++ (H 130 :: diag2) ≡ᵤ (H 130 :: opt2) ++ res3 :=
 with_head _ _ _ _ 130 phase_sound2 (by decide +kernel)

theorem raw_sound3 : raw3 ≡ᵤ diag3 := motifs_checked 131 ps3 (by decide +kernel)

theorem phase_sound3 : res3 ++ diag3 ≡ᵤ opt3 ++ res4 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step3 : res3 ++ (H 131 :: diag3) ≡ᵤ (H 131 :: opt3) ++ res4 :=
 with_head _ _ _ _ 131 phase_sound3 (by decide +kernel)

theorem raw_sound4 : raw4 ≡ᵤ diag4 := motifs_checked 132 ps4 (by decide +kernel)

theorem phase_sound4 : res4 ++ diag4 ≡ᵤ opt4 ++ res5 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step4 : res4 ++ (H 132 :: diag4) ≡ᵤ (H 132 :: opt4) ++ res5 :=
 with_head _ _ _ _ 132 phase_sound4 (by decide +kernel)

theorem raw_sound5 : raw5 ≡ᵤ diag5 := motifs_checked 133 ps5 (by decide +kernel)

theorem phase_sound5 : res5 ++ diag5 ≡ᵤ opt5 ++ res6 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step5 : res5 ++ (H 133 :: diag5) ≡ᵤ (H 133 :: opt5) ++ res6 :=
 with_head _ _ _ _ 133 phase_sound5 (by decide +kernel)

theorem raw_sound6 : raw6 ≡ᵤ diag6 := motifs_checked 134 ps6 (by decide +kernel)

theorem phase_sound6 : res6 ++ diag6 ≡ᵤ opt6 ++ res7 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step6 : res6 ++ (H 134 :: diag6) ≡ᵤ (H 134 :: opt6) ++ res7 :=
 with_head _ _ _ _ 134 phase_sound6 (by decide +kernel)

theorem raw_sound7 : raw7 ≡ᵤ diag7 := motifs_checked 135 ps7 (by decide +kernel)

theorem phase_sound7 : res7 ++ diag7 ≡ᵤ opt7 ++ res8 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step7 : res7 ++ (H 135 :: diag7) ≡ᵤ (H 135 :: opt7) ++ res8 :=
 with_head _ _ _ _ 135 phase_sound7 (by decide +kernel)

theorem raw_sound8 : raw8 ≡ᵤ diag8 := motifs_checked 136 ps8 (by decide +kernel)

theorem phase_sound8 : res8 ++ diag8 ≡ᵤ opt8 ++ res9 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step8 : res8 ++ (H 136 :: diag8) ≡ᵤ (H 136 :: opt8) ++ res9 :=
 with_head _ _ _ _ 136 phase_sound8 (by decide +kernel)

theorem raw_sound9 : raw9 ≡ᵤ diag9 := motifs_checked 137 ps9 (by decide +kernel)

theorem phase_sound9 : res9 ++ diag9 ≡ᵤ opt9 ++ res10 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step9 : res9 ++ (H 137 :: diag9) ≡ᵤ (H 137 :: opt9) ++ res10 :=
 with_head _ _ _ _ 137 phase_sound9 (by decide +kernel)

theorem raw_sound10 : raw10 ≡ᵤ diag10 := motifs_checked 138 ps10 (by decide +kernel)

theorem phase_sound10 : res10 ++ diag10 ≡ᵤ opt10 ++ res11 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step10 : res10 ++ (H 138 :: diag10) ≡ᵤ (H 138 :: opt10) ++ res11 :=
 with_head _ _ _ _ 138 phase_sound10 (by decide +kernel)

theorem raw_sound11 : raw11 ≡ᵤ diag11 := motifs_checked 139 ps11 (by decide +kernel)

theorem phase_sound11 : res11 ++ diag11 ≡ᵤ opt11 ++ res12 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step11 : res11 ++ (H 139 :: diag11) ≡ᵤ (H 139 :: opt11) ++ res12 :=
 with_head _ _ _ _ 139 phase_sound11 (by decide +kernel)

theorem raw_sound12 : raw12 ≡ᵤ diag12 := motifs_checked 140 ps12 (by decide +kernel)

theorem phase_sound12 : res12 ++ diag12 ≡ᵤ opt12 ++ res13 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step12 : res12 ++ (H 140 :: diag12) ≡ᵤ (H 140 :: opt12) ++ res13 :=
 with_head _ _ _ _ 140 phase_sound12 (by decide +kernel)

theorem raw_sound13 : raw13 ≡ᵤ diag13 := motifs_checked 141 ps13 (by decide +kernel)

theorem phase_sound13 : res13 ++ diag13 ≡ᵤ opt13 ++ res14 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step13 : res13 ++ (H 141 :: diag13) ≡ᵤ (H 141 :: opt13) ++ res14 :=
 with_head _ _ _ _ 141 phase_sound13 (by decide +kernel)

theorem raw_sound14 : raw14 ≡ᵤ diag14 := motifs_checked 142 ps14 (by decide +kernel)

theorem phase_sound14 : res14 ++ diag14 ≡ᵤ opt14 ++ res15 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step14 : res14 ++ (H 142 :: diag14) ≡ᵤ (H 142 :: opt14) ++ res15 :=
 with_head _ _ _ _ 142 phase_sound14 (by decide +kernel)

theorem raw_sound15 : raw15 ≡ᵤ diag15 := motifs_checked 143 ps15 (by decide +kernel)

theorem phase_sound15 : res15 ++ diag15 ≡ᵤ opt15 ++ res16 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step15 : res15 ++ (H 143 :: diag15) ≡ᵤ (H 143 :: opt15) ++ res16 :=
 with_head _ _ _ _ 143 phase_sound15 (by decide +kernel)

theorem raw_sound16 : raw16 ≡ᵤ diag16 := motifs_checked 144 ps16 (by decide +kernel)

theorem phase_sound16 : res16 ++ diag16 ≡ᵤ opt16 ++ res17 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step16 : res16 ++ (H 144 :: diag16) ≡ᵤ (H 144 :: opt16) ++ res17 :=
 with_head _ _ _ _ 144 phase_sound16 (by decide +kernel)

theorem raw_sound17 : raw17 ≡ᵤ diag17 := motifs_checked 145 ps17 (by decide +kernel)

theorem phase_sound17 : res17 ++ diag17 ≡ᵤ opt17 ++ res18 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step17 : res17 ++ (H 145 :: diag17) ≡ᵤ (H 145 :: opt17) ++ res18 :=
 with_head _ _ _ _ 145 phase_sound17 (by decide +kernel)

theorem raw_sound18 : raw18 ≡ᵤ diag18 := motifs_checked 146 ps18 (by decide +kernel)

theorem phase_sound18 : res18 ++ diag18 ≡ᵤ opt18 ++ res19 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step18 : res18 ++ (H 146 :: diag18) ≡ᵤ (H 146 :: opt18) ++ res19 :=
 with_head _ _ _ _ 146 phase_sound18 (by decide +kernel)

theorem raw_sound19 : raw19 ≡ᵤ diag19 := motifs_checked 147 ps19 (by decide +kernel)

theorem phase_sound19 : res19 ++ diag19 ≡ᵤ opt19 ++ res20 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step19 : res19 ++ (H 147 :: diag19) ≡ᵤ (H 147 :: opt19) ++ res20 :=
 with_head _ _ _ _ 147 phase_sound19 (by decide +kernel)

theorem raw_sound20 : raw20 ≡ᵤ diag20 := motifs_checked 148 ps20 (by decide +kernel)

theorem phase_sound20 : res20 ++ diag20 ≡ᵤ opt20 ++ res21 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step20 : res20 ++ (H 148 :: diag20) ≡ᵤ (H 148 :: opt20) ++ res21 :=
 with_head _ _ _ _ 148 phase_sound20 (by decide +kernel)

theorem raw_sound21 : raw21 ≡ᵤ diag21 := motifs_checked 149 ps21 (by decide +kernel)

theorem phase_sound21 : res21 ++ diag21 ≡ᵤ opt21 ++ res22 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step21 : res21 ++ (H 149 :: diag21) ≡ᵤ (H 149 :: opt21) ++ res22 :=
 with_head _ _ _ _ 149 phase_sound21 (by decide +kernel)

theorem raw_sound22 : raw22 ≡ᵤ diag22 := motifs_checked 150 ps22 (by decide +kernel)

theorem phase_sound22 : res22 ++ diag22 ≡ᵤ opt22 ++ res23 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step22 : res22 ++ (H 150 :: diag22) ≡ᵤ (H 150 :: opt22) ++ res23 :=
 with_head _ _ _ _ 150 phase_sound22 (by decide +kernel)

theorem raw_sound23 : raw23 ≡ᵤ diag23 := motifs_checked 151 ps23 (by decide +kernel)

theorem phase_sound23 : res23 ++ diag23 ≡ᵤ opt23 ++ res24 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step23 : res23 ++ (H 151 :: diag23) ≡ᵤ (H 151 :: opt23) ++ res24 :=
 with_head _ _ _ _ 151 phase_sound23 (by decide +kernel)

theorem raw_sound24 : raw24 ≡ᵤ diag24 := motifs_checked 152 ps24 (by decide +kernel)

theorem phase_sound24 : res24 ++ diag24 ≡ᵤ opt24 ++ res25 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step24 : res24 ++ (H 152 :: diag24) ≡ᵤ (H 152 :: opt24) ++ res25 :=
 with_head _ _ _ _ 152 phase_sound24 (by decide +kernel)

theorem raw_sound25 : raw25 ≡ᵤ diag25 := motifs_checked 153 ps25 (by decide +kernel)

theorem phase_sound25 : res25 ++ diag25 ≡ᵤ opt25 ++ res26 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step25 : res25 ++ (H 153 :: diag25) ≡ᵤ (H 153 :: opt25) ++ res26 :=
 with_head _ _ _ _ 153 phase_sound25 (by decide +kernel)

theorem raw_sound26 : raw26 ≡ᵤ diag26 := motifs_checked 154 ps26 (by decide +kernel)

theorem phase_sound26 : res26 ++ diag26 ≡ᵤ opt26 ++ res27 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step26 : res26 ++ (H 154 :: diag26) ≡ᵤ (H 154 :: opt26) ++ res27 :=
 with_head _ _ _ _ 154 phase_sound26 (by decide +kernel)

theorem raw_sound27 : raw27 ≡ᵤ diag27 := motifs_checked 155 ps27 (by decide +kernel)

theorem phase_sound27 : res27 ++ diag27 ≡ᵤ opt27 ++ res28 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step27 : res27 ++ (H 155 :: diag27) ≡ᵤ (H 155 :: opt27) ++ res28 :=
 with_head _ _ _ _ 155 phase_sound27 (by decide +kernel)

theorem raw_sound28 : raw28 ≡ᵤ diag28 := motifs_checked 156 ps28 (by decide +kernel)

theorem phase_sound28 : res28 ++ diag28 ≡ᵤ opt28 ++ res29 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step28 : res28 ++ (H 156 :: diag28) ≡ᵤ (H 156 :: opt28) ++ res29 :=
 with_head _ _ _ _ 156 phase_sound28 (by decide +kernel)

theorem raw_sound29 : raw29 ≡ᵤ diag29 := motifs_checked 157 ps29 (by decide +kernel)

theorem phase_sound29 : res29 ++ diag29 ≡ᵤ opt29 ++ res30 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step29 : res29 ++ (H 157 :: diag29) ≡ᵤ (H 157 :: opt29) ++ res30 :=
 with_head _ _ _ _ 157 phase_sound29 (by decide +kernel)

theorem raw_sound30 : raw30 ≡ᵤ diag30 := motifs_checked 158 ps30 (by decide +kernel)

theorem phase_sound30 : res30 ++ diag30 ≡ᵤ opt30 ++ res31 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step30 : res30 ++ (H 158 :: diag30) ≡ᵤ (H 158 :: opt30) ++ res31 :=
 with_head _ _ _ _ 158 phase_sound30 (by decide +kernel)

theorem raw_sound31 : raw31 ≡ᵤ diag31 := motifs_checked 159 ps31 (by decide +kernel)

theorem phase_sound31 : res31 ++ diag31 ≡ᵤ opt31 ++ res32 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step31 : res31 ++ (H 159 :: diag31) ≡ᵤ (H 159 :: opt31) ++ res32 :=
 with_head _ _ _ _ 159 phase_sound31 (by decide +kernel)

theorem raw_sound32 : raw32 ≡ᵤ diag32 := motifs_checked 160 ps32 (by decide +kernel)

theorem phase_sound32 : res32 ++ diag32 ≡ᵤ opt32 ++ res33 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step32 : res32 ++ (H 160 :: diag32) ≡ᵤ (H 160 :: opt32) ++ res33 :=
 with_head _ _ _ _ 160 phase_sound32 (by decide +kernel)

theorem raw_sound33 : raw33 ≡ᵤ diag33 := motifs_checked 161 ps33 (by decide +kernel)

theorem phase_sound33 : res33 ++ diag33 ≡ᵤ opt33 ++ res34 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step33 : res33 ++ (H 161 :: diag33) ≡ᵤ (H 161 :: opt33) ++ res34 :=
 with_head _ _ _ _ 161 phase_sound33 (by decide +kernel)

theorem raw_sound34 : raw34 ≡ᵤ diag34 := motifs_checked 162 ps34 (by decide +kernel)

theorem phase_sound34 : res34 ++ diag34 ≡ᵤ opt34 ++ res35 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step34 : res34 ++ (H 162 :: diag34) ≡ᵤ (H 162 :: opt34) ++ res35 :=
 with_head _ _ _ _ 162 phase_sound34 (by decide +kernel)

theorem raw_sound35 : raw35 ≡ᵤ diag35 := motifs_checked 163 ps35 (by decide +kernel)

theorem phase_sound35 : res35 ++ diag35 ≡ᵤ opt35 ++ res36 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step35 : res35 ++ (H 163 :: diag35) ≡ᵤ (H 163 :: opt35) ++ res36 :=
 with_head _ _ _ _ 163 phase_sound35 (by decide +kernel)

theorem raw_sound36 : raw36 ≡ᵤ diag36 := motifs_checked 164 ps36 (by decide +kernel)

theorem phase_sound36 : res36 ++ diag36 ≡ᵤ opt36 ++ res37 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step36 : res36 ++ (H 164 :: diag36) ≡ᵤ (H 164 :: opt36) ++ res37 :=
 with_head _ _ _ _ 164 phase_sound36 (by decide +kernel)

theorem raw_sound37 : raw37 ≡ᵤ diag37 := motifs_checked 165 ps37 (by decide +kernel)

theorem phase_sound37 : res37 ++ diag37 ≡ᵤ opt37 ++ res38 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step37 : res37 ++ (H 165 :: diag37) ≡ᵤ (H 165 :: opt37) ++ res38 :=
 with_head _ _ _ _ 165 phase_sound37 (by decide +kernel)

theorem raw_sound38 : raw38 ≡ᵤ diag38 := motifs_checked 166 ps38 (by decide +kernel)

theorem phase_sound38 : res38 ++ diag38 ≡ᵤ opt38 ++ res39 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step38 : res38 ++ (H 166 :: diag38) ≡ᵤ (H 166 :: opt38) ++ res39 :=
 with_head _ _ _ _ 166 phase_sound38 (by decide +kernel)

theorem raw_sound39 : raw39 ≡ᵤ diag39 := motifs_checked 167 ps39 (by decide +kernel)

theorem phase_sound39 : res39 ++ diag39 ≡ᵤ opt39 ++ res40 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step39 : res39 ++ (H 167 :: diag39) ≡ᵤ (H 167 :: opt39) ++ res40 :=
 with_head _ _ _ _ 167 phase_sound39 (by decide +kernel)

theorem raw_sound40 : raw40 ≡ᵤ diag40 := motifs_checked 168 ps40 (by decide +kernel)

theorem phase_sound40 : res40 ++ diag40 ≡ᵤ opt40 ++ res41 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step40 : res40 ++ (H 168 :: diag40) ≡ᵤ (H 168 :: opt40) ++ res41 :=
 with_head _ _ _ _ 168 phase_sound40 (by decide +kernel)

theorem raw_sound41 : raw41 ≡ᵤ diag41 := motifs_checked 169 ps41 (by decide +kernel)

theorem phase_sound41 : res41 ++ diag41 ≡ᵤ opt41 ++ res42 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step41 : res41 ++ (H 169 :: diag41) ≡ᵤ (H 169 :: opt41) ++ res42 :=
 with_head _ _ _ _ 169 phase_sound41 (by decide +kernel)

theorem raw_sound42 : raw42 ≡ᵤ diag42 := motifs_checked 170 ps42 (by decide +kernel)

theorem phase_sound42 : res42 ++ diag42 ≡ᵤ opt42 ++ res43 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step42 : res42 ++ (H 170 :: diag42) ≡ᵤ (H 170 :: opt42) ++ res43 :=
 with_head _ _ _ _ 170 phase_sound42 (by decide +kernel)

theorem raw_sound43 : raw43 ≡ᵤ diag43 := motifs_checked 171 ps43 (by decide +kernel)

theorem phase_sound43 : res43 ++ diag43 ≡ᵤ opt43 ++ res44 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step43 : res43 ++ (H 171 :: diag43) ≡ᵤ (H 171 :: opt43) ++ res44 :=
 with_head _ _ _ _ 171 phase_sound43 (by decide +kernel)

theorem raw_sound44 : raw44 ≡ᵤ diag44 := motifs_checked 172 ps44 (by decide +kernel)

theorem phase_sound44 : res44 ++ diag44 ≡ᵤ opt44 ++ res45 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step44 : res44 ++ (H 172 :: diag44) ≡ᵤ (H 172 :: opt44) ++ res45 :=
 with_head _ _ _ _ 172 phase_sound44 (by decide +kernel)

theorem raw_sound45 : raw45 ≡ᵤ diag45 := motifs_checked 173 ps45 (by decide +kernel)

theorem phase_sound45 : res45 ++ diag45 ≡ᵤ opt45 ++ res46 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step45 : res45 ++ (H 173 :: diag45) ≡ᵤ (H 173 :: opt45) ++ res46 :=
 with_head _ _ _ _ 173 phase_sound45 (by decide +kernel)

theorem raw_sound46 : raw46 ≡ᵤ diag46 := motifs_checked 174 ps46 (by decide +kernel)

theorem phase_sound46 : res46 ++ diag46 ≡ᵤ opt46 ++ res47 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step46 : res46 ++ (H 174 :: diag46) ≡ᵤ (H 174 :: opt46) ++ res47 :=
 with_head _ _ _ _ 174 phase_sound46 (by decide +kernel)

theorem raw_sound47 : raw47 ≡ᵤ diag47 := motifs_checked 175 ps47 (by decide +kernel)

theorem phase_sound47 : res47 ++ diag47 ≡ᵤ opt47 ++ res48 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step47 : res47 ++ (H 175 :: diag47) ≡ᵤ (H 175 :: opt47) ++ res48 :=
 with_head _ _ _ _ 175 phase_sound47 (by decide +kernel)

theorem raw_sound48 : raw48 ≡ᵤ diag48 := motifs_checked 176 ps48 (by decide +kernel)

theorem phase_sound48 : res48 ++ diag48 ≡ᵤ opt48 ++ res49 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step48 : res48 ++ (H 176 :: diag48) ≡ᵤ (H 176 :: opt48) ++ res49 :=
 with_head _ _ _ _ 176 phase_sound48 (by decide +kernel)

theorem raw_sound49 : raw49 ≡ᵤ diag49 := motifs_checked 177 ps49 (by decide +kernel)

theorem phase_sound49 : res49 ++ diag49 ≡ᵤ opt49 ++ res50 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step49 : res49 ++ (H 177 :: diag49) ≡ᵤ (H 177 :: opt49) ++ res50 :=
 with_head _ _ _ _ 177 phase_sound49 (by decide +kernel)

theorem raw_sound50 : raw50 ≡ᵤ diag50 := motifs_checked 178 ps50 (by decide +kernel)

theorem phase_sound50 : res50 ++ diag50 ≡ᵤ opt50 ++ res51 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step50 : res50 ++ (H 178 :: diag50) ≡ᵤ (H 178 :: opt50) ++ res51 :=
 with_head _ _ _ _ 178 phase_sound50 (by decide +kernel)

theorem raw_sound51 : raw51 ≡ᵤ diag51 := motifs_checked 179 ps51 (by decide +kernel)

theorem phase_sound51 : res51 ++ diag51 ≡ᵤ opt51 ++ res52 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step51 : res51 ++ (H 179 :: diag51) ≡ᵤ (H 179 :: opt51) ++ res52 :=
 with_head _ _ _ _ 179 phase_sound51 (by decide +kernel)

theorem raw_sound52 : raw52 ≡ᵤ diag52 := motifs_checked 180 ps52 (by decide +kernel)

theorem phase_sound52 : res52 ++ diag52 ≡ᵤ opt52 ++ res53 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step52 : res52 ++ (H 180 :: diag52) ≡ᵤ (H 180 :: opt52) ++ res53 :=
 with_head _ _ _ _ 180 phase_sound52 (by decide +kernel)

theorem raw_sound53 : raw53 ≡ᵤ diag53 := motifs_checked 181 ps53 (by decide +kernel)

theorem phase_sound53 : res53 ++ diag53 ≡ᵤ opt53 ++ res54 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step53 : res53 ++ (H 181 :: diag53) ≡ᵤ (H 181 :: opt53) ++ res54 :=
 with_head _ _ _ _ 181 phase_sound53 (by decide +kernel)

theorem raw_sound54 : raw54 ≡ᵤ diag54 := motifs_checked 182 ps54 (by decide +kernel)

theorem phase_sound54 : res54 ++ diag54 ≡ᵤ opt54 ++ res55 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step54 : res54 ++ (H 182 :: diag54) ≡ᵤ (H 182 :: opt54) ++ res55 :=
 with_head _ _ _ _ 182 phase_sound54 (by decide +kernel)

theorem raw_sound55 : raw55 ≡ᵤ diag55 := motifs_checked 183 ps55 (by decide +kernel)

theorem phase_sound55 : res55 ++ diag55 ≡ᵤ opt55 ++ res56 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step55 : res55 ++ (H 183 :: diag55) ≡ᵤ (H 183 :: opt55) ++ res56 :=
 with_head _ _ _ _ 183 phase_sound55 (by decide +kernel)

theorem raw_sound56 : raw56 ≡ᵤ diag56 := motifs_checked 184 ps56 (by decide +kernel)

theorem phase_sound56 : res56 ++ diag56 ≡ᵤ opt56 ++ res57 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step56 : res56 ++ (H 184 :: diag56) ≡ᵤ (H 184 :: opt56) ++ res57 :=
 with_head _ _ _ _ 184 phase_sound56 (by decide +kernel)

theorem raw_sound57 : raw57 ≡ᵤ diag57 := motifs_checked 185 ps57 (by decide +kernel)

theorem phase_sound57 : res57 ++ diag57 ≡ᵤ opt57 ++ res58 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step57 : res57 ++ (H 185 :: diag57) ≡ᵤ (H 185 :: opt57) ++ res58 :=
 with_head _ _ _ _ 185 phase_sound57 (by decide +kernel)

theorem raw_sound58 : raw58 ≡ᵤ diag58 := motifs_checked 186 ps58 (by decide +kernel)

theorem phase_sound58 : res58 ++ diag58 ≡ᵤ opt58 ++ res59 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step58 : res58 ++ (H 186 :: diag58) ≡ᵤ (H 186 :: opt58) ++ res59 :=
 with_head _ _ _ _ 186 phase_sound58 (by decide +kernel)

theorem raw_sound59 : raw59 ≡ᵤ diag59 := motifs_checked 187 ps59 (by decide +kernel)

theorem phase_sound59 : res59 ++ diag59 ≡ᵤ opt59 ++ res60 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step59 : res59 ++ (H 187 :: diag59) ≡ᵤ (H 187 :: opt59) ++ res60 :=
 with_head _ _ _ _ 187 phase_sound59 (by decide +kernel)

theorem raw_sound60 : raw60 ≡ᵤ diag60 := motifs_checked 188 ps60 (by decide +kernel)

theorem phase_sound60 : res60 ++ diag60 ≡ᵤ opt60 ++ res61 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step60 : res60 ++ (H 188 :: diag60) ≡ᵤ (H 188 :: opt60) ++ res61 :=
 with_head _ _ _ _ 188 phase_sound60 (by decide +kernel)

theorem raw_sound61 : raw61 ≡ᵤ diag61 := motifs_checked 189 ps61 (by decide +kernel)

theorem phase_sound61 : res61 ++ diag61 ≡ᵤ opt61 ++ res62 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step61 : res61 ++ (H 189 :: diag61) ≡ᵤ (H 189 :: opt61) ++ res62 :=
 with_head _ _ _ _ 189 phase_sound61 (by decide +kernel)

theorem raw_sound62 : raw62 ≡ᵤ diag62 := motifs_checked 190 ps62 (by decide +kernel)

theorem phase_sound62 : res62 ++ diag62 ≡ᵤ opt62 ++ res63 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step62 : res62 ++ (H 190 :: diag62) ≡ᵤ (H 190 :: opt62) ++ res63 :=
 with_head _ _ _ _ 190 phase_sound62 (by decide +kernel)

theorem raw_sound63 : raw63 ≡ᵤ diag63 := motifs_checked 191 ps63 (by decide +kernel)

theorem phase_sound63 : res63 ++ diag63 ≡ᵤ opt63 ++ res64 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step63 : res63 ++ (H 191 :: diag63) ≡ᵤ (H 191 :: opt63) ++ res64 :=
 with_head _ _ _ _ 191 phase_sound63 (by decide +kernel)

theorem raw_sound64 : raw64 ≡ᵤ diag64 := motifs_checked 190 ps64 (by decide +kernel)

theorem phase_sound64 : res64 ++ diag64 ≡ᵤ opt64 ++ res65 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step64 : res64 ++ (H 190 :: diag64) ≡ᵤ (H 190 :: opt64) ++ res65 :=
 with_head _ _ _ _ 190 phase_sound64 (by decide +kernel)

theorem raw_sound65 : raw65 ≡ᵤ diag65 := motifs_checked 189 ps65 (by decide +kernel)

theorem phase_sound65 : res65 ++ diag65 ≡ᵤ opt65 ++ res66 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step65 : res65 ++ (H 189 :: diag65) ≡ᵤ (H 189 :: opt65) ++ res66 :=
 with_head _ _ _ _ 189 phase_sound65 (by decide +kernel)

theorem raw_sound66 : raw66 ≡ᵤ diag66 := motifs_checked 188 ps66 (by decide +kernel)

theorem phase_sound66 : res66 ++ diag66 ≡ᵤ opt66 ++ res67 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step66 : res66 ++ (H 188 :: diag66) ≡ᵤ (H 188 :: opt66) ++ res67 :=
 with_head _ _ _ _ 188 phase_sound66 (by decide +kernel)

theorem raw_sound67 : raw67 ≡ᵤ diag67 := motifs_checked 187 ps67 (by decide +kernel)

theorem phase_sound67 : res67 ++ diag67 ≡ᵤ opt67 ++ res68 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step67 : res67 ++ (H 187 :: diag67) ≡ᵤ (H 187 :: opt67) ++ res68 :=
 with_head _ _ _ _ 187 phase_sound67 (by decide +kernel)

theorem raw_sound68 : raw68 ≡ᵤ diag68 := motifs_checked 186 ps68 (by decide +kernel)

theorem phase_sound68 : res68 ++ diag68 ≡ᵤ opt68 ++ res69 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step68 : res68 ++ (H 186 :: diag68) ≡ᵤ (H 186 :: opt68) ++ res69 :=
 with_head _ _ _ _ 186 phase_sound68 (by decide +kernel)

theorem raw_sound69 : raw69 ≡ᵤ diag69 := motifs_checked 185 ps69 (by decide +kernel)

theorem phase_sound69 : res69 ++ diag69 ≡ᵤ opt69 ++ res70 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step69 : res69 ++ (H 185 :: diag69) ≡ᵤ (H 185 :: opt69) ++ res70 :=
 with_head _ _ _ _ 185 phase_sound69 (by decide +kernel)

theorem raw_sound70 : raw70 ≡ᵤ diag70 := motifs_checked 184 ps70 (by decide +kernel)

theorem phase_sound70 : res70 ++ diag70 ≡ᵤ opt70 ++ res71 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step70 : res70 ++ (H 184 :: diag70) ≡ᵤ (H 184 :: opt70) ++ res71 :=
 with_head _ _ _ _ 184 phase_sound70 (by decide +kernel)

theorem raw_sound71 : raw71 ≡ᵤ diag71 := motifs_checked 183 ps71 (by decide +kernel)

theorem phase_sound71 : res71 ++ diag71 ≡ᵤ opt71 ++ res72 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step71 : res71 ++ (H 183 :: diag71) ≡ᵤ (H 183 :: opt71) ++ res72 :=
 with_head _ _ _ _ 183 phase_sound71 (by decide +kernel)

theorem raw_sound72 : raw72 ≡ᵤ diag72 := motifs_checked 182 ps72 (by decide +kernel)

theorem phase_sound72 : res72 ++ diag72 ≡ᵤ opt72 ++ res73 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step72 : res72 ++ (H 182 :: diag72) ≡ᵤ (H 182 :: opt72) ++ res73 :=
 with_head _ _ _ _ 182 phase_sound72 (by decide +kernel)

theorem raw_sound73 : raw73 ≡ᵤ diag73 := motifs_checked 181 ps73 (by decide +kernel)

theorem phase_sound73 : res73 ++ diag73 ≡ᵤ opt73 ++ res74 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step73 : res73 ++ (H 181 :: diag73) ≡ᵤ (H 181 :: opt73) ++ res74 :=
 with_head _ _ _ _ 181 phase_sound73 (by decide +kernel)

theorem raw_sound74 : raw74 ≡ᵤ diag74 := motifs_checked 180 ps74 (by decide +kernel)

theorem phase_sound74 : res74 ++ diag74 ≡ᵤ opt74 ++ res75 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step74 : res74 ++ (H 180 :: diag74) ≡ᵤ (H 180 :: opt74) ++ res75 :=
 with_head _ _ _ _ 180 phase_sound74 (by decide +kernel)

theorem raw_sound75 : raw75 ≡ᵤ diag75 := motifs_checked 179 ps75 (by decide +kernel)

theorem phase_sound75 : res75 ++ diag75 ≡ᵤ opt75 ++ res76 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step75 : res75 ++ (H 179 :: diag75) ≡ᵤ (H 179 :: opt75) ++ res76 :=
 with_head _ _ _ _ 179 phase_sound75 (by decide +kernel)

theorem raw_sound76 : raw76 ≡ᵤ diag76 := motifs_checked 178 ps76 (by decide +kernel)

theorem phase_sound76 : res76 ++ diag76 ≡ᵤ opt76 ++ res77 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step76 : res76 ++ (H 178 :: diag76) ≡ᵤ (H 178 :: opt76) ++ res77 :=
 with_head _ _ _ _ 178 phase_sound76 (by decide +kernel)

theorem raw_sound77 : raw77 ≡ᵤ diag77 := motifs_checked 177 ps77 (by decide +kernel)

theorem phase_sound77 : res77 ++ diag77 ≡ᵤ opt77 ++ res78 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step77 : res77 ++ (H 177 :: diag77) ≡ᵤ (H 177 :: opt77) ++ res78 :=
 with_head _ _ _ _ 177 phase_sound77 (by decide +kernel)

theorem raw_sound78 : raw78 ≡ᵤ diag78 := motifs_checked 176 ps78 (by decide +kernel)

theorem phase_sound78 : res78 ++ diag78 ≡ᵤ opt78 ++ res79 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step78 : res78 ++ (H 176 :: diag78) ≡ᵤ (H 176 :: opt78) ++ res79 :=
 with_head _ _ _ _ 176 phase_sound78 (by decide +kernel)

theorem raw_sound79 : raw79 ≡ᵤ diag79 := motifs_checked 175 ps79 (by decide +kernel)

theorem phase_sound79 : res79 ++ diag79 ≡ᵤ opt79 ++ res80 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step79 : res79 ++ (H 175 :: diag79) ≡ᵤ (H 175 :: opt79) ++ res80 :=
 with_head _ _ _ _ 175 phase_sound79 (by decide +kernel)

theorem raw_sound80 : raw80 ≡ᵤ diag80 := motifs_checked 174 ps80 (by decide +kernel)

theorem phase_sound80 : res80 ++ diag80 ≡ᵤ opt80 ++ res81 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step80 : res80 ++ (H 174 :: diag80) ≡ᵤ (H 174 :: opt80) ++ res81 :=
 with_head _ _ _ _ 174 phase_sound80 (by decide +kernel)

theorem raw_sound81 : raw81 ≡ᵤ diag81 := motifs_checked 173 ps81 (by decide +kernel)

theorem phase_sound81 : res81 ++ diag81 ≡ᵤ opt81 ++ res82 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step81 : res81 ++ (H 173 :: diag81) ≡ᵤ (H 173 :: opt81) ++ res82 :=
 with_head _ _ _ _ 173 phase_sound81 (by decide +kernel)

theorem raw_sound82 : raw82 ≡ᵤ diag82 := motifs_checked 172 ps82 (by decide +kernel)

theorem phase_sound82 : res82 ++ diag82 ≡ᵤ opt82 ++ res83 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step82 : res82 ++ (H 172 :: diag82) ≡ᵤ (H 172 :: opt82) ++ res83 :=
 with_head _ _ _ _ 172 phase_sound82 (by decide +kernel)

theorem raw_sound83 : raw83 ≡ᵤ diag83 := motifs_checked 171 ps83 (by decide +kernel)

theorem phase_sound83 : res83 ++ diag83 ≡ᵤ opt83 ++ res84 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step83 : res83 ++ (H 171 :: diag83) ≡ᵤ (H 171 :: opt83) ++ res84 :=
 with_head _ _ _ _ 171 phase_sound83 (by decide +kernel)

theorem raw_sound84 : raw84 ≡ᵤ diag84 := motifs_checked 170 ps84 (by decide +kernel)

theorem phase_sound84 : res84 ++ diag84 ≡ᵤ opt84 ++ res85 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step84 : res84 ++ (H 170 :: diag84) ≡ᵤ (H 170 :: opt84) ++ res85 :=
 with_head _ _ _ _ 170 phase_sound84 (by decide +kernel)

theorem raw_sound85 : raw85 ≡ᵤ diag85 := motifs_checked 169 ps85 (by decide +kernel)

theorem phase_sound85 : res85 ++ diag85 ≡ᵤ opt85 ++ res86 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step85 : res85 ++ (H 169 :: diag85) ≡ᵤ (H 169 :: opt85) ++ res86 :=
 with_head _ _ _ _ 169 phase_sound85 (by decide +kernel)

theorem raw_sound86 : raw86 ≡ᵤ diag86 := motifs_checked 168 ps86 (by decide +kernel)

theorem phase_sound86 : res86 ++ diag86 ≡ᵤ opt86 ++ res87 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step86 : res86 ++ (H 168 :: diag86) ≡ᵤ (H 168 :: opt86) ++ res87 :=
 with_head _ _ _ _ 168 phase_sound86 (by decide +kernel)

theorem raw_sound87 : raw87 ≡ᵤ diag87 := motifs_checked 167 ps87 (by decide +kernel)

theorem phase_sound87 : res87 ++ diag87 ≡ᵤ opt87 ++ res88 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step87 : res87 ++ (H 167 :: diag87) ≡ᵤ (H 167 :: opt87) ++ res88 :=
 with_head _ _ _ _ 167 phase_sound87 (by decide +kernel)

theorem raw_sound88 : raw88 ≡ᵤ diag88 := motifs_checked 166 ps88 (by decide +kernel)

theorem phase_sound88 : res88 ++ diag88 ≡ᵤ opt88 ++ res89 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step88 : res88 ++ (H 166 :: diag88) ≡ᵤ (H 166 :: opt88) ++ res89 :=
 with_head _ _ _ _ 166 phase_sound88 (by decide +kernel)

theorem raw_sound89 : raw89 ≡ᵤ diag89 := motifs_checked 165 ps89 (by decide +kernel)

theorem phase_sound89 : res89 ++ diag89 ≡ᵤ opt89 ++ res90 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step89 : res89 ++ (H 165 :: diag89) ≡ᵤ (H 165 :: opt89) ++ res90 :=
 with_head _ _ _ _ 165 phase_sound89 (by decide +kernel)

theorem raw_sound90 : raw90 ≡ᵤ diag90 := motifs_checked 164 ps90 (by decide +kernel)

theorem phase_sound90 : res90 ++ diag90 ≡ᵤ opt90 ++ res91 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step90 : res90 ++ (H 164 :: diag90) ≡ᵤ (H 164 :: opt90) ++ res91 :=
 with_head _ _ _ _ 164 phase_sound90 (by decide +kernel)

theorem raw_sound91 : raw91 ≡ᵤ diag91 := motifs_checked 163 ps91 (by decide +kernel)

theorem phase_sound91 : res91 ++ diag91 ≡ᵤ opt91 ++ res92 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step91 : res91 ++ (H 163 :: diag91) ≡ᵤ (H 163 :: opt91) ++ res92 :=
 with_head _ _ _ _ 163 phase_sound91 (by decide +kernel)

theorem raw_sound92 : raw92 ≡ᵤ diag92 := motifs_checked 162 ps92 (by decide +kernel)

theorem phase_sound92 : res92 ++ diag92 ≡ᵤ opt92 ++ res93 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step92 : res92 ++ (H 162 :: diag92) ≡ᵤ (H 162 :: opt92) ++ res93 :=
 with_head _ _ _ _ 162 phase_sound92 (by decide +kernel)

theorem raw_sound93 : raw93 ≡ᵤ diag93 := motifs_checked 161 ps93 (by decide +kernel)

theorem phase_sound93 : res93 ++ diag93 ≡ᵤ opt93 ++ res94 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step93 : res93 ++ (H 161 :: diag93) ≡ᵤ (H 161 :: opt93) ++ res94 :=
 with_head _ _ _ _ 161 phase_sound93 (by decide +kernel)

theorem raw_sound94 : raw94 ≡ᵤ diag94 := motifs_checked 160 ps94 (by decide +kernel)

theorem phase_sound94 : res94 ++ diag94 ≡ᵤ opt94 ++ res95 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step94 : res94 ++ (H 160 :: diag94) ≡ᵤ (H 160 :: opt94) ++ res95 :=
 with_head _ _ _ _ 160 phase_sound94 (by decide +kernel)

theorem raw_sound95 : raw95 ≡ᵤ diag95 := motifs_checked 159 ps95 (by decide +kernel)

theorem phase_sound95 : res95 ++ diag95 ≡ᵤ opt95 ++ res96 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step95 : res95 ++ (H 159 :: diag95) ≡ᵤ (H 159 :: opt95) ++ res96 :=
 with_head _ _ _ _ 159 phase_sound95 (by decide +kernel)

theorem raw_sound96 : raw96 ≡ᵤ diag96 := motifs_checked 158 ps96 (by decide +kernel)

theorem phase_sound96 : res96 ++ diag96 ≡ᵤ opt96 ++ res97 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step96 : res96 ++ (H 158 :: diag96) ≡ᵤ (H 158 :: opt96) ++ res97 :=
 with_head _ _ _ _ 158 phase_sound96 (by decide +kernel)

theorem raw_sound97 : raw97 ≡ᵤ diag97 := motifs_checked 157 ps97 (by decide +kernel)

theorem phase_sound97 : res97 ++ diag97 ≡ᵤ opt97 ++ res98 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step97 : res97 ++ (H 157 :: diag97) ≡ᵤ (H 157 :: opt97) ++ res98 :=
 with_head _ _ _ _ 157 phase_sound97 (by decide +kernel)

theorem raw_sound98 : raw98 ≡ᵤ diag98 := motifs_checked 156 ps98 (by decide +kernel)

theorem phase_sound98 : res98 ++ diag98 ≡ᵤ opt98 ++ res99 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step98 : res98 ++ (H 156 :: diag98) ≡ᵤ (H 156 :: opt98) ++ res99 :=
 with_head _ _ _ _ 156 phase_sound98 (by decide +kernel)

theorem raw_sound99 : raw99 ≡ᵤ diag99 := motifs_checked 155 ps99 (by decide +kernel)

theorem phase_sound99 : res99 ++ diag99 ≡ᵤ opt99 ++ res100 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step99 : res99 ++ (H 155 :: diag99) ≡ᵤ (H 155 :: opt99) ++ res100 :=
 with_head _ _ _ _ 155 phase_sound99 (by decide +kernel)

theorem raw_sound100 : raw100 ≡ᵤ diag100 := motifs_checked 154 ps100 (by decide +kernel)

theorem phase_sound100 : res100 ++ diag100 ≡ᵤ opt100 ++ res101 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step100 : res100 ++ (H 154 :: diag100) ≡ᵤ (H 154 :: opt100) ++ res101 :=
 with_head _ _ _ _ 154 phase_sound100 (by decide +kernel)

theorem raw_sound101 : raw101 ≡ᵤ diag101 := motifs_checked 153 ps101 (by decide +kernel)

theorem phase_sound101 : res101 ++ diag101 ≡ᵤ opt101 ++ res102 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step101 : res101 ++ (H 153 :: diag101) ≡ᵤ (H 153 :: opt101) ++ res102 :=
 with_head _ _ _ _ 153 phase_sound101 (by decide +kernel)

theorem raw_sound102 : raw102 ≡ᵤ diag102 := motifs_checked 152 ps102 (by decide +kernel)

theorem phase_sound102 : res102 ++ diag102 ≡ᵤ opt102 ++ res103 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step102 : res102 ++ (H 152 :: diag102) ≡ᵤ (H 152 :: opt102) ++ res103 :=
 with_head _ _ _ _ 152 phase_sound102 (by decide +kernel)

theorem raw_sound103 : raw103 ≡ᵤ diag103 := motifs_checked 151 ps103 (by decide +kernel)

theorem phase_sound103 : res103 ++ diag103 ≡ᵤ opt103 ++ res104 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step103 : res103 ++ (H 151 :: diag103) ≡ᵤ (H 151 :: opt103) ++ res104 :=
 with_head _ _ _ _ 151 phase_sound103 (by decide +kernel)

theorem raw_sound104 : raw104 ≡ᵤ diag104 := motifs_checked 150 ps104 (by decide +kernel)

theorem phase_sound104 : res104 ++ diag104 ≡ᵤ opt104 ++ res105 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step104 : res104 ++ (H 150 :: diag104) ≡ᵤ (H 150 :: opt104) ++ res105 :=
 with_head _ _ _ _ 150 phase_sound104 (by decide +kernel)

theorem raw_sound105 : raw105 ≡ᵤ diag105 := motifs_checked 149 ps105 (by decide +kernel)

theorem phase_sound105 : res105 ++ diag105 ≡ᵤ opt105 ++ res106 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step105 : res105 ++ (H 149 :: diag105) ≡ᵤ (H 149 :: opt105) ++ res106 :=
 with_head _ _ _ _ 149 phase_sound105 (by decide +kernel)

theorem raw_sound106 : raw106 ≡ᵤ diag106 := motifs_checked 148 ps106 (by decide +kernel)

theorem phase_sound106 : res106 ++ diag106 ≡ᵤ opt106 ++ res107 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step106 : res106 ++ (H 148 :: diag106) ≡ᵤ (H 148 :: opt106) ++ res107 :=
 with_head _ _ _ _ 148 phase_sound106 (by decide +kernel)

theorem raw_sound107 : raw107 ≡ᵤ diag107 := motifs_checked 147 ps107 (by decide +kernel)

theorem phase_sound107 : res107 ++ diag107 ≡ᵤ opt107 ++ res108 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step107 : res107 ++ (H 147 :: diag107) ≡ᵤ (H 147 :: opt107) ++ res108 :=
 with_head _ _ _ _ 147 phase_sound107 (by decide +kernel)

theorem raw_sound108 : raw108 ≡ᵤ diag108 := motifs_checked 146 ps108 (by decide +kernel)

theorem phase_sound108 : res108 ++ diag108 ≡ᵤ opt108 ++ res109 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step108 : res108 ++ (H 146 :: diag108) ≡ᵤ (H 146 :: opt108) ++ res109 :=
 with_head _ _ _ _ 146 phase_sound108 (by decide +kernel)

theorem raw_sound109 : raw109 ≡ᵤ diag109 := motifs_checked 145 ps109 (by decide +kernel)

theorem phase_sound109 : res109 ++ diag109 ≡ᵤ opt109 ++ res110 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step109 : res109 ++ (H 145 :: diag109) ≡ᵤ (H 145 :: opt109) ++ res110 :=
 with_head _ _ _ _ 145 phase_sound109 (by decide +kernel)

theorem raw_sound110 : raw110 ≡ᵤ diag110 := motifs_checked 144 ps110 (by decide +kernel)

theorem phase_sound110 : res110 ++ diag110 ≡ᵤ opt110 ++ res111 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step110 : res110 ++ (H 144 :: diag110) ≡ᵤ (H 144 :: opt110) ++ res111 :=
 with_head _ _ _ _ 144 phase_sound110 (by decide +kernel)

theorem raw_sound111 : raw111 ≡ᵤ diag111 := motifs_checked 143 ps111 (by decide +kernel)

theorem phase_sound111 : res111 ++ diag111 ≡ᵤ opt111 ++ res112 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step111 : res111 ++ (H 143 :: diag111) ≡ᵤ (H 143 :: opt111) ++ res112 :=
 with_head _ _ _ _ 143 phase_sound111 (by decide +kernel)

theorem raw_sound112 : raw112 ≡ᵤ diag112 := motifs_checked 142 ps112 (by decide +kernel)

theorem phase_sound112 : res112 ++ diag112 ≡ᵤ opt112 ++ res113 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step112 : res112 ++ (H 142 :: diag112) ≡ᵤ (H 142 :: opt112) ++ res113 :=
 with_head _ _ _ _ 142 phase_sound112 (by decide +kernel)

theorem raw_sound113 : raw113 ≡ᵤ diag113 := motifs_checked 141 ps113 (by decide +kernel)

theorem phase_sound113 : res113 ++ diag113 ≡ᵤ opt113 ++ res114 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step113 : res113 ++ (H 141 :: diag113) ≡ᵤ (H 141 :: opt113) ++ res114 :=
 with_head _ _ _ _ 141 phase_sound113 (by decide +kernel)

theorem raw_sound114 : raw114 ≡ᵤ diag114 := motifs_checked 140 ps114 (by decide +kernel)

theorem phase_sound114 : res114 ++ diag114 ≡ᵤ opt114 ++ res115 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step114 : res114 ++ (H 140 :: diag114) ≡ᵤ (H 140 :: opt114) ++ res115 :=
 with_head _ _ _ _ 140 phase_sound114 (by decide +kernel)

theorem raw_sound115 : raw115 ≡ᵤ diag115 := motifs_checked 139 ps115 (by decide +kernel)

theorem phase_sound115 : res115 ++ diag115 ≡ᵤ opt115 ++ res116 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step115 : res115 ++ (H 139 :: diag115) ≡ᵤ (H 139 :: opt115) ++ res116 :=
 with_head _ _ _ _ 139 phase_sound115 (by decide +kernel)

theorem raw_sound116 : raw116 ≡ᵤ diag116 := motifs_checked 138 ps116 (by decide +kernel)

theorem phase_sound116 : res116 ++ diag116 ≡ᵤ opt116 ++ res117 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step116 : res116 ++ (H 138 :: diag116) ≡ᵤ (H 138 :: opt116) ++ res117 :=
 with_head _ _ _ _ 138 phase_sound116 (by decide +kernel)

theorem raw_sound117 : raw117 ≡ᵤ diag117 := motifs_checked 137 ps117 (by decide +kernel)

theorem phase_sound117 : res117 ++ diag117 ≡ᵤ opt117 ++ res118 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step117 : res117 ++ (H 137 :: diag117) ≡ᵤ (H 137 :: opt117) ++ res118 :=
 with_head _ _ _ _ 137 phase_sound117 (by decide +kernel)

theorem raw_sound118 : raw118 ≡ᵤ diag118 := motifs_checked 136 ps118 (by decide +kernel)

theorem phase_sound118 : res118 ++ diag118 ≡ᵤ opt118 ++ res119 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step118 : res118 ++ (H 136 :: diag118) ≡ᵤ (H 136 :: opt118) ++ res119 :=
 with_head _ _ _ _ 136 phase_sound118 (by decide +kernel)

theorem raw_sound119 : raw119 ≡ᵤ diag119 := motifs_checked 135 ps119 (by decide +kernel)

theorem phase_sound119 : res119 ++ diag119 ≡ᵤ opt119 ++ res120 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step119 : res119 ++ (H 135 :: diag119) ≡ᵤ (H 135 :: opt119) ++ res120 :=
 with_head _ _ _ _ 135 phase_sound119 (by decide +kernel)

theorem raw_sound120 : raw120 ≡ᵤ diag120 := motifs_checked 134 ps120 (by decide +kernel)

theorem phase_sound120 : res120 ++ diag120 ≡ᵤ opt120 ++ res121 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step120 : res120 ++ (H 134 :: diag120) ≡ᵤ (H 134 :: opt120) ++ res121 :=
 with_head _ _ _ _ 134 phase_sound120 (by decide +kernel)

theorem raw_sound121 : raw121 ≡ᵤ diag121 := motifs_checked 133 ps121 (by decide +kernel)

theorem phase_sound121 : res121 ++ diag121 ≡ᵤ opt121 ++ res122 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step121 : res121 ++ (H 133 :: diag121) ≡ᵤ (H 133 :: opt121) ++ res122 :=
 with_head _ _ _ _ 133 phase_sound121 (by decide +kernel)

theorem raw_sound122 : raw122 ≡ᵤ diag122 := motifs_checked 132 ps122 (by decide +kernel)

theorem phase_sound122 : res122 ++ diag122 ≡ᵤ opt122 ++ res123 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step122 : res122 ++ (H 132 :: diag122) ≡ᵤ (H 132 :: opt122) ++ res123 :=
 with_head _ _ _ _ 132 phase_sound122 (by decide +kernel)

theorem raw_sound123 : raw123 ≡ᵤ diag123 := motifs_checked 131 ps123 (by decide +kernel)

theorem phase_sound123 : res123 ++ diag123 ≡ᵤ opt123 ++ res124 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step123 : res123 ++ (H 131 :: diag123) ≡ᵤ (H 131 :: opt123) ++ res124 :=
 with_head _ _ _ _ 131 phase_sound123 (by decide +kernel)

theorem raw_sound124 : raw124 ≡ᵤ diag124 := motifs_checked 130 ps124 (by decide +kernel)

theorem phase_sound124 : res124 ++ diag124 ≡ᵤ opt124 ++ res125 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step124 : res124 ++ (H 130 :: diag124) ≡ᵤ (H 130 :: opt124) ++ res125 :=
 with_head _ _ _ _ 130 phase_sound124 (by decide +kernel)

theorem raw_sound125 : raw125 ≡ᵤ diag125 := motifs_checked 129 ps125 (by decide +kernel)

theorem phase_sound125 : res125 ++ diag125 ≡ᵤ opt125 ++ res126 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step125 : res125 ++ (H 129 :: diag125) ≡ᵤ (H 129 :: opt125) ++ res126 :=
 with_head _ _ _ _ 129 phase_sound125 (by decide +kernel)

theorem raw_sound126 : raw126 ≡ᵤ diag126 := motifs_checked 128 ps126 (by decide +kernel)

theorem phase_sound126 : res126 ++ diag126 ≡ᵤ opt126 ++ res127 :=
 (phasePolyChecker 192).sound _ _ (by decide +kernel)

theorem step126 : res126 ++ (H 128 :: diag126) ≡ᵤ (H 128 :: opt126) ++ res127 :=
 with_head _ _ _ _ 128 phase_sound126 (by decide +kernel)

end Quantum.Circuit.Harness