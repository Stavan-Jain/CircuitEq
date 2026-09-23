import Solution.Blocks
import Harness.Task
set_option Elab.async false
set_option maxRecDepth 500000
set_option maxHeartbeats 0
namespace Quantum.Circuit.Harness
open Instr


theorem norm0 : bodies rawGs0 ≡ᵤ bodies diagGs0 := flatten_equiv (List.Forall₂.cons raw_sound0 (List.Forall₂.cons raw_sound1 (List.Forall₂.cons raw_sound2 (List.Forall₂.cons raw_sound3 (List.Forall₂.cons raw_sound4 (List.Forall₂.cons raw_sound5 (List.Forall₂.cons raw_sound6 (List.Forall₂.cons raw_sound7 (List.Forall₂.cons raw_sound8 (List.Forall₂.cons raw_sound9 (List.Forall₂.cons raw_sound10 (List.Forall₂.cons raw_sound11 (List.Forall₂.cons raw_sound12 (List.Forall₂.cons raw_sound13 (List.Forall₂.cons raw_sound14 (List.Forall₂.cons raw_sound15 (List.Forall₂.cons raw_sound16 (List.Forall₂.cons raw_sound17 (List.Forall₂.cons raw_sound18 (List.Forall₂.cons raw_sound19 (List.Forall₂.cons raw_sound20 (List.Forall₂.cons raw_sound21 (List.Forall₂.cons raw_sound22 (List.Forall₂.cons raw_sound23 (List.Forall₂.cons raw_sound24 (List.Forall₂.cons raw_sound25 (List.Forall₂.cons raw_sound26 (List.Forall₂.cons raw_sound27 (List.Forall₂.cons raw_sound28 (List.Forall₂.cons raw_sound29 (List.Forall₂.cons raw_sound30 (List.Forall₂.cons raw_sound31 (List.Forall₂.cons raw_sound32 (List.Forall₂.cons raw_sound33 (List.Forall₂.cons raw_sound34 (List.Forall₂.cons raw_sound35 (List.Forall₂.cons raw_sound36 (List.Forall₂.cons raw_sound37 (List.Forall₂.cons raw_sound38 (List.Forall₂.cons raw_sound39 (List.Forall₂.cons raw_sound40 (List.Forall₂.cons raw_sound41 (List.Forall₂.cons raw_sound42 (List.Forall₂.cons raw_sound43 (List.Forall₂.cons raw_sound44 (List.Forall₂.cons raw_sound45 (List.Forall₂.cons raw_sound46 (List.Forall₂.cons raw_sound47 (List.Forall₂.cons raw_sound48 (List.Forall₂.cons raw_sound49 (List.Forall₂.cons raw_sound50 (List.Forall₂.cons raw_sound51 (List.Forall₂.cons raw_sound52 (List.Forall₂.cons raw_sound53 (List.Forall₂.cons raw_sound54 (List.Forall₂.cons raw_sound55 (List.Forall₂.cons raw_sound56 (List.Forall₂.cons raw_sound57 (List.Forall₂.cons raw_sound58 (List.Forall₂.cons raw_sound59 (List.Forall₂.cons raw_sound60 (List.Forall₂.cons raw_sound61 (List.Forall₂.cons raw_sound62 (List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem dist0 : heads diagGs0 ++ bodies diagGs0 ≡ᵤ distributed diagGs0 := distribute_sound _ (by decide +kernel)

theorem half_sound0 : originalHalf0 ≡ᵤ distributed diagGs0 :=
 ((Equivalent.refl (heads rawGs0)).append norm0).trans dist0

def aa1_3 : Circuit 192 := (H 129 :: diag1) ++ (H 130 :: diag2)

def bb1_3 : Circuit 192 := (H 129 :: opt1) ++ (H 130 :: opt2)

theorem join1_3 : res1 ++ aa1_3 ≡ᵤ bb1_3 ++ res3 := stitch step1 step2

def aa0_3 : Circuit 192 := (H 128 :: diag0) ++ aa1_3

def bb0_3 : Circuit 192 := (H 128 :: opt0) ++ bb1_3

theorem join0_3 : res0 ++ aa0_3 ≡ᵤ bb0_3 ++ res3 := stitch step0 join1_3

def aa3_5 : Circuit 192 := (H 131 :: diag3) ++ (H 132 :: diag4)

def bb3_5 : Circuit 192 := (H 131 :: opt3) ++ (H 132 :: opt4)

theorem join3_5 : res3 ++ aa3_5 ≡ᵤ bb3_5 ++ res5 := stitch step3 step4

def aa5_7 : Circuit 192 := (H 133 :: diag5) ++ (H 134 :: diag6)

def bb5_7 : Circuit 192 := (H 133 :: opt5) ++ (H 134 :: opt6)

theorem join5_7 : res5 ++ aa5_7 ≡ᵤ bb5_7 ++ res7 := stitch step5 step6

def aa3_7 : Circuit 192 := aa3_5 ++ aa5_7

def bb3_7 : Circuit 192 := bb3_5 ++ bb5_7

theorem join3_7 : res3 ++ aa3_7 ≡ᵤ bb3_7 ++ res7 := stitch join3_5 join5_7

def aa0_7 : Circuit 192 := aa0_3 ++ aa3_7

def bb0_7 : Circuit 192 := bb0_3 ++ bb3_7

theorem join0_7 : res0 ++ aa0_7 ≡ᵤ bb0_7 ++ res7 := stitch join0_3 join3_7

def aa7_9 : Circuit 192 := (H 135 :: diag7) ++ (H 136 :: diag8)

def bb7_9 : Circuit 192 := (H 135 :: opt7) ++ (H 136 :: opt8)

theorem join7_9 : res7 ++ aa7_9 ≡ᵤ bb7_9 ++ res9 := stitch step7 step8

def aa9_11 : Circuit 192 := (H 137 :: diag9) ++ (H 138 :: diag10)

def bb9_11 : Circuit 192 := (H 137 :: opt9) ++ (H 138 :: opt10)

theorem join9_11 : res9 ++ aa9_11 ≡ᵤ bb9_11 ++ res11 := stitch step9 step10

def aa7_11 : Circuit 192 := aa7_9 ++ aa9_11

def bb7_11 : Circuit 192 := bb7_9 ++ bb9_11

theorem join7_11 : res7 ++ aa7_11 ≡ᵤ bb7_11 ++ res11 := stitch join7_9 join9_11

def aa11_13 : Circuit 192 := (H 139 :: diag11) ++ (H 140 :: diag12)

def bb11_13 : Circuit 192 := (H 139 :: opt11) ++ (H 140 :: opt12)

theorem join11_13 : res11 ++ aa11_13 ≡ᵤ bb11_13 ++ res13 := stitch step11 step12

def aa13_15 : Circuit 192 := (H 141 :: diag13) ++ (H 142 :: diag14)

def bb13_15 : Circuit 192 := (H 141 :: opt13) ++ (H 142 :: opt14)

theorem join13_15 : res13 ++ aa13_15 ≡ᵤ bb13_15 ++ res15 := stitch step13 step14

def aa11_15 : Circuit 192 := aa11_13 ++ aa13_15

def bb11_15 : Circuit 192 := bb11_13 ++ bb13_15

theorem join11_15 : res11 ++ aa11_15 ≡ᵤ bb11_15 ++ res15 := stitch join11_13 join13_15

def aa7_15 : Circuit 192 := aa7_11 ++ aa11_15

def bb7_15 : Circuit 192 := bb7_11 ++ bb11_15

theorem join7_15 : res7 ++ aa7_15 ≡ᵤ bb7_15 ++ res15 := stitch join7_11 join11_15

def aa0_15 : Circuit 192 := aa0_7 ++ aa7_15

def bb0_15 : Circuit 192 := bb0_7 ++ bb7_15

theorem join0_15 : res0 ++ aa0_15 ≡ᵤ bb0_15 ++ res15 := stitch join0_7 join7_15

def aa15_17 : Circuit 192 := (H 143 :: diag15) ++ (H 144 :: diag16)

def bb15_17 : Circuit 192 := (H 143 :: opt15) ++ (H 144 :: opt16)

theorem join15_17 : res15 ++ aa15_17 ≡ᵤ bb15_17 ++ res17 := stitch step15 step16

def aa17_19 : Circuit 192 := (H 145 :: diag17) ++ (H 146 :: diag18)

def bb17_19 : Circuit 192 := (H 145 :: opt17) ++ (H 146 :: opt18)

theorem join17_19 : res17 ++ aa17_19 ≡ᵤ bb17_19 ++ res19 := stitch step17 step18

def aa15_19 : Circuit 192 := aa15_17 ++ aa17_19

def bb15_19 : Circuit 192 := bb15_17 ++ bb17_19

theorem join15_19 : res15 ++ aa15_19 ≡ᵤ bb15_19 ++ res19 := stitch join15_17 join17_19

def aa19_21 : Circuit 192 := (H 147 :: diag19) ++ (H 148 :: diag20)

def bb19_21 : Circuit 192 := (H 147 :: opt19) ++ (H 148 :: opt20)

theorem join19_21 : res19 ++ aa19_21 ≡ᵤ bb19_21 ++ res21 := stitch step19 step20

def aa21_23 : Circuit 192 := (H 149 :: diag21) ++ (H 150 :: diag22)

def bb21_23 : Circuit 192 := (H 149 :: opt21) ++ (H 150 :: opt22)

theorem join21_23 : res21 ++ aa21_23 ≡ᵤ bb21_23 ++ res23 := stitch step21 step22

def aa19_23 : Circuit 192 := aa19_21 ++ aa21_23

def bb19_23 : Circuit 192 := bb19_21 ++ bb21_23

theorem join19_23 : res19 ++ aa19_23 ≡ᵤ bb19_23 ++ res23 := stitch join19_21 join21_23

def aa15_23 : Circuit 192 := aa15_19 ++ aa19_23

def bb15_23 : Circuit 192 := bb15_19 ++ bb19_23

theorem join15_23 : res15 ++ aa15_23 ≡ᵤ bb15_23 ++ res23 := stitch join15_19 join19_23

def aa23_25 : Circuit 192 := (H 151 :: diag23) ++ (H 152 :: diag24)

def bb23_25 : Circuit 192 := (H 151 :: opt23) ++ (H 152 :: opt24)

theorem join23_25 : res23 ++ aa23_25 ≡ᵤ bb23_25 ++ res25 := stitch step23 step24

def aa25_27 : Circuit 192 := (H 153 :: diag25) ++ (H 154 :: diag26)

def bb25_27 : Circuit 192 := (H 153 :: opt25) ++ (H 154 :: opt26)

theorem join25_27 : res25 ++ aa25_27 ≡ᵤ bb25_27 ++ res27 := stitch step25 step26

def aa23_27 : Circuit 192 := aa23_25 ++ aa25_27

def bb23_27 : Circuit 192 := bb23_25 ++ bb25_27

theorem join23_27 : res23 ++ aa23_27 ≡ᵤ bb23_27 ++ res27 := stitch join23_25 join25_27

def aa27_29 : Circuit 192 := (H 155 :: diag27) ++ (H 156 :: diag28)

def bb27_29 : Circuit 192 := (H 155 :: opt27) ++ (H 156 :: opt28)

theorem join27_29 : res27 ++ aa27_29 ≡ᵤ bb27_29 ++ res29 := stitch step27 step28

def aa29_31 : Circuit 192 := (H 157 :: diag29) ++ (H 158 :: diag30)

def bb29_31 : Circuit 192 := (H 157 :: opt29) ++ (H 158 :: opt30)

theorem join29_31 : res29 ++ aa29_31 ≡ᵤ bb29_31 ++ res31 := stitch step29 step30

def aa27_31 : Circuit 192 := aa27_29 ++ aa29_31

def bb27_31 : Circuit 192 := bb27_29 ++ bb29_31

theorem join27_31 : res27 ++ aa27_31 ≡ᵤ bb27_31 ++ res31 := stitch join27_29 join29_31

def aa23_31 : Circuit 192 := aa23_27 ++ aa27_31

def bb23_31 : Circuit 192 := bb23_27 ++ bb27_31

theorem join23_31 : res23 ++ aa23_31 ≡ᵤ bb23_31 ++ res31 := stitch join23_27 join27_31

def aa15_31 : Circuit 192 := aa15_23 ++ aa23_31

def bb15_31 : Circuit 192 := bb15_23 ++ bb23_31

theorem join15_31 : res15 ++ aa15_31 ≡ᵤ bb15_31 ++ res31 := stitch join15_23 join23_31

def aa0_31 : Circuit 192 := aa0_15 ++ aa15_31

def bb0_31 : Circuit 192 := bb0_15 ++ bb15_31

theorem join0_31 : res0 ++ aa0_31 ≡ᵤ bb0_31 ++ res31 := stitch join0_15 join15_31

def aa31_33 : Circuit 192 := (H 159 :: diag31) ++ (H 160 :: diag32)

def bb31_33 : Circuit 192 := (H 159 :: opt31) ++ (H 160 :: opt32)

theorem join31_33 : res31 ++ aa31_33 ≡ᵤ bb31_33 ++ res33 := stitch step31 step32

def aa33_35 : Circuit 192 := (H 161 :: diag33) ++ (H 162 :: diag34)

def bb33_35 : Circuit 192 := (H 161 :: opt33) ++ (H 162 :: opt34)

theorem join33_35 : res33 ++ aa33_35 ≡ᵤ bb33_35 ++ res35 := stitch step33 step34

def aa31_35 : Circuit 192 := aa31_33 ++ aa33_35

def bb31_35 : Circuit 192 := bb31_33 ++ bb33_35

theorem join31_35 : res31 ++ aa31_35 ≡ᵤ bb31_35 ++ res35 := stitch join31_33 join33_35

def aa35_37 : Circuit 192 := (H 163 :: diag35) ++ (H 164 :: diag36)

def bb35_37 : Circuit 192 := (H 163 :: opt35) ++ (H 164 :: opt36)

theorem join35_37 : res35 ++ aa35_37 ≡ᵤ bb35_37 ++ res37 := stitch step35 step36

def aa37_39 : Circuit 192 := (H 165 :: diag37) ++ (H 166 :: diag38)

def bb37_39 : Circuit 192 := (H 165 :: opt37) ++ (H 166 :: opt38)

theorem join37_39 : res37 ++ aa37_39 ≡ᵤ bb37_39 ++ res39 := stitch step37 step38

def aa35_39 : Circuit 192 := aa35_37 ++ aa37_39

def bb35_39 : Circuit 192 := bb35_37 ++ bb37_39

theorem join35_39 : res35 ++ aa35_39 ≡ᵤ bb35_39 ++ res39 := stitch join35_37 join37_39

def aa31_39 : Circuit 192 := aa31_35 ++ aa35_39

def bb31_39 : Circuit 192 := bb31_35 ++ bb35_39

theorem join31_39 : res31 ++ aa31_39 ≡ᵤ bb31_39 ++ res39 := stitch join31_35 join35_39

def aa39_41 : Circuit 192 := (H 167 :: diag39) ++ (H 168 :: diag40)

def bb39_41 : Circuit 192 := (H 167 :: opt39) ++ (H 168 :: opt40)

theorem join39_41 : res39 ++ aa39_41 ≡ᵤ bb39_41 ++ res41 := stitch step39 step40

def aa41_43 : Circuit 192 := (H 169 :: diag41) ++ (H 170 :: diag42)

def bb41_43 : Circuit 192 := (H 169 :: opt41) ++ (H 170 :: opt42)

theorem join41_43 : res41 ++ aa41_43 ≡ᵤ bb41_43 ++ res43 := stitch step41 step42

def aa39_43 : Circuit 192 := aa39_41 ++ aa41_43

def bb39_43 : Circuit 192 := bb39_41 ++ bb41_43

theorem join39_43 : res39 ++ aa39_43 ≡ᵤ bb39_43 ++ res43 := stitch join39_41 join41_43

def aa43_45 : Circuit 192 := (H 171 :: diag43) ++ (H 172 :: diag44)

def bb43_45 : Circuit 192 := (H 171 :: opt43) ++ (H 172 :: opt44)

theorem join43_45 : res43 ++ aa43_45 ≡ᵤ bb43_45 ++ res45 := stitch step43 step44

def aa45_47 : Circuit 192 := (H 173 :: diag45) ++ (H 174 :: diag46)

def bb45_47 : Circuit 192 := (H 173 :: opt45) ++ (H 174 :: opt46)

theorem join45_47 : res45 ++ aa45_47 ≡ᵤ bb45_47 ++ res47 := stitch step45 step46

def aa43_47 : Circuit 192 := aa43_45 ++ aa45_47

def bb43_47 : Circuit 192 := bb43_45 ++ bb45_47

theorem join43_47 : res43 ++ aa43_47 ≡ᵤ bb43_47 ++ res47 := stitch join43_45 join45_47

def aa39_47 : Circuit 192 := aa39_43 ++ aa43_47

def bb39_47 : Circuit 192 := bb39_43 ++ bb43_47

theorem join39_47 : res39 ++ aa39_47 ≡ᵤ bb39_47 ++ res47 := stitch join39_43 join43_47

def aa31_47 : Circuit 192 := aa31_39 ++ aa39_47

def bb31_47 : Circuit 192 := bb31_39 ++ bb39_47

theorem join31_47 : res31 ++ aa31_47 ≡ᵤ bb31_47 ++ res47 := stitch join31_39 join39_47

def aa47_49 : Circuit 192 := (H 175 :: diag47) ++ (H 176 :: diag48)

def bb47_49 : Circuit 192 := (H 175 :: opt47) ++ (H 176 :: opt48)

theorem join47_49 : res47 ++ aa47_49 ≡ᵤ bb47_49 ++ res49 := stitch step47 step48

def aa49_51 : Circuit 192 := (H 177 :: diag49) ++ (H 178 :: diag50)

def bb49_51 : Circuit 192 := (H 177 :: opt49) ++ (H 178 :: opt50)

theorem join49_51 : res49 ++ aa49_51 ≡ᵤ bb49_51 ++ res51 := stitch step49 step50

def aa47_51 : Circuit 192 := aa47_49 ++ aa49_51

def bb47_51 : Circuit 192 := bb47_49 ++ bb49_51

theorem join47_51 : res47 ++ aa47_51 ≡ᵤ bb47_51 ++ res51 := stitch join47_49 join49_51

def aa51_53 : Circuit 192 := (H 179 :: diag51) ++ (H 180 :: diag52)

def bb51_53 : Circuit 192 := (H 179 :: opt51) ++ (H 180 :: opt52)

theorem join51_53 : res51 ++ aa51_53 ≡ᵤ bb51_53 ++ res53 := stitch step51 step52

def aa53_55 : Circuit 192 := (H 181 :: diag53) ++ (H 182 :: diag54)

def bb53_55 : Circuit 192 := (H 181 :: opt53) ++ (H 182 :: opt54)

theorem join53_55 : res53 ++ aa53_55 ≡ᵤ bb53_55 ++ res55 := stitch step53 step54

def aa51_55 : Circuit 192 := aa51_53 ++ aa53_55

def bb51_55 : Circuit 192 := bb51_53 ++ bb53_55

theorem join51_55 : res51 ++ aa51_55 ≡ᵤ bb51_55 ++ res55 := stitch join51_53 join53_55

def aa47_55 : Circuit 192 := aa47_51 ++ aa51_55

def bb47_55 : Circuit 192 := bb47_51 ++ bb51_55

theorem join47_55 : res47 ++ aa47_55 ≡ᵤ bb47_55 ++ res55 := stitch join47_51 join51_55

def aa55_57 : Circuit 192 := (H 183 :: diag55) ++ (H 184 :: diag56)

def bb55_57 : Circuit 192 := (H 183 :: opt55) ++ (H 184 :: opt56)

theorem join55_57 : res55 ++ aa55_57 ≡ᵤ bb55_57 ++ res57 := stitch step55 step56

def aa57_59 : Circuit 192 := (H 185 :: diag57) ++ (H 186 :: diag58)

def bb57_59 : Circuit 192 := (H 185 :: opt57) ++ (H 186 :: opt58)

theorem join57_59 : res57 ++ aa57_59 ≡ᵤ bb57_59 ++ res59 := stitch step57 step58

def aa55_59 : Circuit 192 := aa55_57 ++ aa57_59

def bb55_59 : Circuit 192 := bb55_57 ++ bb57_59

theorem join55_59 : res55 ++ aa55_59 ≡ᵤ bb55_59 ++ res59 := stitch join55_57 join57_59

def aa59_61 : Circuit 192 := (H 187 :: diag59) ++ (H 188 :: diag60)

def bb59_61 : Circuit 192 := (H 187 :: opt59) ++ (H 188 :: opt60)

theorem join59_61 : res59 ++ aa59_61 ≡ᵤ bb59_61 ++ res61 := stitch step59 step60

def aa61_63 : Circuit 192 := (H 189 :: diag61) ++ (H 190 :: diag62)

def bb61_63 : Circuit 192 := (H 189 :: opt61) ++ (H 190 :: opt62)

theorem join61_63 : res61 ++ aa61_63 ≡ᵤ bb61_63 ++ res63 := stitch step61 step62

def aa59_63 : Circuit 192 := aa59_61 ++ aa61_63

def bb59_63 : Circuit 192 := bb59_61 ++ bb61_63

theorem join59_63 : res59 ++ aa59_63 ≡ᵤ bb59_63 ++ res63 := stitch join59_61 join61_63

def aa55_63 : Circuit 192 := aa55_59 ++ aa59_63

def bb55_63 : Circuit 192 := bb55_59 ++ bb59_63

theorem join55_63 : res55 ++ aa55_63 ≡ᵤ bb55_63 ++ res63 := stitch join55_59 join59_63

def aa47_63 : Circuit 192 := aa47_55 ++ aa55_63

def bb47_63 : Circuit 192 := bb47_55 ++ bb55_63

theorem join47_63 : res47 ++ aa47_63 ≡ᵤ bb47_63 ++ res63 := stitch join47_55 join55_63

def aa31_63 : Circuit 192 := aa31_47 ++ aa47_63

def bb31_63 : Circuit 192 := bb31_47 ++ bb47_63

theorem join31_63 : res31 ++ aa31_63 ≡ᵤ bb31_63 ++ res63 := stitch join31_47 join47_63

def aa0_63 : Circuit 192 := aa0_31 ++ aa31_63

def bb0_63 : Circuit 192 := bb0_31 ++ bb31_63

theorem join0_63 : res0 ++ aa0_63 ≡ᵤ bb0_63 ++ res63 := stitch join0_31 join31_63

theorem check_half0 : res0 ++ distributed diagGs0 ≡ᵤ distributed optGs0 ++ res63 := join0_63

theorem norm1 : bodies rawGs1 ≡ᵤ bodies diagGs1 := flatten_equiv (List.Forall₂.cons raw_sound63 (List.Forall₂.cons raw_sound64 (List.Forall₂.cons raw_sound65 (List.Forall₂.cons raw_sound66 (List.Forall₂.cons raw_sound67 (List.Forall₂.cons raw_sound68 (List.Forall₂.cons raw_sound69 (List.Forall₂.cons raw_sound70 (List.Forall₂.cons raw_sound71 (List.Forall₂.cons raw_sound72 (List.Forall₂.cons raw_sound73 (List.Forall₂.cons raw_sound74 (List.Forall₂.cons raw_sound75 (List.Forall₂.cons raw_sound76 (List.Forall₂.cons raw_sound77 (List.Forall₂.cons raw_sound78 (List.Forall₂.cons raw_sound79 (List.Forall₂.cons raw_sound80 (List.Forall₂.cons raw_sound81 (List.Forall₂.cons raw_sound82 (List.Forall₂.cons raw_sound83 (List.Forall₂.cons raw_sound84 (List.Forall₂.cons raw_sound85 (List.Forall₂.cons raw_sound86 (List.Forall₂.cons raw_sound87 (List.Forall₂.cons raw_sound88 (List.Forall₂.cons raw_sound89 (List.Forall₂.cons raw_sound90 (List.Forall₂.cons raw_sound91 (List.Forall₂.cons raw_sound92 (List.Forall₂.cons raw_sound93 (List.Forall₂.cons raw_sound94 (List.Forall₂.cons raw_sound95 (List.Forall₂.cons raw_sound96 (List.Forall₂.cons raw_sound97 (List.Forall₂.cons raw_sound98 (List.Forall₂.cons raw_sound99 (List.Forall₂.cons raw_sound100 (List.Forall₂.cons raw_sound101 (List.Forall₂.cons raw_sound102 (List.Forall₂.cons raw_sound103 (List.Forall₂.cons raw_sound104 (List.Forall₂.cons raw_sound105 (List.Forall₂.cons raw_sound106 (List.Forall₂.cons raw_sound107 (List.Forall₂.cons raw_sound108 (List.Forall₂.cons raw_sound109 (List.Forall₂.cons raw_sound110 (List.Forall₂.cons raw_sound111 (List.Forall₂.cons raw_sound112 (List.Forall₂.cons raw_sound113 (List.Forall₂.cons raw_sound114 (List.Forall₂.cons raw_sound115 (List.Forall₂.cons raw_sound116 (List.Forall₂.cons raw_sound117 (List.Forall₂.cons raw_sound118 (List.Forall₂.cons raw_sound119 (List.Forall₂.cons raw_sound120 (List.Forall₂.cons raw_sound121 (List.Forall₂.cons raw_sound122 (List.Forall₂.cons raw_sound123 (List.Forall₂.cons raw_sound124 (List.Forall₂.cons raw_sound125 (List.Forall₂.cons raw_sound126 (List.Forall₂.nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem dist1 : heads diagGs1 ++ bodies diagGs1 ≡ᵤ distributed diagGs1 := distribute_sound _ (by decide +kernel)

theorem head_reverse : finalH ≡ᵤ heads diagGs1 :=
 layer_perm .H (a := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (b := [191, 190, 189, 188, 187, 186, 185, 184, 183, 182, 181, 180, 179, 178, 177, 176, 175, 174, 173, 172, 171, 170, 169, 168, 167, 166, 165, 164, 163, 162, 161, 160, 159, 158, 157, 156, 155, 154, 153, 152, 151, 150, 149, 148, 147, 146, 145, 144, 143, 142, 141, 140, 139, 138, 137, 136, 135, 134, 133, 132, 131, 130, 129, 128]) (by decide +kernel)

theorem half_sound1 : originalHalf1 ≡ᵤ distributed diagGs1 :=
 (head_reverse.append norm1).trans dist1

def aa63_65 : Circuit 192 := (H 191 :: diag63) ++ (H 190 :: diag64)

def bb63_65 : Circuit 192 := (H 191 :: opt63) ++ (H 190 :: opt64)

theorem join63_65 : res63 ++ aa63_65 ≡ᵤ bb63_65 ++ res65 := stitch step63 step64

def aa65_67 : Circuit 192 := (H 189 :: diag65) ++ (H 188 :: diag66)

def bb65_67 : Circuit 192 := (H 189 :: opt65) ++ (H 188 :: opt66)

theorem join65_67 : res65 ++ aa65_67 ≡ᵤ bb65_67 ++ res67 := stitch step65 step66

def aa63_67 : Circuit 192 := aa63_65 ++ aa65_67

def bb63_67 : Circuit 192 := bb63_65 ++ bb65_67

theorem join63_67 : res63 ++ aa63_67 ≡ᵤ bb63_67 ++ res67 := stitch join63_65 join65_67

def aa67_69 : Circuit 192 := (H 187 :: diag67) ++ (H 186 :: diag68)

def bb67_69 : Circuit 192 := (H 187 :: opt67) ++ (H 186 :: opt68)

theorem join67_69 : res67 ++ aa67_69 ≡ᵤ bb67_69 ++ res69 := stitch step67 step68

def aa69_71 : Circuit 192 := (H 185 :: diag69) ++ (H 184 :: diag70)

def bb69_71 : Circuit 192 := (H 185 :: opt69) ++ (H 184 :: opt70)

theorem join69_71 : res69 ++ aa69_71 ≡ᵤ bb69_71 ++ res71 := stitch step69 step70

def aa67_71 : Circuit 192 := aa67_69 ++ aa69_71

def bb67_71 : Circuit 192 := bb67_69 ++ bb69_71

theorem join67_71 : res67 ++ aa67_71 ≡ᵤ bb67_71 ++ res71 := stitch join67_69 join69_71

def aa63_71 : Circuit 192 := aa63_67 ++ aa67_71

def bb63_71 : Circuit 192 := bb63_67 ++ bb67_71

theorem join63_71 : res63 ++ aa63_71 ≡ᵤ bb63_71 ++ res71 := stitch join63_67 join67_71

def aa71_73 : Circuit 192 := (H 183 :: diag71) ++ (H 182 :: diag72)

def bb71_73 : Circuit 192 := (H 183 :: opt71) ++ (H 182 :: opt72)

theorem join71_73 : res71 ++ aa71_73 ≡ᵤ bb71_73 ++ res73 := stitch step71 step72

def aa73_75 : Circuit 192 := (H 181 :: diag73) ++ (H 180 :: diag74)

def bb73_75 : Circuit 192 := (H 181 :: opt73) ++ (H 180 :: opt74)

theorem join73_75 : res73 ++ aa73_75 ≡ᵤ bb73_75 ++ res75 := stitch step73 step74

def aa71_75 : Circuit 192 := aa71_73 ++ aa73_75

def bb71_75 : Circuit 192 := bb71_73 ++ bb73_75

theorem join71_75 : res71 ++ aa71_75 ≡ᵤ bb71_75 ++ res75 := stitch join71_73 join73_75

def aa75_77 : Circuit 192 := (H 179 :: diag75) ++ (H 178 :: diag76)

def bb75_77 : Circuit 192 := (H 179 :: opt75) ++ (H 178 :: opt76)

theorem join75_77 : res75 ++ aa75_77 ≡ᵤ bb75_77 ++ res77 := stitch step75 step76

def aa77_79 : Circuit 192 := (H 177 :: diag77) ++ (H 176 :: diag78)

def bb77_79 : Circuit 192 := (H 177 :: opt77) ++ (H 176 :: opt78)

theorem join77_79 : res77 ++ aa77_79 ≡ᵤ bb77_79 ++ res79 := stitch step77 step78

def aa75_79 : Circuit 192 := aa75_77 ++ aa77_79

def bb75_79 : Circuit 192 := bb75_77 ++ bb77_79

theorem join75_79 : res75 ++ aa75_79 ≡ᵤ bb75_79 ++ res79 := stitch join75_77 join77_79

def aa71_79 : Circuit 192 := aa71_75 ++ aa75_79

def bb71_79 : Circuit 192 := bb71_75 ++ bb75_79

theorem join71_79 : res71 ++ aa71_79 ≡ᵤ bb71_79 ++ res79 := stitch join71_75 join75_79

def aa63_79 : Circuit 192 := aa63_71 ++ aa71_79

def bb63_79 : Circuit 192 := bb63_71 ++ bb71_79

theorem join63_79 : res63 ++ aa63_79 ≡ᵤ bb63_79 ++ res79 := stitch join63_71 join71_79

def aa79_81 : Circuit 192 := (H 175 :: diag79) ++ (H 174 :: diag80)

def bb79_81 : Circuit 192 := (H 175 :: opt79) ++ (H 174 :: opt80)

theorem join79_81 : res79 ++ aa79_81 ≡ᵤ bb79_81 ++ res81 := stitch step79 step80

def aa81_83 : Circuit 192 := (H 173 :: diag81) ++ (H 172 :: diag82)

def bb81_83 : Circuit 192 := (H 173 :: opt81) ++ (H 172 :: opt82)

theorem join81_83 : res81 ++ aa81_83 ≡ᵤ bb81_83 ++ res83 := stitch step81 step82

def aa79_83 : Circuit 192 := aa79_81 ++ aa81_83

def bb79_83 : Circuit 192 := bb79_81 ++ bb81_83

theorem join79_83 : res79 ++ aa79_83 ≡ᵤ bb79_83 ++ res83 := stitch join79_81 join81_83

def aa83_85 : Circuit 192 := (H 171 :: diag83) ++ (H 170 :: diag84)

def bb83_85 : Circuit 192 := (H 171 :: opt83) ++ (H 170 :: opt84)

theorem join83_85 : res83 ++ aa83_85 ≡ᵤ bb83_85 ++ res85 := stitch step83 step84

def aa85_87 : Circuit 192 := (H 169 :: diag85) ++ (H 168 :: diag86)

def bb85_87 : Circuit 192 := (H 169 :: opt85) ++ (H 168 :: opt86)

theorem join85_87 : res85 ++ aa85_87 ≡ᵤ bb85_87 ++ res87 := stitch step85 step86

def aa83_87 : Circuit 192 := aa83_85 ++ aa85_87

def bb83_87 : Circuit 192 := bb83_85 ++ bb85_87

theorem join83_87 : res83 ++ aa83_87 ≡ᵤ bb83_87 ++ res87 := stitch join83_85 join85_87

def aa79_87 : Circuit 192 := aa79_83 ++ aa83_87

def bb79_87 : Circuit 192 := bb79_83 ++ bb83_87

theorem join79_87 : res79 ++ aa79_87 ≡ᵤ bb79_87 ++ res87 := stitch join79_83 join83_87

def aa87_89 : Circuit 192 := (H 167 :: diag87) ++ (H 166 :: diag88)

def bb87_89 : Circuit 192 := (H 167 :: opt87) ++ (H 166 :: opt88)

theorem join87_89 : res87 ++ aa87_89 ≡ᵤ bb87_89 ++ res89 := stitch step87 step88

def aa89_91 : Circuit 192 := (H 165 :: diag89) ++ (H 164 :: diag90)

def bb89_91 : Circuit 192 := (H 165 :: opt89) ++ (H 164 :: opt90)

theorem join89_91 : res89 ++ aa89_91 ≡ᵤ bb89_91 ++ res91 := stitch step89 step90

def aa87_91 : Circuit 192 := aa87_89 ++ aa89_91

def bb87_91 : Circuit 192 := bb87_89 ++ bb89_91

theorem join87_91 : res87 ++ aa87_91 ≡ᵤ bb87_91 ++ res91 := stitch join87_89 join89_91

def aa91_93 : Circuit 192 := (H 163 :: diag91) ++ (H 162 :: diag92)

def bb91_93 : Circuit 192 := (H 163 :: opt91) ++ (H 162 :: opt92)

theorem join91_93 : res91 ++ aa91_93 ≡ᵤ bb91_93 ++ res93 := stitch step91 step92

def aa93_95 : Circuit 192 := (H 161 :: diag93) ++ (H 160 :: diag94)

def bb93_95 : Circuit 192 := (H 161 :: opt93) ++ (H 160 :: opt94)

theorem join93_95 : res93 ++ aa93_95 ≡ᵤ bb93_95 ++ res95 := stitch step93 step94

def aa91_95 : Circuit 192 := aa91_93 ++ aa93_95

def bb91_95 : Circuit 192 := bb91_93 ++ bb93_95

theorem join91_95 : res91 ++ aa91_95 ≡ᵤ bb91_95 ++ res95 := stitch join91_93 join93_95

def aa87_95 : Circuit 192 := aa87_91 ++ aa91_95

def bb87_95 : Circuit 192 := bb87_91 ++ bb91_95

theorem join87_95 : res87 ++ aa87_95 ≡ᵤ bb87_95 ++ res95 := stitch join87_91 join91_95

def aa79_95 : Circuit 192 := aa79_87 ++ aa87_95

def bb79_95 : Circuit 192 := bb79_87 ++ bb87_95

theorem join79_95 : res79 ++ aa79_95 ≡ᵤ bb79_95 ++ res95 := stitch join79_87 join87_95

def aa63_95 : Circuit 192 := aa63_79 ++ aa79_95

def bb63_95 : Circuit 192 := bb63_79 ++ bb79_95

theorem join63_95 : res63 ++ aa63_95 ≡ᵤ bb63_95 ++ res95 := stitch join63_79 join79_95

def aa95_97 : Circuit 192 := (H 159 :: diag95) ++ (H 158 :: diag96)

def bb95_97 : Circuit 192 := (H 159 :: opt95) ++ (H 158 :: opt96)

theorem join95_97 : res95 ++ aa95_97 ≡ᵤ bb95_97 ++ res97 := stitch step95 step96

def aa97_99 : Circuit 192 := (H 157 :: diag97) ++ (H 156 :: diag98)

def bb97_99 : Circuit 192 := (H 157 :: opt97) ++ (H 156 :: opt98)

theorem join97_99 : res97 ++ aa97_99 ≡ᵤ bb97_99 ++ res99 := stitch step97 step98

def aa95_99 : Circuit 192 := aa95_97 ++ aa97_99

def bb95_99 : Circuit 192 := bb95_97 ++ bb97_99

theorem join95_99 : res95 ++ aa95_99 ≡ᵤ bb95_99 ++ res99 := stitch join95_97 join97_99

def aa99_101 : Circuit 192 := (H 155 :: diag99) ++ (H 154 :: diag100)

def bb99_101 : Circuit 192 := (H 155 :: opt99) ++ (H 154 :: opt100)

theorem join99_101 : res99 ++ aa99_101 ≡ᵤ bb99_101 ++ res101 := stitch step99 step100

def aa101_103 : Circuit 192 := (H 153 :: diag101) ++ (H 152 :: diag102)

def bb101_103 : Circuit 192 := (H 153 :: opt101) ++ (H 152 :: opt102)

theorem join101_103 : res101 ++ aa101_103 ≡ᵤ bb101_103 ++ res103 := stitch step101 step102

def aa99_103 : Circuit 192 := aa99_101 ++ aa101_103

def bb99_103 : Circuit 192 := bb99_101 ++ bb101_103

theorem join99_103 : res99 ++ aa99_103 ≡ᵤ bb99_103 ++ res103 := stitch join99_101 join101_103

def aa95_103 : Circuit 192 := aa95_99 ++ aa99_103

def bb95_103 : Circuit 192 := bb95_99 ++ bb99_103

theorem join95_103 : res95 ++ aa95_103 ≡ᵤ bb95_103 ++ res103 := stitch join95_99 join99_103

def aa103_105 : Circuit 192 := (H 151 :: diag103) ++ (H 150 :: diag104)

def bb103_105 : Circuit 192 := (H 151 :: opt103) ++ (H 150 :: opt104)

theorem join103_105 : res103 ++ aa103_105 ≡ᵤ bb103_105 ++ res105 := stitch step103 step104

def aa105_107 : Circuit 192 := (H 149 :: diag105) ++ (H 148 :: diag106)

def bb105_107 : Circuit 192 := (H 149 :: opt105) ++ (H 148 :: opt106)

theorem join105_107 : res105 ++ aa105_107 ≡ᵤ bb105_107 ++ res107 := stitch step105 step106

def aa103_107 : Circuit 192 := aa103_105 ++ aa105_107

def bb103_107 : Circuit 192 := bb103_105 ++ bb105_107

theorem join103_107 : res103 ++ aa103_107 ≡ᵤ bb103_107 ++ res107 := stitch join103_105 join105_107

def aa107_109 : Circuit 192 := (H 147 :: diag107) ++ (H 146 :: diag108)

def bb107_109 : Circuit 192 := (H 147 :: opt107) ++ (H 146 :: opt108)

theorem join107_109 : res107 ++ aa107_109 ≡ᵤ bb107_109 ++ res109 := stitch step107 step108

def aa109_111 : Circuit 192 := (H 145 :: diag109) ++ (H 144 :: diag110)

def bb109_111 : Circuit 192 := (H 145 :: opt109) ++ (H 144 :: opt110)

theorem join109_111 : res109 ++ aa109_111 ≡ᵤ bb109_111 ++ res111 := stitch step109 step110

def aa107_111 : Circuit 192 := aa107_109 ++ aa109_111

def bb107_111 : Circuit 192 := bb107_109 ++ bb109_111

theorem join107_111 : res107 ++ aa107_111 ≡ᵤ bb107_111 ++ res111 := stitch join107_109 join109_111

def aa103_111 : Circuit 192 := aa103_107 ++ aa107_111

def bb103_111 : Circuit 192 := bb103_107 ++ bb107_111

theorem join103_111 : res103 ++ aa103_111 ≡ᵤ bb103_111 ++ res111 := stitch join103_107 join107_111

def aa95_111 : Circuit 192 := aa95_103 ++ aa103_111

def bb95_111 : Circuit 192 := bb95_103 ++ bb103_111

theorem join95_111 : res95 ++ aa95_111 ≡ᵤ bb95_111 ++ res111 := stitch join95_103 join103_111

def aa111_113 : Circuit 192 := (H 143 :: diag111) ++ (H 142 :: diag112)

def bb111_113 : Circuit 192 := (H 143 :: opt111) ++ (H 142 :: opt112)

theorem join111_113 : res111 ++ aa111_113 ≡ᵤ bb111_113 ++ res113 := stitch step111 step112

def aa113_115 : Circuit 192 := (H 141 :: diag113) ++ (H 140 :: diag114)

def bb113_115 : Circuit 192 := (H 141 :: opt113) ++ (H 140 :: opt114)

theorem join113_115 : res113 ++ aa113_115 ≡ᵤ bb113_115 ++ res115 := stitch step113 step114

def aa111_115 : Circuit 192 := aa111_113 ++ aa113_115

def bb111_115 : Circuit 192 := bb111_113 ++ bb113_115

theorem join111_115 : res111 ++ aa111_115 ≡ᵤ bb111_115 ++ res115 := stitch join111_113 join113_115

def aa115_117 : Circuit 192 := (H 139 :: diag115) ++ (H 138 :: diag116)

def bb115_117 : Circuit 192 := (H 139 :: opt115) ++ (H 138 :: opt116)

theorem join115_117 : res115 ++ aa115_117 ≡ᵤ bb115_117 ++ res117 := stitch step115 step116

def aa117_119 : Circuit 192 := (H 137 :: diag117) ++ (H 136 :: diag118)

def bb117_119 : Circuit 192 := (H 137 :: opt117) ++ (H 136 :: opt118)

theorem join117_119 : res117 ++ aa117_119 ≡ᵤ bb117_119 ++ res119 := stitch step117 step118

def aa115_119 : Circuit 192 := aa115_117 ++ aa117_119

def bb115_119 : Circuit 192 := bb115_117 ++ bb117_119

theorem join115_119 : res115 ++ aa115_119 ≡ᵤ bb115_119 ++ res119 := stitch join115_117 join117_119

def aa111_119 : Circuit 192 := aa111_115 ++ aa115_119

def bb111_119 : Circuit 192 := bb111_115 ++ bb115_119

theorem join111_119 : res111 ++ aa111_119 ≡ᵤ bb111_119 ++ res119 := stitch join111_115 join115_119

def aa119_121 : Circuit 192 := (H 135 :: diag119) ++ (H 134 :: diag120)

def bb119_121 : Circuit 192 := (H 135 :: opt119) ++ (H 134 :: opt120)

theorem join119_121 : res119 ++ aa119_121 ≡ᵤ bb119_121 ++ res121 := stitch step119 step120

def aa121_123 : Circuit 192 := (H 133 :: diag121) ++ (H 132 :: diag122)

def bb121_123 : Circuit 192 := (H 133 :: opt121) ++ (H 132 :: opt122)

theorem join121_123 : res121 ++ aa121_123 ≡ᵤ bb121_123 ++ res123 := stitch step121 step122

def aa119_123 : Circuit 192 := aa119_121 ++ aa121_123

def bb119_123 : Circuit 192 := bb119_121 ++ bb121_123

theorem join119_123 : res119 ++ aa119_123 ≡ᵤ bb119_123 ++ res123 := stitch join119_121 join121_123

def aa123_125 : Circuit 192 := (H 131 :: diag123) ++ (H 130 :: diag124)

def bb123_125 : Circuit 192 := (H 131 :: opt123) ++ (H 130 :: opt124)

theorem join123_125 : res123 ++ aa123_125 ≡ᵤ bb123_125 ++ res125 := stitch step123 step124

def aa125_127 : Circuit 192 := (H 129 :: diag125) ++ (H 128 :: diag126)

def bb125_127 : Circuit 192 := (H 129 :: opt125) ++ (H 128 :: opt126)

theorem join125_127 : res125 ++ aa125_127 ≡ᵤ bb125_127 ++ res127 := stitch step125 step126

def aa123_127 : Circuit 192 := aa123_125 ++ aa125_127

def bb123_127 : Circuit 192 := bb123_125 ++ bb125_127

theorem join123_127 : res123 ++ aa123_127 ≡ᵤ bb123_127 ++ res127 := stitch join123_125 join125_127

def aa119_127 : Circuit 192 := aa119_123 ++ aa123_127

def bb119_127 : Circuit 192 := bb119_123 ++ bb123_127

theorem join119_127 : res119 ++ aa119_127 ≡ᵤ bb119_127 ++ res127 := stitch join119_123 join123_127

def aa111_127 : Circuit 192 := aa111_119 ++ aa119_127

def bb111_127 : Circuit 192 := bb111_119 ++ bb119_127

theorem join111_127 : res111 ++ aa111_127 ≡ᵤ bb111_127 ++ res127 := stitch join111_119 join119_127

def aa95_127 : Circuit 192 := aa95_111 ++ aa111_127

def bb95_127 : Circuit 192 := bb95_111 ++ bb111_127

theorem join95_127 : res95 ++ aa95_127 ≡ᵤ bb95_127 ++ res127 := stitch join95_111 join111_127

def aa63_127 : Circuit 192 := aa63_95 ++ aa95_127

def bb63_127 : Circuit 192 := bb63_95 ++ bb95_127

theorem join63_127 : res63 ++ aa63_127 ≡ᵤ bb63_127 ++ res127 := stitch join63_95 join95_127

theorem check_half1 : res63 ++ distributed diagGs1 ≡ᵤ distributed optGs1 ++ res127 := join63_127

theorem middle_sound : res63 ++ middle ≡ᵤ middle ++ res63 := blocks_disjoint _ _ (by decide +kernel)

theorem core_sound : distributed diagGs0 ++ middle ++ distributed diagGs1 ≡ᵤ distributed optGs0 ++ middle ++ distributed optGs1 := by
 have h := stitch (stitch check_half0 middle_sound) check_half1
 simpa only [res0, res127, List.nil_append, List.append_nil, List.append_assoc] using h

theorem original_shape : original = originalHalf0 ++ middle ++ originalHalf1 ++ finalH := by
 rfl

theorem optimized_shape : optimized = distributed optGs0 ++ middle ++ distributed optGs1 ++ finalH := by
 rfl

theorem equiv : original ≡ₚ optimized := by
 apply Equivalent.toUpToPhase
 rw [original_shape, optimized_shape]
 exact (((half_sound0.append (Equivalent.refl middle)).append half_sound1).trans core_sound).append (Equivalent.refl finalH)

end Quantum.Circuit.Harness