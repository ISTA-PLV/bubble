module

public import Iris.BI
public import Iris.ProofMode
public import Bubble

@[expose] public section

namespace BubbleTest.Benchmark.Generated
open Iris Iris.BI

set_option Elab.async false
set_option maxRecDepth 10000

#eval IO.println "BENCH propositions=10 pairs=5 requested_density=0.200000 realized_density=0.200000 conflicts=2"
set_option linter.unusedVariables false in
#time
set_option maxHeartbeats 2000000 in
theorem bench_robustness_p10_d20 [BI PROP]
    (P0 P1 P2 P3 P4 Q0 Q1 Q2 : PROP)
    (Q3 Q4 : PROP)
    -- Canonical rules
    (hCanon0 : P0 ⊢ Q0)
    (hCanon1 : P1 ⊢ Q1)
    (hCanon2 : P2 ⊢ Q2)
    (hCanon3 : P3 ⊢ Q3)
    (hCanon4 : P4 ⊢ Q4)
    -- Decoy rules
    (hDecoy0 : P3 ⊢ Q0)
    (hDecoy1 : P2 ⊢ Q0)
    : P0 ∗ P4 ∗ P1 ∗ P2 ∗ P3 ⊢
      Q3 ∗ Q1 ∗ Q0 ∗ Q2 ∗ Q4 := by
  ibubble maxDepth 100
/- benchmark-metadata: {"conflictEdges":[[3,0],[2,0]],"conflicts":2,"family":"triangular-resource-contention","maximumConflicts":10,"propositions":10,"realizedDensity":0.2,"requestedDensity":0.2,"resourceOrder":[0,4,1,2,3],"resourceTargetPairs":5,"ruleRepresentation":"lean-entailment-hypothesis","seed":42,"targetOrder":[3,1,0,2,4]} -/

#eval IO.println "BENCH propositions=20 pairs=10 requested_density=0.200000 realized_density=0.200000 conflicts=9"
set_option linter.unusedVariables false in
#time
set_option maxHeartbeats 2000000 in
theorem bench_robustness_p20_d20 [BI PROP]
    (P0 P1 P2 P3 P4 P5 P6 P7 : PROP)
    (P8 P9 Q0 Q1 Q2 Q3 Q4 Q5 : PROP)
    (Q6 Q7 Q8 Q9 : PROP)
    -- Canonical rules
    (hCanon0 : P0 ⊢ Q0)
    (hCanon1 : P1 ⊢ Q1)
    (hCanon2 : P2 ⊢ Q2)
    (hCanon3 : P3 ⊢ Q3)
    (hCanon4 : P4 ⊢ Q4)
    (hCanon5 : P5 ⊢ Q5)
    (hCanon6 : P6 ⊢ Q6)
    (hCanon7 : P7 ⊢ Q7)
    (hCanon8 : P8 ⊢ Q8)
    (hCanon9 : P9 ⊢ Q9)
    -- Decoy rules
    (hDecoy0 : P7 ⊢ Q1)
    (hDecoy1 : P9 ⊢ Q4)
    (hDecoy2 : P7 ⊢ Q0)
    (hDecoy3 : P6 ⊢ Q0)
    (hDecoy4 : P8 ⊢ Q3)
    (hDecoy5 : P5 ⊢ Q2)
    (hDecoy6 : P3 ⊢ Q1)
    (hDecoy7 : P6 ⊢ Q5)
    (hDecoy8 : P9 ⊢ Q5)
    : P5 ∗ P4 ∗ P1 ∗ P3 ∗ P7 ∗ P8 ∗ P2 ∗ P6 ∗ P0 ∗ P9 ⊢
      Q5 ∗ Q9 ∗ Q3 ∗ Q1 ∗ Q2 ∗ Q6 ∗ Q4 ∗ Q7 ∗ Q0 ∗ Q8 := by
  ibubble maxDepth 100
/- benchmark-metadata: {"conflictEdges":[[7,1],[9,4],[7,0],[6,0],[8,3],[5,2],[3,1],[6,5],[9,5]],"conflicts":9,"family":"triangular-resource-contention","maximumConflicts":45,"propositions":20,"realizedDensity":0.2,"requestedDensity":0.2,"resourceOrder":[5,4,1,3,7,8,2,6,0,9],"resourceTargetPairs":10,"ruleRepresentation":"lean-entailment-hypothesis","seed":42,"targetOrder":[5,9,3,1,2,6,4,7,0,8]} -/

#eval IO.println "BENCH propositions=30 pairs=15 requested_density=0.200000 realized_density=0.200000 conflicts=21"
set_option linter.unusedVariables false in
#time
set_option maxHeartbeats 2000000 in
theorem bench_robustness_p30_d20 [BI PROP]
    (P0 P1 P2 P3 P4 P5 P6 P7 : PROP)
    (P8 P9 P10 P11 P12 P13 P14 Q0 : PROP)
    (Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 : PROP)
    (Q9 Q10 Q11 Q12 Q13 Q14 : PROP)
    -- Canonical rules
    (hCanon0 : P0 ⊢ Q0)
    (hCanon1 : P1 ⊢ Q1)
    (hCanon2 : P2 ⊢ Q2)
    (hCanon3 : P3 ⊢ Q3)
    (hCanon4 : P4 ⊢ Q4)
    (hCanon5 : P5 ⊢ Q5)
    (hCanon6 : P6 ⊢ Q6)
    (hCanon7 : P7 ⊢ Q7)
    (hCanon8 : P8 ⊢ Q8)
    (hCanon9 : P9 ⊢ Q9)
    (hCanon10 : P10 ⊢ Q10)
    (hCanon11 : P11 ⊢ Q11)
    (hCanon12 : P12 ⊢ Q12)
    (hCanon13 : P13 ⊢ Q13)
    (hCanon14 : P14 ⊢ Q14)
    -- Decoy rules
    (hDecoy0 : P12 ⊢ Q3)
    (hDecoy1 : P14 ⊢ Q6)
    (hDecoy2 : P10 ⊢ Q5)
    (hDecoy3 : P9 ⊢ Q7)
    (hDecoy4 : P11 ⊢ Q6)
    (hDecoy5 : P11 ⊢ Q7)
    (hDecoy6 : P7 ⊢ Q5)
    (hDecoy7 : P13 ⊢ Q0)
    (hDecoy8 : P10 ⊢ Q4)
    (hDecoy9 : P6 ⊢ Q4)
    (hDecoy10 : P11 ⊢ Q3)
    (hDecoy11 : P14 ⊢ Q11)
    (hDecoy12 : P4 ⊢ Q2)
    (hDecoy13 : P12 ⊢ Q9)
    (hDecoy14 : P14 ⊢ Q12)
    (hDecoy15 : P11 ⊢ Q1)
    (hDecoy16 : P10 ⊢ Q7)
    (hDecoy17 : P9 ⊢ Q2)
    (hDecoy18 : P12 ⊢ Q6)
    (hDecoy19 : P11 ⊢ Q8)
    (hDecoy20 : P2 ⊢ Q1)
    : P9 ∗ P1 ∗ P8 ∗ P11 ∗ P14 ∗ P4 ∗ P13 ∗ P2 ∗ P12 ∗ P6 ∗ P7 ∗ P3 ∗ P5 ∗ P0 ∗ P10 ⊢
      Q11 ∗ Q12 ∗ Q13 ∗ Q8 ∗ Q10 ∗ Q3 ∗ Q9 ∗ Q6 ∗ Q4 ∗ Q14 ∗ Q5 ∗ Q2 ∗ Q7 ∗ Q1 ∗ Q0 := by
  ibubble maxDepth 100
/- benchmark-metadata: {"conflictEdges":[[12,3],[14,6],[10,5],[9,7],[11,6],[11,7],[7,5],[13,0],[10,4],[6,4],[11,3],[14,11],[4,2],[12,9],[14,12],[11,1],[10,7],[9,2],[12,6],[11,8],[2,1]],"conflicts":21,"family":"triangular-resource-contention","maximumConflicts":105,"propositions":30,"realizedDensity":0.2,"requestedDensity":0.2,"resourceOrder":[9,1,8,11,14,4,13,2,12,6,7,3,5,0,10],"resourceTargetPairs":15,"ruleRepresentation":"lean-entailment-hypothesis","seed":42,"targetOrder":[11,12,13,8,10,3,9,6,4,14,5,2,7,1,0]} -/

#eval IO.println "BENCH propositions=40 pairs=20 requested_density=0.200000 realized_density=0.200000 conflicts=38"
set_option linter.unusedVariables false in
#time
set_option maxHeartbeats 2000000 in
theorem bench_robustness_p40_d20 [BI PROP]
    (P0 P1 P2 P3 P4 P5 P6 P7 : PROP)
    (P8 P9 P10 P11 P12 P13 P14 P15 : PROP)
    (P16 P17 P18 P19 Q0 Q1 Q2 Q3 : PROP)
    (Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 : PROP)
    (Q12 Q13 Q14 Q15 Q16 Q17 Q18 Q19 : PROP)
    -- Canonical rules
    (hCanon0 : P0 ⊢ Q0)
    (hCanon1 : P1 ⊢ Q1)
    (hCanon2 : P2 ⊢ Q2)
    (hCanon3 : P3 ⊢ Q3)
    (hCanon4 : P4 ⊢ Q4)
    (hCanon5 : P5 ⊢ Q5)
    (hCanon6 : P6 ⊢ Q6)
    (hCanon7 : P7 ⊢ Q7)
    (hCanon8 : P8 ⊢ Q8)
    (hCanon9 : P9 ⊢ Q9)
    (hCanon10 : P10 ⊢ Q10)
    (hCanon11 : P11 ⊢ Q11)
    (hCanon12 : P12 ⊢ Q12)
    (hCanon13 : P13 ⊢ Q13)
    (hCanon14 : P14 ⊢ Q14)
    (hCanon15 : P15 ⊢ Q15)
    (hCanon16 : P16 ⊢ Q16)
    (hCanon17 : P17 ⊢ Q17)
    (hCanon18 : P18 ⊢ Q18)
    (hCanon19 : P19 ⊢ Q19)
    -- Decoy rules
    (hDecoy0 : P19 ⊢ Q11)
    (hDecoy1 : P18 ⊢ Q12)
    (hDecoy2 : P6 ⊢ Q1)
    (hDecoy3 : P16 ⊢ Q10)
    (hDecoy4 : P7 ⊢ Q2)
    (hDecoy5 : P6 ⊢ Q2)
    (hDecoy6 : P7 ⊢ Q1)
    (hDecoy7 : P16 ⊢ Q6)
    (hDecoy8 : P13 ⊢ Q4)
    (hDecoy9 : P15 ⊢ Q1)
    (hDecoy10 : P14 ⊢ Q2)
    (hDecoy11 : P4 ⊢ Q1)
    (hDecoy12 : P13 ⊢ Q1)
    (hDecoy13 : P12 ⊢ Q1)
    (hDecoy14 : P15 ⊢ Q9)
    (hDecoy15 : P18 ⊢ Q15)
    (hDecoy16 : P10 ⊢ Q2)
    (hDecoy17 : P13 ⊢ Q11)
    (hDecoy18 : P3 ⊢ Q0)
    (hDecoy19 : P18 ⊢ Q0)
    (hDecoy20 : P13 ⊢ Q7)
    (hDecoy21 : P18 ⊢ Q5)
    (hDecoy22 : P19 ⊢ Q12)
    (hDecoy23 : P11 ⊢ Q10)
    (hDecoy24 : P6 ⊢ Q5)
    (hDecoy25 : P14 ⊢ Q8)
    (hDecoy26 : P16 ⊢ Q11)
    (hDecoy27 : P17 ⊢ Q16)
    (hDecoy28 : P14 ⊢ Q7)
    (hDecoy29 : P18 ⊢ Q16)
    (hDecoy30 : P11 ⊢ Q0)
    (hDecoy31 : P7 ⊢ Q6)
    (hDecoy32 : P19 ⊢ Q13)
    (hDecoy33 : P12 ⊢ Q10)
    (hDecoy34 : P15 ⊢ Q10)
    (hDecoy35 : P11 ⊢ Q8)
    (hDecoy36 : P16 ⊢ Q3)
    (hDecoy37 : P16 ⊢ Q4)
    : P16 ∗ P5 ∗ P7 ∗ P2 ∗ P18 ∗ P3 ∗ P10 ∗ P13 ∗ P6 ∗ P4 ∗ P0 ∗ P9 ∗ P8 ∗ P11 ∗ P15 ∗ P17 ∗ P1 ∗ P19 ∗ P12 ∗ P14 ⊢
      Q14 ∗ Q13 ∗ Q10 ∗ Q7 ∗ Q16 ∗ Q8 ∗ Q15 ∗ Q17 ∗ Q3 ∗ Q4 ∗ Q6 ∗ Q1 ∗ Q12 ∗ Q9 ∗ Q18 ∗ Q0 ∗ Q2 ∗ Q11 ∗ Q19 ∗ Q5 := by
  ibubble maxDepth 100
/- benchmark-metadata: {"conflictEdges":[[19,11],[18,12],[6,1],[16,10],[7,2],[6,2],[7,1],[16,6],[13,4],[15,1],[14,2],[4,1],[13,1],[12,1],[15,9],[18,15],[10,2],[13,11],[3,0],[18,0],[13,7],[18,5],[19,12],[11,10],[6,5],[14,8],[16,11],[17,16],[14,7],[18,16],[11,0],[7,6],[19,13],[12,10],[15,10],[11,8],[16,3],[16,4]],"conflicts":38,"family":"triangular-resource-contention","maximumConflicts":190,"propositions":40,"realizedDensity":0.2,"requestedDensity":0.2,"resourceOrder":[16,5,7,2,18,3,10,13,6,4,0,9,8,11,15,17,1,19,12,14],"resourceTargetPairs":20,"ruleRepresentation":"lean-entailment-hypothesis","seed":42,"targetOrder":[14,13,10,7,16,8,15,17,3,4,6,1,12,9,18,0,2,11,19,5]} -/

#eval IO.println "BENCH propositions=50 pairs=25 requested_density=0.200000 realized_density=0.200000 conflicts=60"
set_option linter.unusedVariables false in
#time
set_option maxHeartbeats 4000000 in
theorem bench_robustness_p50_d20 [BI PROP]
    (P0 P1 P2 P3 P4 P5 P6 P7 : PROP)
    (P8 P9 P10 P11 P12 P13 P14 P15 : PROP)
    (P16 P17 P18 P19 P20 P21 P22 P23 : PROP)
    (P24 Q0 Q1 Q2 Q3 Q4 Q5 Q6 : PROP)
    (Q7 Q8 Q9 Q10 Q11 Q12 Q13 Q14 : PROP)
    (Q15 Q16 Q17 Q18 Q19 Q20 Q21 Q22 : PROP)
    (Q23 Q24 : PROP)
    -- Canonical rules
    (hCanon0 : P0 ⊢ Q0)
    (hCanon1 : P1 ⊢ Q1)
    (hCanon2 : P2 ⊢ Q2)
    (hCanon3 : P3 ⊢ Q3)
    (hCanon4 : P4 ⊢ Q4)
    (hCanon5 : P5 ⊢ Q5)
    (hCanon6 : P6 ⊢ Q6)
    (hCanon7 : P7 ⊢ Q7)
    (hCanon8 : P8 ⊢ Q8)
    (hCanon9 : P9 ⊢ Q9)
    (hCanon10 : P10 ⊢ Q10)
    (hCanon11 : P11 ⊢ Q11)
    (hCanon12 : P12 ⊢ Q12)
    (hCanon13 : P13 ⊢ Q13)
    (hCanon14 : P14 ⊢ Q14)
    (hCanon15 : P15 ⊢ Q15)
    (hCanon16 : P16 ⊢ Q16)
    (hCanon17 : P17 ⊢ Q17)
    (hCanon18 : P18 ⊢ Q18)
    (hCanon19 : P19 ⊢ Q19)
    (hCanon20 : P20 ⊢ Q20)
    (hCanon21 : P21 ⊢ Q21)
    (hCanon22 : P22 ⊢ Q22)
    (hCanon23 : P23 ⊢ Q23)
    (hCanon24 : P24 ⊢ Q24)
    -- Decoy rules
    (hDecoy0 : P5 ⊢ Q1)
    (hDecoy1 : P20 ⊢ Q5)
    (hDecoy2 : P18 ⊢ Q4)
    (hDecoy3 : P23 ⊢ Q8)
    (hDecoy4 : P9 ⊢ Q1)
    (hDecoy5 : P11 ⊢ Q0)
    (hDecoy6 : P10 ⊢ Q8)
    (hDecoy7 : P15 ⊢ Q3)
    (hDecoy8 : P21 ⊢ Q19)
    (hDecoy9 : P22 ⊢ Q14)
    (hDecoy10 : P16 ⊢ Q3)
    (hDecoy11 : P17 ⊢ Q2)
    (hDecoy12 : P17 ⊢ Q6)
    (hDecoy13 : P11 ⊢ Q4)
    (hDecoy14 : P14 ⊢ Q5)
    (hDecoy15 : P13 ⊢ Q4)
    (hDecoy16 : P20 ⊢ Q1)
    (hDecoy17 : P12 ⊢ Q5)
    (hDecoy18 : P22 ⊢ Q17)
    (hDecoy19 : P16 ⊢ Q4)
    (hDecoy20 : P23 ⊢ Q16)
    (hDecoy21 : P16 ⊢ Q0)
    (hDecoy22 : P21 ⊢ Q16)
    (hDecoy23 : P17 ⊢ Q15)
    (hDecoy24 : P20 ⊢ Q7)
    (hDecoy25 : P3 ⊢ Q2)
    (hDecoy26 : P13 ⊢ Q12)
    (hDecoy27 : P9 ⊢ Q2)
    (hDecoy28 : P19 ⊢ Q14)
    (hDecoy29 : P19 ⊢ Q0)
    (hDecoy30 : P12 ⊢ Q7)
    (hDecoy31 : P22 ⊢ Q21)
    (hDecoy32 : P13 ⊢ Q9)
    (hDecoy33 : P16 ⊢ Q12)
    (hDecoy34 : P22 ⊢ Q18)
    (hDecoy35 : P14 ⊢ Q0)
    (hDecoy36 : P10 ⊢ Q7)
    (hDecoy37 : P7 ⊢ Q3)
    (hDecoy38 : P19 ⊢ Q17)
    (hDecoy39 : P4 ⊢ Q1)
    (hDecoy40 : P24 ⊢ Q4)
    (hDecoy41 : P13 ⊢ Q7)
    (hDecoy42 : P1 ⊢ Q0)
    (hDecoy43 : P22 ⊢ Q2)
    (hDecoy44 : P21 ⊢ Q5)
    (hDecoy45 : P21 ⊢ Q6)
    (hDecoy46 : P12 ⊢ Q9)
    (hDecoy47 : P18 ⊢ Q17)
    (hDecoy48 : P22 ⊢ Q0)
    (hDecoy49 : P22 ⊢ Q11)
    (hDecoy50 : P24 ⊢ Q22)
    (hDecoy51 : P12 ⊢ Q0)
    (hDecoy52 : P13 ⊢ Q3)
    (hDecoy53 : P22 ⊢ Q7)
    (hDecoy54 : P10 ⊢ Q5)
    (hDecoy55 : P19 ⊢ Q7)
    (hDecoy56 : P23 ⊢ Q12)
    (hDecoy57 : P14 ⊢ Q9)
    (hDecoy58 : P22 ⊢ Q3)
    (hDecoy59 : P18 ⊢ Q13)
    : P21 ∗ P12 ∗ P8 ∗ P23 ∗ P22 ∗ P2 ∗ P4 ∗ P1 ∗ P6 ∗ P10 ∗ P3 ∗ P7 ∗ P24 ∗ P19 ∗ P20 ∗ P5 ∗ P9 ∗ P14 ∗ P13 ∗ P11 ∗ P16 ∗ P0 ∗ P17 ∗ P15 ∗ P18 ⊢
      Q1 ∗ Q22 ∗ Q14 ∗ Q2 ∗ Q21 ∗ Q3 ∗ Q13 ∗ Q17 ∗ Q10 ∗ Q16 ∗ Q11 ∗ Q4 ∗ Q15 ∗ Q19 ∗ Q5 ∗ Q0 ∗ Q7 ∗ Q23 ∗ Q9 ∗ Q20 ∗ Q6 ∗ Q8 ∗ Q18 ∗ Q12 ∗ Q24 := by
  ibubble maxDepth 500
/- benchmark-metadata: {"conflictEdges":[[5,1],[20,5],[18,4],[23,8],[9,1],[11,0],[10,8],[15,3],[21,19],[22,14],[16,3],[17,2],[17,6],[11,4],[14,5],[13,4],[20,1],[12,5],[22,17],[16,4],[23,16],[16,0],[21,16],[17,15],[20,7],[3,2],[13,12],[9,2],[19,14],[19,0],[12,7],[22,21],[13,9],[16,12],[22,18],[14,0],[10,7],[7,3],[19,17],[4,1],[24,4],[13,7],[1,0],[22,2],[21,5],[21,6],[12,9],[18,17],[22,0],[22,11],[24,22],[12,0],[13,3],[22,7],[10,5],[19,7],[23,12],[14,9],[22,3],[18,13]],"conflicts":60,"family":"triangular-resource-contention","maximumConflicts":300,"propositions":50,"realizedDensity":0.2,"requestedDensity":0.2,"resourceOrder":[21,12,8,23,22,2,4,1,6,10,3,7,24,19,20,5,9,14,13,11,16,0,17,15,18],"resourceTargetPairs":25,"ruleRepresentation":"lean-entailment-hypothesis","seed":42,"targetOrder":[1,22,14,2,21,3,13,17,10,16,11,4,15,19,5,0,7,23,9,20,6,8,18,12,24]} -/

#eval IO.println "BENCH propositions=30 pairs=15 requested_density=0.000000 realized_density=0.000000 conflicts=0"
set_option linter.unusedVariables false in
#time
set_option maxHeartbeats 2000000 in
theorem bench_robustness_p30_d0 [BI PROP]
    (P0 P1 P2 P3 P4 P5 P6 P7 : PROP)
    (P8 P9 P10 P11 P12 P13 P14 Q0 : PROP)
    (Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 : PROP)
    (Q9 Q10 Q11 Q12 Q13 Q14 : PROP)
    -- Canonical rules
    (hCanon0 : P0 ⊢ Q0)
    (hCanon1 : P1 ⊢ Q1)
    (hCanon2 : P2 ⊢ Q2)
    (hCanon3 : P3 ⊢ Q3)
    (hCanon4 : P4 ⊢ Q4)
    (hCanon5 : P5 ⊢ Q5)
    (hCanon6 : P6 ⊢ Q6)
    (hCanon7 : P7 ⊢ Q7)
    (hCanon8 : P8 ⊢ Q8)
    (hCanon9 : P9 ⊢ Q9)
    (hCanon10 : P10 ⊢ Q10)
    (hCanon11 : P11 ⊢ Q11)
    (hCanon12 : P12 ⊢ Q12)
    (hCanon13 : P13 ⊢ Q13)
    (hCanon14 : P14 ⊢ Q14)
    -- Decoy rules
    : P9 ∗ P1 ∗ P8 ∗ P11 ∗ P14 ∗ P4 ∗ P13 ∗ P2 ∗ P12 ∗ P6 ∗ P7 ∗ P3 ∗ P5 ∗ P0 ∗ P10 ⊢
      Q11 ∗ Q12 ∗ Q13 ∗ Q8 ∗ Q10 ∗ Q3 ∗ Q9 ∗ Q6 ∗ Q4 ∗ Q14 ∗ Q5 ∗ Q2 ∗ Q7 ∗ Q1 ∗ Q0 := by
  ibubble maxDepth 100
/- benchmark-metadata: {"conflictEdges":[],"conflicts":0,"family":"triangular-resource-contention","maximumConflicts":105,"propositions":30,"realizedDensity":0.0,"requestedDensity":0.0,"resourceOrder":[9,1,8,11,14,4,13,2,12,6,7,3,5,0,10],"resourceTargetPairs":15,"ruleRepresentation":"lean-entailment-hypothesis","seed":42,"targetOrder":[11,12,13,8,10,3,9,6,4,14,5,2,7,1,0]} -/

#eval IO.println "BENCH propositions=30 pairs=15 requested_density=0.400000 realized_density=0.400000 conflicts=42"
set_option linter.unusedVariables false in
#time
set_option maxHeartbeats 2000000 in
theorem bench_robustness_p30_d40 [BI PROP]
    (P0 P1 P2 P3 P4 P5 P6 P7 : PROP)
    (P8 P9 P10 P11 P12 P13 P14 Q0 : PROP)
    (Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 : PROP)
    (Q9 Q10 Q11 Q12 Q13 Q14 : PROP)
    -- Canonical rules
    (hCanon0 : P0 ⊢ Q0)
    (hCanon1 : P1 ⊢ Q1)
    (hCanon2 : P2 ⊢ Q2)
    (hCanon3 : P3 ⊢ Q3)
    (hCanon4 : P4 ⊢ Q4)
    (hCanon5 : P5 ⊢ Q5)
    (hCanon6 : P6 ⊢ Q6)
    (hCanon7 : P7 ⊢ Q7)
    (hCanon8 : P8 ⊢ Q8)
    (hCanon9 : P9 ⊢ Q9)
    (hCanon10 : P10 ⊢ Q10)
    (hCanon11 : P11 ⊢ Q11)
    (hCanon12 : P12 ⊢ Q12)
    (hCanon13 : P13 ⊢ Q13)
    (hCanon14 : P14 ⊢ Q14)
    -- Decoy rules
    (hDecoy0 : P12 ⊢ Q3)
    (hDecoy1 : P14 ⊢ Q6)
    (hDecoy2 : P10 ⊢ Q5)
    (hDecoy3 : P9 ⊢ Q7)
    (hDecoy4 : P11 ⊢ Q6)
    (hDecoy5 : P11 ⊢ Q7)
    (hDecoy6 : P7 ⊢ Q5)
    (hDecoy7 : P13 ⊢ Q0)
    (hDecoy8 : P10 ⊢ Q4)
    (hDecoy9 : P6 ⊢ Q4)
    (hDecoy10 : P11 ⊢ Q3)
    (hDecoy11 : P14 ⊢ Q11)
    (hDecoy12 : P4 ⊢ Q2)
    (hDecoy13 : P12 ⊢ Q9)
    (hDecoy14 : P14 ⊢ Q12)
    (hDecoy15 : P11 ⊢ Q1)
    (hDecoy16 : P10 ⊢ Q7)
    (hDecoy17 : P9 ⊢ Q2)
    (hDecoy18 : P12 ⊢ Q6)
    (hDecoy19 : P11 ⊢ Q8)
    (hDecoy20 : P2 ⊢ Q1)
    (hDecoy21 : P4 ⊢ Q1)
    (hDecoy22 : P7 ⊢ Q4)
    (hDecoy23 : P13 ⊢ Q8)
    (hDecoy24 : P12 ⊢ Q4)
    (hDecoy25 : P14 ⊢ Q2)
    (hDecoy26 : P11 ⊢ Q9)
    (hDecoy27 : P8 ⊢ Q3)
    (hDecoy28 : P14 ⊢ Q13)
    (hDecoy29 : P10 ⊢ Q2)
    (hDecoy30 : P5 ⊢ Q2)
    (hDecoy31 : P6 ⊢ Q1)
    (hDecoy32 : P10 ⊢ Q1)
    (hDecoy33 : P10 ⊢ Q9)
    (hDecoy34 : P14 ⊢ Q4)
    (hDecoy35 : P12 ⊢ Q5)
    (hDecoy36 : P5 ⊢ Q4)
    (hDecoy37 : P7 ⊢ Q1)
    (hDecoy38 : P9 ⊢ Q4)
    (hDecoy39 : P5 ⊢ Q3)
    (hDecoy40 : P8 ⊢ Q5)
    (hDecoy41 : P13 ⊢ Q9)
    : P9 ∗ P1 ∗ P8 ∗ P11 ∗ P14 ∗ P4 ∗ P13 ∗ P2 ∗ P12 ∗ P6 ∗ P7 ∗ P3 ∗ P5 ∗ P0 ∗ P10 ⊢
      Q11 ∗ Q12 ∗ Q13 ∗ Q8 ∗ Q10 ∗ Q3 ∗ Q9 ∗ Q6 ∗ Q4 ∗ Q14 ∗ Q5 ∗ Q2 ∗ Q7 ∗ Q1 ∗ Q0 := by
  ibubble maxDepth 100
/- benchmark-metadata: {"conflictEdges":[[12,3],[14,6],[10,5],[9,7],[11,6],[11,7],[7,5],[13,0],[10,4],[6,4],[11,3],[14,11],[4,2],[12,9],[14,12],[11,1],[10,7],[9,2],[12,6],[11,8],[2,1],[4,1],[7,4],[13,8],[12,4],[14,2],[11,9],[8,3],[14,13],[10,2],[5,2],[6,1],[10,1],[10,9],[14,4],[12,5],[5,4],[7,1],[9,4],[5,3],[8,5],[13,9]],"conflicts":42,"family":"triangular-resource-contention","maximumConflicts":105,"propositions":30,"realizedDensity":0.4,"requestedDensity":0.4,"resourceOrder":[9,1,8,11,14,4,13,2,12,6,7,3,5,0,10],"resourceTargetPairs":15,"ruleRepresentation":"lean-entailment-hypothesis","seed":42,"targetOrder":[11,12,13,8,10,3,9,6,4,14,5,2,7,1,0]} -/

#eval IO.println "BENCH propositions=30 pairs=15 requested_density=0.600000 realized_density=0.600000 conflicts=63"
set_option linter.unusedVariables false in
#time
set_option maxHeartbeats 2000000 in
theorem bench_robustness_p30_d60 [BI PROP]
    (P0 P1 P2 P3 P4 P5 P6 P7 : PROP)
    (P8 P9 P10 P11 P12 P13 P14 Q0 : PROP)
    (Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 : PROP)
    (Q9 Q10 Q11 Q12 Q13 Q14 : PROP)
    -- Canonical rules
    (hCanon0 : P0 ⊢ Q0)
    (hCanon1 : P1 ⊢ Q1)
    (hCanon2 : P2 ⊢ Q2)
    (hCanon3 : P3 ⊢ Q3)
    (hCanon4 : P4 ⊢ Q4)
    (hCanon5 : P5 ⊢ Q5)
    (hCanon6 : P6 ⊢ Q6)
    (hCanon7 : P7 ⊢ Q7)
    (hCanon8 : P8 ⊢ Q8)
    (hCanon9 : P9 ⊢ Q9)
    (hCanon10 : P10 ⊢ Q10)
    (hCanon11 : P11 ⊢ Q11)
    (hCanon12 : P12 ⊢ Q12)
    (hCanon13 : P13 ⊢ Q13)
    (hCanon14 : P14 ⊢ Q14)
    -- Decoy rules
    (hDecoy0 : P12 ⊢ Q3)
    (hDecoy1 : P14 ⊢ Q6)
    (hDecoy2 : P10 ⊢ Q5)
    (hDecoy3 : P9 ⊢ Q7)
    (hDecoy4 : P11 ⊢ Q6)
    (hDecoy5 : P11 ⊢ Q7)
    (hDecoy6 : P7 ⊢ Q5)
    (hDecoy7 : P13 ⊢ Q0)
    (hDecoy8 : P10 ⊢ Q4)
    (hDecoy9 : P6 ⊢ Q4)
    (hDecoy10 : P11 ⊢ Q3)
    (hDecoy11 : P14 ⊢ Q11)
    (hDecoy12 : P4 ⊢ Q2)
    (hDecoy13 : P12 ⊢ Q9)
    (hDecoy14 : P14 ⊢ Q12)
    (hDecoy15 : P11 ⊢ Q1)
    (hDecoy16 : P10 ⊢ Q7)
    (hDecoy17 : P9 ⊢ Q2)
    (hDecoy18 : P12 ⊢ Q6)
    (hDecoy19 : P11 ⊢ Q8)
    (hDecoy20 : P2 ⊢ Q1)
    (hDecoy21 : P4 ⊢ Q1)
    (hDecoy22 : P7 ⊢ Q4)
    (hDecoy23 : P13 ⊢ Q8)
    (hDecoy24 : P12 ⊢ Q4)
    (hDecoy25 : P14 ⊢ Q2)
    (hDecoy26 : P11 ⊢ Q9)
    (hDecoy27 : P8 ⊢ Q3)
    (hDecoy28 : P14 ⊢ Q13)
    (hDecoy29 : P10 ⊢ Q2)
    (hDecoy30 : P5 ⊢ Q2)
    (hDecoy31 : P6 ⊢ Q1)
    (hDecoy32 : P10 ⊢ Q1)
    (hDecoy33 : P10 ⊢ Q9)
    (hDecoy34 : P14 ⊢ Q4)
    (hDecoy35 : P12 ⊢ Q5)
    (hDecoy36 : P5 ⊢ Q4)
    (hDecoy37 : P7 ⊢ Q1)
    (hDecoy38 : P9 ⊢ Q4)
    (hDecoy39 : P5 ⊢ Q3)
    (hDecoy40 : P8 ⊢ Q5)
    (hDecoy41 : P13 ⊢ Q9)
    (hDecoy42 : P12 ⊢ Q7)
    (hDecoy43 : P12 ⊢ Q2)
    (hDecoy44 : P6 ⊢ Q3)
    (hDecoy45 : P5 ⊢ Q0)
    (hDecoy46 : P6 ⊢ Q0)
    (hDecoy47 : P8 ⊢ Q1)
    (hDecoy48 : P10 ⊢ Q8)
    (hDecoy49 : P7 ⊢ Q6)
    (hDecoy50 : P13 ⊢ Q3)
    (hDecoy51 : P4 ⊢ Q3)
    (hDecoy52 : P12 ⊢ Q10)
    (hDecoy53 : P11 ⊢ Q4)
    (hDecoy54 : P7 ⊢ Q2)
    (hDecoy55 : P11 ⊢ Q10)
    (hDecoy56 : P14 ⊢ Q1)
    (hDecoy57 : P11 ⊢ Q0)
    (hDecoy58 : P13 ⊢ Q10)
    (hDecoy59 : P8 ⊢ Q0)
    (hDecoy60 : P6 ⊢ Q2)
    (hDecoy61 : P13 ⊢ Q4)
    (hDecoy62 : P4 ⊢ Q0)
    : P9 ∗ P1 ∗ P8 ∗ P11 ∗ P14 ∗ P4 ∗ P13 ∗ P2 ∗ P12 ∗ P6 ∗ P7 ∗ P3 ∗ P5 ∗ P0 ∗ P10 ⊢
      Q11 ∗ Q12 ∗ Q13 ∗ Q8 ∗ Q10 ∗ Q3 ∗ Q9 ∗ Q6 ∗ Q4 ∗ Q14 ∗ Q5 ∗ Q2 ∗ Q7 ∗ Q1 ∗ Q0 := by
  ibubble maxDepth 100
/- benchmark-metadata: {"conflictEdges":[[12,3],[14,6],[10,5],[9,7],[11,6],[11,7],[7,5],[13,0],[10,4],[6,4],[11,3],[14,11],[4,2],[12,9],[14,12],[11,1],[10,7],[9,2],[12,6],[11,8],[2,1],[4,1],[7,4],[13,8],[12,4],[14,2],[11,9],[8,3],[14,13],[10,2],[5,2],[6,1],[10,1],[10,9],[14,4],[12,5],[5,4],[7,1],[9,4],[5,3],[8,5],[13,9],[12,7],[12,2],[6,3],[5,0],[6,0],[8,1],[10,8],[7,6],[13,3],[4,3],[12,10],[11,4],[7,2],[11,10],[14,1],[11,0],[13,10],[8,0],[6,2],[13,4],[4,0]],"conflicts":63,"family":"triangular-resource-contention","maximumConflicts":105,"propositions":30,"realizedDensity":0.6,"requestedDensity":0.6,"resourceOrder":[9,1,8,11,14,4,13,2,12,6,7,3,5,0,10],"resourceTargetPairs":15,"ruleRepresentation":"lean-entailment-hypothesis","seed":42,"targetOrder":[11,12,13,8,10,3,9,6,4,14,5,2,7,1,0]} -/

#eval IO.println "BENCH propositions=30 pairs=15 requested_density=0.800000 realized_density=0.800000 conflicts=84"
set_option linter.unusedVariables false in
#time
set_option maxHeartbeats 2000000 in
theorem bench_robustness_p30_d80 [BI PROP]
    (P0 P1 P2 P3 P4 P5 P6 P7 : PROP)
    (P8 P9 P10 P11 P12 P13 P14 Q0 : PROP)
    (Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 : PROP)
    (Q9 Q10 Q11 Q12 Q13 Q14 : PROP)
    -- Canonical rules
    (hCanon0 : P0 ⊢ Q0)
    (hCanon1 : P1 ⊢ Q1)
    (hCanon2 : P2 ⊢ Q2)
    (hCanon3 : P3 ⊢ Q3)
    (hCanon4 : P4 ⊢ Q4)
    (hCanon5 : P5 ⊢ Q5)
    (hCanon6 : P6 ⊢ Q6)
    (hCanon7 : P7 ⊢ Q7)
    (hCanon8 : P8 ⊢ Q8)
    (hCanon9 : P9 ⊢ Q9)
    (hCanon10 : P10 ⊢ Q10)
    (hCanon11 : P11 ⊢ Q11)
    (hCanon12 : P12 ⊢ Q12)
    (hCanon13 : P13 ⊢ Q13)
    (hCanon14 : P14 ⊢ Q14)
    -- Decoy rules
    (hDecoy0 : P12 ⊢ Q3)
    (hDecoy1 : P14 ⊢ Q6)
    (hDecoy2 : P10 ⊢ Q5)
    (hDecoy3 : P9 ⊢ Q7)
    (hDecoy4 : P11 ⊢ Q6)
    (hDecoy5 : P11 ⊢ Q7)
    (hDecoy6 : P7 ⊢ Q5)
    (hDecoy7 : P13 ⊢ Q0)
    (hDecoy8 : P10 ⊢ Q4)
    (hDecoy9 : P6 ⊢ Q4)
    (hDecoy10 : P11 ⊢ Q3)
    (hDecoy11 : P14 ⊢ Q11)
    (hDecoy12 : P4 ⊢ Q2)
    (hDecoy13 : P12 ⊢ Q9)
    (hDecoy14 : P14 ⊢ Q12)
    (hDecoy15 : P11 ⊢ Q1)
    (hDecoy16 : P10 ⊢ Q7)
    (hDecoy17 : P9 ⊢ Q2)
    (hDecoy18 : P12 ⊢ Q6)
    (hDecoy19 : P11 ⊢ Q8)
    (hDecoy20 : P2 ⊢ Q1)
    (hDecoy21 : P4 ⊢ Q1)
    (hDecoy22 : P7 ⊢ Q4)
    (hDecoy23 : P13 ⊢ Q8)
    (hDecoy24 : P12 ⊢ Q4)
    (hDecoy25 : P14 ⊢ Q2)
    (hDecoy26 : P11 ⊢ Q9)
    (hDecoy27 : P8 ⊢ Q3)
    (hDecoy28 : P14 ⊢ Q13)
    (hDecoy29 : P10 ⊢ Q2)
    (hDecoy30 : P5 ⊢ Q2)
    (hDecoy31 : P6 ⊢ Q1)
    (hDecoy32 : P10 ⊢ Q1)
    (hDecoy33 : P10 ⊢ Q9)
    (hDecoy34 : P14 ⊢ Q4)
    (hDecoy35 : P12 ⊢ Q5)
    (hDecoy36 : P5 ⊢ Q4)
    (hDecoy37 : P7 ⊢ Q1)
    (hDecoy38 : P9 ⊢ Q4)
    (hDecoy39 : P5 ⊢ Q3)
    (hDecoy40 : P8 ⊢ Q5)
    (hDecoy41 : P13 ⊢ Q9)
    (hDecoy42 : P12 ⊢ Q7)
    (hDecoy43 : P12 ⊢ Q2)
    (hDecoy44 : P6 ⊢ Q3)
    (hDecoy45 : P5 ⊢ Q0)
    (hDecoy46 : P6 ⊢ Q0)
    (hDecoy47 : P8 ⊢ Q1)
    (hDecoy48 : P10 ⊢ Q8)
    (hDecoy49 : P7 ⊢ Q6)
    (hDecoy50 : P13 ⊢ Q3)
    (hDecoy51 : P4 ⊢ Q3)
    (hDecoy52 : P12 ⊢ Q10)
    (hDecoy53 : P11 ⊢ Q4)
    (hDecoy54 : P7 ⊢ Q2)
    (hDecoy55 : P11 ⊢ Q10)
    (hDecoy56 : P14 ⊢ Q1)
    (hDecoy57 : P11 ⊢ Q0)
    (hDecoy58 : P13 ⊢ Q10)
    (hDecoy59 : P8 ⊢ Q0)
    (hDecoy60 : P6 ⊢ Q2)
    (hDecoy61 : P13 ⊢ Q4)
    (hDecoy62 : P4 ⊢ Q0)
    (hDecoy63 : P11 ⊢ Q2)
    (hDecoy64 : P8 ⊢ Q4)
    (hDecoy65 : P5 ⊢ Q1)
    (hDecoy66 : P11 ⊢ Q5)
    (hDecoy67 : P7 ⊢ Q3)
    (hDecoy68 : P14 ⊢ Q5)
    (hDecoy69 : P13 ⊢ Q1)
    (hDecoy70 : P3 ⊢ Q1)
    (hDecoy71 : P12 ⊢ Q0)
    (hDecoy72 : P14 ⊢ Q7)
    (hDecoy73 : P10 ⊢ Q3)
    (hDecoy74 : P12 ⊢ Q1)
    (hDecoy75 : P10 ⊢ Q6)
    (hDecoy76 : P14 ⊢ Q3)
    (hDecoy77 : P9 ⊢ Q6)
    (hDecoy78 : P13 ⊢ Q2)
    (hDecoy79 : P9 ⊢ Q0)
    (hDecoy80 : P7 ⊢ Q0)
    (hDecoy81 : P14 ⊢ Q0)
    (hDecoy82 : P8 ⊢ Q6)
    (hDecoy83 : P14 ⊢ Q10)
    : P9 ∗ P1 ∗ P8 ∗ P11 ∗ P14 ∗ P4 ∗ P13 ∗ P2 ∗ P12 ∗ P6 ∗ P7 ∗ P3 ∗ P5 ∗ P0 ∗ P10 ⊢
      Q11 ∗ Q12 ∗ Q13 ∗ Q8 ∗ Q10 ∗ Q3 ∗ Q9 ∗ Q6 ∗ Q4 ∗ Q14 ∗ Q5 ∗ Q2 ∗ Q7 ∗ Q1 ∗ Q0 := by
  ibubble maxDepth 100
/- benchmark-metadata: {"conflictEdges":[[12,3],[14,6],[10,5],[9,7],[11,6],[11,7],[7,5],[13,0],[10,4],[6,4],[11,3],[14,11],[4,2],[12,9],[14,12],[11,1],[10,7],[9,2],[12,6],[11,8],[2,1],[4,1],[7,4],[13,8],[12,4],[14,2],[11,9],[8,3],[14,13],[10,2],[5,2],[6,1],[10,1],[10,9],[14,4],[12,5],[5,4],[7,1],[9,4],[5,3],[8,5],[13,9],[12,7],[12,2],[6,3],[5,0],[6,0],[8,1],[10,8],[7,6],[13,3],[4,3],[12,10],[11,4],[7,2],[11,10],[14,1],[11,0],[13,10],[8,0],[6,2],[13,4],[4,0],[11,2],[8,4],[5,1],[11,5],[7,3],[14,5],[13,1],[3,1],[12,0],[14,7],[10,3],[12,1],[10,6],[14,3],[9,6],[13,2],[9,0],[7,0],[14,0],[8,6],[14,10]],"conflicts":84,"family":"triangular-resource-contention","maximumConflicts":105,"propositions":30,"realizedDensity":0.8,"requestedDensity":0.8,"resourceOrder":[9,1,8,11,14,4,13,2,12,6,7,3,5,0,10],"resourceTargetPairs":15,"ruleRepresentation":"lean-entailment-hypothesis","seed":42,"targetOrder":[11,12,13,8,10,3,9,6,4,14,5,2,7,1,0]} -/

end BubbleTest.Benchmark.Generated
