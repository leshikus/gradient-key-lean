import Theorem44
import Lemma41
import Lemma43
import Hoeffding
import GradientKeySection4

open GradientKey.Concrete

#check @theorem_4_4
#print tG
#print cost
#print leafDepth
#print displayedBound
#print GradientKey.Concrete.greedyRow
#print GradientKey.Concrete.candidateStep
#print axioms theorem_4_4

-- Lemmas 4.1–4.3 on the concrete sample space
#check @GradientKey.Concrete.concrete_expectedExcess_succ
#print axioms GradientKey.Concrete.concrete_expectedExcess_succ
#check @GradientKey.FinitePathData.expectedTail
#print axioms GradientKey.FinitePathData.expectedTail
#check @GradientKey.Concrete.concrete_expectedTail
#print axioms GradientKey.Concrete.concrete_expectedTail
#check @GradientKey.Concrete.expectedDepth_eq_tG
#print axioms GradientKey.Concrete.expectedDepth_eq_tG
#check @GradientKey.RowDeletion.conditional_inserted_imbalance_le_one
#print axioms GradientKey.RowDeletion.conditional_inserted_imbalance_le_one
#check @GradientKey.RowDeletion.conditional_inserted_imbalance_tail
#print axioms GradientKey.RowDeletion.conditional_inserted_imbalance_tail
#check @GradientKey.Concrete.expectedImbalance_le_rows
#print axioms GradientKey.Concrete.expectedImbalance_le_rows
#check @GradientKey.Concrete.expectedImbalance_le_log
#print axioms GradientKey.Concrete.expectedImbalance_le_log
