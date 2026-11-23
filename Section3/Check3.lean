import Dense
import NearDense
import Asymptotic
import NearDense2
import SmallItems
import Examples
import NumerZero
import PathFork
import PathShape
import PathGreedy
import PathFactor
import PathMobius
import PathRows
import PathDefs
import PathChainBridge
import PathEvent
import PathCells
import PathCoeff
import PathCoeff2
import PathBlocks
import PathRowCount
import PathFixed
import PathFormula
import PathPrune
import PathExample

open GradientKey.Concrete

#check @prop_dense_cost
#check @prop_dense
#check @prop_near_dense_one
#check @prop_near_dense_two
#check @prop_small_m
#check @cor_exp
#check @excess_small
#check @Bint_nonneg
#check @Bint_numTypes
#check @Bint_small
#check @Bint_comb
#check @J_bounds
#check @coeffA_J
#check @numTypes_eq
#print axioms prop_dense
#print axioms prop_near_dense_one
#print axioms prop_near_dense_two
#print axioms prop_dense_cost
#print axioms prop_small_m
#print axioms cor_exp
#print axioms excess_small

-- Small items of Propositions 3.2 and 3.5
#check @prop32_stirling_identity
#check @prop32_stirling_form
#check @Bk_eq_tuple_sum
#check @numer_eq_zero_of_two_pow_lt
#check @numer_zero
#check @alt_sum_Bint
#check @example_full
#check @example_n1_m2
#check @example_m2
#check @example_n3_m4
#check @example_n4_m11
#check @example_n4_m10
#print axioms prop32_stirling_identity
#print axioms prop32_stirling_form
#print axioms Bk_eq_tuple_sum
#print axioms numer_eq_zero_of_two_pow_lt
#print axioms numer_zero
#print axioms alt_sum_Bint
#print axioms example_full
#print axioms example_n1_m2
#print axioms example_m2
#print axioms example_n3_m4
#print axioms example_n4_m11
#print axioms example_n4_m10
-- Proposition 3.1, steps (partial)
#check @tG_eq_forkTableCounts
#print axioms tG_eq_forkTableCounts
#check @pathCandidates_step_ssubset
#print axioms pathCandidates_step_ssubset
#check @pathFork_size_budget
#print axioms pathFork_size_budget
#check @pathOneStepTest_iff
#print axioms pathOneStepTest_iff
#check @mobius_table_indicator
#print axioms mobius_table_indicator
#check @card_valid_with_row_constraints
#print axioms card_valid_with_row_constraints
#check @fixedPath_card_factor
#print axioms fixedPath_card_factor
#check @fixedPath_mobius_factor
#print axioms fixedPath_mobius_factor
#check @pathChainOfFork_sizes
#print axioms pathChainOfFork_sizes
#check @candidateAt_of_rowwise
#print axioms candidateAt_of_rowwise
#check @rowwise_of_candidateAt
#print axioms rowwise_of_candidateAt
#check @rowwise_unique
#print axioms rowwise_unique
#check @path_indicator_eq_sum
#print axioms path_indicator_eq_sum
#check @card_path_eq
#print axioms card_path_eq
#check @cell_sep
#print axioms cell_sep
#check @distinct_iff_cells
#print axioms distinct_iff_cells
#check @distinct_indicator_cells
#print axioms distinct_indicator_cells
#check @card_path_cells
#print axioms card_path_cells
#check @coef_term1
#print axioms coef_term1
#check @coef_term2
#print axioms coef_term2
#check @coef_rec
#print axioms coef_rec
#check @tsum_rec
#print axioms tsum_rec
#check @tsum_eq_coef
#print axioms tsum_eq_coef
#check @sum_mu_by_type
#print axioms sum_mu_by_type
#check @ones_rowOf
#print axioms ones_rowOf
#check @adm_rowOf_iff
#print axioms adm_rowOf_iff
#check @card_rows_eq_blk
#print axioms card_rows_eq_blk
#check @rowcount_eq_blk
#print axioms rowcount_eq_blk
#check @card_blkAdm_equiv
#print axioms card_blkAdm_equiv
#check @rowcount_eq_cntU
#print axioms rowcount_eq_cntU
#check @sum_mu_pi
#print axioms sum_mu_pi
#check @cntU_W
#print axioms cntU_W
#check @cntU_V
#print axioms cntU_V
#check @card_path_fixed
#print axioms card_path_fixed
#check @card_pathFams
#print axioms card_pathFams
#check @chain_count
#print axioms chain_count
#check @prop_path_formula
#print axioms prop_path_formula
#check @path_shape_bounds
#print axioms path_shape_bounds
#check @prop_path_prune
#print axioms prop_path_prune
#check @GradientKey.Concrete.Example34.example34_coeff
#print axioms GradientKey.Concrete.Example34.example34_coeff
#check @GradientKey.Concrete.Example34.example34_W
#print axioms GradientKey.Concrete.Example34.example34_W
#check @GradientKey.Concrete.Example34.example34_V
#print axioms GradientKey.Concrete.Example34.example34_V
#check @GradientKey.Concrete.Example34.example34_F
#print axioms GradientKey.Concrete.Example34.example34_F
#check @GradientKey.Concrete.Example34.path_formula_n3_m4_total
#print axioms GradientKey.Concrete.Example34.path_formula_n3_m4_total
#check @chain_term_natural
#print axioms chain_term_natural
#check @chain_term_nonneg
#print axioms chain_term_nonneg
#check @path_chain_term_depth_zero
#print axioms path_chain_term_depth_zero
#check @GradientKey.Concrete.Example34.example34_chains
#print axioms GradientKey.Concrete.Example34.example34_chains
#check @GradientKey.Concrete.Example34.example34_chain4
#print axioms GradientKey.Concrete.Example34.example34_chain4
#check @GradientKey.Concrete.Example34.example34_chain42
#print axioms GradientKey.Concrete.Example34.example34_chain42
#check @GradientKey.Concrete.Example34.example34_chain43
#print axioms GradientKey.Concrete.Example34.example34_chain43
#check @GradientKey.Concrete.Example34.example34_chain432
#print axioms GradientKey.Concrete.Example34.example34_chain432
#check @GradientKey.Concrete.Example34.example34_F43
#print axioms GradientKey.Concrete.Example34.example34_F43
#check @GradientKey.Concrete.Example34.example34_F432
#print axioms GradientKey.Concrete.Example34.example34_F432
#check @GradientKey.Concrete.Example34.example34_rhs
#print axioms GradientKey.Concrete.Example34.example34_rhs
#check @GradientKey.Concrete.Example34.example34_tG
#print axioms GradientKey.Concrete.Example34.example34_tG
