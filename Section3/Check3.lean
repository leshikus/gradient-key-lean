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
import PathRecurrence
import BkInteger
import StrictFive
import ExactAnalytic
import Table2Small
import Interpolation
import Translation
import MaxLength

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

-- Small items of Propositions 3.3 and 3.6
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
-- Proposition 3.2, steps (partial)
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
#check @prop_path_formula_sets
#print axioms prop_path_formula_sets
#check @pathD_eq_sum
#print axioms pathD_eq_sum
#check @pathF_eq_pathD
#print axioms pathF_eq_pathD
#check @pathD_empty
#print axioms pathD_empty
#check @pathD_eq_zero_of_lt_card
#print axioms pathD_eq_zero_of_lt_card
#check @GradientKey.Concrete.Example34.example34_D
#print axioms GradientKey.Concrete.Example34.example34_D
#check @GradientKey.Concrete.Example34.example34_F_eq_D
#print axioms GradientKey.Concrete.Example34.example34_F_eq_D
#check @sum_ldepth_eq
#print axioms sum_ldepth_eq
#check @factorial_dvd_card
#print axioms factorial_dvd_card
#check @Bint_dvd
#print axioms Bint_dvd
#check @Bk_integer
#print axioms Bk_integer
#check @GradientKey.Concrete.strict_five
#print axioms GradientKey.Concrete.strict_five
#check @GradientKey.Concrete.exact_n1_m2
#print axioms GradientKey.Concrete.exact_n1_m2
#check @GradientKey.Concrete.exact_n2_m2
#print axioms GradientKey.Concrete.exact_n2_m2
#check @GradientKey.Concrete.exact_n2_m3
#print axioms GradientKey.Concrete.exact_n2_m3
#check @GradientKey.Concrete.exact_n2_m4
#print axioms GradientKey.Concrete.exact_n2_m4
#check @GradientKey.Concrete.exact_n3_m2
#print axioms GradientKey.Concrete.exact_n3_m2
#check @GradientKey.Concrete.exact_n3_m3
#print axioms GradientKey.Concrete.exact_n3_m3
#check @GradientKey.Concrete.exact_n3_m4
#print axioms GradientKey.Concrete.exact_n3_m4
#check @GradientKey.Concrete.exact_n3_m5
#print axioms GradientKey.Concrete.exact_n3_m5
#check @GradientKey.Concrete.exact_n3_m6
#print axioms GradientKey.Concrete.exact_n3_m6
#check @GradientKey.Concrete.exact_n3_m7
#print axioms GradientKey.Concrete.exact_n3_m7
#check @GradientKey.Concrete.exact_n3_m8
#print axioms GradientKey.Concrete.exact_n3_m8
#check @GradientKey.Concrete.exact_n4_m2
#print axioms GradientKey.Concrete.exact_n4_m2
#check @GradientKey.Concrete.exact_n4_m3
#print axioms GradientKey.Concrete.exact_n4_m3
#check @GradientKey.Concrete.exact_n4_m10
#print axioms GradientKey.Concrete.exact_n4_m10
#check @GradientKey.Concrete.exact_n4_m11
#print axioms GradientKey.Concrete.exact_n4_m11
#check @GradientKey.Concrete.exact_n4_m12
#print axioms GradientKey.Concrete.exact_n4_m12
#check @GradientKey.Concrete.exact_n4_m13
#print axioms GradientKey.Concrete.exact_n4_m13
#check @GradientKey.Concrete.exact_n4_m14
#print axioms GradientKey.Concrete.exact_n4_m14
#check @GradientKey.Concrete.exact_n4_m15
#print axioms GradientKey.Concrete.exact_n4_m15
#check @GradientKey.Concrete.exact_n4_m16
#print axioms GradientKey.Concrete.exact_n4_m16
#check @GradientKey.Concrete.exact_n5_m2
#print axioms GradientKey.Concrete.exact_n5_m2
#check @GradientKey.Concrete.exact_n5_m3
#print axioms GradientKey.Concrete.exact_n5_m3
#check @GradientKey.Concrete.exact_n5_m25
#print axioms GradientKey.Concrete.exact_n5_m25
#check @GradientKey.Concrete.exact_n5_m26
#print axioms GradientKey.Concrete.exact_n5_m26
#check @GradientKey.Concrete.exact_n5_m27
#print axioms GradientKey.Concrete.exact_n5_m27
#check @GradientKey.Concrete.exact_n5_m28
#print axioms GradientKey.Concrete.exact_n5_m28
#check @GradientKey.Concrete.exact_n5_m29
#print axioms GradientKey.Concrete.exact_n5_m29
#check @GradientKey.Concrete.exact_n5_m30
#print axioms GradientKey.Concrete.exact_n5_m30
#check @GradientKey.Concrete.exact_n5_m31
#print axioms GradientKey.Concrete.exact_n5_m31
#check @GradientKey.Concrete.exact_n5_m32
#print axioms GradientKey.Concrete.exact_n5_m32
#check @GradientKey.Concrete.exact_n6_m2
#print axioms GradientKey.Concrete.exact_n6_m2
#check @GradientKey.Concrete.exact_n6_m3
#print axioms GradientKey.Concrete.exact_n6_m3
#check @GradientKey.Concrete.exact_n6_m56
#print axioms GradientKey.Concrete.exact_n6_m56
#check @GradientKey.Concrete.exact_n6_m57
#print axioms GradientKey.Concrete.exact_n6_m57
#check @GradientKey.Concrete.exact_n6_m58
#print axioms GradientKey.Concrete.exact_n6_m58
#check @GradientKey.Concrete.exact_n6_m59
#print axioms GradientKey.Concrete.exact_n6_m59
#check @GradientKey.Concrete.exact_n6_m60
#print axioms GradientKey.Concrete.exact_n6_m60
#check @GradientKey.Concrete.exact_n6_m61
#print axioms GradientKey.Concrete.exact_n6_m61
#check @GradientKey.Concrete.exact_n6_m62
#print axioms GradientKey.Concrete.exact_n6_m62
#check @GradientKey.Concrete.exact_n6_m63
#print axioms GradientKey.Concrete.exact_n6_m63
#check @GradientKey.Concrete.exact_n6_m64
#print axioms GradientKey.Concrete.exact_n6_m64
#check @GradientKey.Concrete.table2_n1_bound
#print axioms GradientKey.Concrete.table2_n1_bound
#check @GradientKey.Concrete.table2_n1_attained
#print axioms GradientKey.Concrete.table2_n1_attained
#check @GradientKey.Concrete.table2_n2_bound
#print axioms GradientKey.Concrete.table2_n2_bound
#check @GradientKey.Concrete.table2_n2_attained
#print axioms GradientKey.Concrete.table2_n2_attained
#check @GradientKey.Concrete.table2_n3_bound
#print axioms GradientKey.Concrete.table2_n3_bound
#check @GradientKey.Concrete.table2_n3_attained
#print axioms GradientKey.Concrete.table2_n3_attained
#check @GradientKey.Concrete.table2_n3_unique
#print axioms GradientKey.Concrete.table2_n3_unique
#check @GradientKey.Concrete.sum_table_leafDepth_eq
#print axioms GradientKey.Concrete.sum_table_leafDepth_eq
#check @GradientKey.Concrete.scaled_tG_eq_column_sum
#print axioms GradientKey.Concrete.scaled_tG_eq_column_sum
#check @GradientKey.Concrete.tG_scaled_natural
#print axioms GradientKey.Concrete.tG_scaled_natural
#check @GradientKey.Concrete.numer_eq_scaled_sub
#print axioms GradientKey.Concrete.numer_eq_scaled_sub
#check @GradientKey.Concrete.coeffA_determined
#print axioms GradientKey.Concrete.coeffA_determined
#check @GradientKey.Concrete.sampleNumer_eq
#print axioms GradientKey.Concrete.sampleNumer_eq
#check @GradientKey.Concrete.coeffA_determined_samples
#print axioms GradientKey.Concrete.coeffA_determined_samples
#check @GradientKey.Concrete.translate_totalDepth
#print axioms GradientKey.Concrete.translate_totalDepth
#check @GradientKey.Concrete.translate_missing
#print axioms GradientKey.Concrete.translate_missing
#check @GradientKey.Concrete.missing_weighted_count
#print axioms GradientKey.Concrete.missing_weighted_count
#check @GradientKey.Concrete.missing_mean_eq_of_invariant
#print axioms GradientKey.Concrete.missing_mean_eq_of_invariant
#check @GradientKey.Concrete.totalDepth_eq_of_missing_eq
#print axioms GradientKey.Concrete.totalDepth_eq_of_missing_eq
#check @GradientKey.Concrete.missingDepth_eq_table
#print axioms GradientKey.Concrete.missingDepth_eq_table
#check @GradientKey.Concrete.sum_totalDepth_eq_missing
#print axioms GradientKey.Concrete.sum_totalDepth_eq_missing
#check @GradientKey.Concrete.missing_mean_eq
#print axioms GradientKey.Concrete.missing_mean_eq
#check @GradientKey.Concrete.sum_stat_eq
#print axioms GradientKey.Concrete.sum_stat_eq
#check @GradientKey.Concrete.statB_excess
#print axioms GradientKey.Concrete.statB_excess
#check @GradientKey.Concrete.sum_stat_numer
#print axioms GradientKey.Concrete.sum_stat_numer
#check @GradientKey.Concrete.prop_max_length
#print axioms GradientKey.Concrete.prop_max_length
#check @GradientKey.Concrete.prop_max_length_stirling
#print axioms GradientKey.Concrete.prop_max_length_stirling
