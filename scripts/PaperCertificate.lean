import GlobalRegularization

/-! Coverage of the manuscript's mathematical theorem statements.
The spectrum equalities use the necessary nontriviality hypotheses.
Every named result below is a proved theorem or a constructed chart. -/

-- Theorem 1.1 (principal statement).
#check GlobalRegularization.mainClaim
#print axioms GlobalRegularization.mainClaim

-- Coordinate lemma and its derivative/spectrum/isotopy conclusions.
#check GlobalRegularization.localized_straightening_of_bounded_approximants
#check GlobalRegularization.C1Straightening.HasTriangularDerivative.spectrum_eq
#check GlobalRegularization.RealComplexification.norm_embed
#check GlobalRegularization.RealComplexification.decomposition
#check GlobalRegularization.RealComplexification.map_unique
#check GlobalRegularization.LocalizedHistoryStraightening.localized_isotopy_of_affine

-- Endpoint representation and endpoint-atom limit.
#check GlobalRegularization.historyFunctional_matrix_representation
#check GlobalRegularization.matrixHistoryFunctional_terminal_operator_limit
#check GlobalRegularization.matrixHistoryFunctional_terminal_zero_iff

-- Adapted-approximation lemma, with actual operators and an empty-family case.
#check GlobalRegularization.exists_adapted_operators_for_separable_family
#check GlobalRegularization.adaptedTerminalWidth_pos
#check GlobalRegularization.adaptedTerminalWidth_antitone
#check GlobalRegularization.adaptedTerminalWidth_tendsto

-- Stronger terminal-atom theorem, including its actual complex spectrum.
#check GlobalRegularization.terminal_atom_full_straightening
#check GlobalRegularization.terminal_atom_full_straightening_spectrum_inclusion
#print axioms GlobalRegularization.terminal_atom_full_straightening

-- All-level corollary, global split fiber charts, tangent and normal spaces.
#check GlobalRegularization.terminal_atom_all_levels
#check GlobalRegularization.terminal_atom_fiber_geometry
#check GlobalRegularization.C1Straightening.splitFiberParametrization
#check GlobalRegularization.C1Straightening.fiber_parameter_derivative
#check GlobalRegularization.C1Straightening.fiberTangent_range
#check GlobalRegularization.C1Straightening.continuous_complement_family
#check GlobalRegularization.C1Straightening.normal_dimension

-- Endpoint coupling and its corrected comparison example.
#check GlobalRegularization.terminal_atom_endpoint_coupling_of_isUnit
#check GlobalRegularization.no_endpoint_identity_straightening
#check GlobalRegularization.empty_domain_endpoint_identity_straightening
#check GlobalRegularization.endpointIdentityStraighteningOfSubsingleton

-- Remote observations and the concrete past-derivative example.
#check GlobalRegularization.remote_observation_full_straightening
#check GlobalRegularization.pastDerivative_full_straightening
#check GlobalRegularization.scalarPastDerivativeFeedback_no_extended_derivative_at_zero

-- Infinite-dimensional separable Hilbert spaces, with genuine cutoffs.
#check GlobalRegularization.exists_hilbert_C1_cutoff
#check GlobalRegularization.property_e_Hilbert_bounded_C1_approximants
#check GlobalRegularization.property_e_Hilbert_full_straightening
#check GlobalRegularization.property_e_Hilbert_straightening_spectrum_inclusion
#print axioms GlobalRegularization.property_e_Hilbert_full_straightening

-- A machine-checked counterexample to the uncorrected zero-space equality.
#check GlobalRegularization.zero_space_identity_spectrum_ne_one
