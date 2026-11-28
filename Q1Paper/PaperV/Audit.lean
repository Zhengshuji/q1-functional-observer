import Q1Paper.PaperV.MainTheorems

/-!
Q1Paper/PaperV/Audit.lean

The axiom footprint of every declaration of Paper V's Lean development.

Hand-written (the Paper V tree is small; `scripts/generate_audit.py` generates the
Paper II counterpart).  Every audited declaration must depend only on `propext`,
`Classical.choice` and `Quot.sound`; `scripts/check_paperI_axioms.py` enforces this on
the output of `lake env lean Q1Paper/PaperV/Audit.lean`.
-/

-- Fibre.lean
#print axioms Q1Paper.PaperV.fibre
#print axioms Q1Paper.PaperV.mem_fibre
#print axioms Q1Paper.PaperV.fibre_nonempty_iff
#print axioms Q1Paper.PaperV.fibre_eq_coset
#print axioms Q1Paper.PaperV.fibre_prod_nonempty_iff

-- LeadingCoeff.lean
#print axioms Q1Paper.PaperV.coeff_det_smul_sub_X
#print axioms Q1Paper.PaperV.coeff_det_smul_sub_X_ne_zero

-- ColumnDrop.lean
#print axioms Q1Paper.PaperV.rank_le_card_compl_of_cols_zero

-- Specialize.lean
#print axioms Q1Paper.PaperV.natDegree_map_eval_of_leadingCoeff_const
#print axioms Q1Paper.PaperV.map_dvd_of_dvd
#print axioms Q1Paper.PaperV.specialized_common_factor
