import FermatHodge

/-! Prints the axioms behind the main theorems.  Expected: `propext`, `Classical.choice`,
`Quot.sound` for each, and no `sorryAx`.  The primed theorems are the classification and the
Fermat fourfold theorem with `BernoulliNV` discharged by `bernoulliNV`. -/

#print axioms FermatHodge.quadruple
#print axioms FermatHodge.sextuple
#print axioms FermatHodge.hodge_quadruple
#print axioms FermatHodge.hodge_sextuple
#print axioms FermatHodge.hodge_fermat_fourfold
#print axioms FermatHodge.bernoulliNV
#print axioms FermatHodge.quadruple'
#print axioms FermatHodge.sextuple'
#print axioms FermatHodge.hodge_quadruple'
#print axioms FermatHodge.hodge_sextuple'
#print axioms FermatHodge.hodge_fermat_fourfold'
