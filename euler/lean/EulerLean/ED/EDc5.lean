import EDc4
import EDc2

/-!
# EDc5.lean   (UNTESTED until compiled by CI)

Composition only.  `EDc4.hprime204_of_rpeigen : RPEigen → HPrime204Restricted` followed by
`EDc2.H31gt3A_of_hprime204 : HPrime204Restricted → H31gt3A` gives the end-to-end implication
`RPEigen → H31gt3A`.

This proves NO new mathematics.  It is a one-line composition of two checked implications, recorded so that the whole
chain from the single external hypothesis to the target statement is one gated theorem.  `RPEigen` remains OPEN and
is not proved in this development.
-/

namespace EDc5

theorem H31gt3A_of_rpeigen (hR : EDc4.RPEigen) : EDcDefs.H31gt3A :=
  EDc2.H31gt3A_of_hprime204 (EDc4.hprime204_of_rpeigen hR)

end EDc5

#print axioms EDc5.H31gt3A_of_rpeigen
