This is the artifact associated with Section 6.3 in the paper. The entries in
Table 1 as well as the information in the section regarding the McCarthy 91
function can all be justified with this code.

The first column in Table 1 corresponds to an associated file in this
directory. The second column represents the number of recursive definitions that
needed to be unfolded in proving each lemma.

<!-- heaplet definitions functional for convenience, could be modeled as relations -->
<!-- (and are when proving heaplet props) -->

All files correspond to entries in Table 1 of the paper, with the exception of
`hlseg_lemmas/hlseg_lemma2.smt2`, which is a lemma used for verification of
other properties that is valid without adding an induction principle, and the
McCarthy 91 function (`mccarthy.smt2`).

The user must have z3 installed. 

Running the command `z3 file.smt2` will run the inputted file, and check if the
negation of the lemma is unsatisfiable, generally both with and without the
added induction principle. We refer to the weaker induction principle as the one
seen at the beginning of Section 6.1, denoted $IP$ in the paper, and the
stronger induction principle as the one seen at the end of Section 6.1, denoted
$IP_s$.

The user can run the script `test_all.sh`, which checks if the last invocation of
`(check-sat)` in all files returns `unsat` (the negation of the claim
unsatisfiable implies the claim is valid).
