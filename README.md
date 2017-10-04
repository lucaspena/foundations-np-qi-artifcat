This is the artifact associated with Section 6.3 in the paper. The entries in
Table 1 as well as the information in the section regarding the McCarthy 91
function can all be justified with this code. The user must have z3 installed.

The first column in Table 1 corresponds to an associated file in this
directory. The only smt2 file not in Table 1 is `mccarthy.smt2`, which
corresponds to the McCarthy 91 function mentioned at the end of the section. The
second column represents the number of recursive definitions that needed to be
unfolded in proving each lemma. It is important to note that these definitions
were unfolded manually, not in any systematic or automatic way.

However, the third column represents the depth at which the definitions need to
be unfolded. At depth 1 are all the ground terms originally present in the lemma
we are trying to prove. These include skolemized constants as well as constants
seen in the induction principles added. At depth 2 are all ground terms from
depth 1, and those which arise from one unfolding of the recursive definitions,
and so on. Thus, while the definitions were unfolded manually, any automatic
procedure would unfold the same definitions relatively quickly, since the
maximum depth unfolded for all examples in Section 6.3 is 2.

In the examples from Table 1 (besides `hlseg_lemma.smt2`), we represent the
heaplet functionally for convenience. However, we represent it as a recursive
definition when proving the property in `hlseg_lemma.smt2` that is necessary in
proving some other lemmas.

Running the command `z3 file.smt2` will run the inputted file, and check if the
negation of the lemma is unsatisfiable, generally both with and without the
added induction principle. We refer to the weaker induction principle as the one
seen at the beginning of Section 6.1, denoted $IP$ in the paper, and the
stronger induction principle as the one seen at the end of Section 6.1, denoted
$IP_s$.

The user can run the script `test_all.sh`, which checks if the last invocation of
`(check-sat)` in all files returns `unsat` (the negation of the claim
unsatisfiable implies the claim is valid).
