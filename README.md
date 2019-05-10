# En Garde! Unguarded Iteration for Reversible Computation in the Delay Monad

## Robin Kaarsgaard and Niccolò Veltri

Reversible computation studies computations which exhibit both forward
and backward determinism. Among others, it has been studied for half a
century for its applications in low-power computing, and forms the
basis for quantum computing.

Though certified program equivalence is useful for a number of
applications (e.g., certified compilation and optimization), little
work on this topic has been carried out for reversible programming
languages. As a notable exception, Carette and Sabry have studied the
equivalences of the finitary fragment of Πo, a reversible combinator
calculus, yielding a two-level calculus of type isomorphisms and
equivalences between them. In this paper, we extend the two-level
calculus of finitary Πo to one for full Πo (i.e., with both recursive
types and iteration by means of a trace combinator) using the delay
monad, which can be regarded as a “computability-aware” analogue of
the usual maybe monad for partiality. This yields a calculus of
iterative (and possibly non-terminating) reversible programs acting on
user-defined dynamic data structures together with a calculus of
certified program equivalences between these programs.

Structure of the code:
- code/Utilities.agda, contains (part of) the proof that types form a
rig groupoid, which is part of Carette and Sabry ESOP'16

- code/pi0-syntax/Types.agda, types of Πo (Section 2.1)
- code/pi0-syntax/1Programs.agda, terms of Πo (Section 2.2)
- code/pi0-syntax/2Programs.agda, term equivalences of Πo
(Section 2.2)

- code/delay/Delay.agda, delay datatype and weak bisimilarity (Section
  3) 
- code/delay/Monad.agda, monad structure (Section 3) 
- code/delay/Structure.agda, finite products and coproducts
(Section 3.1)
- code/delay/PartialInv.agda, partial isomorphisms (Section 3.2)
- code/delay/Elgot.agda, Elgot iteration and dagger trace (Section 3.3
and 3.4)

- code/pi0-semantics/Types.agda, interpretation of types (Section 6) 
- code/pi0-semantics/1Programs.agda, interpretation of terms
  (Section 6) 
- code/pi0-semantics/2Programs.agda, interpretation of term
equivalences (Section 6)



