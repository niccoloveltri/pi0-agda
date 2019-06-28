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
- [Utilities.agda](https://github.com/niccoloveltri/pi0-agda/blob/master/code/Utilities.agda), part of the proof that types form a
rig groupoid, as in Carette and Sabry ESOP'16
- [pi0-syntax/Types.agda](https://github.com/niccoloveltri/pi0-agda/blob/master/code/pi0-syntax/Types.agda), types of Πo (Section 2.1)
- [pi0-syntax/1Programs.agda](https://github.com/niccoloveltri/pi0-agda/blob/master/code/pi0-syntax/1Programs.agda), terms of Πo (Section 2.2)
- [pi0-syntax/2Programs.agda](https://github.com/niccoloveltri/pi0-agda/blob/master/code/pi0-syntax/2Programs.agda), term equivalences of Πo
(Section 2.2)
- [delay/Delay.agda](https://github.com/niccoloveltri/pi0-agda/blob/master/code/delay/Delay.agda), delay datatype and weak bisimilarity (Section
  3) 
- [delay/Monad.agda](https://github.com/niccoloveltri/pi0-agda/blob/master/code/delay/Monad.agda), monad structure (Section 3) 
- [delay/Structure.agda](https://github.com/niccoloveltri/pi0-agda/blob/master/code/delay/Structure.agda), finite products and coproducts
(Section 3.1)
- [delay/PartialInv.agda](https://github.com/niccoloveltri/pi0-agda/blob/master/code/delay/PartialInv.agda), partial isomorphisms (Section 3.2)
- [delay/Elgot.agda](https://github.com/niccoloveltri/pi0-agda/blob/master/code/delay/Elgot.agda), Elgot iteration and dagger trace (Section 3.3
and 3.4)
- [pi0-semantics/Types.agda](https://github.com/niccoloveltri/pi0-agda/blob/master/code/pi0-semantics/Types.agda), interpretation of types (Section 6) 
- [pi0-semantics/1Programs.agda](https://github.com/niccoloveltri/pi0-agda/blob/master/code/pi0-semantics/1Programs.agda), interpretation of terms
  (Section 6) 
- [pi0-semantics/2Programs.agda](https://github.com/niccoloveltri/pi0-agda/blob/master/code/pi0-semantics/2Programs.agda), interpretation of term
equivalences (Section 6)

The formalization uses Agda 2.6.0.
