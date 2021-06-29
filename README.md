# lean_portmanteau

A Lean formalization of Portmanteau's theorem.

This was mainly an exercise for myself to get familiar with Lean and mathlib.

## The main definition

Let X be a topological space. The "set" of Borel probability measures on X is equipped with the topology of weak convergence, defined as follows. The topology is induced by the mapping that takes a probability measure to the functional that takes a continuous bounded extended non-negative real valued function to its integral against the measure, when such functionals are first equipped with the topology of pointwise (testfunctionwise) convergence. This is contained in <portmanteau_definitions.lean>.

## The main statement

The main statements are summarized (and its proof finished) in <portmanteau_conclusions.lean>.

In the case of a general topological space X, the main statement is the equivalence of the following conditions for a sequence (P_n) of Borel probability measures on X:
 1. The sequence (P_n) converges in the topology of weak convergence to P.
 2. For any continuous bounded extended non-negative real valued function f, the Lebesgue integrals of f against P_n tend to the Lebesgue integral of f against P.
 3. For any continuous bounded real valued function f, the Bochner integrals of f against P_n tend to the Bochner integral of f against P.

In the case of a metric space X, the main statement is the equivalence of the following conditions for a sequence (P_n) of Borel probability measures on X:
 1. The sequence (P_n) converges in the topology of weak convergence to P.
 2. For any continuous bounded extended non-negative real valued function f, the Lebesgue integrals of f against P_n tend to the Lebesgue integral of f against P.
 3. For any continuous bounded real valued function f, the Bochner integrals of f against P_n tend to the Bochner integral of f against P.
 4. For any open set G in X, we have liminf P_n(G) >= P(G).
 5. For any closed set F in X, we have limsup P_n(F) <= P(F).
 6. For any Borel set B in X such that P(bdry B) = 0, we have lim P_n(B) = P(B).
