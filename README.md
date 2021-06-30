# lean_portmanteau

A Lean formalization of the Portmanteau Theorem.

This was mainly an exercise for myself to get familiar with Lean and mathlib.



## The main definition

Let X be a topological space. The "set" of Borel probability measures on X is equipped with the topology of weak convergence, defined as follows. The topology is induced by the mapping that takes a probability measure to the functional that takes a continuous bounded extended non-negative real valued function to its integral against the measure, when such functionals are first equipped with the topology of pointwise (testfunctionwise) convergence. This is contained in _<portmanteau_definitions.lean>_.



## The main statement

The main statements are summarized (and its proof finished) in _<portmanteau_conclusions.lean>_.

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



## Comments

 * In fact the equivalence of 1-5 is proven for topological spaces X where the indicator of every closed set has a pointwise decreasing approximation by bounded continuous functions.



## Perspectives

 * In the case of the real line, there are two additional useful characterizations: one in terms of cumulative distribution functions and another in terms of characteristic functions. Proving the equivalence with the former should be quite easy. Proving the equivalence with the latter requires Lévy's inversion theorem or some other suitable form of Fourier analysis of measures, and some form of tightness argument (Helly's selection theorem specific to the real line, or ideally Prokhorov's theorem).
   * After proving the characterization of weak convergence on the real line with characteristic functions, the proof of the Central Limit Theorem should be quite doable.
 * In complete separable metric spaces X (or Polish spaces), the topology of weak convergence of Borel probability measures is metrizable by the Lévy-Prokhorov metric. Proving this should not be particularly difficult given Portmanteau's theorem above.
 * Proving Prokhorov's theorem would be much nicer!



