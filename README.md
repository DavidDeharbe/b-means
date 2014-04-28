Introduction
============

The goal of this project is to define a framework to reason formally about the B method. 

At the core of the project is the definition of a formal semantics for B in 
the logic of a proof assistant, namely Isabelle/HOL.

Roadmap
=======

* B components as state-transition systems. 

** Define the notion of reachability.

** Show some basic properties about reachability.

* Observable behaviour of a B component as a set of traces.

* B refinement, relates a (concrete) component together with
an (abstract) component, using through a gluing relation between
their state space. 

* Composition of refinements.

** Define an identity refinement, show it is neutral for the
composition of refinements.

** Property: transitivity.

* Enrich the semantics associating input and outputs to the transitions.

