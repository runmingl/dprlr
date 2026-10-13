Accompanying artifact for the paper _Directed proof-relevant logical relations in simplicial HoTT_.

See [AEC.md](./AEC.md) and [README.agda](./DPRLR/README.agda) for artifact evaluation instructions.

The formalization is checked against Agda v2.8.0 with cubical library v0.9. It covers the simply typed variant of the
proofs described in the paper, and is structured as follows:
- The `Simplicial` directory contains the added simplicial infrastructure on top of HoTT. 
- The `Object` directory contains the inductive definition of the object language and their corresponding CwF structure.
- The `Gluing` directory contains the definition of the gluing construction (a.k.a proof-relevant logical relations) and
  the proof of the fundamental theorem.

###### _AI disclosure_

This artifact was written with the assistance of an AI agent. In particular, we find the AI tool effective in
generating repetitive code patterns, of which there are many in a formalization of metatheory.

The authors made all design decisions, including what to prove and how to prove it. AI was used only to help
fill in implementation details and repetitive code for proofs whose methods had already been determined by the
authors. The authors take full responsibility for the entire codebase.


###### _Inspirations_
This artifact takes inspiration from the following existing formalizations:
- The [Cubical Agda](https://github.com/agda/cubical) library.
- The [1Lab](https://1lab.dev/) project.
- The [Agda Synthetic Categories](https://samtoth.github.io/agda-synthetic-categories/index/index.xml) project.