Accompanying artifact for the paper _Directed proof-relevant logical relations in simplicial HoTT_.

See [README.agda](./DPRLR/README.agda) for a tour of the code.

The formalization is checked against Agda v2.8.0 with cubical library v0.9. It covers the simply typed variant of the
proofs described in the paper, and is structured as follows:
- The `Simplicial` directory contains the added simplicial infrastructure on top of HoTT. 
- The `Object` directory contains the inductive definition of the object language and their corresponding CwF structure.
- The `Gluing` directory contains the definition of the gluing construction (a.k.a proof-relevant logical relations) on the inductively defined object language as a displayed model, and the proof of the fundamental lemma.

_AI disclosure_   
This artifact was written with the assistant of an AI agent codex. In particular, we find the AI tool very effective in
generating repetitive code patterns such as ones in `LocalizedCoherence.agda`, as well as in dealing with the
``transport hell'' such as that found in the substitutions clauses of the logical relations proof. This allowed us (human) to
focus on the more interesting parts of the formalization, such as the definition of the gluing construction and the
directed infrastructure. This artifact should therefore be seen only as a proof of concept, and we do not claim this is
the ideal way to formalize CwF style intrinsic syntax in Agda. 