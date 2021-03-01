## (paper 0) On Etiology of Cybersecurity 

**Authors**: The Science Club [@V-Research](http://v-research.it) (knowledgezero@v-research.it)

**Abstract**: The objective of this research is the development of a theory that defines (all
and only) the possible insecurity and security configurations of any
abstract system. The theory is structured upon other theories that
defines how a component of a system can be abstracted into an agent,
defining how agents can be formalized (both syntactically and
semantically) to describe an abstract system, such as a graph. The core
theories are the epistemological definition of knowledge, Beliefs, and
Information, the Assertion-Belief-Fact framework, and mereotopology.
We implemented a formal theory (of axioms) of a mereotopology, and of
the Region Connection Calculus (RCC3 and RCC5) in a Python program that
uses the Z3 SMT solver. The results show that a single component (i.e.
agent) of an abstract system has a definite number of  different
insecurity configurations (e.g. 53 using RCC5 over a topological
structure) and only 1 secure (i.e.  expected) configuration. The
configurations are reported as models satisfying the abstract system
semantics. We use these results to predict all possible security
weaknesses of a system, instead of relying on databases of known
weaknesses, and to lay the foundations of a scientific theory of
cybersecurity.  We show a concrete applications of our theory to the
risk assessment of an ad-hoc system.

- [PDF](./paper_0/main.pdf)
- [Source](./paper_0)
- [Slides](../presentations/presentation_0.pdf)
- [License](./LICENSE.md)

```
@online{TheScienceClub2020Etiology,
  author    = {Science-Club, The},
  title     = {On Etiology of Cybersecurity},
  year      = {2020},
  url       = {https://github.com/v-research/cybersecurity/tree/marco/reports/paper_0}
}
```
