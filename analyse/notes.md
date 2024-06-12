# Towards Formally Verified Rule Language Compilers

## Central Question 
How can we adapt (proof) techniques from the field of formally verified compilers to the verification
of Datalog reasoning engines?

## Subquestions
### 1 how does nemo's (or a general rule engine's) input look like?
  the rule language is a datalog extension (which exactly?),
  stratified negation, existential rule heads
  
  - 1.1 regarding syntax and semantics
  - 1.2 what rule langugages are there that are used in rule engies?
  - 1.3 can they be classified regarding expressivity?
### 2 how could one specify datalog reasoning (i.e. processing of input) (e.g. in lean)?
  - 2.1 how does nemo process datalog?
        or vlog, ddlog, soufflé?
  - 2.2 and what is the best way to process the input?
  - 2.3 how did people already do it?
  - 2.4 what can their implementations do and what problems did they cause? (e.g. regarding proofs)
  - 2.5 what questions were left to them?
  - 2.6 what language (coq/lean/other) did they use?
  - 2.7 can one re-use their work?
### 3 how to formalize the semantics of the rule language (e.g. semantics of datalog) (e.g. in lean)?
  - 3.1 how did people already do it?
  - 3.2 and what problems did their implementation cause?
  - 3.3 what questions were left to them?
### 4 what are (high-lvl to low-lvl) transformations inside the engine to be adressed by the formalization?
  - 4.1 are any of them comparable to those of the field of compiler verification?
  - 4.2 which one need to be thought of completely from the scratch?
  - 4.3 how to formalize them (e.g. in lean)?
### 5 can the analyzed proof techniques help in the re-interpretation task?
