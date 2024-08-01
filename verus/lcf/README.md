## Verified Kernel in Dafny

## Purpose 

## The purpose of this verified kernel is to encode a RuleSet corresponding to a set of Datalog rules and encode a set of facts( rules without bodies) in order to solve Datalog predicates. The major goal of this kernel is to one day encode a set of rules of criteria for verifiable X.509 web certificate fields and sets of facts corresponding to the fields' values in order to produce a theorem if the proof tree corresponding to these rules and facts is valid. 

## Data types of Kernel

## Const types 

## Verus specific features in implementation of kernel

## deep_view

## Missing features

## Toy Example of kernel working

## Future work

## We still need to: 1. Add support for builtinops 2. Make ghost versions for proof 3. Make examples meet all postcondtions and preconstions 4. Port trace reconstruction from Dafny to Verus
