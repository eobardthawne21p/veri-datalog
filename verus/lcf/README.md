## Verified Kernel in Dafny

## Purpose 

## The purpose of this verified kernel is to encode a RuleSet corresponding to a set of Datalog rules and encode a set of facts( rules without bodies) in order to solve Datalog predicates. The major goal of this kernel is to one day encode a set of rules of criteria for verifiable X.509 web certificate fields and sets of facts corresponding to the fields' values in order to produce a theorem if the proof tree corresponding to these rules and facts is valid. 

## Data types of Kernel

## Const 

## Term

## Prop

## Rule

## Ruleset

## Proof

## Thm

## mk-leaf and mk_thm

## mk_lf and mk_thm are called in the functions that you will write that will take take rulesets, Subst types, indexes of rules to apply, and arguments that will be used to determine if the proof tree is valid. In the toy example that will be shown, the ruleset is constructed manually by the programmer, and then the separate function testing the trace through the rules will produce a theorem if the trace is valid and return err if it is not. In the toy example and future toy examples used, it is useful to draw out the proof tree and then use mk_leaf to construct nodes of the tree that are terminal points. You can call mk_lf to call intermediate nodes and follow the trace until it's natural termination. Once the final thm has been produced, run Ok on that last thm.

## Verus specific features in implementation of kernel                  

One Verus specific feature in the implementation of the kernel is the separation between spec and exec code. Exec code is executable code such as functions susbt, mk_lf, and mk_thm that are commonly used in the kernel and are compileed. Spec code is code that reasons about the exec code without compiling and returns errors to the verifier if the code is not correct. Another is the use of loop invariants, triggers, assertions, and lemmas that were used to aid the verifier in reasoning about preconditions, postconditions, and recommendations. The ones left are essential for kernel verification, so do not remove them. They have been thoroughly commented and described in the code body.

Another verus specific feature used was deep_view which allowed us to access the deep_view of exec functions and call spec functions in exec mode when writing invariants, preconditions, poscondtions, and asserts. Additional ensures statements were used to help the verifier understand that the deep_view call could be before or after accessing fields of dat types and also reasoning that the exec versions and spec versions functioned the same way. here's an example:

    exec version:

    pub fn wf(self) -> (res: bool)
        ensures
            res <==> self.deep_view().spec_wf(),
    {
      //using flag to check if all elements in the body are well formed
        let mut flag = true;
        assert(forall|k: int|
            0 <= k < self.rs.len() ==> (#[trigger] self.rs[k].deep_view())
                == self.deep_view().rs[k]);
        for i in 0..self.rs.len()
            invariant
                0 <= i <= self.rs.len(),
                //invariant forall checks all body elements if they are well formed using deep_view
                flag <==> forall|j: int| #![auto] 0 <= j < i ==> self.rs[j].deep_view().spec_wf(),
        {
            flag = self.rs[i].wf() && flag
        }
        flag
    }

    spec version:

    pub open spec fn spec_wf(self) -> bool {
        forall|i: int| #![auto] 0 <= i < self.rs.len() ==> self.rs[i].spec_wf()
    }




TmpStringHashMap was another Verus specific feature in the implementation of the kernel. Developed by Jay Lorch, the StringHashMap data structure was introduced to the vstd library for Verus. Our team utilized addtional functions such as deep_view and partial_eq for StringHashMap, so the attached file in the repository is the version that incldues that functions that are used.

## Missing features



## Toy Example of kernel working

## Future work

## We still need to: 1. Add support for builtinops 2. Make ghost versions for proof 3. Make examples meet all postcondtions and preconstions 4. Port trace reconstruction from Dafny to Verus
