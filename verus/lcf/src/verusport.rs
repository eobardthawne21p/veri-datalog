

// We should be able to not need this, but left this here just in case. Using vstd::std_specs::result
//code is below after verus macro
/* datatype Result<A> = Ok(val : A) | Err {
  predicate IsFailure() { this.Err? }
  fn PropagateFailure() : Result<A>
    requires IsFailure() {
    Err
  }
  fn Extract() : A
    requires !IsFailure() {
    val
  }
} */



//#[allow(inconsistent_fields)]
//use vstd::std_specs::result;
use vstd::prelude::*;
use crate::string_hash_map::StringHashMap;
use vstd::seq::Seq;
use vstd::std_specs::result;



verus! {

/* enum Result<A> {
    Ok { val: A },
    Err,
}

impl<A> Result<A> {
    
    spec fn IsFailure(&self) -> bool {
        matches!(self, Result::Err {err})
    }

    
    fn PropagateFailure(&self) -> Result<A> 
        requires self.IsFailure()
    {
        Result::Err 
    }                                         // use vstd::std_specs::result instead
                                              // code is here just in case

    
    fn Extract(&self) -> &A 
        requires !self.IsFailure()
    {
      match self {
        Result::Ok { val } => val,
        Result::Err => Err,
    } 
    }
  } */

  // enum Const declaration
  pub enum Const {
    Atom (String),
    Nat (u64), 
    Str (String),
    List (Vec<Const>) // vector???
    } 

/* pub enum SpecConst {
  Atom (String),
  Nat (u64),            // waiting on conversion from vec to seq issue to be resolved
  Str (String),
  List (Seq<SpecConst>)
  } */

/* impl DeepView for Const {    // attmept at forcing vec units into seq
  type V = SpecConst;

  open spec fn deep_view(&self) -> Self::V {
    match self {
      Const::Atom(s) => SpecConst::Atom(*s), 
      Const::Nat(n) => SpecConst::Nat(*n),
      Const::Str(s) => SpecConst::Str(*s),
      Const::List(vec) => SpecConst::List(vec.deep_view()),
        
        /* let mut seq = Seq::<SpecConst>::empty();
        for i in 0..vec.len() {
            seq = seq.push(vec[i as int].deep_view());
        }

        SpecConst::List(seq) */
    
      
    }
  }
} */

  // Subst using StringHashMap from string_hash_map crate
  type Subst = StringHashMap<Const>;
  
  /* 
  predicate compatible_subst(s : Subst, t : Subst) {
    forall v :: v in s.Keys && v in t.Keys ==> s[v] == t[v]
  }
*/
spec fn compatible_subst(s : Subst, t : Subst) -> bool
{
  forall|v: String| s.view()[v.view()] == t.view()[v.view()]
}
  

  fn main(){

  }
}  

    



